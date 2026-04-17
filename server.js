require('dotenv').config();
const express  = require('express');
const multer   = require('multer');
const cors     = require('cors');
const path     = require('path');
const fs       = require('fs');
const { execSync, spawnSync, exec, spawn } = require('child_process');
const { promisify } = require('util');
const crypto = require('crypto');
const execAsync = promisify(exec);
const Anthropic = require('@anthropic-ai/sdk');
const OpenAI    = require('openai');
const fetch     = require('node-fetch');

const app  = express();
const PORT = process.env.PORT || 3000;

// ── Controle de concorrência (máx 5 análises simultâneas) ──
let analiseEmCurso = 0;
const MAX_ANALISES = 5;

// ── Rate Limiting: 1 análise por @ por semana + 2 por IP/fingerprint por semana ──
const RATE_LIMIT_SEMANAS_MS = 7 * 24 * 60 * 60 * 1000; // 7 dias
const RATE_LIMIT_IP_MAX     = 2; // análises por IP por semana
const RATE_LIMIT_FP_MAX     = 2; // análises por fingerprint por semana
const RATE_LIMIT_FILE       = path.join('/app/data', 'rate-limits.json');
const RATE_LIMIT_FILE_LOCAL = path.join(__dirname, 'data', 'rate-limits.json');

let rateLimits = { usernames: {}, ips: {}, fps: {}, erros: {} };

function getRateLimitFile() {
  // Usa volume do Railway se disponível, senão pasta local
  try {
    if (fs.existsSync('/app/data')) return RATE_LIMIT_FILE;
  } catch(e) {}
  try {
    fs.mkdirSync(path.join(__dirname, 'data'), { recursive: true });
    return RATE_LIMIT_FILE_LOCAL;
  } catch(e) {}
  return null;
}

function loadRateLimits() {
  const file = getRateLimitFile();
  if (!file) return;
  try {
    if (fs.existsSync(file)) {
      const loaded = JSON.parse(fs.readFileSync(file, 'utf8'));
      rateLimits = { usernames: {}, ips: {}, fps: {}, ...loaded };
    }
  } catch(e) {}
}

function saveRateLimits() {
  const file = getRateLimitFile();
  if (!file) return;
  try {
    fs.writeFileSync(file, JSON.stringify(rateLimits, null, 2), 'utf8');
  } catch(e) {}
}

function limparExpirados() {
  const agora = Date.now();
  for (const k of Object.keys(rateLimits.usernames)) {
    if (agora - rateLimits.usernames[k] > RATE_LIMIT_SEMANAS_MS) {
      delete rateLimits.usernames[k];
      if (rateLimits.usernameCount) delete rateLimits.usernameCount[k];
      if (rateLimits.erros) delete rateLimits.erros[`user_${k}`];
    }
  }
  for (const ip of Object.keys(rateLimits.ips)) {
    rateLimits.ips[ip] = (rateLimits.ips[ip] || []).filter(t => agora - t < RATE_LIMIT_SEMANAS_MS);
    if (rateLimits.ips[ip].length === 0) delete rateLimits.ips[ip];
  }
  if (!rateLimits.fps) rateLimits.fps = {};
  for (const fp of Object.keys(rateLimits.fps)) {
    rateLimits.fps[fp] = (rateLimits.fps[fp] || []).filter(t => agora - t < RATE_LIMIT_SEMANAS_MS);
    if (rateLimits.fps[fp].length === 0) delete rateLimits.fps[fp];
  }
  if (!rateLimits.erros) rateLimits.erros = {};
  for (const k of Object.keys(rateLimits.erros)) {
    rateLimits.erros[k] = (rateLimits.erros[k] || []).filter(t => agora - t < RATE_LIMIT_SEMANAS_MS);
    if (rateLimits.erros[k].length === 0) delete rateLimits.erros[k];
  }
}

function checkRateLimit(arroba, ip, fp) {
  limparExpirados();
  const agora = Date.now();
  const username = arroba.toLowerCase().replace('@', '');

  if (!rateLimits.erros) rateLimits.erros = {};

  // Limita apenas pelo @arroba — cada perfil do Instagram pode ser analisado 2x por semana
  const usernameUltima = rateLimits.usernames[username];
  if (usernameUltima) {
    const usernameErros = (rateLimits.erros[`user_${username}`] || []).length;
    const usernameTotal = (rateLimits.usernameCount?.[username] || 1);
    const usernameSucesso = Math.max(0, usernameTotal - usernameErros);
    if (usernameSucesso >= RATE_LIMIT_IP_MAX) {
      const diasRestantes = Math.ceil((RATE_LIMIT_SEMANAS_MS - (agora - usernameUltima)) / (24 * 60 * 60 * 1000));
      return { bloqueado: true, motivo: `O perfil @${username} já foi analisado ${RATE_LIMIT_IP_MAX}x esta semana. Tente novamente em ${diasRestantes} dia${diasRestantes > 1 ? 's' : ''}.` };
    }
  }

  return { bloqueado: false };
}

function registrarAnalise(arroba, ip, fp) {
  const username = arroba.toLowerCase().replace('@', '');
  rateLimits.usernames[username] = Date.now();
  if (!rateLimits.usernameCount) rateLimits.usernameCount = {};
  rateLimits.usernameCount[username] = (rateLimits.usernameCount[username] || 0) + 1;
  saveRateLimits();
}

// Registra tentativa com erro — desconta do contador do username
function registrarErro(ip, fp, arroba) {
  if (!rateLimits.erros) rateLimits.erros = {};
  const username = arroba ? arroba.toLowerCase().replace('@', '') : null;
  if (username) {
    const key = `user_${username}`;
    if (!rateLimits.erros[key]) rateLimits.erros[key] = [];
    rateLimits.erros[key].push(Date.now());
  }
  saveRateLimits();
}

// Carrega limites ao iniciar
loadRateLimits();

// ── Sanitiza texto para evitar JSON inválido ─────────────────
// Cobre todos os casos que quebram JSON na API da Claude/Anthropic:
//   1. Null bytes (\u0000)
//   2. Caracteres de controle (exceto \t \n \r)
//   3. Surrogates solitários (\uD800-\uDFFF sem par) — emojis corrompidos do Instagram
function sanitizeText(text) {
  if (!text) return '';
  return String(text)
    .replace(/\u0000/g, '')                            // null bytes
    .replace(/[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]/g, '') // control chars (preserva \t \n \r)
    .replace(/[\uD800-\uDFFF]/g, '')                   // surrogates solitários
    .trim();
}

// ── Cache de virais por nicho (24h) ──────────────────────────
const VIRAIS_CACHE_TTL = 72 * 60 * 60 * 1000; // 72 horas (era 24h)
const VIRAIS_CACHE_FILE = path.join('/tmp', 'virais-cache.json');

// Cache em arquivo — sobrevive a restarts normais do Railway
let viraisCache = {};
try {
  if (fs.existsSync(VIRAIS_CACHE_FILE)) {
    viraisCache = JSON.parse(fs.readFileSync(VIRAIS_CACHE_FILE, 'utf8'));
  }
} catch(e) { viraisCache = {}; }

function normalizarNicho(nicho) {
  return nicho.toLowerCase().trim()
    .normalize('NFD').replace(/[\u0300-\u036f]/g, '') // remove acentos
    .replace(/\s+/g, '_');
}

function getViraisCache(nicho) {
  const key = normalizarNicho(nicho);
  const entry = viraisCache[key];
  if (entry && Date.now() - entry.ts < VIRAIS_CACHE_TTL) return entry.data;
  return null;
}

function setViraisCache(nicho, data) {
  const key = normalizarNicho(nicho);
  viraisCache[key] = { data, ts: Date.now() };
  try { fs.writeFileSync(VIRAIS_CACHE_FILE, JSON.stringify(viraisCache)); } catch(e) {}
}

app.use(cors({ origin: '*' }));
app.use(express.json({ limit: '50mb' }));

// ── Redireciona domínio Render → Railway ───────────────────
app.use((req, res, next) => {
  const host = req.headers.host || '';
  if (host.includes('onrender.com')) {
    return res.redirect(301, 'https://hospitable-patience-production.up.railway.app' + req.originalUrl);
  }
  next();
});

app.use(express.static(path.join(__dirname, 'frontend')));

// ── Upload config ──────────────────────────────────────────
const storage = multer.diskStorage({
  destination: (req, file, cb) => {
    const dir = path.join(__dirname, 'uploads');
    if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
    cb(null, dir);
  },
  filename: (req, file, cb) => cb(null, `${Date.now()}-${file.originalname}`)
});
const upload = multer({ storage, limits: { fileSize: 50 * 1024 * 1024 } });

// ── Clientes IA ────────────────────────────────────────────
const anthropic = new Anthropic({ apiKey: process.env.ANTHROPIC_API_KEY });
const openai    = new OpenAI({ apiKey: process.env.OPENAI_API_KEY || '' });

// ══════════════════════════════════════════════════════════════
//  SUPERVISOR — Orquestra o Squad e reporta progresso
// ══════════════════════════════════════════════════════════════
//
//  Squad Engrene:
//   Scout      → Apify: métricas reais do perfil (seguidores, posts, legendas)
//   Downloader → yt-dlp: baixa o Reel via URL pública
//   Transcriber→ OpenAI Whisper API: transcreve áudio do Reel
//   Analyst    → Claude Haiku: análise profunda com todo o contexto
//
// ══════════════════════════════════════════════════════════════

class Supervisor {
  constructor(jobId) {
    this.jobId = jobId;
    this.log   = [];
  }

  info(agent, msg) {
    const entry = `[${agent.toUpperCase()}] ${msg}`;
    this.log.push(entry);
    console.log(`🔷 ${entry}`);
  }

  warn(agent, msg) {
    const entry = `[${agent.toUpperCase()}] ⚠️  ${msg}`;
    this.log.push(entry);
    console.warn(`🟡 ${entry}`);
  }

  err(agent, msg) {
    const entry = `[${agent.toUpperCase()}] ❌ ${msg}`;
    this.log.push(entry);
    console.error(`🔴 ${entry}`);
  }

  // Executa a pipeline completa e retorna o contexto consolidado
  async run({ arroba, nicho, reelUrl, reelLegenda }) {
    this.info('supervisor', `Pipeline iniciada — @${arroba} | nicho: ${nicho}`);

    const results = {
      perfilApify:    null,
      perfilFallback: null,
      imagensPosts:   [],
      transcricao:    null,
      conteudosVirais: '',
    };

    // ── Executa Scout + Download + Hashtag em PARALELO ───────
    const [scoutResult, downloadResult, hashtagResult] = await Promise.allSettled([
      arroba ? agentScout(arroba, this) : Promise.resolve(null),
      reelUrl ? agentDownloader(reelUrl, this) : Promise.resolve(null),
      (process.env.APIFY_TOKEN && nicho) ? agentHashtag(nicho, this).catch(e => {
        this.warn('supervisor', `Hashtag ignorado: ${e.message}`); return '';
      }) : Promise.resolve(''),
    ]);

    // Consolida resultados paralelos
    results.perfilApify    = scoutResult.value ?? null;
    const videoPath        = downloadResult.value ?? null;
    results.conteudosVirais = hashtagResult.value ?? '';

    // Fallback para Instaloader se Scout falhou
    if (!results.perfilApify?.ok) {
      if (results.perfilApify?.erroTipo === 'private') {
        // Perfil detectado como privado — não tenta fallback
        this.warn('supervisor', `@${arroba} é privado — abortando análise`);
      } else {
        this.warn('supervisor', 'Scout falhou — usando Instaloader como fallback');
        results.perfilFallback = await agentInstaloader(arroba, this);
      }
    }

    // ── Imager: baixa imagens dos posts (depende do Scout) ───
    const perfilOk = results.perfilApify?.ok ? results.perfilApify : null;
    if (perfilOk?.posts?.length > 0) {
      results.imagensPosts = await agentImager(perfilOk.posts, this);
    }

    // ── Transcriber: depende do download ────────────────────
    if (videoPath) {
      results.transcricao = await agentTranscriber(videoPath, this);
      try { fs.unlinkSync(videoPath); } catch(e) {}
    }

    this.info('supervisor', `Pipeline concluída — passando para Analyst (Haiku)`);
    return results;
  }
}

// ══════════════════════════════════════════════════════════════
//  AGENT: SCOUT — busca dados reais do Instagram
//  Estratégia em camadas:
//   1. Apify (se token disponível e não esgotado)
//   2. Instagram API pública (web_profile_info) — sem autenticação
//   3. Falha com erro explícito (não inventa dados)
// ══════════════════════════════════════════════════════════════
async function agentScout(username, sv) {
  sv.info('scout', `Buscando perfil @${username}...`);
  let erroTipo = null;

  // ── Tentativa 1: Apify ─────────────────────────────────────
  if (process.env.APIFY_TOKEN) {
    try {
      const url = `https://api.apify.com/v2/acts/apify~instagram-profile-scraper/run-sync-get-dataset-items` +
                  `?token=${process.env.APIFY_TOKEN}&timeout=60&memory=128`;

      const resp = await fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ usernames: [username], resultsLimit: 9, proxy: { useApifyProxy: true } }),
        timeout: 70000
      });

      if (resp.ok) {
        const items = await resp.json();
        if (Array.isArray(items) && items.length > 0) {
          const p = items[0];
          if (p.isPrivate) {
            sv.warn('scout', `@${p.username} é privado (Apify) — não é possível analisar`);
            erroTipo = 'private';
          } else {
          sv.info('scout', `✅ Apify — @${p.username} | ${p.followersCount} seguidores`);
          return normalizarPerfil('apify', p, (p.latestPosts || []).slice(0, 9).map(post => ({
            tipo:        post.type || 'GraphImage',
            legenda:     (post.caption || '').substring(0, 300),
            curtidas:    post.likesCount    || 0,
            comentarios: post.commentsCount || 0,
            views:       post.videoViewCount || 0,
            is_video:    post.type === 'Video' || post.type === 'GraphVideo',
            shortcode:   post.shortCode  || '',
            imagem_url:  post.displayUrl || '',
            video_url:   post.videoUrl   || '',
            timestamp:   post.timestamp  || post.takenAt || null
          })));
          }
        }
      } else {
        const body = await resp.json().catch(() => ({}));
        sv.warn('scout', `Apify HTTP ${resp.status}: ${body?.error?.message || ''}`);
      }
    } catch(e) {
      sv.warn('scout', `Apify erro: ${e.message}`);
    }
  }

  // ── Tentativa 2: Instagram Web API pública (sem login) ───
  try {
    sv.info('scout', 'Apify indisponível — tentando Instagram Web API...');
    const igResp = await fetch(
      `https://www.instagram.com/api/v1/users/web_profile_info/?username=${encodeURIComponent(username)}`,
      {
        headers: {
          'X-IG-App-ID': '936619743392459',
          'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
          'Accept': '*/*',
          'Accept-Language': 'pt-BR,pt;q=0.9',
          'Referer': 'https://www.instagram.com/',
        },
        signal: AbortSignal.timeout(15000)
      }
    );

    if (igResp.ok) {
      const json = await igResp.json();
      const u = json?.data?.user;
      if (u && u.id) {
        if (u.is_private) {
          sv.warn('scout', `@${username} é privado — não é possível analisar`);
          erroTipo = 'private';
        } else {
          sv.info('scout', `✅ Instagram Web API — @${u.username} | ${u.edge_followed_by?.count} seguidores`);

          const edges = u.edge_owner_to_timeline_media?.edges || [];
          const posts = edges.slice(0, 9).map(e => {
            const n = e.node;
            return {
              tipo:        n.__typename || 'GraphImage',
              legenda:     (n.edge_media_to_caption?.edges?.[0]?.node?.text || '').substring(0, 300),
              curtidas:    n.edge_liked_by?.count || n.edge_media_preview_like?.count || 0,
              comentarios: n.edge_media_to_comment?.count || 0,
              views:       n.video_view_count || 0,
              is_video:    n.is_video || false,
              shortcode:   n.shortcode || '',
              imagem_url:  n.display_url || '',
              video_url:   n.video_url   || '',
              timestamp:   n.taken_at_timestamp ? new Date(n.taken_at_timestamp * 1000).toISOString() : null
            };
          });

          return normalizarPerfil('instagram_web', {
            username:             u.username,
            fullName:             u.full_name,
            biography:            u.biography,
            externalUrl:          u.external_url,
            followersCount:       u.edge_followed_by?.count || 0,
            followsCount:         u.edge_follow?.count || 0,
            postsCount:           u.edge_owner_to_timeline_media?.count || 0,
            isBusinessAccount:    u.is_business_account || false,
            businessCategoryName: u.category_name || '',
            verified:             u.is_verified || false,
            profilePicUrl:        u.profile_pic_url || '',
          }, posts);
        }
      }
    } else {
      sv.warn('scout', `Instagram Web API HTTP ${igResp.status}`);
    }
  } catch(e) {
    sv.warn('scout', `Instagram Web API erro: ${e.message}`);
  }

  // ── Tentativa 3: instagrapi com login ────────────────────
  if (process.env.IG_USERNAME && process.env.IG_PASSWORD) {
    sv.info('scout', 'Tentando instagrapi (conta IG configurada)...');
    const resultado = await agentInstagrapiLogin(username, sv);
    if (resultado) return resultado;
  } else {
    sv.warn('scout', 'IG_USERNAME/IG_PASSWORD não configurados');
  }

  sv.err('scout', 'Todas as fontes falharam.');
  return erroTipo ? { ok: false, erroTipo } : null;
}

function normalizarPerfil(fonte, p, posts) {
  return {
    ok:          true,
    fonte,
    username:    p.username     || '',
    nome:        p.fullName     || '',
    bio:         p.biography    || '',
    link_bio:    p.externalUrl  || '',
    seguidores:  p.followersCount || 0,
    seguindo:    p.followsCount   || 0,
    posts_count: p.postsCount     || 0,
    is_business: p.isBusinessAccount || false,
    categoria:   p.businessCategoryName || '',
    verificado:  p.verified || false,
    foto_perfil: p.profilePicUrl || '',
    posts
  };
}

// ── instagrapi com login (fallback quando Apify esgotado) ──
async function agentInstagrapiLogin(username, sv) {
  const script = `
import json, sys
try:
    from instagrapi import Client
    import os

    session_file = '/tmp/ig_session_${Date.now() % 10000}.json'
    cl = Client()
    cl.login(os.environ['IG_USERNAME'], os.environ['IG_PASSWORD'])

    user = cl.user_info_by_username(${JSON.stringify(username)})
    uid  = user.pk

    medias = cl.user_medias(uid, amount=9)
    posts = []
    for m in medias:
        posts.append({
            "tipo":        m.media_type == 2 and "GraphVideo" or "GraphImage",
            "legenda":     (m.caption_text or "")[:300],
            "curtidas":    m.like_count or 0,
            "comentarios": m.comment_count or 0,
            "views":       m.view_count or 0,
            "is_video":    m.media_type == 2,
            "shortcode":   m.code or "",
            "imagem_url":  str(m.thumbnail_url or m.image_versions2 and m.image_versions2.candidates and m.image_versions2.candidates[0].url or ""),
            "video_url":   str(m.video_url or "")
        })

    print(json.dumps({
        "ok": True, "fonte": "instagrapi",
        "username":    user.username,
        "fullName":    user.full_name,
        "biography":   user.biography or "",
        "externalUrl": str(user.external_url or ""),
        "followersCount":      user.follower_count,
        "followsCount":        user.following_count,
        "postsCount":          user.media_count,
        "isBusinessAccount":   user.is_business,
        "businessCategoryName":user.category or "",
        "verified":            user.is_verified,
        "profilePicUrl":       str(user.profile_pic_url or ""),
        "posts": posts
    }, ensure_ascii=False))
except Exception as e:
    print(json.dumps({"ok": False, "err": str(e)}, ensure_ascii=False))
`;

  try {
    const env = { ...process.env };
    const stdout = await new Promise((resolve, reject) => {
      const proc = spawn('python3', ['-c', script], { env });
      let out = '', err = '';
      const timer = setTimeout(() => { proc.kill(); reject(new Error('Timeout instagrapi 60s')); }, 60000);
      proc.stdout.on('data', d => out += d);
      proc.stderr.on('data', d => err += d);
      proc.on('close', () => { clearTimeout(timer); resolve(out.trim()); });
      proc.on('error', e => { clearTimeout(timer); reject(e); });
    });

    if (!stdout) {
      sv.err('scout', 'instagrapi sem saída');
      return null;
    }

    const data = JSON.parse(stdout);
    if (!data.ok) {
      sv.err('scout', `instagrapi erro: ${data.err}`);
      return null;
    }

    sv.info('scout', `✅ instagrapi — @${data.username} | ${data.followersCount} seguidores`);
    return normalizarPerfil('instagrapi', data, data.posts || []);

  } catch(e) {
    sv.err('scout', `instagrapi exceção: ${e.message}`);
    return null;
  }
}

// ══════════════════════════════════════════════════════════════
//  AGENT: INSTALOADER FALLBACK — scraping local via Python
// ══════════════════════════════════════════════════════════════
async function agentInstaloader(username, sv) {
  sv.info('instaloader', `Tentando Instaloader para @${username}...`);

  const script = `
import instaloader, json, sys
L = instaloader.Instaloader(
    download_pictures=False, download_videos=False,
    download_comments=False, save_metadata=False, quiet=True,
    max_connection_attempts=1
)
ig_user = ${process.env.IG_USERNAME ? `"${process.env.IG_USERNAME}"` : 'None'}
ig_pass = ${process.env.IG_PASSWORD ? `"${process.env.IG_PASSWORD}"` : 'None'}
if ig_user and ig_pass:
    try: L.login(ig_user, ig_pass)
    except: pass
try:
    profile = instaloader.Profile.from_username(L.context, "${username}")
    posts_data = []
    count = 0
    for post in profile.get_posts():
        if count >= 9: break
        posts_data.append({
            "tipo": post.typename,
            "legenda": post.caption[:300] if post.caption else "",
            "curtidas": post.likes,
            "comentarios": post.comments,
            "views": post.video_view_count if post.is_video else 0,
            "is_video": post.is_video,
            "shortcode": post.shortcode
        })
        count += 1
    print(json.dumps({
        "ok": True, "fonte": "instaloader",
        "username": profile.username,
        "nome": profile.full_name,
        "bio": profile.biography,
        "link_bio": profile.external_url or "",
        "seguidores": profile.followers,
        "seguindo": profile.followees,
        "posts_count": profile.mediacount,
        "is_business": profile.is_business_account,
        "categoria": profile.business_category_name or "",
        "posts": posts_data
    }, ensure_ascii=False))
except Exception as e:
    print(json.dumps({"ok": False, "err": str(e)}, ensure_ascii=False))
`;

  try {
    const out = await new Promise((resolve, reject) => {
      const proc = spawn('python3', ['-c', script], { env: process.env });
      let stdout = '', stderr = '';
      const timer = setTimeout(() => { proc.kill(); reject(new Error('Timeout instaloader 25s')); }, 25000);
      proc.stdout.on('data', d => stdout += d);
      proc.stderr.on('data', d => stderr += d);
      proc.on('close', () => { clearTimeout(timer); resolve(stdout.trim()); });
      proc.on('error', e => { clearTimeout(timer); reject(e); });
    });
    if (out) {
      const data = JSON.parse(out);
      if (data.ok) sv.info('instaloader', `✅ @${data.username} — ${data.seguidores} seguidores`);
      else sv.warn('instaloader', data.err || 'erro desconhecido');
      return data;
    }
    sv.err('instaloader', 'sem output');
    return { ok: false };
  } catch(e) {
    sv.err('instaloader', e.message);
    return { ok: false };
  }
}

// ══════════════════════════════════════════════════════════════
//  AGENT: DOWNLOADER — yt-dlp baixa o Reel via URL pública
// ══════════════════════════════════════════════════════════════
async function agentDownloader(reelUrl, sv) {
  sv.info('downloader', `Baixando Reel: ${reelUrl}`);

  const tmpPath = `/tmp/reel_${crypto.randomUUID()}.mp4`;
  const ytdlp   = '/home/roberto/.local/bin/yt-dlp';

  try {
    // Usa spawn com array — previne shell injection via URL maliciosa
    await new Promise((resolve, reject) => {
      const proc = spawn(ytdlp, [
        '-o', tmpPath, '--no-playlist', '--max-filesize', '50m',
        '--merge-output-format', 'mp4',
        '-f', 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]/best',
        reelUrl
      ]);
      const timer = setTimeout(() => { proc.kill(); reject(new Error('Timeout yt-dlp 60s')); }, 60000);
      proc.on('close', code => { clearTimeout(timer); code === 0 ? resolve() : reject(new Error(`yt-dlp exit ${code}`)); });
      proc.on('error', e => { clearTimeout(timer); reject(e); });
    });

    if (fs.existsSync(tmpPath)) {
      const sizeMB = (fs.statSync(tmpPath).size / 1024 / 1024).toFixed(1);
      sv.info('downloader', `✅ Reel baixado — ${sizeMB}MB`);
      return tmpPath;
    }
    sv.warn('downloader', 'Arquivo não criado');
    return null;
  } catch(e) {
    sv.err('downloader', `yt-dlp falhou: ${e.message?.substring(0, 150)}`);
    return null;
  }
}

// ══════════════════════════════════════════════════════════════
//  AGENT: TRANSCRIBER — OpenAI Whisper API transcreve o Reel
// ══════════════════════════════════════════════════════════════
async function agentTranscriber(videoPath, sv) {
  if (!process.env.OPENAI_API_KEY) {
    sv.warn('transcriber', 'OPENAI_API_KEY não configurado — usando Whisper local como fallback');
    return agentWhisperLocal(videoPath, sv);
  }

  sv.info('transcriber', 'Transcrevendo áudio via OpenAI Whisper API...');

  const audioPath = videoPath.replace('.mp4', `.${crypto.randomUUID()}.mp3`);
  try {
    // Extrai apenas o áudio para reduzir tamanho no upload
    await execAsync(`ffmpeg -i "${videoPath}" -q:a 0 -map a "${audioPath}" -y 2>/dev/null`, { timeout: 30000 });

    const audioFile = fs.createReadStream(fs.existsSync(audioPath) ? audioPath : videoPath);

    const transcription = await openai.audio.transcriptions.create({
      file:     audioFile,
      model:    'whisper-1',
      language: 'pt',
      response_format: 'text'
    });

    const texto = typeof transcription === 'string' ? transcription : transcription?.text || '';
    sv.info('transcriber', `✅ Transcrição concluída — ${texto.split(' ').length} palavras`);
    return texto;

  } catch(e) {
    sv.err('transcriber', `Whisper API falhou: ${e.message}`);
    sv.info('transcriber', 'Tentando Whisper local como fallback...');
    return agentWhisperLocal(videoPath, sv);
  } finally {
    // Garante limpeza do áudio mesmo em caso de erro
    try { if (fs.existsSync(audioPath)) fs.unlinkSync(audioPath); } catch(e) {}
  }
}

// Fallback: Whisper local (mais lento, sem custo)
async function agentWhisperLocal(videoPath, sv) {
  try {
    sv.info('transcriber-local', 'Rodando Whisper local (model=small)...');
    const outDir = '/tmp';
    await execAsync(
      `whisper "${videoPath}" --language Portuguese --model small ` +
      `--output_format txt --output_dir "${outDir}" 2>/dev/null`,
      { timeout: 120000 }
    );
    const txtPath = path.join(outDir, path.basename(videoPath, '.mp4') + '.txt');
    if (fs.existsSync(txtPath)) {
      const texto = fs.readFileSync(txtPath, 'utf-8').trim();
      try { fs.unlinkSync(txtPath); } catch(e) {}
      sv.info('transcriber-local', `✅ ${texto.split(' ').length} palavras`);
      return texto;
    }
    return null;
  } catch(e) {
    sv.err('transcriber-local', e.message);
    return null;
  }
}

// ══════════════════════════════════════════════════════════════
//  AGENT: IMAGER — Baixa imagens dos posts via URL do CDN
//  Retorna array de buffers base64 prontos para Claude Vision
// ══════════════════════════════════════════════════════════════
async function agentImager(posts, sv) {
  const fetch = require('node-fetch');
  const imagensBase64 = [];

  // Pega até 6 posts com imagem
  const comImagem = posts.filter(p => p.imagem_url).slice(0, 6);
  sv.info('imager', `Baixando ${comImagem.length} imagens dos posts...`);

  for (const post of comImagem) {
    try {
      const resp = await fetch(post.imagem_url, {
        timeout: 15000,
        headers: { 'User-Agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 16_0 like Mac OS X) AppleWebKit/605.1.15' }
      });
      if (!resp.ok) continue;
      const buf    = await resp.buffer();
      const base64 = buf.toString('base64');
      const mime   = resp.headers.get('content-type') || 'image/jpeg';
      imagensBase64.push({ base64, mime, legenda: post.legenda, curtidas: post.curtidas, views: post.views });
    } catch(e) {
      sv.warn('imager', `Falhou imagem: ${e.message?.substring(0,60)}`);
    }
  }

  sv.info('imager', `✅ ${imagensBase64.length} imagens baixadas`);
  return imagensBase64;
}

// ══════════════════════════════════════════════════════════════
//  AGENT: HASHTAG — Apify busca conteúdos virais do nicho
// ══════════════════════════════════════════════════════════════
async function agentHashtag(nicho, sv) {

  const mapaHashtags = {
    'salão': ['salaobeleza', 'cabeleireiro'],
    'beleza': ['salaobeleza', 'cabeleireiro'],
    'manicure': ['manicure', 'naildesigner'],
    'nail': ['naildesigner', 'unhasdecoradas'],
    'sobrancelha': ['designdesobrancelha', 'sobrancelhas'],
    'lash': ['lashdesigner', 'ciliosposticos'],
    'barbearia': ['barbearia', 'barbeiro'],
    'massagem': ['massagem', 'fisioterapia'],
    'fisioterapia': ['fisioterapia', 'massoterapia'],
    'confeitaria': ['confeitaria', 'bolosdecorados'],
    'doce': ['confeitaria', 'doces'],
    'padaria': ['padaria', 'padariaartesanal'],
    'café': ['cafeteria', 'cafe'],
    'cafe': ['cafeteria', 'cafe'],
    'restaurante': ['restaurante', 'gastronomia'],
    'alimentação': ['gastronomia', 'foodie'],
    'roupa': ['modafeminina', 'lojaderoupas'],
    'moda': ['modafeminina', 'moda'],
    'ótica': ['otica', 'oculosdesol'],
    'otica': ['otica', 'oculosdesol'],
    'joalheria': ['joias', 'joalheria'],
    'acessórios': ['acessorios', 'bijuterias'],
    'acessorios': ['acessorios', 'bijuterias'],
    'papelaria': ['papelaria', 'personalizados'],
    'presente': ['presentescriativos', 'lembrancinhas'],
    'artesanato': ['artesanato', 'feitoamao'],
    'handmade': ['feitoamao', 'artesanato'],
    'floricultura': ['floricultura', 'decoracao'],
    'decoração': ['decoracaodeinteriores', 'decoracao'],
    'decoracao': ['decoracaodeinteriores', 'decoracao'],
    'estética': ['estetica', 'skincare'],
    'estetica': ['estetica', 'skincare'],
    'pet': ['petshop', 'cachorros'],
    'farmácia': ['farmacia', 'suplementos'],
    'farmacia': ['farmacia', 'suplementos'],
    'suplemento': ['suplementos', 'fitness'],
    'academia': ['academia', 'fitness'],
    'nutrição': ['nutricao', 'alimentacaosaudavel'],
    'nutricao': ['nutricao', 'alimentacaosaudavel'],
    'médico': ['saude', 'medicina'],
    'medico': ['saude', 'medicina'],
    'dentista': ['odontologia', 'dentista'],
    'advogado': ['direito', 'advogado'],
    'contabilidade': ['contabilidade', 'contabilidadeempresarial'],
    'arquitetura': ['arquitetura', 'designdeinteriores'],
    'imobiliária': ['imobiliaria', 'corretorodeimoveis'],
    'imobiliaria': ['imobiliaria', 'corretorodeimoveis'],
    'corretor': ['corretorodeimoveis', 'imoveisabravenda'],
    'fotografia': ['fotografia', 'fotografo'],
    'escola': ['aulapresencial', 'escolaparticular'],
    'curso': ['cursopresencial', 'escolaprofissionalizante'],
    'organização': ['organizacaodeambientes', 'personalorganizer'],
    'organizacao': ['organizacaodeambientes', 'personalorganizer'],
    'organizer': ['personalorganizer', 'organizacaodeambientes'],
    'limpeza': ['limpezaresidencial', 'higienizacao'],
    'higienização': ['higienizacao', 'limpezaprofissional'],
    'higienizacao': ['higienizacao', 'limpezaprofissional'],
    'marketing': ['marketingdigital', 'socialmedia'],
    'social media': ['socialmedia', 'marketingdigital'],
    'buffet': ['buffet', 'festaseventos'],
    'evento': ['festaseventos', 'decoracaodeeventos'],
    'costura': ['costura', 'ateliedecostura'],
    'ateliê': ['ateliedecostura', 'costureira'],
    'atelie': ['ateliedecostura', 'costureira'],
    'calçado': ['calcados', 'tenis'],
    'calcado': ['calcados', 'tenis'],
    'sapato': ['calcados', 'sapatos'],
    'mercadinho': ['mercadinho', 'hortifruti'],
    'hortifruti': ['hortifruti', 'feiradebairro'],
    'bebida': ['drinks', 'coqueteis'],
    'drinks': ['drinks', 'bartender'],
    'bar': ['bar', 'barzinho'],
    'móveis': ['moveis', 'marcenaria'],
    'moveis': ['moveis', 'marcenaria'],
    'marcenaria': ['marcenaria', 'moveissobmedida'],
    'auto': ['esteticaautomotiva', 'carros'],
    'automotiv': ['esteticaautomotiva', 'lavagemdecarro'],
  };

  const nichoLower = nicho.toLowerCase();
  let hashtags = ['empreendedorismo', 'negocioslocais'];

  for (const [key, tags] of Object.entries(mapaHashtags)) {
    if (nichoLower.includes(key)) { hashtags = tags; break; }
  }

  // Verifica cache antes de chamar Apify
  const cached = getViraisCache(nicho);
  if (cached) {
    sv.info('hashtag', `✅ Virais do nicho "${nicho}" servidos do cache (24h)`);
    return cached;
  }

  sv.info('hashtag', `Buscando virais para #${hashtags[0]}...`);

  const url = `https://api.apify.com/v2/acts/apify~instagram-hashtag-scraper/run-sync-get-dataset-items` +
              `?token=${process.env.APIFY_TOKEN}&timeout=45&memory=128`;

  const resp = await fetch(url, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ hashtags: hashtags.slice(0, 1), resultsLimit: 5, proxy: { useApifyProxy: true } }),
    timeout: 55000
  });

  if (!resp.ok) return '';

  const items = await resp.json();
  if (!Array.isArray(items) || items.length === 0) return '';

  // Filtrar apenas posts dos últimos 90 dias
  const corte90dias = Date.now() - 90 * 24 * 60 * 60 * 1000;

  const resultado = items
    .filter(i => {
      if ((i.likesCount || 0) <= 50) return false;
      const ts = i.timestamp
        ? (typeof i.timestamp === 'number' ? i.timestamp * 1000 : new Date(i.timestamp).getTime())
        : null;
      if (ts && !isNaN(ts) && ts < corte90dias) return false;
      return true;
    })
    .sort((a, b) => {
      const ta = a.timestamp ? (typeof a.timestamp === 'number' ? a.timestamp : new Date(a.timestamp).getTime() / 1000) : 0;
      const tb = b.timestamp ? (typeof b.timestamp === 'number' ? b.timestamp : new Date(b.timestamp).getTime() / 1000) : 0;
      return tb - ta;
    })
    .slice(0, 5)
    .map(i => {
      const dataPost = i.timestamp
        ? new Date(typeof i.timestamp === 'number' ? i.timestamp * 1000 : i.timestamp)
            .toLocaleDateString('pt-BR', { month: 'short', year: 'numeric' })
        : '';
      return `- "${(i.caption || 'sem legenda').substring(0, 80)}..." | ❤️ ${i.likesCount} | 💬 ${i.commentsCount} | Tipo: ${i.type}${dataPost ? ` | 📅 ${dataPost}` : ''}`;
    })
    .join('\n');

  setViraisCache(nicho, resultado);
  sv.info('hashtag', `✅ ${items.length} posts virais encontrados para o nicho (cacheado por 24h)`);
  return resultado;
}

// ══════════════════════════════════════════════════════════════
//  AGENT: ANALYST — Claude Haiku — Análise Profunda
//  Sistema baseado no agente diagnostico-instagram.md
// ══════════════════════════════════════════════════════════════

const PROMPT_ANALYST = `Você é um Analista de Perfil Instagram especializado em negócios locais brasileiros. Você segue o Método Engrene, desenvolvido pela equipe da Suellen Warmling, baseado em 120+ análises reais de perfis de donas de negócios locais.

REGRAS ABSOLUTAS DE QUALIDADE:
❌ NUNCA invente dados, métricas ou informações que não estejam nos dados fornecidos
❌ NUNCA diga "Publique mais conteúdo", "Interaja com seus seguidores", "Use hashtags relevantes"
❌ NUNCA faça recomendações genéricas — seja ESPECÍFICO para ESTE nicho e ESTE perfil
✅ SEMPRE analise COM OS DADOS REAIS fornecidos — bio real, posts reais com números reais
✅ SEMPRE cite números exatos quando disponíveis: "Post de [tema] — [X] curtidas, [Y] comentários"
✅ SEMPRE conecte cada diagnóstico ao nicho específico
✅ SEMPRE entregue: O QUÊ + COMO + POR QUÊ funciona para ESSE negócio
✅ Se um dado não foi coletado, analise com o que existe — nunca invente

TOM OBRIGATÓRIO:
- Direto mas acolhedor. Use "a gente" (coletivo com a equipe Engrene).
- Simule a perspectiva do cliente: "Se eu tô chegando aqui agora..."
- Elogie antes de criticar. Seja específico, nunca vago.
- Frases de calibração: "A foto atrai, a legenda vende." | "O óbvio precisa ser dito." | "Vocês estão deixando dinheiro em cima da mesa." | "Pode fazer tudo maravilhosamente bem, mas se você fica 20 semanas sem postar, não adianta de nada."

BENCHMARKS DE REFERÊNCIA:
- Frequência mínima: 3 posts/semana (abaixo = algoritmo para de distribuir)
- Stories: ~10% da audiência, duram 24h — feed é permanente e atinge muito mais
- Perfis médios ativos: 5.000-8.000 views por vídeo
- 8.000 seguidores = >800 pessoas alcançadas por post. Abaixo = investigar shadow ban
- Link WhatsApp: wa.me/55+DDD+número (sem zero, sem redirecionador)
- Legenda ChatGPT detectável: verbos no imperativo (Descubra, Transforme, Crie), emojis no final das frases, travessão americano (—), linguagem genérica

EXECUTE A ANÁLISE SEGUINDO ESTA SEQUÊNCIA EXATA — 12 PASSOS:

PASSO 0: PRIMEIRA IMPRESSÃO (antes de ler qualquer texto)
Simule ser um cliente novo chegando ao perfil pela primeira vez. É possível identificar o nicho em menos de 3 segundos olhando para a grade de fotos e foto de perfil? O visual é coerente com o tipo de negócio? Passa sensação de profissionalismo ou amadorismo?
Classifique: APROVADO / ATENÇÃO / URGENTE
Benchmark: "Se eu tô chegando aqui agora, eu consigo entender em 3 segundos o que você faz?"

PASSO 1: NOME DE USUÁRIO (@)
Fácil de ler, escrever e encontrar? Sem underlines duplos, pontos combinados, caracteres desnecessários? Máximo ~25 caracteres?
Classifique: APROVADO / ATENÇÃO / URGENTE — se problema, diga exatamente o que mudar.

PASSO 2: NOME DE DESTAQUE
Contém nome + nicho + localização? São palavras-chave pesquisáveis? Gera confusão sobre o que a pessoa faz?
Classifique: APROVADO / ATENÇÃO / URGENTE — se problema, sugira o nome de destaque ideal.
Benchmark: "Nome, nicho e localização — tudo pesquisável na barra do Instagram."

PASSO 3: BIO (fórmula de 5 elementos)
1. Especialidade — o que faz, qual diferencial (claro para quem nunca ouviu falar)
2. Promessa — frase forte, NÃO genérica como "feito com amor"
3. Prova social — tempo de mercado, clientes atendidos, com número concreto
4. CTA — chamada para ação com verbo claro (Agende, Compre, Fale conosco)
5. Link — presente e funcional
TAMBÉM verifique nível de consciência: a bio pressupõe que o visitante já sabe o que você vende? Para nichos menos óbvios, a especialidade precisa ser mais explícita.
Classifique: APROVADO / ATENÇÃO / URGENTE — se problema, reescreva a bio usando a fórmula.

PASSO 4: LINK DA BIO
Funciona? Para onde leva? WhatsApp direto (wa.me/55+DDD+número sem zero) ou redirecionador (Bitly, Linktree) que demora >5 segundos?
Classifique: APROVADO / ATENÇÃO / URGENTE
Referência: "Tem pessoas que desistem de entrar em contato porque esses redirecionadores parecem cliques de vírus."

PASSO 5: FOTO DE PERFIL
SE a pessoa É a marca: rosto visível e bem enquadrado (mostrando ombros, não cortado no pescoço), fundo adequado, expressão de confiança, boa resolução.
SE é marca/loja: logomarca profissional, legível no formato circular pequeno.
EM AMBOS: NÃO deve ter endereço, telefone ou QR code na foto.
Classifique: APROVADO / ATENÇÃO / URGENTE

PASSO 6: STORIES
Tem stories ativos nas últimas 24h? Tem narrativa ou só foto de produto (previsível = mata retenção)? Variação de formato (bastidores, enquete, produto, processo)?
Classifique: APROVADO / ATENÇÃO / URGENTE — se ausente, diga o impacto.

PASSO 7: DESTAQUES
VISUAL: capinhas padronizadas na identidade visual? Títulos em texto (não só emojis)?
CONTEÚDO: separados por categoria relevante ao negócio? NÃO por datas comemorativas? Atualizados? Algum chamado "destaques" (é ignorado pelas pessoas)?
Classifique: APROVADO / ATENÇÃO / URGENTE — sugira categorias ideais para o nicho.

PASSO 8: POSTS FIXADOS
Estratégia dos 3 fixados:
1° = Apresentação/Tour (quem é, como funciona, tour pela loja se física)
2° = Diferencial/Catálogo (produtos/serviços com detalhes)
3° = Ação atual (flutuante — promoção, lançamento)
Capas dos fixados são explicativas sem precisar abrir? Vídeos com capa customizada (não cena aleatória)?
Classifique: APROVADO / ATENÇÃO / URGENTE

PASSO 9: ÚLTIMA PUBLICAÇÃO + QUALIDADE
Quando foi? Formato? Qualidade técnica (iluminação, nitidez, som)? Legenda presente e com qualidade? Título na capa se reel?
Detecte sinais de ChatGPT: verbos no imperativo, emojis no final das frases, travessão americano (—), linguagem genérica sem detalhes do produto.
Classifique: APROVADO / ATENÇÃO / URGENTE — benchmark: ideal a cada 2-3 dias.

PASSO 10: FEED GERAL
Frequência entre posts (3x/semana é o mínimo)? Engajamento proporcional aos seguidores? Identidade visual consistente? Equilíbrio de formatos? Humanização (a pessoa aparece) vs catálogo puro? Respostas a comentários?
Classifique: APROVADO / ATENÇÃO / URGENTE
Referência: "Catálogo geralmente a gente só olha. A gente não consome assim, engaja."

PASSO 11: ESPECÍFICO DO NICHO
Aplique as regras do nicho:
- Casa/Decoração: tour obrigatório se loja física (fixado 1), destaques por tipo (não por datas)
- Gastronomia/Confeitaria: cardápio indispensável — sabores, tamanhos, preços, porções
- Serviços: serviço em ação (não só bastidores), local/horários/valor, landing page recomendada
- Saúde/Estética: não presumir conhecimento (nível de consciência baixo), explicar o tratamento, cardápio de serviços
- Beleza: antes/depois como conteúdo principal, título na capa de reels, NUNCA só fotos do fornecedor
- Moda: provadores como formato campeão, legenda com tecido/tamanhos/cores/preço, responder TODOS os comentários
- Comércio: cardápio no feed (não só stories), fotos com iluminação, processo + resultado + preço
- Infoprodutos: bio com nicho claro e público definido, perfil público (nunca privado), prova social de resultados de clientes (depoimentos, prints, antes/depois de resultados), conteúdo educativo para aquecimento de audiência

CRITÉRIOS DE PONTUAÇÃO 0-10 (use estes critérios para atribuir nota a cada elemento):

primeira_impressao: 10=nicho identificável em <3s visual profissional | 7=nicho identificável na bio visual ok mas inconsistente | 3=nicho confuso visual amador | 0=impossível identificar nicho
nome_usuario: 10=fácil de ler escrever encontrar sem caracteres extras | 7=pequeno problema legível | 3=confuso longo muitos caracteres especiais | 0=ilegível
nome_destaque: 10=nome+nicho+localização presentes e pesquisáveis | 7=2 dos 3 elementos | 3=só nome pessoal | 0=vazio ou irrelevante
bio: 10=5/5 elementos(especialidade+promessa+prova social c/número+CTA c/verbo+link)+nível consciência correto | 8=4/5 | 6=3/5 | 3=2/5 | 0=vazia ou 1 elemento
link_bio: 10=wa.me direto funcional ou link direto site/catálogo | 7=funcional mas com redirecionador Bitly/Linktree | 3=quebrado desatualizado ou destino errado | 0=sem link
foto_perfil(pessoa é marca): 10=rosto visível bem enquadrado(ombros) fundo adequado expressão confiante | 7=rosto visível mas enquadramento ou fundo fracos | 3=cortada no pescoço casual demais ou cartão de visitas | 0=sem foto ou inadequada
foto_perfil(marca/loja): 10=logomarca profissional legível no formato circular | 7=logo presente mas pouco legível | 3=foto pessoal no lugar da logo | 0=sem foto
stories: 10=ativos com narrativa e variação de formatos | 7=ativos mas só foto de produto sem narrativa | 3=inativos há 24-48h | 0=sem stories há mais de 48h
destaques: 10=capinhas padronizadas categorias relevantes ao negócio atualizados conteúdo completo | 7=capinhas presentes mas categorias confusas ou desatualizadas | 3=sem capinhas desorganizados | 0=sem destaques ou com mais de 143 semanas sem atualização
fixados: 10=3 fixados estratégicos(apresentação+catálogo+ação atual) com capas explicativas | 7=1-2 fixados com alguma estratégia | 3=fixados sem estratégia ou capas confusas | 0=sem fixados
constancia: 10=3+ posts/semana consistente | 7=2 posts/semana | 3=1 post/semana ou esporádico | 0=parado há mais de 2 semanas
legendas: 10=detalhes completos do produto(material sabor tamanho preço)+diferencial+CTA+autêntica | 7=informativas mas sem CTA ou preço | 3=genéricas ou sinais de ChatGPT(imperativo+emojis no final+travessão americano) | 0=sem legenda
humanizacao: 10=pessoa aparece regularmente feed variado comentários respondidos | 7=aparece às vezes feed misto alguns comentários respondidos | 3=feed 100% catálogo aparições raras poucos comentários | 0=nunca aparece feed catálogo puro zero respostas

Regras de status por nota: 8-10=APROVADO ✅ | 4-7=ATENÇÃO ⚠️ | 0-3=URGENTE 🔴

OUTPUT — Gere o relatório NESTE FORMATO EXATO:

## 📊 DIAGNÓSTICO ENGRENE
### [Nome do Negócio] — @[arroba]
**Nicho:** [nicho] | **Seguidores:** [número coletado] | **Data:** [data de hoje]

---

## Resumo Executivo
[3-4 frases: estado geral do perfil, pontos mais críticos, potencial de melhoria]

---

## Análise por Elemento

| # | Elemento | Nota | Status | Diagnóstico em 1 frase |
|---|----------|------|--------|------------------------|
| 1 | Primeira impressão | X/10 | APROVADO/ATENÇÃO/URGENTE | [1 frase] |
| 2 | Nome de usuário (@) | X/10 | [status] | [1 frase] |
| 3 | Nome de destaque | X/10 | [status] | [1 frase] |
| 4 | Bio | X/10 | [status] | [1 frase] |
| 5 | Link da bio | X/10 | [status] | [1 frase] |
| 6 | Foto de perfil | X/10 | [status] | [1 frase] |
| 7 | Stories | X/10 | [status] | [1 frase] |
| 8 | Destaques | X/10 | [status] | [1 frase] |
| 9 | Posts fixados | X/10 | [status] | [1 frase] |
| 10 | Constância | X/10 | [status] | [1 frase] |
| 11 | Legendas | X/10 | [status] | [1 frase] |
| 12 | Humanização | X/10 | [status] | [1 frase] |

---

## Detalhamento — Elementos com ATENÇÃO ou URGENTE
[Para cada elemento que não passou: o que está errado, o que fazer, referência concreta do nicho]
[Aplique também as regras específicas do nicho informado, diagnosticando o que falta para ESTE negócio]

---

## 🔴 Top 3 Ações Prioritárias
1. **[Ação mais urgente]** — [o que fazer, como fazer, por que é o mais importante]
2. **[Segunda ação]** — [o que fazer, impacto esperado]
3. **[Melhoria de médio prazo]** — [o que fazer, resultado esperado]

---

## Bio Reescrita
**Bio atual:** [texto da bio coletada]
**Bio proposta:**
\`\`\`
[Nova bio: especialidade + promessa forte + prova social com número + CTA + link — máx 150 caracteres]
\`\`\`
*Por que funciona:* [o que foi otimizado]

---

## Nome de Destaque Sugerido
[Se precisar de ajuste: Nome + nicho + localização em formato pesquisável]

---

## Pontuação do Perfil
**[soma das notas]/120 pontos — [percentual]%**
- 96-120 pts (80%+) = ✅ Perfil Otimizado
- 54-95 pts (45-79%) = 🟡 Perfil em Construção
- 0-53 pts (abaixo de 45%) = 🔴 Perfil Crítico

---

## Próximo Passo — Engrene
Quer ter uma análise aprofundada feita por especialistas e aprender a aplicar cada melhoria?
**Conheça o Método Engrene:** [https://suellenwarmling.com.br/](https://suellenwarmling.com.br/)

---

CHECKLIST INTERNO (execute antes de entregar — NÃO mostre ao usuário):
[ ] A bio proposta tem no máximo 150 caracteres?
[ ] As ações prioritárias são executáveis em menos de 2 horas cada?
[ ] Os diagnósticos citam dados reais (números, bio real, posts reais)?
[ ] Nenhuma recomendação é genérica — todas são específicas para ESTE nicho?
[ ] A pontuação total (soma/120 e percentual) foi calculada corretamente?
Se não → corrija antes de entregar.`;

// ══════════════════════════════════════════════════════════════
//  ENDPOINT PRINCIPAL: POST /api/analisar
// ══════════════════════════════════════════════════════════════
app.post('/api/analisar', upload.fields([
  { name: 'print_bio',      maxCount: 1 },
  { name: 'print_insights', maxCount: 1 },
  { name: 'print_posts',    maxCount: 1 },
  { name: 'print_audiencia',maxCount: 1 },
]), async (req, res) => {

  // ── Limite de concorrência ───────────────────────────────
  if (analiseEmCurso >= MAX_ANALISES) {
    return res.status(429).json({ sucesso: false, erro: 'Muitas análises simultâneas. Aguarde um momento e tente novamente.' });
  }
  analiseEmCurso++;

  // Keepalive: envia \n a cada 20s para evitar timeout do proxy Nginx do Render
  // JSON.parse ignora whitespace no inicio, entao o cliente processa normalmente
  res.setHeader('Content-Type', 'application/json; charset=utf-8');
  res.setHeader('Transfer-Encoding', 'chunked');
  const keepAlive = setInterval(() => { try { res.write('\n'); } catch(e) {} }, 20000);

  const uploadedFiles = [];
  const jobId = `job_${Date.now()}`;
  const sv    = new Supervisor(jobId);

  try {
    const { nome, nicho, arroba, objetivo, seguidores, frequencia, descricao,
            nome_destaque, pessoa_e_a_marca, tem_loja_fisica, estrutura_perfil, qualidade_tecnica } = req.body;

    // ── Validação básica ────────────────────────────────────
    if (!nome?.trim() || !nicho?.trim() || !arroba?.trim()) {
      clearInterval(keepAlive);
      return res.end(JSON.stringify({ sucesso: false, erro: 'Nome, nicho e @ do Instagram são obrigatórios.' }));
    }

    // ── Rate Limiting ───────────────────────────────────────
    const clienteIP = req.headers['x-forwarded-for']?.split(',')[0]?.trim()
                   || req.socket?.remoteAddress
                   || 'unknown';
    const clienteFP = (req.body._dfp || '').toString().trim().slice(0, 20);
    const rl = checkRateLimit(arroba.trim(), clienteIP, clienteFP);
    if (rl.bloqueado) {
      clearInterval(keepAlive);
      analiseEmCurso--;
      return res.end(JSON.stringify({ sucesso: false, erro: rl.motivo }));
    }

    const reelUrl     = (req.body.reel_url     || '').trim();
    const reelLegenda = (req.body.reel_legenda || '').trim();

    sv.info('supervisor', `Novo job: ${nome} | @${arroba} | ${nicho}`);

    // ── Executa Squad em paralelo onde possível ─────────────
    const squadResultado = await sv.run({ arroba, nicho, reelUrl, reelLegenda });

    // ── Escolhe melhor fonte de dados do perfil ─────────────
    const perfilData = squadResultado.perfilApify?.ok
      ? squadResultado.perfilApify
      : squadResultado.perfilFallback?.ok
        ? squadResultado.perfilFallback
        : null;

    // ── Sem dados reais: erro claro ──────────────────────────
    if (!perfilData) {
      clearInterval(keepAlive);
      const isPrivate = squadResultado.perfilApify?.erroTipo === 'private';
      const erroMsg = isPrivate
        ? `O perfil @${arroba} está configurado como privado. Para analisar, deixe o perfil público e tente novamente.`
        : `Não conseguimos coletar os dados do perfil @${arroba}. Verifique se o @ está correto e se a conta é pública, depois tente novamente.`;
      return res.end(JSON.stringify({ sucesso: false, erro: erroMsg }));
    }

    // ── GAP D: nome_destaque automático via fullName do Apify ──
    const nomeDestaqueEfetivo = nome_destaque || perfilData?.nome || '';

    // ── GAP C: calcular frequência real via timestamps dos posts ─
    let frequenciaCalculada = '';
    const postsComData = (perfilData?.posts || []).filter(p => p.timestamp);
    if (postsComData.length >= 2) {
      const datas = postsComData.map(p => new Date(p.timestamp)).sort((a, b) => b - a);
      const diasEntrePosts = [];
      for (let i = 0; i < datas.length - 1; i++) {
        diasEntrePosts.push((datas[i] - datas[i+1]) / (1000 * 60 * 60 * 24));
      }
      const mediaIntervaloDias = diasEntrePosts.reduce((a, b) => a + b, 0) / diasEntrePosts.length;
      const diasDesdeUltimo = (Date.now() - datas[0]) / (1000 * 60 * 60 * 24);
      const postsUltimos30 = datas.filter(d => (Date.now() - d) / (1000 * 60 * 60 * 24) <= 30).length;
      frequenciaCalculada = `Intervalo médio entre posts: ${mediaIntervaloDias.toFixed(1)} dias | Posts nos últimos 30 dias: ${postsUltimos30} | Último post: há ${diasDesdeUltimo.toFixed(0)} dias`;
    }

    // ── Prepara imagens para o Analyst (Claude) ─────────────
    sv.info('analyst', 'Preparando contexto visual...');
    const imagensConteudo = [];

    // GAP B: foto de perfil — baixar e enviar ao Claude Vision
    if (perfilData?.foto_perfil) {
      try {
        const fotoPerfResp = await fetch(perfilData.foto_perfil, {
          timeout: 10000,
          headers: { 'User-Agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 16_0 like Mac OS X) AppleWebKit/605.1.15' }
        });
        if (fotoPerfResp.ok) {
          const buf = await fotoPerfResp.buffer();
          const mime = fotoPerfResp.headers.get('content-type') || 'image/jpeg';
          imagensConteudo.push({ type: 'text', text: '\n--- FOTO DE PERFIL (coletada automaticamente — use para avaliar enquadramento, expressão, profissionalismo) ---' });
          imagensConteudo.push({ type: 'image', source: { type: 'base64', media_type: mime, data: buf.toString('base64') } });
          sv.info('analyst', '✅ Foto de perfil incluída na análise visual');
        }
      } catch(e) {
        sv.warn('analyst', `Foto de perfil não carregada: ${e.message?.substring(0, 60)}`);
      }
    }

    // 1. Imagens automáticas baixadas do Apify (posts reais do perfil)
    if (squadResultado.imagensPosts?.length > 0) {
      imagensConteudo.push({ type: 'text', text: `\n--- IMAGENS REAIS DO FEED (${squadResultado.imagensPosts.length} posts baixados automaticamente) ---` });
      for (const [i, img] of squadResultado.imagensPosts.entries()) {
        imagensConteudo.push({ type: 'text', text: `\nPost ${i+1} — ❤️ ${img.curtidas} curtidas${img.views ? ` | 👁️ ${img.views} views` : ''} | Legenda: ${sanitizeText(img.legenda) || '(sem legenda)'}` });
        imagensConteudo.push({ type: 'image', source: { type: 'base64', media_type: img.mime, data: img.base64 } });
      }
    }

    // 2. Prints manuais enviados pelo usuário (complementam a análise)
    const printLabels = {
      print_bio:      'PRINT MANUAL — Bio do perfil',
      print_insights: 'PRINT MANUAL — Post adicional #1',
      print_posts:    'PRINT MANUAL — Post adicional #2',
      print_audiencia:'PRINT MANUAL — Post adicional #3'
    };
    for (const [fieldName, label] of Object.entries(printLabels)) {
      if (req.files?.[fieldName]) {
        const file = req.files[fieldName][0];
        uploadedFiles.push(file.path);
        const base64   = fs.readFileSync(file.path).toString('base64');
        const mimeType = file.mimetype || 'image/jpeg';
        imagensConteudo.push({ type: 'text', text: `\n--- ${label} ---` });
        imagensConteudo.push({ type: 'image', source: { type: 'base64', media_type: mimeType, data: base64 } });
      }
    }

    // ── Monta contexto consolidado para Analyst ─────────────
    let ctxPerfil = '';
    if (perfilData?.ok) {
      const fonte = perfilData.fonte === 'apify' ? 'Apify (dados reais)' : 'Instaloader';
      ctxPerfil = `
DADOS DO PERFIL @${arroba} [fonte: ${fonte}]:
- Nome: ${sanitizeText(perfilData.nome)}
- Bio: ${sanitizeText(perfilData.bio)}
- Link na bio: ${sanitizeText(perfilData.link_bio) || 'não informado'}
- Seguidores: ${perfilData.seguidores?.toLocaleString('pt-BR')}
- Seguindo: ${perfilData.seguindo?.toLocaleString('pt-BR')}
- Total de posts: ${perfilData.posts_count}
- Conta comercial: ${perfilData.is_business ? 'Sim' : 'Não'}
- Categoria: ${sanitizeText(perfilData.categoria) || 'não informada'}
- Verificado: ${perfilData.verificado ? 'Sim' : 'Não'}

ÚLTIMOS ${perfilData.posts?.length || 0} POSTS (dados reais coletados agora):
${(perfilData.posts || []).map((p, i) => {
  const dataStr = p.timestamp ? ` | 📅 ${new Date(p.timestamp).toLocaleDateString('pt-BR')}` : '';
  return `Post ${i+1} [${p.tipo}${p.is_video ? ' · Vídeo' : ''}] — ❤️ ${p.curtidas} | 💬 ${p.comentarios}${p.views ? ` | 👁️ ${p.views} views` : ''}${dataStr}\nLegenda: ${sanitizeText(p.legenda) || '(sem legenda)'}`;
}).join('\n\n')}
`;
    }

    let ctxReel = '';
    if (reelUrl) {
      ctxReel = `\nREEL ENVIADO PARA ANÁLISE:\nURL: ${reelUrl}\n`;
      if (squadResultado.transcricao) {
        ctxReel += `\nTRANSCRIÇÃO DO ÁUDIO (via Whisper):\n"${squadResultado.transcricao}"\n`;
      } else if (reelLegenda) {
        ctxReel += `\nLEGENDA/ROTEIRO (informado pelo usuário):\n"${reelLegenda}"\n`;
      }
    } else if (reelLegenda) {
      ctxReel = `\nROTEIRO/LEGENDA DO REEL:\n"${reelLegenda}"\n`;
    }

    const contextoCompleto = `
DADOS DO NEGÓCIO:
- Nome: ${nome}
- Nicho: ${nicho}
- Instagram: @${arroba}
- Objetivo principal: ${objetivo || 'não informado'}
- Seguidores declarados pelo usuário: ${seguidores || 'não informado'}
- Frequência de postagem declarada: ${frequencia || 'não informada'}
- Descrição do negócio: ${descricao || ''}

INFORMAÇÕES ESTRUTURAIS DO PERFIL:
- Nome de destaque (campo em negrito abaixo do @): ${nomeDestaqueEfetivo || 'não informado'}${!nome_destaque && perfilData?.nome ? ' [coletado automaticamente via fullName do perfil]' : ''}
- A pessoa É a marca (profissional liberal/prestador) ou tem marca/loja com identidade própria?: ${pessoa_e_a_marca || 'não informado'}
- Tem loja física?: ${tem_loja_fisica || 'não informado'}
- Qualidade técnica geral do conteúdo: ${qualidade_tecnica || 'não informada'}
${frequenciaCalculada ? `- Frequência real calculada via timestamps: ${frequenciaCalculada}` : ''}
${estrutura_perfil ? `- Stories, destaques e fixados (informado pelo usuário): ${estrutura_perfil}` : '- Stories, destaques e fixados: não informados pelo usuário — classifique como "Não verificado" e oriente a verificar manualmente'}

${ctxPerfil}
${ctxReel}
${squadResultado.conteudosVirais ? `\nCONTEÚDOS VIRAIS DO NICHO "${nicho}" (coletados agora via Apify):\n${squadResultado.conteudosVirais}` : ''}

INSTRUÇÃO: Execute os 12 passos do Método Engrene. Para os passos cujos dados não foram coletados automaticamente (stories, destaques, fixados), analise com base no que foi informado pelo usuário. Se não há dado algum sobre um elemento, classifique como "Não verificado" e oriente o que verificar manualmente.
`.trim();

    // ── Analyst: Claude Haiku — análise profunda ─────────────
    sv.info('analyst', `Chamando Claude Haiku para análise profunda...`);

    const response = await anthropic.messages.create({
      model: 'claude-haiku-4-5',
      max_tokens: 6000,
      system: [{ type: 'text', text: PROMPT_ANALYST, cache_control: { type: 'ephemeral' } }],
      messages: [{
        role: 'user',
        content: [
          { type: 'text', text: contextoCompleto },
          ...imagensConteudo,
          { type: 'text', text: '\nCom base em TODOS esses dados reais (perfil coletado automaticamente + prints + transcrição + virais do nicho), faça o diagnóstico completo conforme estrutura. Seja CIRÚRGICO e ESPECÍFICO — cite os números reais fornecidos.' }
        ]
      }],
    });

    const relatorio = response.content?.[0]?.text || '';
    const inputTokens  = response.usage?.input_tokens  || 0;
    const outputTokens = response.usage?.output_tokens || 0;
    const tokens = inputTokens + outputTokens;

    sv.info('analyst', `✅ Análise concluída — ${tokens} tokens (input: ${inputTokens} | output: ${outputTokens})`);

    // Limpa uploads
    uploadedFiles.forEach(f => { try { fs.unlinkSync(f); } catch(e) {} });

    // Só registra se a análise teve conteúdo real
    if (relatorio.length > 200) {
      registrarAnalise(arroba.trim(), clienteIP, clienteFP);
    }

    clearInterval(keepAlive);

    if (relatorio.length <= 200) {
      registrarErro(clienteIP, clienteFP, arroba.trim());
      res.end(JSON.stringify({ sucesso: false, erro: 'Análise não disponível — tente novamente.' }));
      return;
    }

    res.end(JSON.stringify({
      sucesso: true,
      relatorio,
      tokens_usados: tokens,
      squad_log: sv.log,
      fontes: {
        perfil:      perfilData?.fonte || 'não coletado',
        transcricao: squadResultado.transcricao ? 'whisper' : (reelLegenda ? 'manual' : 'não disponível'),
        virais:      squadResultado.conteudosVirais ? 'apify' : 'não coletado'
      }
    }));

  } catch (error) {
    clearInterval(keepAlive);
    uploadedFiles.forEach(f => { try { fs.unlinkSync(f); } catch(e) {} });
    sv.err('supervisor', error.message);
    registrarErro(clienteIP, clienteFP, arroba);
    res.end(JSON.stringify({ sucesso: false, erro: error.message }));
  } finally {
    analiseEmCurso--;
  }
});

// ══════════════════════════════════════════════════════════════
//  ENDPOINT FALLBACK: POST /api/analisar-manual
//  Aceita dados digitados pelo usuário quando scraping falha
// ══════════════════════════════════════════════════════════════
app.post('/api/analisar-manual', async (req, res) => {

  if (analiseEmCurso >= MAX_ANALISES) {
    return res.status(429).json({ sucesso: false, erro: 'Muitas análises simultâneas. Aguarde.' });
  }
  analiseEmCurso++;

  const jobId = `manual_${Date.now()}`;
  const sv    = new Supervisor(jobId);

  try {
    const {
      nome, nicho, arroba,
      objetivo, frequencia, descricao,
      seg_total,       // seguidores totais
      med_curtidas,    // média de curtidas por post
      med_comentarios, // média de comentários (opcional)
      bio_texto,       // texto da bio
      posts_descricao, // descrição livre dos últimos posts
      tipo_conta       // pessoal/comercial
    } = req.body;

    if (!nome?.trim() || !nicho?.trim() || !arroba?.trim()) {
      analiseEmCurso--;
      return res.status(400).json({ sucesso: false, erro: 'Nome, nicho e @ são obrigatórios.' });
    }

    // ── Rate Limiting (mesmo critério do endpoint principal) ──
    const clienteIP = req.headers['x-forwarded-for']?.split(',')[0]?.trim()
                   || req.socket?.remoteAddress
                   || 'unknown';
    const clienteFP = (req.body._dfp || '').toString().trim().slice(0, 20);
    const rl = checkRateLimit(arroba.trim(), clienteIP, clienteFP);
    if (rl.bloqueado) {
      analiseEmCurso--;
      return res.status(429).json({ sucesso: false, erro: rl.motivo });
    }

    sv.info('supervisor', `Análise manual: ${nome} | @${arroba} | ${nicho}`);

    // Contexto a partir dos dados manuais
    const seguidores = parseInt(seg_total) || 0;
    const curtidas   = parseInt(med_curtidas) || 0;
    const coments    = parseInt(med_comentarios) || 0;
    const taxaEng    = seguidores > 0 ? ((curtidas + coments) / seguidores * 100).toFixed(2) : '?';

    const contextoCompleto = `
DADOS DO NEGÓCIO:
- Nome: ${nome}
- Nicho: ${nicho}
- Instagram: @${arroba}
- Objetivo principal: ${objetivo || 'não informado'}
- Frequência de postagem: ${frequencia || 'não informada'}
- Descrição do negócio: ${descricao || ''}

DADOS DO PERFIL @${arroba} [fonte: informado pelo usuário]:
- Seguidores: ${seguidores.toLocaleString('pt-BR')}
- Bio: ${bio_texto || 'não informada'}
- Tipo de conta: ${tipo_conta || 'não informado'}

MÉTRICAS DOS POSTS (médias informadas pelo usuário):
- Média de curtidas por post: ${curtidas}
- Média de comentários por post: ${coments}
- Taxa de engajamento estimada: ${taxaEng}% (curtidas+comentários ÷ seguidores)

${posts_descricao ? `DESCRIÇÃO DOS ÚLTIMOS POSTS (informado pelo usuário):\n${posts_descricao}` : ''}

NOTA: Dados coletados manualmente pelo usuário durante o evento. Use exatamente esses números na análise.
`.trim();

    sv.info('analyst', 'Chamando Claude Haiku para análise (modo manual)...');

    // Tenta também buscar virais do nicho via Apify (pode estar disponível)
    let conteudosVirais = '';
    if (process.env.APIFY_TOKEN) {
      try {
        conteudosVirais = await agentHashtag(nicho, sv).catch(() => '');
      } catch(e) {}
    }

    const contextoFinal = contextoCompleto +
      (conteudosVirais ? `\n\nCONTEÚDOS VIRAIS DO NICHO "${nicho}":\n${conteudosVirais}` : '');

    const response = await anthropic.messages.create({
      model: 'claude-haiku-4-5',
      max_tokens: 6000,
      system: [{ type: 'text', text: PROMPT_ANALYST, cache_control: { type: 'ephemeral' } }],
      messages: [{
        role: 'user',
        content: [
          { type: 'text', text: contextoFinal },
          { type: 'text', text: '\nCom base nos dados informados, faça o diagnóstico completo conforme estrutura. Use EXATAMENTE os números fornecidos. Seja CIRÚRGICO e ESPECÍFICO para o nicho.' }
        ]
      }],
    });

    const relatorio = response.content?.[0]?.text ?? 'Análise não disponível.';
    const tokens    = (response.usage?.input_tokens || 0) + (response.usage?.output_tokens || 0);

    sv.info('analyst', `✅ Análise manual concluída — ${tokens} tokens`);

    registrarAnalise(arroba.trim(), clienteIP, clienteFP);

    res.json({
      sucesso: true,
      relatorio,
      tokens_usados: tokens,
      fontes: { perfil: 'manual', transcricao: 'não disponível', virais: conteudosVirais ? 'apify' : 'não coletado' }
    });

  } catch(error) {
    sv.err('supervisor', error.message);
    registrarErro(clienteIP, clienteFP, arroba);
    res.status(500).json({ sucesso: false, erro: error.message });
  } finally {
    analiseEmCurso--;
  }
});

// ── Admin: reset rate limits (todos) ───────────────────────
app.post('/admin/reset-rate-limits', (req, res) => {
  const { senha } = req.body;
  if (senha !== (process.env.ADMIN_SECRET || 'engrene2025')) {
    return res.status(403).json({ erro: 'Não autorizado' });
  }
  rateLimits = { usernames: {}, ips: {}, fps: {}, erros: {} };
  saveRateLimits();
  console.log('[ADMIN] Rate limits resetados');
  res.json({ sucesso: true, mensagem: 'Rate limits resetados com sucesso.' });
});

// ── Admin: reset rate limit de um @username específico ─────
app.post('/admin/reset-username', (req, res) => {
  const { senha, username } = req.body;
  if (senha !== (process.env.ADMIN_SECRET || 'engrene2025')) {
    return res.status(403).json({ erro: 'Não autorizado' });
  }
  if (!username?.trim()) {
    return res.status(400).json({ erro: 'username é obrigatório.' });
  }
  const user = username.toLowerCase().replace('@', '').trim();
  delete rateLimits.usernames[user];
  if (rateLimits.usernameCount) delete rateLimits.usernameCount[user];
  if (rateLimits.erros) delete rateLimits.erros[`user_${user}`];
  saveRateLimits();
  console.log(`[ADMIN] Rate limit resetado para @${user}`);
  res.json({ sucesso: true, mensagem: `Rate limit de @${user} removido com sucesso.` });
});

// ── Admin: status dos rate limits ──────────────────────────
app.get('/admin/status-rate-limits', (req, res) => {
  const senha = req.query.senha;
  if (senha !== (process.env.ADMIN_SECRET || 'engrene2025')) {
    return res.status(403).json({ erro: 'Não autorizado' });
  }
  limparExpirados();
  const agora = Date.now();
  const usuarios = Object.entries(rateLimits.usernames).map(([user, ultima]) => {
    const total   = rateLimits.usernameCount?.[user] || 1;
    const erros   = (rateLimits.erros?.[`user_${user}`] || []).length;
    const sucesso = Math.max(0, total - erros);
    const expiraEm = Math.ceil((RATE_LIMIT_SEMANAS_MS - (agora - ultima)) / (24 * 60 * 60 * 1000));
    return { username: user, analises_sucesso: sucesso, analises_erro: erros, expira_em_dias: expiraEm, bloqueado: sucesso >= RATE_LIMIT_IP_MAX };
  });
  res.json({ total_usuarios: usuarios.length, usuarios });
});

// ── Status da fila ─────────────────────────────────────────
app.get('/api/status', (req, res) => {
  const disponivel = analiseEmCurso < MAX_ANALISES;
  const posicaoFila = analiseEmCurso;
  const tempoEstimadoSeg = disponivel ? 60 : 60 + Math.ceil((posicaoFila - MAX_ANALISES + 1) * 5);
  res.json({
    analiseEmCurso,
    maxAnalises: MAX_ANALISES,
    disponivel,
    posicaoFila,
    tempoEstimadoSeg
  });
});

// ── Serve frontend ─────────────────────────────────────────
app.get('*', (req, res) => {
  res.sendFile(path.join(__dirname, 'frontend', 'index.html'));
});

const server = app.listen(PORT, () => {
  console.log(`\n🔥 Diagnóstico Engrene — Squad IA — http://localhost:${PORT}`);
  console.log(`\n👥 Squad ativo:`);
  console.log(`   🔷 Supervisor  — orquestra a pipeline`);
  console.log(`   🔎 Scout       — Apify: métricas do perfil ${process.env.APIFY_TOKEN ? '✅' : '⚠️  (sem APIFY_TOKEN)'}`);
  console.log(`   📥 Downloader  — yt-dlp: download de Reels`);
  console.log(`   🎙️  Transcriber — Whisper API: transcrição ${process.env.OPENAI_API_KEY ? '✅' : '⚠️  (sem OPENAI_API_KEY, usa fallback local)'}`);
  console.log(`   🧠 Analyst     — Claude Haiku: análise profunda\n`);
  server.timeout = 120000;
});
