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
  if (process.env.NODE_ENV === 'development') return { bloqueado: false };
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
  // Preserva o timestamp da PRIMEIRA análise da semana — não sobrescreve
  // Assim a janela de 7 dias expira a partir da 1ª análise, não da última
  if (!rateLimits.usernames[username]) {
    rateLimits.usernames[username] = Date.now();
  }
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
    return res.redirect(301, 'https://diagnostico-engrene-production.up.railway.app' + req.originalUrl);
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
      destaques:      null,
      stories:        null,
    };

    // ── Etapa 1: Scout + Download + Hashtag em PARALELO ──────
    const [scoutResult, downloadResult, hashtagResult] = await Promise.allSettled([
      arroba ? agentScout(arroba, this) : Promise.resolve(null),
      reelUrl ? agentDownloader(reelUrl, this) : Promise.resolve(null),
      (process.env.APIFY_TOKEN && nicho) ? agentHashtag(nicho, this).catch(e => {
        this.warn('supervisor', `Hashtag ignorado: ${e.message}`); return '';
      }) : Promise.resolve(''),
    ]);

    // Consolida resultados paralelos (allSettled — checar status antes de .value)
    results.perfilApify    = scoutResult.status === 'fulfilled'   ? scoutResult.value    : null;
    const videoPath        = downloadResult.status === 'fulfilled' ? downloadResult.value : null;
    results.conteudosVirais = hashtagResult.status === 'fulfilled' ? (hashtagResult.value ?? '') : '';

    // Fallback para Instaloader se Scout falhou
    if (!results.perfilApify?.ok) {
      if (results.perfilApify?.erroTipo === 'private') {
        this.warn('supervisor', `@${arroba} é privado — abortando análise`);
      } else {
        this.warn('supervisor', 'Scout falhou — usando Instaloader como fallback');
        results.perfilFallback = await agentInstaloader(arroba, this);
      }
    }

    // ── Etapa 2: Destaques via Apify (paralelo ao Imager) ────
    const perfilOk = results.perfilApify?.ok ? results.perfilApify : null;
    const [imagerResult, destaquesResult, storiesResult] = await Promise.allSettled([
      perfilOk?.posts?.length > 0 ? agentImager(perfilOk.posts, this) : Promise.resolve([]),
      // Etapa 2: Destaques
      (process.env.APIFY_TOKEN && arroba) ? agentDestaques(arroba, this).catch(e => {
        this.warn('supervisor', `Destaques ignorados: ${e.message}`); return null;
      }) : Promise.resolve(null),
      // Etapa 3: Stories
      (process.env.APIFY_TOKEN && arroba) ? agentStories(arroba, this).catch(e => {
        this.warn('supervisor', `Stories ignorados: ${e.message}`); return null;
      }) : Promise.resolve(null),
    ]);

    results.imagensPosts = imagerResult.status === 'fulfilled'    ? (imagerResult.value    ?? [])   : [];
    results.destaques    = destaquesResult.status === 'fulfilled' ? (destaquesResult.value ?? null) : null;
    results.stories      = storiesResult.status === 'fulfilled'   ? (storiesResult.value   ?? null) : null;

    // ── Etapa 4: Transcriber (depende do download) ───────────
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
        body: JSON.stringify({ usernames: [username], resultsLimit: 30, proxy: { useApifyProxy: true } }),
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
          return normalizarPerfil('apify', p, (p.latestPosts || []).slice(0, 20).map(post => ({
            tipo:        post.type || 'GraphImage',
            legenda:     (post.caption || '').substring(0, 300),
            curtidas:    post.likesCount    || 0,
            comentarios: post.commentsCount || 0,
            views:       post.videoViewCount || 0,
            is_video:    post.type === 'Video' || post.type === 'GraphVideo',
            shortcode:   post.shortCode  || '',
            imagem_url:  post.displayUrl || '',
            video_url:   post.videoUrl   || '',
            timestamp:   post.timestamp  || post.takenAt || null,
            fixado:      post.isPinned   || false,
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
          const posts = edges.slice(0, 20).map(e => {
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

// ══════════════════════════════════════════════════════════════
//  AGENT: DESTAQUES — louisdeconinck~instagram-highlights-scraper (actor dedicado)
// ══════════════════════════════════════════════════════════════
async function agentDestaques(username, sv) {
  sv.info('destaques', `Coletando destaques de @${username}...`);
  try {
    // Actor dedicado para highlights — não requer login, funciona com perfis públicos
    const url = `https://api.apify.com/v2/acts/louisdeconinck~instagram-highlights-scraper/runs` +
                `?token=${process.env.APIFY_TOKEN}&waitForFinish=90`;
    const resp = await fetch(url, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        usernames: [username],
        proxy: { useApifyProxy: true }
      }),
      signal: AbortSignal.timeout(110000)
    });
    if (!resp.ok) {
      sv.warn('destaques', `HTTP ${resp.status} no run — sem destaques coletados`);
      return null;
    }
    const run = await resp.json();
    const datasetId = run?.data?.defaultDatasetId;
    if (!datasetId) {
      sv.warn('destaques', 'Sem datasetId no run');
      return null;
    }
    const dsResp = await fetch(
      `https://api.apify.com/v2/datasets/${datasetId}/items?token=${process.env.APIFY_TOKEN}`,
      { signal: AbortSignal.timeout(30000) }
    );
    if (!dsResp.ok) { sv.warn('destaques', `Dataset HTTP ${dsResp.status}`); return null; }
    const items = await dsResp.json();

    if (!Array.isArray(items) || items.length === 0) {
      sv.info('destaques', 'Nenhum destaque encontrado (perfil sem highlights)');
      return { temDestaques: false, total: 0, lista: [] };
    }
    // Cada item é um highlight com título e mídias internas
    const lista = items.map(h => ({
      titulo:      h.title || h.name || h.id || 'Sem título',
      capinha_url: h.coverUrl || h.coverImageUrl || h.thumbnailUrl || '',
      total_itens: h.itemsCount ?? (Array.isArray(h.items) ? h.items.length : 0),
    }));
    sv.info('destaques', `✅ ${lista.length} destaques coletados`);
    return { temDestaques: true, total: lista.length, lista };
  } catch(e) {
    sv.warn('destaques', `Erro: ${e.message}`);
    return null;
  }
}

// ══════════════════════════════════════════════════════════════
//  AGENT: STORIES — datavoyantlab~advanced-instagram-stories-scraper
//  Actor dedicado, sem login, 116K runs, rating 4.4/5
// ══════════════════════════════════════════════════════════════
async function agentStories(username, sv) {
  sv.info('stories', `Coletando stories de @${username}...`);
  try {
    const url = `https://api.apify.com/v2/acts/datavoyantlab~advanced-instagram-stories-scraper/runs` +
                `?token=${process.env.APIFY_TOKEN}&waitForFinish=90`;
    const resp = await fetch(url, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        usernames: [username],
        proxy: { useApifyProxy: true }
      }),
      signal: AbortSignal.timeout(110000)
    });
    if (!resp.ok) {
      sv.warn('stories', `HTTP ${resp.status} no run — sem stories coletados`);
      return null;
    }
    const run = await resp.json();
    const datasetId = run?.data?.defaultDatasetId;
    if (!datasetId) {
      sv.warn('stories', 'Sem datasetId no run');
      return null;
    }
    const dsResp = await fetch(
      `https://api.apify.com/v2/datasets/${datasetId}/items?token=${process.env.APIFY_TOKEN}`,
      { signal: AbortSignal.timeout(30000) }
    );
    if (!dsResp.ok) { sv.warn('stories', `Dataset HTTP ${dsResp.status}`); return null; }
    const items = await dsResp.json();

    if (!Array.isArray(items) || items.length === 0) {
      sv.info('stories', 'Nenhum story ativo encontrado (últimas 24h)');
      return { temStories: false, total: 0, lista: [] };
    }
    const lista = items.map(s => ({
      tipo:       s.type || (s.isVideo ? 'video' : 'imagem'),
      timestamp:  s.timestamp || s.takenAt || s.createdAt || null,
      tem_texto:  !!(s.caption || s.text || s.storyContent || ''),
      tem_link:   !!(s.linkUrl || s.externalLink || s.swipeUpUrl || ''),
      imagem_url: s.displayUrl || s.imageUrl || s.url || '',
    }));
    sv.info('stories', `✅ ${lista.length} stories ativos (últimas 24h)`);
    return { temStories: true, total: lista.length, lista };
  } catch(e) {
    sv.warn('stories', `Erro: ${e.message}`);
    return null;
  }
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
    signal: AbortSignal.timeout(55000)
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

REGRA SOBRE DATA (INVIOLÁVEL):
Use EXCLUSIVAMENTE a data do campo DATA_COLETA. Esta é a data real da coleta. PROIBIDO usar qualquer outra data. PROIBIDO usar a data de postagens do Instagram como data do relatório.

REGRA ABSOLUTA DE FORMATAÇÃO:
❌ PROIBIDO usar travessão (— ou –) em qualquer parte do relatório. Nem em títulos, nem em listas, nem em frases.
❌ PROIBIDO usar hífen (-) como marcador de lista. Use apenas bullet (•) quando necessário.
❌ PROIBIDO truncar ou abreviar títulos de seção.
❌ PROIBIDO usar | (pipe) dentro do texto das células de tabela. Use / ou ponto como separador interno.
✅ Para separar ideias: use dois pontos (:) ou ponto final.
✅ Números com separador: use "3 a 5" em vez de "3-5" quando for intervalo em texto.

REGRA MÁXIMA — DADOS AUSENTES E LIMITES DA AMOSTRA (INVIOLÁVEL, ACIMA DE TUDO):
Você recebe uma AMOSTRA limitada de dados. Não é o perfil completo. Respeite os limites do que você tem.

❌ PROIBIDO classificar como URGENTE, ATENÇÃO ou APROVADO qualquer elemento sem dado real coletado.
❌ PROIBIDO escrever "Sem stories nas últimas 24h" se não há dado de stories coletado.
❌ PROIBIDO escrever "Sem destaques" se não há dado de destaques coletado.
❌ PROIBIDO inventar ausência de dados. Ausência de dado ≠ ausência do elemento no perfil real.
❌ PROIBIDO extrapolar frequência: se coletou 20 posts e o intervalo entre eles é curto, isso não significa que o perfil posta "X vezes por semana" — pode ter muito mais posts não coletados.
❌ PROIBIDO afirmar "11 posts em 30 dias" ou qualquer contagem de período quando você só tem uma amostra dos posts mais recentes, não todos os posts do período.
❌ PROIBIDO inventar datas, métricas ou números que não estejam explicitamente nos dados fornecidos.
❌ PROIBIDO citar um post específico com data e views se esses dados não estiverem na entrada.

✅ Frequência: use os dados de "Frequência real calculada via timestamps" se fornecidos. Se não fornecidos ou incompletos, diga: "Com base nos [N] posts coletados, o intervalo médio entre eles é de X dias — mas o perfil pode ter mais posts não coletados nesta amostra."
✅ Quando um dado não foi coletado: status N/A, descrição "Não coletado nesta análise". Nada mais.
✅ Cite apenas o que está nos dados. Se não está nos dados, não existe para você.

REGRAS ABSOLUTAS DE QUALIDADE:
❌ NUNCA invente dados, métricas ou informações que não estejam nos dados fornecidos
❌ NUNCA diga "Publique mais conteúdo", "Interaja com seus seguidores", "Use hashtags relevantes"
❌ NUNCA faça recomendações genéricas. Seja ESPECÍFICO para ESTE nicho e ESTE perfil.
✅ SEMPRE analise COM OS DADOS REAIS fornecidos: bio real, posts reais com números reais
✅ SEMPRE cite números exatos quando disponíveis E quando estiverem nos dados: "Post de [tema]: [X] curtidas, [Y] comentários"
✅ SEMPRE conecte cada diagnóstico ao nicho específico
✅ SEMPRE entregue: O QUE + COMO + POR QUE funciona para ESSE negócio
✅ Se um dado não foi coletado ou é incompleto: seja honesto sobre o limite. Nunca preencha com suposição.

PÚBLICO-ALVO DO RELATÓRIO (INVIOLÁVEL):
Mulheres donas de negócio local (salão, confeitaria, loja, serviço). Não entendem de marketing, vendas ou Instagram. Nunca ouviram falar de "algoritmo", "engajamento" ou "CTA". Se você usar esses termos sem explicar, elas vão se sentir burras e fechar o relatório.

TOM OBRIGATÓRIO:
• Simples como uma conversa entre amigas. Nada de termos técnicos sem explicação.
• Quando precisar usar um termo técnico, explique na mesma frase. Exemplo: "curtidas, comentários e salvamentos (que é o que o Instagram usa para decidir se vai mostrar seu post para mais gente)".
• Use "a gente" — nunca "você deve" ou "recomenda-se".
• Seja direta: diga o problema, diga o que fazer. Sem rodeios.
• Elogie antes de criticar. Sempre encontre algo positivo primeiro.
• Repita conceitos importantes sem se desculpar: "Eu sei que parece óbvio, mas é o que a gente vê em 70% dos perfis."
• Simule a perspectiva da cliente que chega no perfil: "Se eu tô chegando aqui agora, como cliente, o que eu vejo?"

FRASES CALIBRADORAS DE TOM (use quando fizer sentido, não force):
• "A foto atrai, a legenda vende."
• "O óbvio precisa ser dito."
• "Vocês estão deixando dinheiro em cima da mesa."
• "Pode fazer tudo maravilhosamente bem, mas se você fica 20 semanas sem postar, não adianta de nada."
• "Toda vez que você aparece no vídeo, claramente chama mais atenção."
• "Até eu descobrir o que vocês vendem, já vou procurar em outro lugar."
• "Catálogo a gente só olha. A gente não interage com catálogo."
• "A IA não está vendo o produto. Ela deixa o mais genérico possível."
• "Cadê você respondendo essas pessoas? Quem responde, vende mais."

LINGUAGEM PROIBIDA (vai afastar o público):
❌ algoritmo, engajamento, CTA, taxa de engajamento, feed, persona, funil, tráfego orgânico, alcance, impressões, insights, benchmark, estratégia de conteúdo
✅ Substitua por linguagem simples:
• "algoritmo" → "o Instagram" ou "o sistema do Instagram"
• "engajamento" → "curtidas, comentários e salvamentos"
• "CTA" → "chamada para ação" ou "convite para comprar"
• "feed" → "página do Instagram" ou "perfil"
• "alcance" → "quantas pessoas viram"
• "tráfego orgânico" → "pessoas que chegam no perfil sem pagar anúncio"
• "taxa de engajamento" → "proporção de pessoas que interagem com os posts"

REGRA DE EXPLICAÇÃO DE NÚMEROS:
Quando citar qualquer número ou métrica, explique o que significa na prática.
Exemplo: "Seus posts têm em média 45 curtidas. Para um perfil com 800 seguidores, isso representa cerca de 5% das suas seguidoras interagindo — o que é um número razoável."
Nunca solte um número sem contexto.

BENCHMARKS DE REFERÊNCIA:
Frequência mínima: 3 posts/semana (abaixo disso o algoritmo para de distribuir)
Stories: cerca de 10% da audiência, duram 24h. O feed é permanente e atinge muito mais.
Perfis médios ativos: 5.000 a 8.000 views por vídeo
8.000 seguidores significa mais de 800 pessoas alcançadas por post. Abaixo disso: investigar shadow ban.
Link WhatsApp: wa.me/55+DDD+número (sem zero, sem redirecionador)
Legenda gerada por IA detectável: verbos no imperativo (Descubra, Transforme, Crie), emojis no final das frases, travessão americano, linguagem genérica sem detalhes reais do produto.

REFERÊNCIA DO MÉTODO ANA DRUMON (use para enriquecer diagnósticos por nicho):

ERROS MAIS COMUNS (base: ~120 perfis analisados) — use para contextualizar o diagnóstico:
1. Fica muito tempo sem postar (menos de 3 vezes por semana): ~75% dos perfis
2. Legenda fraca, sem informação do produto, ou feita por IA: ~70%
3. Nome do perfil sem dizer o nicho e a cidade: ~70%
4. Sem posts fixados com estratégia: ~65%
5. Bio incompleta (faltando 2 ou mais elementos): ~60%
6. Destaques sem capinhas ou mal organizados: ~55%
7. Perfil só com fotos de produto, sem a pessoa aparecer: ~50%
8. Sem cardápio ou lista de produtos/serviços: ~45%
9. Vídeos sem título na capa: ~40%
10. Link do WhatsApp com redirecionador (Bitly, Linktree): ~30%
11. Sem convite para comprar na bio ou nas legendas: ~30%
12. Usando só fotos do fornecedor em vez de fotos próprias: ~20%
13. Curtidas e comentários muito abaixo do esperado para o tamanho do perfil: ~15%
14. Nome de usuário muito longo, difícil de escrever ou com símbolos: ~12%
15. Legendas claramente feitas por IA (verbos no imperativo, emojis no fim, linguagem genérica): ~10%

PADRÕES ESPECÍFICOS POR NICHO (aplique no PASSO 11 e nos detalhamentos):

Casa/Arquitetura/Decoração/Imóveis:
• Tour pelo espaço é OBRIGATÓRIO para quem tem loja física
• Mostrar antes e depois de projetos
• Destaques separados por tipo (tapetes, móveis, iluminação) — NUNCA por datas comemorativas
• Para aromas/velas: fixado dos aromas e das embalagens para facilitar escolha
• Para imóveis: posicionar no estilo de vida do público, não em selfies fora de contexto

Gastronomia/Eventos/Confeitaria:
• CARDÁPIO é indispensável (fixado, destaque ou link na bio)
• Produto como protagonista (resultado final) > bastidores/processo
• Cenário de fotos padronizado com iluminação boa
• Para confeitaria: sabores, tamanhos, preços, "para quantas pessoas serve"
• Para restaurantes: almoços, sobremesas, sucos — rodar temas por dia da semana
• Para eventos (peg-monte, decoração): separar por tipo (menina, menino, adulto, bebê)
• Nunca deixar o cliente sem saber como comprar
• Citação-chave: "Até eu descobrir quais são os aromas que vocês têm, já vou procurar em outro lugar."

Serviços Gerais (Celebrante, Organizadora, Fotógrafo, Dança):
• Mostrar o SERVIÇO em ação (não só bastidores)
• Para celebrantes: mostrar discursos, reações, cerimônia ao vivo
• Para professores (dança, pilates): informar local, horários, como se matricular, valor
• Portfolio visual é essencial
• Landing page recomendada em vez de só WhatsApp

Saúde (Estética, Personal, Nutrição, Psicologia, Odontologia):
• Nível de consciência: não presumir que o cliente sabe o que você vende
• Explicar o "veículo" (suplementos? exercícios? procedimentos?)
• Cardápio de serviços detalhado com explicação de cada tratamento
• Para suplementos: mostrar o PRODUTO, não só o resultado
• Para profissionais de saúde: quebrar objeções, tirar dúvidas frequentes
• Cuidado com CTA "Saiba mais" apontando para WhatsApp (pessoa não "sabe mais" no WhatsApp)
• Citação-chave: "Compre no site, onde comprar, do que que você tá falando? Eu achei que você ensinava a emagrecer."

Beleza (Maquiagem, Cabelo, Estética, Micropigmentação):
• Resultados antes/depois são o conteúdo principal
• Título/headline na capa dos reels (obrigatório quando tem assunto específico)
• Para lojas de maquiagem: NUNCA só fotos do fornecedor — criar conteúdo próprio
• Comparações de produtos (marca A vs marca B) geram engajamento alto
• Para cabelo: explicar tonalidades, por que aquela cor, tipo de pele que combina
• Citação-chave: "Você tá fazendo propaganda para as marcas e não pra sua loja."

Moda/Calçados/Acessórios/Lingerie:
• Provadores são o formato campeão do nicho
• Legenda deve conter: tecido, tamanhos, cores disponíveis, preço, CTA
• Responder TODOS os comentários (especialmente perguntas de valor)
• Para plus size: comunicação inclusiva, empoderamento como diferencial
• Para semijoias: separar por tipo (brincos, colares, anéis) nos destaques
• Para infantil: separar por faixa etária e/ou personagem
• Citação-chave: "Cadê você respondendo essas pessoas? Quanto mais você responde, mais engajamento você traz pro conteúdo."

Comércio em Geral:
• Para delivery/restaurante: cardápio no feed (não só stories)
• Para móveis/pneus: fotos com iluminação adequada, sem sombras fortes
• Para artesanato: mostrar o processo + resultado + preço
• Para assinatura/serviço recorrente: PDF explicativo > link de WhatsApp

Infoprodutos/Marketing Digital:
• Bio deve ter nicho claro (não só "marketing digital")
• Perfis privados eliminam alcance orgânico completamente
• Conteúdo técnico deve ser balanceado com prova social
• Mostrar resultados de clientes/mentorados

ANTES DE INICIAR A ANÁLISE — VERIFIQUE SE O PERFIL É ANALISÁVEL:
• Perfil privado: análise limitada a nome de usuário, nome de destaque, bio e foto de perfil. Informe isso no início do relatório e recomende tornar o perfil público.
• Perfil sem nenhum post: marque URGENTE em todos os critérios de conteúdo. Recomende começar a postar imediatamente.
• Perfil pessoal (não tem conta profissional): recomende migrar para conta profissional antes de qualquer outra coisa.
• Não consegue identificar o que a pessoa vende depois de ler bio + ver 10 posts: registre isso como problema crítico antes de continuar.
• Perfil inexistente ou desativado: informe que não é possível analisar.

EXECUTE A ANÁLISE NESTA SEQUÊNCIA EXATA. CADA PASSO CORRESPONDE A UM ELEMENTO DA TABELA. NÃO PULE, NÃO REORDENE, NÃO MISTURE PASSOS:

PASSO 0: PRIMEIRA IMPRESSÃO (elemento 0 da tabela)
Simule ser um cliente novo chegando ao perfil pela primeira vez. É possível identificar o nicho em menos de 3 segundos olhando para a grade de fotos e foto de perfil? O visual é coerente com o tipo de negócio? Passa sensação de profissionalismo ou amadorismo?
Benchmark: "Se eu tô chegando aqui agora, eu consigo entender em 3 segundos o que você faz?"
Classifique: APROVADO / ATENÇÃO / URGENTE.

PASSO 1: NOME DE USUÁRIO (elemento 1 da tabela)
Fácil de ler, escrever e encontrar? Sem underlines duplos, pontos combinados, caracteres desnecessários? Máximo 25 caracteres?
Se houver problema, diga exatamente o que mudar.
Classifique: APROVADO / ATENÇÃO / URGENTE.

PASSO 2: NOME DE DESTAQUE (elemento 2 da tabela)
Contém nome + nicho + localização? São palavras-chave pesquisáveis? Gera confusão sobre o que a pessoa faz?
Benchmark: "Tudo que tá nesses nomes é mecanismo de busca, é pesquisável na barra de pesquisa. Nome, nicho e localização."
Se houver problema, sugira o nome de destaque ideal.
Classifique: APROVADO / ATENÇÃO / URGENTE.

PASSO 3: BIO (elemento 3 da tabela)
Verifique os 5 elementos da fórmula:
1. Especialidade: o que faz e qual o diferencial (explicado para quem nunca ouviu falar do negócio)
2. Promessa: uma frase forte que diz o resultado que a cliente vai ter. Não serve frases genéricas como "feito com amor" ou "qualidade garantida".
3. Prova social: quantos clientes já atendeu, há quantos anos está no mercado, quantos projetos entregues, quantas cidades atendidas — qualquer indicador de experiência real. Precisa de número concreto. ❌ NUNCA sugira usar número de seguidores como prova social: seguidores não são conquistas do negócio, são dados do Instagram.
4. Convite para agir: um verbo claro dizendo o que fazer. Por exemplo: "Agende pelo link", "Compre agora", "Fale comigo no WhatsApp".
5. Link: precisa estar presente e funcionar.

TAMBÉM verifique o nível de clareza: a bio dá para entender o que a pessoa vende mesmo para quem nunca ouviu falar do negócio? Para nichos menos óbvios (suplementos, tratamentos específicos, serviços especializados), precisa ser ainda mais claro.

Critério:
• APROVADO = 4 ou 5 elementos presentes
• ATENÇÃO = 3 elementos presentes
• URGENTE = 2 ou menos elementos. Bio vazia ou só com frases emocionais sem informação prática.

Se houver problema, reescreva a bio usando a fórmula.

PASSO 4: LINK DA BIO (elemento 4 da tabela)
Funciona? Para onde leva? WhatsApp direto (wa.me/55+DDD+número sem zero) ou redirecionador (Bitly, Linktree) que demora mais de 5 segundos?
Referência: "Tem pessoas que desistem de entrar em contato porque esses redirecionadores parecem cliques de vírus."
Classifique: APROVADO / ATENÇÃO / URGENTE.

PASSO 5: FOTO DE PERFIL (elemento 5 da tabela)
SE a pessoa É a marca (profissional liberal, prestador de serviço):
• Rosto visível e bem enquadrado (não cortado no pescoço — mostrar ombros)
• Fundo adequado ao posicionamento (neutro, espaço de trabalho, coerente com o nicho)
• Expressão de confiança (não foto casual, selfie no carro, ou muito descontraída)
• Boa resolução — legível no formato circular pequeno
SE é uma marca/loja com identidade própria:
• Logomarca profissional (não foto pessoal)
• Logo legível no formato circular pequeno do Instagram
EM AMBOS OS CASOS verificar que NÃO tem: endereço, telefone, QR code na foto (isso vai na bio).
Referência: "A foto de perfil não precisa ser um cartão de visitas. Endereço, telefone, a gente deixa na bio."
Classifique: APROVADO / ATENÇÃO / URGENTE.

PASSO 6: STORIES (elemento 6 da tabela)
REGRA MÁXIMA: use SOMENTE o que está no campo "STORIES" dos dados fornecidos. Nada mais.
• Se o campo diz "não foi possível coletar": Status N/A. Escreva apenas "Não coletado nesta análise." NÃO classifique, NÃO diga "sem stories", NÃO escreva benchmark.
• Se o campo diz "sem stories ativos nas últimas 24h" (dado real coletado): Status URGENTE. Informe o impacto.
• Se o campo traz dados reais de stories: analise quantidade, formato (foto/vídeo), narrativa, variação.
Classifique: APROVADO / ATENÇÃO / URGENTE / N/A (obrigatório N/A quando não coletado).

PASSO 7: DESTAQUES (elemento 7 da tabela)
REGRA: Se o Apify não coletou os destaques, informe apenas: "Destaques não foram coletados nesta análise. Recomendamos organizar os destaques com capinhas padronizadas e categorias úteis para o cliente (ex: Serviços, Preços, Localização, Resultados, Depoimentos). Revise os destaques pelo menos a cada 6 meses." Classifique como N/A e siga para o próximo passo. NÃO invente conteúdo de destaque.

SE os dados dos destaques foram coletados, analise de forma resumida:
• Os títulos fazem sentido para quem chega pela primeira vez? (ex: "Natal 2022" é ruim. "Cardápio" é bom.)
• Há capinhas padronizadas ou são aleatórias?
• As categorias são úteis para o cliente? (produtos, serviços, cardápio, resultados, depoimentos, localização)

NÃO sugira número fixo de destaques. NÃO elabore um plano detalhado de reestruturação. Seja breve: 3 linhas no máximo.
Oriente que os destaques sejam revisados periodicamente, pelo menos a cada 6 meses.
Classifique: APROVADO / ATENÇÃO / URGENTE (ou N/A se não coletado).

PASSO 8: POSTS FIXADOS (elemento 8 da tabela)
Estratégia dos 3 fixados:
1° fixado: Apresentação/Tour (quem é, como funciona, tour pela loja se física)
2° fixado: Diferencial/Catálogo (produtos/serviços com detalhes)
3° fixado: Flutuante: ação de vendas atual, lançamento, promoção (rotativo)
As capas dos fixados são explicativas sem precisar abrir? Vídeos com capa customizada e não cena aleatória?
Referência: "Todo mundo que presta serviço deveria ter esse post de conheça meus serviços."
Classifique: APROVADO / ATENÇÃO / URGENTE.

PASSO 9: ÚLTIMA PUBLICAÇÃO + QUALIDADE (elemento 9 da tabela)
Quando foi a última publicação? Formato? Qualidade técnica (iluminação, nitidez, som)? Legenda presente e com qualidade? Título na capa se reel?
Detecte sinais de IA: verbos no imperativo (Descubra, Transforme, Crie), emojis no final das frases, travessão americano, linguagem genérica sem detalhes do produto.
Benchmark: ideal a cada 2 a 3 dias. Máximo 1 semana sem postar.

REGRA DO GANCHO (aplique em todos os vídeos/Reels analisados):
Todo vídeo precisa de um gancho ou headline chamativa nos primeiros segundos ou na capa. Sem gancho, o vídeo não para o scroll e não chega a novas pessoas.
• O gancho deve aparecer em destaque: texto grande na capa, primeira fala do vídeo, ou legenda de abertura impactante.
• Vídeos sem gancho visível devem ser sinalizados como problema de performance — independente do conteúdo ser bom.
• Ao analisar cada Reel/vídeo nos dados coletados: verifique se há evidência de gancho (título na capa, primeiros segundos descritos na legenda). Se não houver: aponte como correção prioritária.

Classifique: APROVADO / ATENÇÃO / URGENTE.

PASSO 10: FEED GERAL (elemento 10 da tabela)
FREQUÊNCIA — REGRA CRÍTICA DE HONESTIDADE:
Você recebeu uma AMOSTRA de posts (máximo 20). O perfil pode ter muito mais posts que não foram coletados.
• USE o campo "Frequência real calculada via timestamps" dos dados se ele estiver presente — é o dado mais confiável.
• Se ele não estiver presente: informe o intervalo entre os posts que você TEM. Nunca extrapole para "X posts em 30 dias" como se tivesse todos os posts do período.
• Fórmula correta: "Entre o post mais antigo ([data]) e o mais recente ([data]) da amostra coletada, foram [N] posts — intervalo médio de X dias entre eles. Nota: esta é uma amostra dos posts mais recentes, pode haver mais publicações não coletadas."
• Se os posts da amostra são todos recentes (concentrados em poucos dias): diga que a amostra é limitada, não que o perfil posta muito rápido.
• Se os posts da amostra são muito antigos (último post há mais de 30 dias): classifique URGENTE.

❌ PROIBIDO afirmar "X posts em 30 dias" sem ter dados de todos os posts desse período.
❌ PROIBIDO classificar frequência sem citar datas reais dos posts coletados.
❌ PROIBIDO dizer "o perfil posta regularmente" sem embasar com datas concretas.

ALÉM DA FREQUÊNCIA, verifique com os dados que você TEM: engajamento proporcional aos seguidores, identidade visual consistente, equilíbrio de formatos (reel/foto/carrossel), humanização vs catálogo, respostas a comentários, qualidade técnica geral.
Benchmarks: 3 ou mais posts por semana. 8.000 seguidores = mais de 800 pessoas alcançadas por post esperadas.
Referência: "Catálogo geralmente a gente só olha. A gente não consome assim, engaja."
Classifique: APROVADO / ATENÇÃO / URGENTE.

PASSO 11: SÍNTESE FINAL (elemento 11 da tabela)
Com base em tudo que analisou nos passos 0 a 10, organize as conclusões nesta estrutura:

✅ O que está bem (máximo 3 pontos — sempre elogiar antes de criticar):
Liste o que o perfil faz de certo. Seja específico.

🔴 URGENTE — fazer essa semana (máximo 3 itens):
O que está prejudicando o negócio agora. Cada item precisa ser uma ação concreta que pode ser feita em menos de 2 horas.

🟡 IMPORTANTE — fazer este mês (2 a 4 itens):
O que vai melhorar o resultado mas não precisa ser hoje.

🟢 MELHORIA — quando der (1 a 3 itens):
Ajustes de longo prazo para quem já resolveu o urgente.

Próximo passo: 1 ação única, concreta, para começar hoje. Não pode ser vaga. Exemplo certo: "Troca o link do WhatsApp no perfil agora, usando o formato wa.me/55 mais o número com DDD sem o zero." Exemplo errado: "Melhore sua bio."

Classifique o PASSO 11 como APROVADO se a síntese foi possível com dados reais.

CRITÉRIOS DE CLASSIFICAÇÃO (use para cada elemento):
APROVADO: está bem, não precisa de nenhuma ação agora
ATENÇÃO: tem problema que está limitando o resultado, precisa corrigir em breve
URGENTE: está prejudicando o negócio hoje, precisa corrigir essa semana

REGRA DE LINGUAGEM DO NICHO: aplique as regras do nicho dentro de cada passo acima, não como passo separado.
• Casa/Decoração: tour pela loja é obrigatório se tiver loja física, destaques por tipo de produto (não por datas)
• Gastronomia/Confeitaria: cardápio é indispensável com sabores, tamanhos, preços e porções
• Serviços: mostrar o serviço em ação (não só bastidores), informar local, horários e valor
• Saúde/Estética: não presumir que o cliente sabe o que você vende, explicar o que é o tratamento
• Beleza: antes/depois como conteúdo principal, título na capa dos vídeos, nunca só fotos do fornecedor
• Moda: vídeos experimentando a roupa são o formato que mais vende, legenda com tecido/tamanhos/cores/preço, responder todos os comentários
• Comércio: cardápio no perfil (não só nos stories), fotos com boa iluminação
• Infoprodutos: bio com nicho claro, perfil público (perfil privado não aparece para novas pessoas), mostrar resultados de clientes

REGRA DO CARTÃO DE AÇÃO: A seção "✅ Faça Isso Agora" no topo do relatório deve conter exatamente as mesmas ações dos itens 🔴 1 e 🟡 2 da seção "As 3 coisas mais urgentes", reescritas de forma ainda mais direta e sem nenhum termo técnico. Nada além das 2 ações e o tempo estimado.

OUTPUT: Gere o relatório NESTE FORMATO EXATO e NESTA ORDEM. Não altere a sequência das seções.

REGRAS DE FORMATAÇÃO DO RELATÓRIO (INEGOCIÁVEL):
❌ PROIBIDO travessão (— ou –) em qualquer parte do relatório
❌ PROIBIDO hífen (-) como marcador de lista
❌ PROIBIDO truncar títulos de seção
❌ PROIBIDO reordenar os 12 elementos da tabela
✅ Use dois pontos (:) para separar ideias
✅ Use ponto final para encerrar frases
✅ Bullet (•) como único marcador de lista
✅ Títulos de seção SEMPRE por extenso
✅ Os 12 elementos SEMPRE na ordem: 0.Primeira impressão, 1.Nome de usuário, 2.Nome de destaque, 3.Bio, 4.Link da bio, 5.Foto de perfil, 6.Stories, 7.Destaques, 8.Posts fixados, 9.Última publicação, 10.Feed geral, 11.Síntese final

# Diagnóstico de Perfil — @[arroba]
**Nicho:** [nicho] | **Cidade:** [cidade] | **Seguidores:** [número coletado]
**Data da análise:** [DATA_COLETA]

---

## ✅ Faça Isso Agora

Antes de ler o relatório completo, comece por aqui. Se você só fizer essas 2 coisas essa semana, seu perfil já vai melhorar:

**1. [Ação mais urgente em linguagem de conversa]** — isso leva em torno de [X minutos]
**2. [Segunda ação mais urgente em linguagem de conversa]** — isso leva em torno de [X minutos]

---

## Resumo Executivo
[3 a 4 frases: estado geral do perfil, pontos mais críticos, potencial de melhoria. Sem travessões.]

---

## Análise por Elemento

OBRIGATÓRIO: a tabela abaixo DEVE conter EXATAMENTE 12 linhas de dados (elementos 0 a 11), NESTA ORDEM, SEM PULAR nenhum.
FORMATAÇÃO: resumo com no máximo 55 caracteres, sem travessões, NUNCA use | (pipe) dentro das células.
REGRA PARA DADOS NÃO COLETADOS: quando Stories, Destaques ou Posts Fixados não foram coletados, use "N/A" no Status.

| # | Elemento              | Status              | Resumo                                     |
|---|-----------------------|---------------------|--------------------------------------------|
| 0 | Primeira impressão    | [APROVADO/ATENÇÃO/URGENTE] | [máx 55 chars, sem travessão, sem pipe] |
| 1 | Nome de usuário       | [status]            | [máx 55 chars]                             |
| 2 | Nome de destaque      | [status]            | [máx 55 chars]                             |
| 3 | Bio                   | [status]            | [máx 55 chars]                             |
| 4 | Link da bio           | [status]            | [máx 55 chars]                             |
| 5 | Foto de perfil        | [status]            | [máx 55 chars]                             |
| 6 | Stories               | [status ou N/A]     | [máx 55 chars]                             |
| 7 | Destaques             | [status ou N/A]     | [máx 55 chars]                             |
| 8 | Posts fixados         | [status ou N/A]     | [máx 55 chars]                             |
| 9 | Última publicação     | [status]            | [máx 55 chars]                             |
|10 | Feed geral            | [status]            | [máx 55 chars]                             |
|11 | Síntese final         | [status]            | [máx 55 chars]                             |

Status: ✅ APROVADO | ⚠️ ATENÇÃO | 🔴 URGENTE

---

## O que está bem

[2 a 3 pontos positivos reais do perfil. Sempre elogiar antes de criticar. Seja específico: não diga "o perfil é bonito", diga "as fotos dos produtos têm boa iluminação e o cardápio do destaque está completo com preços".]

---

## O que precisa melhorar

REGRA DE ORDEM: NÃO percorra os elementos na ordem 0 a 10. Percorra na ordem de IMPACTO NO NEGÓCIO:
• Primeiro: elementos URGENTE que afetam vendas hoje (Constância/Feed, Legendas, Bio, Posts Fixados, Link)
• Depois: elementos URGENTE que afetam visibilidade (Primeira impressão, Nome de destaque, Destaques)
• Por último: elementos ATENÇÃO (na ordem de impacto, não na ordem numérica)
• Dentro de cada grupo: o mais fácil de corrigir vem primeiro.
Elementos APROVADO não geram bloco. Máximo de 6 blocos no total — priorize os que mais impactam.

REGRA DE LINGUAGEM: escreva como se estivesse conversando com uma dona de negócio que nunca estudou marketing. Sem jargões. Se usar um termo técnico, explique entre parênteses na mesma frase.

Formato de cada bloco:
### [emoji] [Nº]. [NOME DO ELEMENTO]
**Como está hoje:** [descreva a situação com dados reais, em linguagem simples]
**O problema:** [explique o impacto concreto no negócio. Ex: "Com isso, as pessoas chegam no seu perfil e não entendem o que você vende, então saem sem entrar em contato."]
**O que fazer:** [ação simples, passo a passo, que pode ser feita em menos de 2 horas, sem termos técnicos]

---

## As 3 coisas mais urgentes para fazer agora

🔴 1. **[Ação mais urgente]:** [o que fazer, como fazer, o que vai melhorar em linguagem concreta]
🟡 2. **[Segunda ação]:** [o que fazer, o que vai melhorar]
🟢 3. **[Terceira ação]:** [melhoria de médio prazo, o que vai melhorar]

---

## Bio Reescrita
**Bio atual:** [texto da bio coletada]

**Nova bio sugerida:**
\`\`\`
[Nova bio: especialidade + promessa forte + prova social com número (clientes atendidos, anos de mercado, projetos entregues — NUNCA número de seguidores) + CTA + link. Máximo 150 caracteres. Sem travessões.]
\`\`\`

**Por que essa bio funciona melhor:** [explique em linguagem simples o que foi melhorado]

---

## Nome de Destaque Sugerido
[Se precisar de ajuste: Nome + nicho + localização em formato pesquisável]

---

## Pontuação Geral

[X/12 elementos APROVADOS]
• 10 a 12 APROVADOS: ✅ Perfil Otimizado
• 6 a 9 APROVADOS: 🟡 Perfil em Construção
• 0 a 5 APROVADOS: 🔴 Perfil Crítico

---

## Próximo Passo
Quer ter uma análise aprofundada feita por especialistas e aprender a aplicar cada melhoria?
**Conheça o Método Engrene:** https://suellenwarmling.com.br/

---

PASSO 13: O QUE ESTÁ FUNCIONANDO NOS POSTS (use os dados coletados pelo Apify)
Com base nos últimos posts coletados, identifique padrões reais — não listas de números.
Sua análise deve responder 3 perguntas, em linguagem simples:
1. Qual tipo de post teve mais resultado? (ex: "os vídeos mostrando o processo tiveram em média 3x mais visualizações que as fotos do produto")
2. Qual tipo de post não está funcionando? (ex: "as fotos só de produto com legenda curta quase não aparecem para novas pessoas")
3. Qual é a UMA coisa para testar essa semana? (baseada no padrão de sucesso já existente no perfil)
❌ NUNCA use dados fictícios. Se o Apify não coletou métricas suficientes, informe isso claramente e analise o que houver.
❌ NUNCA solte tabelas com colunas de Post/Curtidas/Comentários/Views — não significa nada para este público.
✅ SEMPRE compare em termos relativos e claros: "3 vezes mais", "a metade", "quase não chegou a ninguém".

PASSO 14: ANÁLISE DE FORMATO DE CONTEÚDO
Com base nos posts coletados, calcule a proporção aproximada de:
• Reels/Vídeos (%)
• Carrosséis (%)
• Imagens estáticas (%)
Identifique desequilíbrio (ex: 90% imagem, 0% Reels).
Aplique a regra do nicho: Reels alcançam mais novos seguidores. Carrosséis geram mais salvamentos. Imagens têm menor alcance orgânico atualmente.
Sugira redistribuição estratégica com percentuais concretos para o nicho.

PASSO 15: RECOMENDAÇÕES ESTRATÉGICAS
Com base nos PASSOs 13 e 14, entregue ajustes concretos de:
• Frequência: quantos posts por semana, em quais formatos
• Abordagem: proporção sugerida entre Conexão / Autoridade / Vendas (ex: 40/30/30)
• Erros evidentes detectados: conteúdo raso, repetitivo, sem convite para comprar, sem contexto de venda
Cada recomendação deve ser executável em menos de 48h.

PASSO 16: BENCHMARK DO NICHO (use o nicho identificado no PASSO 1)
Identifique padrões de conteúdo que performam bem neste nicho no Instagram brasileiro:
• 3 tipos de conteúdo viral comprovados para o nicho
• 2 tendências atuais de formato (ex: POV, "dia na rotina", comparativo)
Explique por que cada um performa: gatilho emocional, nível de consciência do público, facilidade de compartilhamento.
Adapte cada ideia para a realidade do perfil analisado (produto/serviço/nicho específico).
❌ NUNCA cite exemplos genéricos como "faça vídeos autênticos". Seja específico para ESTE negócio.

PASSO 17: SUGESTÕES DE CONTEÚDO IMEDIATO
Entregue 9 ideias prontas para executar esta semana:
• 3 Reels: tema + primeira fala (gancho de abertura em destaque na capa ou nos primeiros segundos do vídeo — OBRIGATÓRIO)
• 3 Carrosséis: tema + título da capa (headline chamativa que force o clique)
• 3 Stories estratégicos: objetivo (venda / conexão / interação) + formato (enquete, pergunta, convite para responder)
REGRA: todo Reel sugerido deve ter gancho explícito. Não sugira vídeo sem indicar a frase de abertura em destaque.
Para produtos físicos: cada ideia deve incluir uso real do produto em contexto específico (rotina, ocasião, comparação, truque prático).

PASSO 18: OS 3 PRÓXIMOS CONTEÚDOS DA SEMANA
NÃO gere um plano de 20 conteúdos. Este público se paralisa com listas longas.
Entregue APENAS 3 conteúdos para postar essa semana.
Para cada conteúdo, forneça:
• Formato: [Reel / Foto / Carrossel]
• Quanto tempo leva para fazer: [estimativa realista, ex: 20 minutos]
• O que falar: [primeira frase ou texto pronto para usar]
• Por que esse conteúdo: [1 linha explicando o motivo em linguagem simples, sem termos técnicos]
Escolha os 3 conteúdos com base no que já funcionou no perfil (PASSO 13) e nos problemas mais urgentes identificados.
Regra de título: use estruturas simples e diretas, que qualquer pessoa entende sem estudar marketing.

FORMATO DE SAÍDA DOS BLOCOS 13 A 18 (inclua ao final do relatório, após "## Próximo Passo"):

## O que está funcionando nos posts

**Olhando os posts coletados desta amostra, dá para ver um padrão claro:**

**O que funciona:** [descreva o tipo de post que teve mais resultado em linguagem simples, com comparação relativa — ex: "Seus vídeos mostrando o processo de fazer o doce tiveram em média 3 vezes mais visualizações do que as fotos do produto pronto."]

**O que não está funcionando:** [descreva o padrão dos posts com menos resultado — ex: "As fotos com fundo branco e legenda curta quase não chegam a novas pessoas."]

**Uma coisa para testar essa semana:** [1 sugestão concreta baseada no que já funcionou neste perfil específico — ex: "Grave um vídeo curto mostrando você fazendo [produto/serviço]. Baseado no que já funcionou aqui, esse tipo de conteúdo tem grande chance de aparecer para mais gente."]

---

## Análise de Formato

| Formato | Proporção Atual | Proporção Sugerida |
|---------|-----------------|-------------------|
| Reels | X% | X% |
| Carrossel | X% | X% |
| Imagem | X% | X% |

**Desequilíbrio detectado:** [descrição direta]
**Correção:** [o que mudar e por quê]

---

## Recomendações Estratégicas

1. **Frequência:** [X posts/semana, distribuição por formato]
2. **Mix de abordagem:** Conexão X% / Autoridade X% / Vendas X%
3. **Erro prioritário a corrigir:** [específico, executável em 48h]

---

## Benchmark do Nicho

| Conteúdo viral | Por que performa | Adaptação para este perfil |
|----------------|-----------------|---------------------------|
| [tipo 1] | [gatilho] | [ideia concreta] |
| [tipo 2] | [gatilho] | [ideia concreta] |
| [tipo 3] | [gatilho] | [ideia concreta] |

---

## Sugestões de Conteúdo Imediato

**Reels:**
• R1: [tema] : Gancho: "[primeira fala]"
• R2: [tema] : Gancho: "[primeira fala]"
• R3: [tema] : Gancho: "[primeira fala]"

**Carrosséis:**
• C1: [tema] : Capa: "[título]"
• C2: [tema] : Capa: "[título]"
• C3: [tema] : Capa: "[título]"

**Stories estratégicos:**
• S1: [objetivo] : [formato: enquete / pergunta / convite para responder]
• S2: [objetivo] : [formato]
• S3: [objetivo] : [formato]

---

## Os 3 Conteúdos da Semana

**Conteúdo 1**
• Formato: [Reel / Foto / Carrossel]
• Tempo: [X minutos para fazer]
• O que falar: "[primeira frase ou texto pronto]"
• Por que funciona: [1 linha em linguagem simples]

**Conteúdo 2**
• Formato: [Reel / Foto / Carrossel]
• Tempo: [X minutos para fazer]
• O que falar: "[primeira frase ou texto pronto]"
• Por que funciona: [1 linha em linguagem simples]

**Conteúdo 3**
• Formato: [Reel / Foto / Carrossel]
• Tempo: [X minutos para fazer]
• O que falar: "[primeira frase ou texto pronto]"
• Por que funciona: [1 linha em linguagem simples]

Quando postar esses 3 e quiser mais ideias, é só pedir.

---

CHECKLIST INTERNO (execute antes de entregar, NÃO mostre ao usuário):
[ ] A bio proposta tem no máximo 150 caracteres?
[ ] A bio proposta NÃO usa número de seguidores como prova social?
[ ] As ações prioritárias são executáveis em menos de 2 horas cada?
[ ] Os diagnósticos citam dados reais (números, bio real, posts reais)?
[ ] Todas as recomendações são específicas para ESTE nicho (não genéricas)?
[ ] A pontuação geral foi calculada como X/12 elementos APROVADOS?
[ ] A frequência de posts foi calculada com datas reais (não estimada)?
[ ] Os destaques foram tratados como N/A se não coletados (sem inventar conteúdo)?
[ ] Nenhuma afirmação foi feita sem base nos dados coletados?
[ ] A tabela de análise tem 12 linhas (elementos 0 a 11)?
[ ] O Cartão de Ação no topo tem as mesmas ações do Top 3?
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

  // Keepalive: envia \n a cada 20s para evitar timeout de proxy reverso
  // JSON.parse ignora whitespace no inicio, entao o cliente processa normalmente
  res.setHeader('Content-Type', 'application/json; charset=utf-8');
  res.setHeader('Transfer-Encoding', 'chunked');
  const keepAlive = setInterval(() => { try { res.write('\n'); } catch(e) {} }, 20000);

  const uploadedFiles = [];
  const jobId = `job_${Date.now()}`;
  const sv    = new Supervisor(jobId);

  try {
    const { nome, nicho, arroba, objetivo, descricao } = req.body;

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

    const nomeDestaqueEfetivo = perfilData?.nome || '';

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
  const fixadoStr = p.fixado ? ' | 📌 FIXADO' : '';
  return `Post ${i+1} [${p.tipo}${p.is_video ? ' · Vídeo' : ''}${fixadoStr}] — ❤️ ${p.curtidas} | 💬 ${p.comentarios}${p.views ? ` | 👁️ ${p.views} views` : ''}${dataStr}\nLegenda: ${sanitizeText(p.legenda) || '(sem legenda)'}`;
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

    const dataColeta = new Date().toLocaleDateString('pt-BR', { day: '2-digit', month: '2-digit', year: 'numeric' });

    const contextoCompleto = `
DATA_COLETA: ${dataColeta} (use esta data no relatório, dados coletados hoje)

DADOS DO NEGÓCIO:
- Nome: ${nome}
- Nicho: ${nicho}
- Instagram: @${arroba}
- Objetivo principal: ${objetivo || 'não informado'}
- Descrição do negócio: ${descricao || ''}
${frequenciaCalculada ? `- Frequência real calculada via timestamps: ${frequenciaCalculada}` : '- Frequência: timestamps não disponíveis para cálculo automático — analise com base na sequência de datas visíveis nas legendas e no intervalo entre os posts listados'}

${(() => {
  const d = squadResultado.destaques;
  const s = squadResultado.stories;
  const postsFixados = (perfilData?.posts || []).filter(p => p.fixado);
  let ctx = '';

  // Destaques
  if (d === null) {
    ctx += '- DESTAQUES: não foi possível coletar via Apify nesta análise\n';
  } else if (!d.temDestaques) {
    ctx += '- DESTAQUES (coletado via Apify): perfil SEM destaques\n';
  } else {
    ctx += `- DESTAQUES (coletado via Apify, dados reais): ${d.total} destaques encontrados\n`;
    ctx += d.lista.map(h => `  • "${h.titulo}" (${h.total_itens} itens)`).join('\n') + '\n';
  }

  // Stories
  if (s === null) {
    ctx += '- STORIES: não foi possível coletar via Apify nesta análise\n';
  } else if (!s.temStories) {
    ctx += '- STORIES (coletado via Apify): sem stories ativos nas últimas 24h\n';
  } else {
    ctx += `- STORIES (coletado via Apify, dados reais): ${s.total} stories ativos nas últimas 24h\n`;
    const tipos = s.lista.map(st => st.tipo).join(', ');
    const comTexto = s.lista.filter(st => st.tem_texto).length;
    const comLink  = s.lista.filter(st => st.tem_link).length;
    ctx += `  Formatos: ${tipos} | Com texto/legenda: ${comTexto} | Com link: ${comLink}\n`;
  }

  // Fixados
  if (postsFixados.length > 0) {
    ctx += `- POSTS FIXADOS (identificados nos posts coletados): ${postsFixados.length} post(s) fixado(s)\n`;
    ctx += postsFixados.map(p => `  • [${p.tipo}] ${sanitizeText(p.legenda).substring(0, 80) || '(sem legenda)'}`).join('\n') + '\n';
  } else {
    ctx += '- POSTS FIXADOS: nenhum detectado nos posts coletados (verifique manualmente se há fixados mais antigos)\n';
  }

  return ctx.trim();
})()}

${ctxPerfil}
${ctxReel}
${squadResultado.conteudosVirais ? `\nCONTEÚDOS VIRAIS DO NICHO "${nicho}" (coletados agora via Apify):\n${squadResultado.conteudosVirais}` : ''}

INSTRUÇÃO: Execute TODOS OS 18 PASSOS do Método Engrene (PASSOs 1 a 12 do diagnóstico de perfil + PASSOs 13 a 18 de análise de conteúdo e performance). Stories, destaques e fixados foram coletados via Apify com dados reais — analise com base nesses dados. Quando a coleta falhou para algum elemento, sinalize com "⚠️ Não coletado" e oriente o que verificar manualmente. NÃO encerre o relatório no PASSO 12 — os blocos de Performance, Formato, Recomendações, Benchmark, Sugestões e Cronograma são OBRIGATÓRIOS.
`.trim();

    // ── Analyst: Claude Haiku — análise profunda ─────────────
    sv.info('analyst', `Chamando Claude Haiku para análise profunda...`);

    const response = await anthropic.messages.create({
      model: 'claude-haiku-4-5',
      max_tokens: 10000,
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
    const dataColeta = new Date().toLocaleDateString('pt-BR', { day: '2-digit', month: '2-digit', year: 'numeric' });

    const contextoCompleto = `
DATA_COLETA: ${dataColeta} (use esta data no relatório, dados coletados hoje)

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

// ── Health check (Render keep-alive) ───────────────────────
app.get('/health', (req, res) => {
  res.status(200).json({ status: 'ok', ts: Date.now() });
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

  // ── Self-ping a cada 14 min (Railway não hiberna, mas protege contra crash silencioso) ──
  const SELF_URL = process.env.RAILWAY_PUBLIC_DOMAIN
    ? `https://${process.env.RAILWAY_PUBLIC_DOMAIN}`
    : `http://localhost:${PORT}`;
  setInterval(async () => {
    try {
      await fetch(`${SELF_URL}/health`, { method: 'GET' });
    } catch (e) {
      // silencia
    }
  }, 14 * 60 * 1000);
});
