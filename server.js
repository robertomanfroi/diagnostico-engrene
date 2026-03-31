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

// ── Controle de concorrência (máx 50 análises simultâneas) ──
let analiseEmCurso = 0;
const MAX_ANALISES = 50;

app.use(cors({ origin: '*' }));
app.use(express.json({ limit: '50mb' }));
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
      this.warn('supervisor', 'Scout falhou — usando Instaloader como fallback');
      results.perfilFallback = await agentInstaloader(arroba, this);
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

  // ── Tentativa 1: Apify ─────────────────────────────────────
  if (process.env.APIFY_TOKEN) {
    try {
      const url = `https://api.apify.com/v2/acts/apify~instagram-profile-scraper/run-sync-get-dataset-items` +
                  `?token=${process.env.APIFY_TOKEN}&timeout=60&memory=256`;

      const resp = await fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ usernames: [username], resultsLimit: 12, proxy: { useApifyProxy: true } }),
        timeout: 70000
      });

      if (resp.ok) {
        const items = await resp.json();
        if (Array.isArray(items) && items.length > 0) {
          const p = items[0];
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
            video_url:   post.videoUrl   || ''
          })));
        }
      } else {
        const body = await resp.json().catch(() => ({}));
        sv.warn('scout', `Apify HTTP ${resp.status}: ${body?.error?.message || ''}`);
      }
    } catch(e) {
      sv.warn('scout', `Apify erro: ${e.message}`);
    }
  }

  // ── Tentativa 2: instagrapi com login ────────────────────
  if (process.env.IG_USERNAME && process.env.IG_PASSWORD) {
    sv.info('scout', 'Apify indisponível — usando instagrapi (conta IG configurada)...');
    const resultado = await agentInstagrapiLogin(username, sv);
    if (resultado) return resultado;
  } else {
    sv.warn('scout', 'IG_USERNAME/IG_PASSWORD não configurados — configure no .env para usar como fallback');
  }

  sv.err('scout', 'Todas as fontes falharam. Configure IG_USERNAME+IG_PASSWORD no .env ou recarregue os créditos do Apify.');
  return null;
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
    'confeitaria': ['confeitaria', 'bolosdecorados'],
    'doce': ['confeitaria', 'doces'],
    'roupa': ['modafeminina', 'lojaderoupas'],
    'moda': ['modafeminina', 'moda'],
    'restaurante': ['restaurante', 'gastronomia'],
    'estética': ['estetica', 'skincare'],
    'estetica': ['estetica', 'skincare'],
    'pet': ['petshop', 'cachorros'],
    'academia': ['academia', 'fitness'],
    'nutrição': ['nutricao', 'alimentacaosaudavel'],
    'nutricao': ['nutricao', 'alimentacaosaudavel'],
    'médico': ['saude', 'medicina'],
    'medico': ['saude', 'medicina'],
    'dentista': ['odontologia', 'dentista'],
    'advogado': ['direito', 'advogado'],
  };

  const nichoLower = nicho.toLowerCase();
  let hashtags = ['empreendedorismo', 'negocioslocais'];

  for (const [key, tags] of Object.entries(mapaHashtags)) {
    if (nichoLower.includes(key)) { hashtags = tags; break; }
  }

  sv.info('hashtag', `Buscando virais para #${hashtags[0]}...`);

  const url = `https://api.apify.com/v2/acts/apify~instagram-hashtag-scraper/run-sync-get-dataset-items` +
              `?token=${process.env.APIFY_TOKEN}&timeout=45&memory=256`;

  const resp = await fetch(url, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ hashtags: hashtags.slice(0, 2), resultsLimit: 15, proxy: { useApifyProxy: true } }),
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
      // Aceita timestamp em segundos (Unix) ou string ISO
      const ts = i.timestamp
        ? (typeof i.timestamp === 'number' ? i.timestamp * 1000 : new Date(i.timestamp).getTime())
        : null;
      if (ts && !isNaN(ts) && ts < corte90dias) return false; // descarta antigos
      return true;
    })
    .sort((a, b) => {
      // Mais recentes primeiro
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
      return `- "${(i.caption || 'sem legenda').substring(0, 120)}..." | ❤️ ${i.likesCount} | 💬 ${i.commentsCount} | Tipo: ${i.type}${dataPost ? ` | 📅 ${dataPost}` : ''}`;
    })
    .join('\n');

  sv.info('hashtag', `✅ ${items.length} posts virais encontrados para o nicho`);
  return resultado;
}

// ══════════════════════════════════════════════════════════════
//  AGENT: ANALYST — Claude Haiku — Análise Profunda
//  Sistema baseado no agente diagnostico-instagram.md
// ══════════════════════════════════════════════════════════════

const PROMPT_ANALYST = `Você é um Analista Sênior de Instagram para negócios locais brasileiros. Você analisa dados reais (prints, métricas coletadas automaticamente, transcrição de Reels) e entrega diagnósticos CIRÚRGICOS — não conselhos genéricos.

REGRAS ABSOLUTAS DE QUALIDADE:
❌ NUNCA invente dados, métricas ou informações do perfil que não estejam nos dados fornecidos
❌ NUNCA escreva "[Não foi fornecida nos dados coletados]" — se não há dado, diga o que foi coletado e analise com o que existe
❌ NUNCA diga "Publique mais conteúdo", "Interaja com seus seguidores", "Use hashtags relevantes", "Mantenha uma frequência consistente"
❌ NUNCA faça recomendações que se apliquem a QUALQUER conta — seja ESPECÍFICO para ESTE nicho e ESTE perfil
✅ SEMPRE analise COM OS DADOS REAIS fornecidos — bio real, posts reais com números reais, imagens reais
✅ SEMPRE cite números exatos dos dados: "Post de [tema] — [X] curtidas, [Y] comentários" (não invente)
✅ SEMPRE conecte cada diagnóstico ao nicho específico
✅ SEMPRE entregue: O QUÊ + COMO + POR QUÊ funciona para ESSE negócio
✅ SEMPRE priorize Pareto: 20% das ações que geram 80% do resultado

IMPORTANTE SOBRE OS DADOS:
- Os dados do perfil foram coletados AUTOMATICAMENTE pelo Scout (Apify ou Instagram API) em tempo real
- A bio, o número de seguidores, os posts com curtidas e legendas estão todos no contexto abaixo
- As imagens dos posts também foram baixadas e estão disponíveis para análise visual
- Se algum dado estiver ausente, diga explicitamente qual foi coletado e qual não foi — NUNCA invente o que falta

BENCHMARKS (use para diagnóstico):
| Métrica | Ruim | Médio | Bom | Excelente |
|---------|------|-------|-----|-----------|
| Alcance/seguidores (Reel) | <30% | 30-100% | 100-300% | >300% |
| Save rate | <0,5% | 0,5-1,5% | 1,5-3% | >3% |
| Share rate | <0,3% | 0,3-1% | 1-2% | >2% |
| Comentários/alcance | <0,1% | 0,1-0,5% | 0,5-1% | >1% |
| Engajamento geral | <1% | 1-3% | 3-6% | >6% |

ESTRUTURA OBRIGATÓRIA DO RELATÓRIO:

## 📊 DIAGNÓSTICO ENGRENE
### [Nome do Negócio] — @[arroba]

---

## 1. NOTA GERAL: [X]/10
**Justificativa técnica:** [baseada nos dados reais coletados — números, padrões, benchmarks]

---

## 2. SAÚDE DO PERFIL
- Seguidores: [número] | Seguindo: [número] | Ratio: [cálculo]
- Taxa de postagem: [frequência calculada se disponível]
- Bio: [avaliação técnica da bio atual]
- Diagnóstico geral: [o que os números revelam]
- **Gap crítico identificado:** [o maior problema desta conta especificamente]

---

## 3. ANÁLISE DE CONTEÚDO (posts reais)
[Analise cada post dos dados coletados + prints enviados]
Para os posts com maior engajamento:
- Post [N]: [tipo] — [curtidas/comentários/views] → Por que performou: [análise específica]
- **Padrão de sucesso identificado:** [o que os melhores posts têm em comum]
- **Padrão de fracasso identificado:** [o que os posts fracos têm em comum]

**Fórmula que já funciona para [nicho]:** [descrição específica]

---

## 4. ANÁLISE DO REEL ENVIADO
[Se transcrição disponível — analise gancho, estrutura, CTA, potencial viral]
- Gancho (primeiros 3 segundos): [avaliação]
- Estrutura do roteiro: [análise]
- CTA: [avaliação]
- Potencial viral: [nota /10 + justificativa]
- **Como melhorar este Reel específico:** [3 ações concretas]

[Se não há Reel — pule esta seção]

---

## 5. ANÁLISE VISUAL (prints do feed)
[Analise os prints enviados]
- Identidade visual: [consistente/inconsistente + o que precisa mudar]
- Qualidade das imagens: [avaliação técnica]
- Legibilidade nos stories/feed: [avaliação]
- **O que mudar primeiro:** [ação específica de maior impacto]

---

## 6. CONTEÚDOS VIRAIS DO NICHO AGORA
[Baseado nos dados coletados do nicho — se disponíveis]
Top 3 temas que estão funcionando no nicho agora:
1. [Tema] — Estrutura que está viralizando: [análise]
2. [Tema] — Por que esse formato funciona para [nicho]: [análise]
3. [Tema] — Como adaptar para [negócio específico]: [aplicação]

---

## 7. BIO OTIMIZADA
**Bio atual:** [texto da bio se coletado]
**Bio proposta:**
\`\`\`
[Nova bio — máximo 150 caracteres]
[Link sugerido na bio]
\`\`\`
**Por que funciona:** [o que foi otimizado e por quê]

---

## 8. 5 GANCHOS DE REEL PARA [NICHO]

**Gancho 1 — Provocação:**
> "[Texto do gancho — máximo 10 palavras, específico para o nicho]"
*Por que vai funcionar:* [justificativa técnica + qual emoção ativa]

**Gancho 2 — Inversão de Crença:**
> "[Texto do gancho]"
*Por que vai funcionar:* [justificativa]

**Gancho 3 — Prova Social:**
> "[Texto do gancho]"
*Por que vai funcionar:* [justificativa]

**Gancho 4 — Urgência/Escassez:**
> "[Texto do gancho]"
*Por que vai funcionar:* [justificativa]

**Gancho 5 — Curiosidade/Segredo:**
> "[Texto do gancho]"
*Por que vai funcionar:* [justificativa]

---

## 9. CALENDÁRIO — PRÓXIMAS 4 SEMANAS

**Semana 1 — Autoridade:**
- Seg: [tema específico ao nicho] | Formato: [Reel/Carrossel] | Gancho: [texto]
- Qua: [tema] | Formato: | Gancho:
- Sex: [tema] | Formato: | Gancho:

**Semana 2 — Atração (alcance):**
[mesma estrutura]

**Semana 3 — Conversão:**
[mesma estrutura]

**Semana 4 — Relacionamento:**
[mesma estrutura]

---

## 10. PLANO DE ATAQUE — 90 DIAS

### 🔴 URGENTE (Esta semana):
1. [Ação específica] → Impacto esperado: [resultado mensurável]
2. [Ação específica] → Impacto esperado: [resultado mensurável]
3. [Ação específica] → Impacto esperado: [resultado mensurável]

### 🟡 IMPORTANTE (Próximo mês):
1. [Estratégia específica para o nicho]
2. [Estratégia específica]
3. [Estratégia específica]

### 🟢 ESTRATÉGICO (90 dias):
1. [Meta de crescimento realista baseada nos dados atuais]
2. [Estratégia de monetização para o nicho]

---

## 11. MÉTRICAS PARA MONITORAR
**Em 30 dias, acompanhe:**
- Alcance semanal: meta [X] (base atual: [Y])
- Taxa de engajamento: meta [X%] (base atual: [Y%])
- Novos seguidores/semana: meta [X]

---

## 12. SEU PRÓXIMO PASSO

Com base no diagnóstico acima, o gap mais crítico identificado no seu perfil é: **[resumir em 1 frase o gap crítico da seção 2]**.

O **Método Clientes no Direct** foi desenvolvido especificamente para negócios locais como o seu. A [Parte X] do método resolve exatamente esse gap — [conectar o gap ao módulo específico do método: Diagnóstico / Perfil / Os 5 Posts / Sequência de Venda / Plano 30 dias].

Com o método você vai:
- Saber exatamente qual conteúdo postar para atrair clientes (não só seguidores)
- Ter um Protocolo C.L.I.E.N.T.E. para transformar mensagens no Direct em vendas
- Aplicar os 5 tipos de post que funcionam para o seu nicho específico

> **Disponível no Engrene Experience** — converse com a Suellen para saber como aplicar o método no seu negócio.

---
*Diagnóstico gerado por Squad IA Engrene | Dados coletados em tempo real*`;

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
    const { nome, nicho, arroba, objetivo, seguidores, frequencia, descricao } = req.body;

    // ── Validação básica ────────────────────────────────────
    if (!nome?.trim() || !nicho?.trim() || !arroba?.trim()) {
      clearInterval(keepAlive);
      return res.end(JSON.stringify({ sucesso: false, erro: 'Nome, nicho e @ do Instagram são obrigatórios.' }));
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
      return res.end(JSON.stringify({
        sucesso: false,
        erro: `Não consegui acessar o perfil @${arroba}. Verifique se o @ está correto e se a conta é pública.`
      }));
    }

    // ── Prepara imagens para o Analyst (Claude) ─────────────
    sv.info('analyst', 'Preparando contexto visual...');
    const imagensConteudo = [];

    // 1. Imagens automáticas baixadas do Apify (posts reais do perfil)
    if (squadResultado.imagensPosts?.length > 0) {
      imagensConteudo.push({ type: 'text', text: `\n--- IMAGENS REAIS DO FEED (${squadResultado.imagensPosts.length} posts baixados automaticamente) ---` });
      for (const [i, img] of squadResultado.imagensPosts.entries()) {
        imagensConteudo.push({ type: 'text', text: `\nPost ${i+1} — ❤️ ${img.curtidas} curtidas${img.views ? ` | 👁️ ${img.views} views` : ''} | Legenda: ${img.legenda || '(sem legenda)'}` });
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
- Nome: ${perfilData.nome}
- Bio: ${perfilData.bio}
- Link na bio: ${perfilData.link_bio || 'não informado'}
- Seguidores: ${perfilData.seguidores?.toLocaleString('pt-BR')}
- Seguindo: ${perfilData.seguindo?.toLocaleString('pt-BR')}
- Total de posts: ${perfilData.posts_count}
- Conta comercial: ${perfilData.is_business ? 'Sim' : 'Não'}
- Categoria: ${perfilData.categoria || 'não informada'}
- Verificado: ${perfilData.verificado ? 'Sim' : 'Não'}

ÚLTIMOS ${perfilData.posts?.length || 0} POSTS (dados reais coletados agora):
${(perfilData.posts || []).map((p, i) =>
  `Post ${i+1} [${p.tipo}${p.is_video ? ' · Vídeo' : ''}] — ❤️ ${p.curtidas} | 💬 ${p.comentarios}${p.views ? ` | 👁️ ${p.views} views` : ''}
Legenda: ${p.legenda || '(sem legenda)'}`
).join('\n\n')}
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
- Objetivo principal: ${objetivo}
- Seguidores declarados: ${seguidores || (perfilData?.seguidores || 'não informado')}
- Frequência de postagem: ${frequencia || 'não informada'}
- Descrição do negócio: ${descricao || ''}

${ctxPerfil}
${ctxReel}
${squadResultado.conteudosVirais ? `\nCONTEÚDOS VIRAIS DO NICHO "${nicho}" (coletados agora via Apify):\n${squadResultado.conteudosVirais}` : ''}
`.trim();

    // ── Analyst: Claude Haiku — análise profunda ─────────────
    sv.info('analyst', `Chamando Claude Haiku para análise profunda...`);

    const response = await anthropic.messages.create({
      model: 'claude-haiku-4-5',
      max_tokens: 8000,
      system: PROMPT_ANALYST,
      messages: [{
        role: 'user',
        content: [
          { type: 'text', text: contextoCompleto },
          ...imagensConteudo,
          { type: 'text', text: '\nCom base em TODOS esses dados reais (perfil coletado automaticamente + prints + transcrição + virais do nicho), faça o diagnóstico completo conforme estrutura. Seja CIRÚRGICO e ESPECÍFICO — cite os números reais fornecidos.' }
        ]
      }]
    });

    const relatorio = response.content?.[0]?.text ?? 'Análise não disponível — tente novamente.';
    const tokens    = (response.usage?.input_tokens || 0) + (response.usage?.output_tokens || 0);

    sv.info('analyst', `✅ Análise concluída — ${tokens} tokens usados`);

    // Limpa uploads
    uploadedFiles.forEach(f => { try { fs.unlinkSync(f); } catch(e) {} });

    clearInterval(keepAlive);
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
      return res.status(400).json({ sucesso: false, erro: 'Nome, nicho e @ são obrigatórios.' });
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
      max_tokens: 8000,
      system: PROMPT_ANALYST,
      messages: [{
        role: 'user',
        content: [
          { type: 'text', text: contextoFinal },
          { type: 'text', text: '\nCom base nos dados informados, faça o diagnóstico completo conforme estrutura. Use EXATAMENTE os números fornecidos. Seja CIRÚRGICO e ESPECÍFICO para o nicho.' }
        ]
      }]
    });

    const relatorio = response.content?.[0]?.text ?? 'Análise não disponível.';
    const tokens    = (response.usage?.input_tokens || 0) + (response.usage?.output_tokens || 0);

    sv.info('analyst', `✅ Análise manual concluída — ${tokens} tokens`);

    res.json({
      sucesso: true,
      relatorio,
      tokens_usados: tokens,
      fontes: { perfil: 'manual', transcricao: 'não disponível', virais: conteudosVirais ? 'apify' : 'não coletado' }
    });

  } catch(error) {
    sv.err('supervisor', error.message);
    res.status(500).json({ sucesso: false, erro: error.message });
  } finally {
    analiseEmCurso--;
  }
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
