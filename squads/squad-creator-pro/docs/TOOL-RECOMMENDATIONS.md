# Recomendações de Ferramentas para Squad Creator

> **Nota:** Este documento é um snapshot de 2026-02-05. Para o catálogo atualizado de tools, consulte `data/tool-registry.yaml`.

> **Documento gerado por:** Squad Architect
> **Data:** 2026-03-27
> **Baseado em:** Tool Discovery para domínio squad-creator

---

## Resumo Executivo

Este documento consolida as ferramentas recomendadas para potencializar o Squad Creator, identificadas através do comando `*discover-tools squad-creator`.

### Capability Gaps Identificados

| Gap | Impacto | Solução Recomendada |
|-----|---------|---------------------|
| **Source Acquisition** | 🔴 CRÍTICO | mcp-youtube-transcript + Firecrawl |
| **Deep Research** | 🔴 CRÍTICO | mcp-perplexity + Exa (já instalado) |
| **Knowledge Storage** | 🟡 ALTO | Knowledge Graph Memory |
| **Web Scraping** | 🟡 ALTO | Firecrawl MCP |
| **Content Processing** | 🟢 MÉDIO | yt2doc + summarize CLI |

---

## Ferramentas Recomendadas

### 🏆 Prioridade 1: Quick Wins (Instalar ASAP)

#### 1. mcp-youtube-transcript

**Propósito:** Extrair transcrições de vídeos YouTube para clonagem de minds.

```bash
# Instalação
npx -y @jkawamoto/mcp-youtube-transcript
```

**Por que é crítico:**
- Transcripts de entrevistas são a fonte #1 de Voice DNA
- Keynotes e masterclasses capturam Thinking DNA
- Suporte multi-idioma (experts internacionais)

**Integração:**
- `wf-auto-acquire-sources.yaml` - Fase 1
- `collect-sources.md` - Aquisição automática
- `*auto-acquire-sources` - Comando standalone

**Métricas:**
| Métrica | Valor |
|---------|-------|
| GitHub Stars | 271 |
| Impacto | 10/10 |
| Esforço | Baixo |
| API Key | Não requer |

---

#### 2. Firecrawl MCP

**Propósito:** Scraping avançado de websites, artigos e blogs de experts.

```bash
# Instalação
env FIRECRAWL_API_KEY=fc-YOUR_KEY npx -y firecrawl-mcp
```

**Por que é crítico:**
- Converte qualquer URL em markdown limpo (LLM-ready)
- Extrai artigos de blogs de experts
- Lida com anti-bot measures
- Batch processing para múltiplas URLs

**Integração:**
- `wf-auto-acquire-sources.yaml` - Fases 2 e 4
- `deep-research-pre-agent.md`
- `collect-sources.md`

**Métricas:**
| Métrica | Valor |
|---------|-------|
| GitHub Stars | 3,303 |
| Impacto | 10/10 |
| Esforço | Baixo |
| API Key | Sim (free tier disponível) |

**Obter API Key:**
1. Acesse https://firecrawl.dev
2. Crie conta gratuita
3. Copie API key do dashboard

---

### 📅 Prioridade 2: Enhancement (Próxima Semana)

#### 3. mcp-perplexity

**Propósito:** Deep research com citações para validar frameworks de experts.

```bash
# Instalação
npx -y mcp-perplexity
```

**Por que é importante:**
- Research com citações (fontes verificáveis)
- Validar existência de frameworks documentados
- Complementa Exa para research iterativo
- Melhor para perguntas complexas

**Integração:**
- `mind-research-loop.md` - Iterações de pesquisa
- `deep-research-pre-agent.md`

**Métricas:**
| Métrica | Valor |
|---------|-------|
| Impacto | 9/10 |
| Esforço | Baixo |
| API Key | Sim |

---

#### 4. Knowledge Graph Memory

**Propósito:** Persistir Mind DNA entre sessões.

```bash
# Instalação
npx -y @modelcontextprotocol/server-memory
```

**Por que é importante:**
- Armazena Voice DNA e Thinking DNA
- Mantém contexto entre sessões
- Relaciona minds com frameworks
- Evita re-processamento

**Integração:**
- `wf-clone-mind.yaml` - Persistir outputs
- `create-agent.md` - Recuperar DNA

**Métricas:**
| Métrica | Valor |
|---------|-------|
| GitHub Stars | 77,100 (official) |
| Impacto | 9/10 |
| Esforço | Médio |
| API Key | Não |

---

### 🔮 Prioridade 3: Advanced (Futuro)

#### 5. Supadata MCP

Multi-platform transcript extraction (YouTube, TikTok, Twitter).

```bash
npx -y supadata-mcp
```

**Quando usar:** Experts com presença forte em social media.

---

#### 6. mcp-omnisearch

Unified access to multiple search engines (Tavily, Brave, Kagi, Perplexity).

```bash
# Requer setup mais complexo
```

**Quando usar:** Quando Exa não encontra resultados suficientes.

---

#### 7. Cognee MCP

Advanced knowledge graph with LLM memory.

**Quando usar:** Squads muito complexos com muitos minds inter-relacionados.

---

## CLI Tools (Complementares)

### yt2doc

YouTube e Apple Podcasts para Markdown.

```bash
pip install yt2doc
```

**Uso:** Backup quando MCP não disponível, ou para Apple Podcasts.

---

### summarize

CLI + Chrome extension para summarization.

```bash
npm i -g @steipete/summarize
```

**Uso:** Summarizar URLs rapidamente via terminal.

---

### yt-dlp

Download de vídeos YouTube (dependência de vários MCPs).

```bash
brew install yt-dlp
```

**Uso:** Dependência para YouTube MCPs e download de áudio para Whisper.

---

## Matriz de Decisão

```
                    IMPACTO
                    Alto ─────────────────────┐
                         │ 🎯 FAZER AGORA     │
                         │                    │
                         │ • mcp-youtube-     │
                         │   transcript       │
                         │ • Firecrawl MCP    │
                         │ • mcp-perplexity   │
            ─────────────┼────────────────────┤
                         │ 📅 FAZER DEPOIS    │
                         │                    │
                         │ • Knowledge Graph  │
                         │ • Supadata         │
                    Baixo└────────────────────┘
                         Baixo          Alto
                              ESFORÇO
```

---

## Plano de Instalação

### Fase 1: Hoje (30 min)

```bash
# 1. YouTube Transcript MCP
# Adicionar ao .mcp.json ou ~/.claude/settings.json
{
  "mcpServers": {
    "youtube-transcript": {
      "command": "npx",
      "args": ["-y", "@jkawamoto/mcp-youtube-transcript"]
    }
  }
}

# 2. Firecrawl MCP (requer API key)
{
  "mcpServers": {
    "firecrawl": {
      "command": "npx",
      "args": ["-y", "firecrawl-mcp"],
      "env": {
        "FIRECRAWL_API_KEY": "fc-YOUR_KEY"
      }
    }
  }
}
```

### Fase 2: Esta Semana

```bash
# 3. Perplexity MCP
{
  "mcpServers": {
    "perplexity": {
      "command": "npx",
      "args": ["-y", "mcp-perplexity"],
      "env": {
        "PERPLEXITY_API_KEY": "pplx-YOUR_KEY"
      }
    }
  }
}

# 4. Knowledge Graph Memory
{
  "mcpServers": {
    "memory": {
      "command": "npx",
      "args": ["-y", "@modelcontextprotocol/server-memory"]
    }
  }
}
```

---

## Integração com Workflows

### wf-auto-acquire-sources.yaml (v2.0)

```yaml
# Novo workflow criado usando estas ferramentas
phases:
  - phase: 1
    name: "YouTube Mining"
    tool_primary: mcp-youtube-transcript
    tool_fallback: exa + WebFetch

  - phase: 2
    name: "Book Mining"
    tool_primary: firecrawl-mcp
    tool_fallback: WebFetch

  - phase: 4
    name: "Article Mining"
    tool_primary: firecrawl-mcp
    tool_fallback: WebFetch
```

### Fallbacks Implementados

Cada fase tem fallback para quando MCPs não estão instalados:

| MCP | Fallback |
|-----|----------|
| mcp-youtube-transcript | Exa search + WebFetch para transcripts existentes |
| firecrawl-mcp | WebFetch nativo |
| mcp-perplexity | Exa (já instalado) |
| knowledge-graph-memory | Arquivos YAML locais |

---

## Ferramentas Já Instaladas

O squad-creator já tem acesso a:

| Ferramenta | Status | Uso |
|------------|--------|-----|
| **Exa MCP** | ✅ Instalado | Web search, research |
| **Context7 MCP** | ✅ Instalado | Documentação de libraries |
| **Desktop Commander** | ✅ Instalado | File operations, PDF, Excel |
| **WebFetch** (nativo) | ✅ Disponível | Fetch de URLs |
| **WebSearch** (nativo) | ✅ Disponível | Search básico |

---

## Checklist de Implementação

- [ ] Obter API key do Firecrawl (free tier)
- [ ] Instalar mcp-youtube-transcript
- [ ] Instalar firecrawl-mcp
- [ ] Testar `*auto-acquire-sources` com novo workflow
- [ ] Obter API key do Perplexity (se desejado)
- [ ] Instalar mcp-perplexity
- [ ] Instalar knowledge-graph-memory
- [ ] Atualizar `.mcp.json` do projeto

---

## Referências

- [MCP Servers Registry](https://github.com/modelcontextprotocol/servers)
- [Glama MCP Directory](https://glama.ai/mcp/servers)
- [Firecrawl Documentation](https://firecrawl.dev/docs)
- [tool-registry.yaml](../data/tool-registry.yaml) - Registro completo

---

**Squad Architect | Tool Recommendations v1.0**
*"The right tools make elite mind cloning possible at scale."*
