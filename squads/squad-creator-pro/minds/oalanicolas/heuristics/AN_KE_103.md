# AN_KE_103 - Local Caching Over Live Database
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 160b90cc, aiox-stage — "ao invés de pegagarmos do banco, pegarmos de outputs locais"]

## Purpose

A performance transversal do Supabase degrada drasticamente quando se roda `fetch()` de campos Text Text massivos (VTT Transcripts, livros brutos). Muitas pipelines do ecossistema operam como Data Miners que precisam esmiuçar linguística profunda. A regra impõe que sistemas de consulta para processos batch ou análises LLM leiam primordialmente do File System (onde as transições ETL baixaram os docs pré-processados e purgados de erros). O banco relacional é para Estado e Rotas; Arquivos massivos repousam na máquina.

## Configuration

```yaml
AN_KE_103:
  name: "Local Caching Over Live Database"
  zone: "genialidade"
  trigger: "Criando pipelines de IA (RAG) ou processamento batch textual longo (chunks/livros)."

  rule: |
    SE precisar ler ou consumir ativos textuais/binários mastodônticos em execução interna
    ENTÃO PREFIRA OS ASSETS LOCAIS (`outputs/transcriptions`, `/docs`) como fonte primária imutável.
    Otimiza a janela temporal e economiza I/O da pool do banco remoto.

  veto_condition:
    trigger: "Agent constrói um iterador que faz 40 queries em série de `SELECT raw_transcript FROM content_vtt` num banco prod."
    action: "VETO — 'analise se nao seria melhor pegarmos de /outputs/transcriptions onde elas já foram tratadas (...) e além disso nao precisa se coenctar no banco já estao locais'."

  evidence:
    - "[SOURCE: sessão 160b90cc, aiox-stage] 'ao invés de pegagarmos do banco, pegarmos de outputs/transcriptions onde elas já foram tratadas e estao sem tantos erros de portugues, e além disso nao precisa se coenctar no banco já estao locais'"

  sys_tension:
    tension_with: "AN_KE_067 (Database as Single Source of Truth) — Conflito entre FS local para leitura imutável vs Banco como fonte canônica."
    resolution: "Paradoxo aparente: Local FS prioriza performance em leitura; Banco relacional prioriza consistência. Resolução: FS é primária para LEITURA imutável (após ETL); Banco é primária para ESTADO vivo e transações. Docs processados no FS são snapshots validados — mudanças futuras retornam ao banco e regeneram o cache local."
```

## Decision Tree

```javascript
IF (accessing_massive_documents_for_llm_chain_or_script)
  STEP_1: QUERY architecture layout (Are these raw transcripts? RAG sources? Long docs?)
  STEP_2: CHECK existence in `./outputs`, `./data`, or `./sources`.
  STEP_3: IF (Files Exist locally)
    -> Stream directly via file-system paths (`fs.readFileSync`).
    -> Bypass Supabase SQL completely for these blob accesses.
```

## Failure Modes

### Overhead de Conexões VTT
- **Trigger:** Script do backend busca extrair menções à palavra 'AIOX' na tabela gigante de vtt_logs em tempo de requisição de chat.
- **Manifestation:** A resposta do LLM ganha latência de 8 a 15 segundos só pelo tráfego de saída do Supabase via pool.
- **Prevention:** Assuma o disco local como a source primária para blocos literários mortos/tratados.

## Validation

✅ **Paradoxo Identificado:** Conflito entre "Local FS como primária (performance)" vs "Banco como single source of truth (consistência)"

✅ **Resolução Articulada:** Camadas complementares — FS para snapshots imutáveis pós-ETL; Banco para estado vivo e mudanças futuras que regeneram cache

✅ **sys_tension Adicionado:** Referência cruzada com AN_KE_050 explicita a tensão sistêmica

✅ **Aplicabilidade Confirmada:** Heurística válida para RAG, análise batch, processamento LLM de documentos massivos
