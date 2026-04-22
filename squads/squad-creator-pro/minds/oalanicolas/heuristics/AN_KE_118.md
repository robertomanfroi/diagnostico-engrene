# AN_KE_118 - Incremental Context Accumulation in Multi-Phase Pipelines

**Type:** Architecture Heuristic
**Zone:** 🧠 0,8% Genialidade
**Agent:** @oalanicolas
**Pattern:** Snowball Context
**Source:** [SOURCE: sessão sinkra-hub d571db80 — domain-decoder runner, prior phase injection]
**Tags:** [Agnostic, Automation, Pipeline, SINKRA]

## Purpose

Pipelines multi-fase onde cada fase é executada por um LLM perdem contexto entre fases. A solução ingênua é passar TODO o source como contexto em cada fase — explodindo tokens e diluindo foco. A solução correta: injetar outputs de fases anteriores como MANDATORY READS antes do source, em ordem cronológica. Cada fase acumula incrementalmente: Phase 0 sem priors, Phase 1 lê Phase 0 outputs, Phase 2 lê Phase 0+1, etc. Isso cria um efeito bola de neve onde cada fase REFINA o entendimento anterior em vez de redescobrir do zero.

## Configuration (True L3-State)

```yaml
AN_KE_118:
  name: "Incremental Context Accumulation in Multi-Phase Pipelines"
  zone: "genialidade"
  trigger: "Pipeline com 3+ fases executadas por LLM onde cada fase depende de descobertas das anteriores."

  sys_tension:
    tension_with: "Context window limits vs completude de informação"
    resolution: "Prior phase outputs são RESUMOS estruturados (YAML/MD), não raw source. Compactos por natureza."

  rule: |
    SE pipeline multi-fase com LLM executor
    ENTÃO build_prior_context() scans completed phase dirs e gera MANDATORY READS section
    E prompt template enforça: "Read ALL prior phase outputs BEFORE reading source codebase"
    NUNCA enviar apenas source codebase sem prior phase context — cada fase redescobre do zero

  failure_modes:
    omission: "Cada fase redescobre insights que a fase anterior já encontrou. Redundância massiva, inconsistência entre fases."
    misapplication: "Injetar prior context de fases MUITO anteriores em pipelines longos (10+ fases) pode diluir foco. Considerar sliding window."

  evidence_threshold: "[EMPIRICAL]"
  evidence:
    - "[SOURCE: sessão sinkra-hub d571db80] 'build_prior_context() scans outputs/decoded/{slug}/{phase_dir}/ for all completed phases and generates a MANDATORY READS section listing every file with its repo-relative path and size'"
    - "[SOURCE: sessão 02ad333a, decoder.sh] 'Evolução: prior context mudou de LISTA de arquivos (LLM precisa fazer Read) para CONTEÚDO INLINE (3KB/file truncado direto no prompt). Elimina turns gastos em Read — LLM usa turns para ler SOURCE em vez de prior outputs.'"
    - "[SOURCE: sessão opus run] 'Confirmado: prompt cresce 3878→4951→5920 bytes entre fases. Zero fallback para Gemini. Context incremental inline funciona. Anthropic confirma: structured context objects (200-500 tokens) >> full forwarding (5-20K).'"
```

## Decision Tree (Strict Format)

```text
STEP_1: IF (multi-phase pipeline, phase N > 0)
          THEN scan completed phases 0..N-1 for output files
          AND generate MANDATORY READS section with paths + sizes
STEP_2: IF (total prior context > 50% of context window)
          THEN apply sliding window: keep last 3 phases only
STEP_3: Inject prior context BEFORE source codebase in prompt
NEVER:
  - Start a phase without reading prior phase outputs
  - Pass raw source as the only context (ignoring prior work)
```

## Validation & Cross-Mind Divergence

### Self-Validation Ask
1. "A Phase N recebe outputs das Phases 0..N-1? Se não, está redescobindo o que já sabe."

### Divergence Analysis (Baseline IA vs Mente Zero)
- **Base LLM Tendency:** Tratar cada prompt como independente — sem memória entre fases.
- **Mind Zero Override:** "Pipeline é INCREMENTAL. Cada fase constrói sobre a anterior. Sem prior context, não é pipeline — é N execuções desconectadas."

## Behavioral Evidence (Real-World Application)

**Example:** "Domain Decoder Phase 3 que contradisse Phase 1"
- **Context:** Sem prior injection, Phase 3 (extraction) gerou bounded contexts diferentes de Phase 1 (discovery).
- **Information Available:** Phase 1 já tinha mapeado os contextos. Phase 3 não leu.
- **Heuristic Application:** build_prior_context() injeta MANDATORY READS.
- **Outcome:** Phase 3+ consistentes com descobertas anteriores. Zero contradições inter-fase.
