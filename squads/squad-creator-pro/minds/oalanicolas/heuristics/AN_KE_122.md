# AN_KE_122 - Enum-ify Pipeline Status Strings

**Type:** Architecture Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Type Safety at Boundaries
**Source:** [SOURCE: sessão sinkra-hub 4f9f58cf — domain-decoder quality gaps]
**Tags:** [Agnostic, Automation, Pipeline]

## Purpose

Pipelines com status como raw strings ("in_progress", "complete", "failed") funcionam inicialmente mas criam bugs silenciosos com o tempo: typos ("complte"), inconsistências ("done" vs "complete"), e impossibilidade de IDE autocomplete. O fix é criar str(Enum) classes que são backward-compatible (serializam como string) mas previnem typos em compile/import time. Enum-ificar status é investimento de 10 minutos que previne horas de debugging.

## Configuration (True L3-State)

```yaml
AN_KE_122:
  name: "Enum-ify Pipeline Status Strings"
  zone: "impacto"
  trigger: "Pipeline com 3+ status strings usados em comparações, state persistence, ou condicionais."

  rule: |
    SE pipeline usa status como raw strings em 3+ locais
    ENTÃO criar str(Enum) classes (backward-compatible via str serialization)
    E usar Enum em todas comparações e state transitions
    NUNCA comparar raw strings para status em pipelines com 3+ fases

  failure_modes:
    omission: "Typo em status string ('in_progres') silenciosamente pula fase. Debugging pode levar horas."
    misapplication: "Enum-ificar campos que são genuinamente dinâmicos (user input, free text) adiciona rigidez desnecessária."

  evidence_threshold: "[EMPIRICAL]"
  evidence:
    - "[SOURCE: sessão sinkra-hub 4f9f58cf] 'PhaseStatus and PipelineStatus str enums replace raw strings, preventing typos and enabling IDE autocomplete. Backward compatible via str(Enum) serialization.'"
```

## Decision Tree (Strict Format)

```text
STEP_1: IF (pipeline has 3+ status values used in comparisons)
          THEN create str(Enum) class
          AND replace all string literals with Enum members
STEP_2: IF (status is persisted to JSON/YAML)
          THEN ensure str(Enum) serializes transparently (backward compat)
NEVER:
  - Compare raw strings for status in pipeline conditionals
  - Create Enum for genuinely dynamic fields (user input, descriptions)
```

## Validation & Cross-Mind Divergence

### Self-Validation Ask
1. "Grep por strings de status no codebase. Quantos locais? Se > 3, Enum."

### Divergence Analysis (Baseline IA vs Mente Zero)
- **Base LLM Tendency:** Usar strings porque é mais simples inicialmente.
- **Mind Zero Override:** "10 minutos de Enum agora = 0 typo bugs depois. ROI infinito."
