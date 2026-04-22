# AN_KE_117 - Explicit Write Instruction for LLM Executors

**Type:** Veto Heuristic
**Zone:** 💎 4% Excelencia
**Agent:** @oalanicolas
**Pattern:** Tool Blindness
**Source:** [SOURCE: sessao sinkra-hub 4775d0c3 — domain-decoder runner]
**Tags:** [Agnostic, Automation, Pipeline]

## Purpose

LLMs em modo agente possuem tools (Read, Write, Edit, Bash) mas NÃO as usam proativamente a menos que o prompt instrua explicitamente. O caso mais crítico: LLM analisa código, gera output textual, diz "pronto" — mas nunca chamou Write tool. Resultado: zero arquivos em disco. O prompt DEVE conter instrução explícita "use Write tool to save files to disk" com warning de que PHASE_COMPLETE sem arquivos = gate failure + retry.

## Configuration (True L3-State)

```yaml
AN_KE_117:
  name: "Explicit Write Instruction for LLM Executors"
  zone: "excelencia"
  trigger: "Prompt template para LLM executor que deve produzir arquivos em disco."

  rule: |
    SE prompt template envia LLM para executar fase de pipeline
    ENTÃO incluir instrução explícita: "Use the Write tool to save each output file to disk"
    E incluir warning: "PHASE_COMPLETE without files on disk = gate failure + retry"
    NUNCA assumir que LLM vai usar Write tool por iniciativa própria

  failure_modes:
    omission: "LLM gera output textual brilhante, diz PHASE_COMPLETE, mas zero arquivos em disco. Gate falha. Retry desperdiça tokens."
    misapplication: "Forçar Write para TUDO (incluindo análise exploratória) burocratiza fases que não precisam de output em disco."

  evidence_threshold: "[EMPIRICAL]"
  evidence:
    - "[SOURCE: sessão sinkra-hub 4775d0c3] 'LLM not writing files: prompt now explicitly instructs to use the Write tool to save files to disk, with warning that PHASE_COMPLETE without files will trigger gate failure and retry'"
```

## Decision Tree (Strict Format)

```text
STEP_1: IF (prompt template expects file outputs)
          THEN add explicit Write tool instruction
          AND add gate failure warning
STEP_2: IF (phase is analysis-only, no file output expected)
          THEN skip Write instruction (text response is sufficient)
NEVER:
  - Assume LLM will proactively use tools without instruction
  - Rely on LLM "understanding" that files need to be on disk
```

## Validation & Cross-Mind Divergence

### Self-Validation Ask
1. "O prompt template menciona EXPLICITAMENTE 'Write tool' ou equivalente? Se não, LLM vai gerar texto e dizer pronto."

### Divergence Analysis (Baseline IA vs Mente Zero)
- **Base LLM Tendency:** Gerar análise textual completa e sinalizar completion sem persistir.
- **Mind Zero Override:** "Sem Write, sem completion. Disco é a verdade."

## Behavioral Evidence (Real-World Application)

**Example:** "Phase 2 que gerou análise perfeita mas zero arquivos"
- **Context:** Domain decoder Phase 2 (characterization). LLM analisou 50+ arquivos, gerou assessment completo.
- **Information Available:** Output textual excelente no response. Nenhum arquivo em outputs/.
- **Heuristic Application:** Adicionado "MANDATORY: Use Write tool" no prompt template.
- **Outcome:** Todas as fases subsequentes produzem arquivos em disco consistentemente.
