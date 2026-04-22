# AN_KE_116 - LLM Completion Mirage (Status Revert on Gate Fail)

**Type:** Architecture Heuristic
**Zone:** 🧠 0,8% Genialidade
**Agent:** @oalanicolas
**Pattern:** Phantom Completion
**Source:** [SOURCE: sessão sinkra-hub 4775d0c3 — domain-decoder runner, primeiro run real]
**Tags:** [Agnostic, Automation, Pipeline]

## Purpose

LLMs sinalizam "PHASE_COMPLETE" textualmente mesmo quando não cumpriram o contrato real (ex: nenhum arquivo escrito em disco). Se o pipeline marca o status como "complete" baseado na sinalização textual, a próxima iteração do loop vê "complete" e PULA a fase — criando uma fase fantasma que nunca executou. O fix é contraintuitivo: o status DEVE ser revertido para "in_progress" quando o gate de qualidade falha, independente do que o LLM disse.

## Configuration (True L3-State)

```yaml
AN_KE_116:
  name: "LLM Completion Mirage (Status Revert on Gate Fail)"
  zone: "genialidade"
  trigger: "Pipeline multi-fase com LLM executor onde status é persistido entre iterações."

  sys_tension:
    tension_with: "AN_KE_088 (Runners as Product Process)"
    resolution: "Runners produtizados DEVEM ter gate de qualidade. Sem gate, runner vira automação de lixo."

  rule: |
    SE LLM sinaliza PHASE_COMPLETE MAS gate de qualidade falha (ex: zero arquivos em disco)
    ENTÃO REVERTER status para "in_progress" antes do retry
    NUNCA confiar na sinalização textual do LLM como fonte de verdade — disco é a verdade

  failure_modes:
    omission: "Pipeline marca 'complete', próximo loop pula fase. Resultado: fase fantasma sem output real."
    misapplication: "Reverter status em TODA falha (incluindo falhas parciais válidas) pode causar loops infinitos. Gate deve ter threshold claro."

  evidence_threshold: "[EMPIRICAL]"
  evidence:
    - "[SOURCE: sessão sinkra-hub 4775d0c3] 'Gate fail didnt revert status: when LLM signals PHASE_COMPLETE but E9 gate fails (no files on disk), the next iteration saw complete and skipped'"
```

## Decision Tree (Strict Format)

```text
STEP_1: IF (LLM signals PHASE_COMPLETE)
          THEN verify gate conditions (files exist? validation passed? metrics OK?)
          AND VETO (status update if gate fails)
STEP_2: IF (gate FAILS)
          THEN revert status to "in_progress"
          AND increment retry counter
STEP_3: IF (retry > max_retries)
          THEN HALT with explicit error (not silent skip)
NEVER:
  - Trust LLM text output as completion proof
  - Let status remain "complete" when disk state contradicts
```

## Confidence Requirements & Reversibility

- **High-Commitment (One-Way Door):** Status persistence in state files — wrong status propagates to all future iterations.
- **Tactical (Two-Way Door):** Retry count tuning (3 vs 5) — adjustable without architectural change.

## Validation & Cross-Mind Divergence

### Self-Validation Ask
1. "O gate de qualidade verifica DISCO ou TEXTO? Se texto, a heurística não está aplicada."

### Divergence Analysis (Baseline IA vs Mente Zero)
- **Base LLM Tendency:** Aceitar "PHASE_COMPLETE" como verdade e prosseguir.
- **Mind Zero Override:** Disco é a verdade. LLM mente. Gate verifica disco. Status reverte se disco contradiz.

## Behavioral Evidence (Real-World Application)

**Example:** "O Domain Decoder que pulou Phase 2"
- **Context:** Primeiro run real do decoder pipeline com 6 fases.
- **Information Available:** LLM sinalizou PHASE_COMPLETE em Phase 2, mas não usou Write tool.
- **Heuristic Application:** Adicionado revert de status + prompt explícito "use Write tool".
- **Outcome:** Próximos runs executam todas as fases corretamente — zero fases fantasma.
