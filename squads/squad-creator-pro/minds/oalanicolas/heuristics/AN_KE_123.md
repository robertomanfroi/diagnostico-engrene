# AN_KE_123 - JSONL Audit Trail Over Text Logs

**Type:** Architecture Heuristic
**Zone:** 💎 4% Excelencia
**Agent:** @oalanicolas
**Pattern:** Structured Observability
**Source:** [SOURCE: sessão sinkra-hub 4f9f58cf — domain-decoder pipeline logger]
**Tags:** [Agnostic, Automation, Pipeline, Observability]

## Purpose

Pipelines que logam em texto livre (print statements, log files) criam dados que humanos leem mas máquinas não parsam. JSONL audit trail (um JSON por linha) é parsável por jq, grep, e dashboards sem parser customizado. Cada evento tem timestamp, phase, event_type, e payload estruturado. O custo é mínimo (wrapper de 50 linhas), o ganho é total: filtragem, aggregação, e análise automatizada de runs.

## Configuration (True L3-State)

```yaml
AN_KE_123:
  name: "JSONL Audit Trail Over Text Logs"
  zone: "excelencia"
  trigger: "Pipeline com 3+ fases que precisa de observabilidade pós-run."

  sys_tension:
    tension_with: "Simplicidade (print é mais fácil) vs Observabilidade (JSONL é mais útil)"
    resolution: "Pipeline logger como wrapper — não substitui print para debug humano, ADICIONA JSONL para análise automatizada."

  rule: |
    SE pipeline tem 3+ fases com lifecycle events (start, complete, fail, retry)
    ENTÃO implementar JSONL logger com eventos estruturados:
      - timestamp, phase, event_type, payload
      - Persistir em outputs/{slug}/logs/execution-log.jsonl
    E manter print/console para debug humano em paralelo
    NUNCA ter APENAS text logs em pipeline de produção — JSONL é o mínimo

  failure_modes:
    omission: "Post-mortem de run falho depende de 'ler os prints' — impossível filtrar, agregar, ou comparar runs."
    misapplication: "JSONL para TUDO (incluindo debug traces) polui o audit trail. Separar: JSONL = lifecycle events, text = debug."

  evidence_threshold: "[EMPIRICAL]"
  evidence:
    - "[SOURCE: sessão sinkra-hub 4f9f58cf] 'Pipeline Logger: JSONL audit trail (pipeline_logger.py) with structured events for phase lifecycle, E9 gate checks, enforcement violations (E1-E10), and SBVR/quality validation results'"
```

## Decision Tree (Strict Format)

```text
STEP_1: IF (pipeline has 3+ phases with lifecycle events)
          THEN create pipeline_logger module with JSONL output
          AND log: phase_start, phase_complete, gate_check, enforcement_violation
STEP_2: IF (debugging needed)
          THEN use print/console IN ADDITION to JSONL (not instead)
NEVER:
  - Use only print/text logs for production pipelines
  - Mix debug traces with audit trail events in same JSONL
```

## Validation & Cross-Mind Divergence

### Self-Validation Ask
1. "Posso fazer `jq '.event_type' execution-log.jsonl | sort | uniq -c`? Se não, o log não é JSONL."

### Divergence Analysis (Baseline IA vs Mente Zero)
- **Base LLM Tendency:** Usar print() porque é familiar e imediato.
- **Mind Zero Override:** "Print para humanos. JSONL para máquinas. Os dois. Sem escolher."
