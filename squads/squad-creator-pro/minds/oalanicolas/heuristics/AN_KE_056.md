---
id: "AN_KE_056"
title: "Run Immutability"
mind: "oalanicolas"
type: "heuristics"
zone: "excelencia"
tags:
  - "Infrastructure"
  - "Versioning"
  - "Pipeline"
pipeline_instances:
  - "system-updating"
  - "process-architecture"
---

# AN_KE_056 - Run Immutability

**Type:** Infrastructure Architecture Heuristic
**Phase:** 4 (Molecular Assembly)
**Agent:** @process-architect
**Pattern:** HO-PP-AN056

**sys_tension:**
- tension_with: "AN_KE_073 (Parallel Subagents) vs Run Immutability Sequencing"
- resolution: "Novos run IDs para execuções isoladas. Resume aplica patches NA run existente (APPEND, não overwrite). Symlink latest aponta para a run mais recente completada com sucesso, não para execuções em progresso."

## Purpose

Cada execução de pipeline é um snapshot imutável: nunca sobrescrever uma run anterior, nunca reutilizar IDs de run. A análise do modelo A não deve substituir a análise do modelo B — ambas são instâncias de execução separadas e auditáveis. Quando se precisa "resumir" uma pipeline falha, o correto é CONTINUAR na mesma run, não criar uma nova — pois criar uma nova run sem os artefatos das fases anteriores faz o QA final avaliar uma pasta vazia.

## Configuration

```yaml
AN_KE_056:
  name: "Run Immutability"
  phase: 4
  zone: "excelencia"
  trigger: "Desenhando pipelines que geram outputs versionados, relatórios, score cards ou análises auditáveis."

  weights:
    run_versioning_strictness: 1.0
    resume_vs_new_run_distinction: 1.0

  thresholds:
    overwrite_of_existing_run_tolerance: 0
    new_run_for_resume_tolerance: 0

  veto_conditions:
    - condition: "pipeline_overwrites_existing_run_or_creates_new_run_id_for_resume == true"
      action: "VETO - Run Immutability Violation. New executions = new timestamp ID. Resumes = continue in existing run."

  output:
    type: "decision"
    values: ["APPROVE_IMMUTABLE", "RESOLVE_EXISTING_RUN", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "O Score Card Fantasma (The Coward)"
    trigger: "`--phase 8` (QA gate) cria uma nova run ID ao invés de resolver a run existente das fases 1-7."
    manifestation: "QA avalia uma pasta de run vazia (sem artefatos das fases anteriores) e retorna score 4/100. O dev pensa que o pipeline falhou catastroficamente quando na verdade o problema era de resolução de run."
    detection: "Score absurdamente baixo para pipeline que logicamente completou fases anteriores."
    recovery: "Resolver symlink `latest` → continuar na run original das fases 1-7."

  - type: "misapplication"
    name: "Over-Versioning (The Zealot)"
    trigger: "Cada retry de um step individual cria uma nova run ID."
    manifestation: "Depois de 10 retries de um só step, `outputs/` tem 10 runs quase idênticas com 1 artefato cada."
    detection: "outputs/ com muitas runs de diferença temporal mínima (< 60 segundos)."
    recovery: "Retries do mesmo step são parte da mesma run. Nova run apenas para: nova invocação top-level do pipeline (não para retries internos)."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Run ID Uniqueness"
    weight: 1.0
    threshold: "=== unique timestamp per top-level invocation"
    description: "Cada invocação top-level do pipeline gera um ID único (timestamp)?"
  - metric: "Resume Resolution"
    weight: 1.0
    threshold: "=== CONTINUES EXISTING RUN"
    description: "Quando o pipeline é resumido (--continue, --phase N), resolve o ID da run existente ao invés de criar um novo?"
```

## Decision Tree

```javascript
IF (Pipeline Gera Output Versionado) {
  EVALUATE("Tipo de Execução");
  
  IF (Tipo === "Nova Execução Top-Level") {
    CREATE_RUN("run/{YYYYMMDD-HHMMSS}-{executor}/");
    APPROVE_IMMUTABLE("Nova run com timestamp único criada.");
  } ELSE IF (Tipo === "Resume de Execução Anterior") {
    RESOLVE_EXISTING_RUN("Localizar latest run existente via symlink ou estado.json.");
    CONTINUE_IN_EXISTING("Nunca criar nova run para resume. Continuar na existente.");
  } ELSE IF (Tipo === "Comparação de Modelos") {
    CREATE_SEPARATE_RUNS("Cada modelo = run dir próprio. Comparação lê TODAS as runs.");
  }
}

NEVER("Sobrescrever uma run anterior com nova execução. Nunca criar nova run ID quando a operação é um resume de pipeline falho.");
```

## Validation

✅ **Paradoxo resolvido:** Imutabilidade (novos IDs) vs Continuação (resume na mesma run) são operações distintas — a primeira cria, a segunda estende. Resume nunca sobrescreve outputs anteriores; apenas acrescenta novos artefatos à mesma run, mantendo o histórico completo.

✅ **Vinculação:** AN_KE_056 (criar imutavelmente) + AN_KE_024 (resolver symlink) = um sistema de runs com histórico preservado e referência sempre atualizada ao estado mais recente.
