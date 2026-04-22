# Task: Create Pipeline Scaffolding (Composed)

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-pipeline` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Composed` |

## Metadata

```yaml
id: create-pipeline
name: "Create Pipeline Scaffolding"
category: creation
agent: squad-chief
elicit: true
autonomous: false
description: "Task composta que qualifica, desenha, gera, persiste e valida scaffolding de pipeline multi-fase para squads que realmente precisam de runtime sequencial."
owner_workflow: "workflows/wf-create-pipeline.yaml"
pattern: "PIPELINE-SCAFFOLD-001"
accountability:
  human: squad-operator
  scope: review_only
domain: Tactical

```


<!-- SINKRA_CONTRACT -->
Domain: `Tactical`
atomic_layer: Atom
Input: request::create_pipeline
Output: artifact::create_pipeline
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Gerar a camada `lib/` de pipelines para squads com processamento multi-fase,
preservando o veto anti-overengineering, a definição explícita de fases e o
autoteste mínimo antes de entregar o scaffold ao desenvolvedor.

## Execution Sequence

```text
INPUT (squad_name + phase_definitions + requirements)
    |
[1] create-pipeline-qualify
    -> Executa checklist "does this squad need a pipeline?"
    |
[2] create-pipeline-design
    -> Fecha fases, componentes, criticalidade e estratégia de handlers
    |
[3] create-pipeline-render
    -> Renderiza draft dos arquivos a partir dos templates canônicos
    -> INCLUI: scripts/{squad}.sh + templates/pipeline/prompt.md + lib/ + handlers/
    |
[4] create-pipeline-persist
    -> Persiste scripts/{squad}.sh (chmod +x), templates/pipeline/prompt.md,
       lib/, lib/handlers/, __init__.py
    |
[5] create-pipeline-validate
    -> Executa autotestes (python3 lib/*.py) E verifica que .sh parseia --help
    |
OUTPUT: pipeline_scaffolding_report
```

## Sub-Task Reference

| # | Task ID | Responsibility | Executor |
|---|---------|----------------|----------|
| 1 | `create-pipeline-qualify` | Aplicar checklist de qualificação e vetoes | Worker |
| 2 | `create-pipeline-design` | Fechar contrato de fases e componentes | Hybrid |
| 3 | `create-pipeline-render` | Customizar templates e stubs | Hybrid |
| 4 | `create-pipeline-persist` | Salvar arquivos em `lib/` | Worker |
| 5 | `create-pipeline-validate` | Rodar self-tests e emitir veredito | Worker |

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Squad alvo do scaffold |
| `phase_definitions` | array | No | Fases já definidas; se ausentes, coletar/inferir |
| `requirements` | object | No | Requisitos extras do pipeline |
| `item_noun` | string | No | Nome do item processado (`books`, `minds`, `courses`) |

## Outputs

| Output | Location | Description | Required |
|--------|----------|-------------|----------|
| Shell runner | `squads/{squad}/scripts/{squad}.sh` | **PRIMARY** — CLI entry point with runner-lib bootstrap, arg parsing, phase loop, E9 gates | YES |
| Prompt template | `squads/{squad}/templates/pipeline/prompt.md` | LLM prompt template with env vars, phase map, enforcement rules | YES |
| Pipeline library | `squads/{squad}/lib/` | State manager, phase runner, progress tracker (Python) | YES |
| Phase handlers | `squads/{squad}/lib/handlers/` | One handler per phase with build_prompt() + output verification | YES |
| Handler init | `squads/{squad}/lib/handlers/__init__.py` | Exports all handlers | YES |
| Validation report | `runtime_context` | Veredito final e próximos passos | YES |

### Shell Runner Requirements (NON-NEGOTIABLE)

O `.sh` é o deliverable principal — sem ele o scaffold Python é inútil. O runner DEVE:

1. **Bootstrap runner-lib v2** — `source "$RUNNER_LIB_DIR/pipeline-bootstrap.sh"`
2. **Aceitar flags padrão** — `--claude/--codex/--gemini`, `--model <name>`, `--phase <num>`, `--timeout <s>`
3. **Aceitar --source <path>** — caminho para o codebase/diretório alvo (relativo ou absoluto)
4. **greenfield/brownfield** — modo de execução como argumento posicional
5. **State management** — `decoder-state.json` via `state_init`/`state_update`/`state_validate`
6. **Phase loop** — iterar fases sequencialmente com retry e max-iterations
7. **E9 gate validation** — verificar outputs existem (>500 bytes, sem VETO markers) após cada fase
8. **Progress dashboard** — exibir progresso visual entre fases
9. **Job metrics** — JSONL em `logs/job-metrics.jsonl`
10. **Completion signal** — detectar `<promise>PHASE_COMPLETE</promise>` no output do LLM

Referência: `squads/books/scripts/books.sh`, `squads/mmos/scripts/mmos.sh`

## Veto Conditions

- Score de qualificação = `0` -> bloquear
- Menos de `3` sinais de necessidade sem aprovação explícita -> bloquear
- Fases sem input/output claro -> bloquear
- Squad já possui `lib/` conflitante com outro padrão -> bloquear
- Necessidade declarada de paralelismo -> redirecionar para padrão diferente
- **Pipeline sem `scripts/{squad}.sh` -> VETO. O .sh é o deliverable principal.**
- **Pipeline sem `templates/pipeline/prompt.md` -> VETO. O LLM precisa do prompt template.**
- **`.sh` que não aceita `--source`, `--model`, `--phase` -> VETO. Interface padrão obrigatória.**

## Commands

```yaml
commands:
  standard: "*create-pipeline {squad_name}"
  explicit_phases: "*create-pipeline {squad_name} --phases {phase_list}"
  audit: "*create-pipeline {squad_name} --audit"
```

## Acceptance Criteria

- [ ] Checklist de qualificação executado e documentado
- [ ] Design fecha fases, criticalidade, cache e componentes
- [ ] `scripts/{squad}.sh` criado, executável, `--help` funciona
- [ ] `scripts/{squad}.sh` aceita `--source <path>`, `--model <name>`, `--phase <num>`, `--claude/--codex/--gemini`
- [ ] `templates/pipeline/prompt.md` criado com env vars, phase map, enforcement rules
- [ ] `lib/` persistido com `__init__.py`, pipeline_state.py, phase_runner.py, progress.py
- [ ] `lib/handlers/` com um handler por fase (build_prompt + output verification)
- [ ] Self-test: `python3 lib/pipeline_state.py` e `python3 lib/phase_runner.py` passam
- [ ] Self-test: `bash scripts/{squad}.sh --help` parseia argumentos sem erro

## Related Documents

- `workflows/wf-create-pipeline.yaml`
- `data/pipeline-patterns.md`
- `templates/pipeline-state-tmpl.py`
- `templates/pipeline-progress-tmpl.py`
- `templates/pipeline-runner-tmpl.py`

### Reference Implementations (use as pattern, NOT as template)

- `squads/books/scripts/books.sh` — 12-phase book summary pipeline
- `squads/mmos/scripts/mmos.sh` — 8-phase mind mapping pipeline
- `squads/domain-decoder/scripts/decoder.sh` — 6-phase rule extraction pipeline
- `infrastructure/scripts/runner-lib/pipeline-bootstrap.sh` — runner-lib bootstrap

---

_Task Version: 2.0.0_
_Last Updated: 2026-03-27_
