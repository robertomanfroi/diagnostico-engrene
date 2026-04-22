# Task: Create Pipeline — Validate

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `create-pipeline-validate` |
| **Version** | `2.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: create-pipeline-validate
name: "Create Pipeline — Validate"
category: validation
agent: squad-chief
elicit: true
autonomous: false
description: "Executa pipeline-runner-checklist.md (30 items, 7 seções), self-tests, e emite veredito PASS/FAIL."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::create_pipeline_validate
Output: artifact::create_pipeline_validate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Garantir que o scaffold gerado é executável, completo, e incorpora as lições
dos 14 bugs do post-mortem domain-decoder.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Squad alvo |
| `pipeline_design_contract` | object | Yes | Contrato de design |
| `pipeline_persist_report` | object | Yes | Relatório da persistência |

## Workflow

### Step 1: Executar checklist (30 items)

Aplicar `squads/squad-creator/checklists/pipeline-runner-checklist.md` item por item.

**Cada item = PASS ou FAIL com evidência.**

| Seção | Items | Cobertura |
|-------|-------|-----------|
| 1. Deliverables | 7 | Arquivos existem |
| 2. Runner behavior | 5 | Auto-detect, gates |
| 3. Stdout handling | 4 | JSON filter, completion |
| 4. Context & turns | 7 | Injection, scaling |
| 5. Gates & markers | 5 | Regex, jq safety |
| 6. Retry | 4 | Boost, circuit breaker |
| 7. Prompt template | 7 | Placeholders, budget |

### Step 2: Rodar self-tests

```bash
# Test 1: Shell runner parseia --help
bash scripts/{squad}.sh --help

# Test 2: Python state manager importa
python3 -c "import lib.pipeline_state"

# Test 3: Python phase runner importa
python3 -c "import lib.phase_runner"
```

### Step 3: Scoring e veredito

| Score | Veredicto | Ação |
|-------|-----------|------|
| 30/30 | PASS | Pipeline production-ready |
| 25-29 | PASS WITH WARNINGS | Issues menores documentados, pode seguir |
| 20-24 | CONDITIONAL | Fixes obrigatórios antes de uso |
| <20 | FAIL | Requer redesign — voltar para render |

### Step 4: Emitir relatório

Produzir relatório com:
- Score total e por seção
- Items que falharam com BUG-REF
- Self-test results
- Próximos passos

## Acceptance Criteria

- [ ] Checklist de 30 items executado com evidência por item
- [ ] Self-tests executados (3 tests)
- [ ] Score calculado e veredito emitido
- [ ] Se FAIL: lista de fixes específicos com BUG-REF
- [ ] Se PASS: relatório final com próximos passos

## Related Documents

- `create-pipeline.md`
- `checklists/pipeline-runner-checklist.md` — **O checklist de 30 items**
- `docs/research/2026-03-31-decoder-pipeline-lessons-learned/` — Post-mortem completo
- `wf-create-pipeline.yaml`

---

_Task Version: 2.0.0_
_Last Updated: 2026-03-31_
_Incorpora pipeline-runner-checklist.md com 30 items de 14 bugs_
