# Task: Squad Overview — Write

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-overview-write` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: squad-overview-write
name: "Squad Overview — Write"
category: documentation
agent: squad-chief
elicit: false
autonomous: true
description: "Escreve o SQUAD-OVERVIEW.md, aplica checklist de saída e reporta o score final."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::squad_overview_write
Output: artifact::squad_overview_write
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Persistir o overview no root do squad e aplicar as validações finais de
existência, completude e qualidade mínima.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_path` | string | Yes | Path do squad |
| `overview_document` | object | Yes | Saída de `squad-overview-generate` |
| `format` | string | No | `detailed` ou `compact` |

## Workflow

### Step 1: Gravar o arquivo

- Escrever `{squad_path}/SQUAD-OVERVIEW.md`
- Confirmar criação e tamanho final

### Step 2: Aplicar validação de saída

Checar:

- arquivo existe
- seções essenciais presentes
- sem placeholders
- comprimento adequado ao formato

### Step 3: Emitir relatório final

Responder com:

- path do arquivo
- linhas geradas
- score do checklist
- próximos passos sugeridos

## Output

```yaml
overview_report:
  output_path: ""
  line_count: 0
  quality_score: 0
  verdict: "PASS|CONDITIONAL|FAIL"
  next_action: ""
```

## Acceptance Criteria

- [ ] `SQUAD-OVERVIEW.md` gravado no root do squad
- [ ] Checklist de saída aplicado
- [ ] Relatório final emitido com score e veredicto

## Related Documents

- `squad-overview.md` -- Task composta
- `checklists/squad-overview-checklist.md` -- Checklist de saída

---

_Task Version: 1.0.0_
