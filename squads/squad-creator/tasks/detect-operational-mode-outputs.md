# Task: Detect Operational Mode — Output Signal

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `detect-operational-mode-outputs` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: detect-operational-mode-outputs
name: "Detect Operational Mode — Output Signal"
category: discovery
agent: squad-chief
elicit: false
autonomous: true
description: "Classifica os outputs esperados como operacionais, textuais ou mistos."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::detect_operational_mode_outputs
Output: artifact::detect_operational_mode_outputs
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Usar os outputs definidos do squad como evidência objetiva do que ele precisa
produzir: artefatos textuais ou efeitos reais em sistemas.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `outputs_defined` | list | Yes | Lista de outputs esperados |

## Workflow

### Step 1: Classificar outputs operacionais

Marcar outputs que impliquem criação, modificação, sincronização, publicação,
notificação, upload, download ou geração real de arquivos/entidades.

### Step 2: Classificar outputs textuais

Marcar outputs que impliquem análise, recomendação, documentação, checklist,
framework, template ou relatório.

### Step 3: Emitir sinal de outputs

Aplicar a regra: qualquer output operacional torna o modo operacional por
default, salvo veto posterior.

## Output

```yaml
output_signal:
  operational_outputs: []
  textual_outputs: []
  operational_outputs_count: 0
  textual_outputs_count: 0
  mode_from_outputs: "OPERATIONAL|TEXTUAL"
```

## Acceptance Criteria

- [ ] Outputs operacionais classificados
- [ ] Outputs textuais classificados
- [ ] Regra de predominância aplicada
- [ ] Sinal de outputs emitido

## Related Documents

- `detect-operational-mode.md` -- Task composta
- `detect-operational-mode-classify.md` -- Consolidação final

---

_Task Version: 1.0.0_
