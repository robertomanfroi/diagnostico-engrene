# Task: Detect Operational Mode — Classify and Report

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `detect-operational-mode-classify` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: detect-operational-mode-classify
name: "Detect Operational Mode — Classify and Report"
category: discovery
agent: squad-chief
elicit: false
autonomous: true
description: "Consolida sinais de verbos, sistemas e outputs para classificar o modo operacional do squad."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::detect_operational_mode_classify
Output: artifact::detect_operational_mode_classify
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Aplicar a lógica de score e veto para determinar se o squad precisa de runtime
operacional completo ou se pode permanecer apenas no modo textual.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `verb_signal` | object | Yes | Saída de `detect-operational-mode-verbs` |
| `system_signal` | object | Yes | Saída de `detect-operational-mode-systems` |
| `output_signal` | object | Yes | Saída de `detect-operational-mode-outputs` |

## Workflow

### Step 1: Calcular score operacional

Aplicar pesos:

```yaml
weights:
  verb_analysis: 0.3
  system_detection: 0.4
  output_analysis: 0.3
operational_threshold: 0.3
```

### Step 2: Aplicar vetoes

- Se não houver verbos acionáveis nem outputs definidos, bloquear classificação.
- Se o score estiver próximo do threshold com confiança baixa, exigir
  confirmação humana.

### Step 3: Gerar relatório de modo

Emitir modo final, confiança, evidências e infraestrutura requerida.

## Output

```yaml
mode_report:
  mode_detected: "OPERATIONAL|TEXTUAL"
  confidence: "HIGH|MEDIUM|LOW"
  scores:
    operational: 0.0
    textual: 0.0
  evidence:
    verbs: {}
    systems: {}
    outputs: {}
  infrastructure_required: []
```

## Veto Conditions

- Sem sinais suficientes para classificar
- Evidência conflitante com baixa confiança

## Acceptance Criteria

- [ ] Score operacional calculado com pesos explícitos
- [ ] Vetoes aplicados quando necessário
- [ ] `mode_report` emitido com confiança e evidências

## Related Documents

- `detect-operational-mode.md` -- Task composta
- `detect-operational-mode-infrastructure.md` -- Próxima task

---

_Task Version: 1.0.0_
