# Task: Detect Operational Mode — External Systems Signal

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `detect-operational-mode-systems` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: detect-operational-mode-systems
name: "Detect Operational Mode — External Systems Signal"
category: discovery
agent: squad-chief
elicit: false
autonomous: true
description: "Detecta referências a sistemas externos e deriva APIs ou conexões necessárias."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::detect_operational_mode_systems
Output: artifact::detect_operational_mode_systems
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Determinar se o briefing pressupõe integração com plataformas externas,
webhooks, automações ou serviços locais que exigem runtime operacional.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `briefing` | string | Yes | Briefing bruto do squad |
| `skills_detected` | list | No | Skills já detectadas para o squad |

## Workflow

### Step 1: Detectar plataformas e serviços

Escanear o briefing por referências a Ads, CRM, planilhas, mensageria, social
media, pagamentos, automação, geração multimodal e serviços locais.

### Step 2: Derivar conexões requeridas

Traduzir cada sistema detectado em uma conexão ou família de APIs esperada.

### Step 3: Emitir sinal de sistemas

Registrar sistemas detectados, conexões exigidas e o modo inferido a partir
desse eixo.

## Output

```yaml
system_signal:
  systems_detected: []
  api_connections_required: []
  mode_from_systems: "OPERATIONAL|TEXTUAL"
```

## Acceptance Criteria

- [ ] Sistemas externos detectados ou ausência confirmada
- [ ] Conexões requeridas derivadas de forma explícita
- [ ] Sinal de sistemas emitido

## Related Documents

- `detect-operational-mode.md` -- Task composta
- `detect-operational-mode-outputs.md` -- Próxima fonte de sinal

---

_Task Version: 1.0.0_
