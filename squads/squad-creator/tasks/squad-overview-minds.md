# Task: Squad Overview — Minds

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-overview-minds` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: squad-overview-minds
name: "Squad Overview — Minds"
category: documentation
agent: squad-chief
elicit: false
autonomous: true
description: "Coleta evidências de DNA e perfis de especialistas quando o squad é mind-based ou possui runtime de minds."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::squad_overview_minds
Output: artifact::squad_overview_minds
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Adicionar ao overview apenas a camada de DNA realmente disponível no squad, sem
inventar perfis nem exigir minds quando o squad é puramente estrutural.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_name` | string | Yes | Nome do squad |
| `squad_path` | string | Yes | Path do squad |
| `include_minds` | boolean | No | Controla inclusão de DNA |
| `agents_packet` | object | Yes | Saída de `squad-overview-agents` |

## Workflow

### Step 1: Aplicar regra de ativação

- Se `include_minds == false`, emitir pacote vazio com `status: skipped`.
- Se não existir `.aiox/squad-runtime/minds/`, emitir pacote vazio com
  `status: unavailable`.

### Step 2: Coletar evidências

Para cada especialista com diretório próprio, levantar:

- arquivos de DNA presentes
- score de fidelidade, se existir
- contagem de fontes e frameworks
- evidências de quality dashboard

### Step 3: Sintetizar perfis

Gerar perfis curtos por especialista, sempre ancorados em arquivos reais.

## Output

```yaml
minds_packet:
  status: "available|skipped|unavailable"
  has_real_experts: false
  has_mind_dna: false
  experts: []
  fidelity_summary: {}
```

## Acceptance Criteria

- [ ] A task não inventa DNA quando o runtime não existe
- [ ] Cada perfil listado está ancorado em arquivo real
- [ ] O pacote indica claramente `available`, `skipped` ou `unavailable`

## Related Documents

- `squad-overview.md` -- Task composta
- `squad-overview-structure.md` -- Próxima task

---

_Task Version: 1.0.0_
