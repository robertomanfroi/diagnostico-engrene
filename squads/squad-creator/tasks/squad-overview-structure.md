# Task: Squad Overview — Structure

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-overview-structure` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: squad-overview-structure
name: "Squad Overview — Structure"
category: documentation
agent: squad-chief
elicit: false
autonomous: true
description: "Analisa árvore do squad, workflows, frameworks, integrações e quality gates para preencher a espinha estrutural do overview."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::squad_overview_structure
Output: artifact::squad_overview_structure
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Consolidar a camada estrutural do squad em um pacote pronto para geração de
documento, cobrindo árvore, workflows, integrações, compliance e quality gates.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_path` | string | Yes | Path do squad |
| `metadata_packet` | object | Yes | Saída de `squad-overview-metadata` |
| `agents_packet` | object | Yes | Saída de `squad-overview-agents` |
| `minds_packet` | object | Yes | Saída de `squad-overview-minds` |

## Workflow

### Step 1: Montar árvore do diretório

Representar o esqueleto do squad com foco em:

- agents
- tasks
- workflows
- templates
- checklists
- data

### Step 2: Mapear frameworks e comandos

- Extrair frameworks e padrões citados nos agents
- Consolidar comandos do líder e dos especialistas

### Step 3: Ler fluxos e integrações

- Resumir os workflows principais
- Identificar handoffs internos
- Detectar integrações, quality gates e sinais de compliance

## Output

```yaml
structure_packet:
  directory_tree: ""
  frameworks: []
  command_rows: []
  workflow_map: []
  integrations: []
  quality_gates: []
  compliance: {}
  metrics: {}
```

## Acceptance Criteria

- [ ] Árvore do squad gerada com cobertura das pastas principais
- [ ] Workflows e integrações principais mapeados
- [ ] Quality gates e sinais de compliance extraídos quando existirem

## Related Documents

- `squad-overview.md` -- Task composta
- `squad-overview-generate.md` -- Próxima task

---

_Task Version: 1.0.0_
