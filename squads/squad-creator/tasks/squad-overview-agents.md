# Task: Squad Overview — Agents

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-overview-agents` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: squad-overview-agents
name: "Squad Overview — Agents"
category: documentation
agent: squad-chief
elicit: false
autonomous: true
description: "Analisa agents, comandos e arquitetura de tiers para compor a seção humana do overview."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::squad_overview_agents
Output: artifact::squad_overview_agents
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Transformar os arquivos de agents em uma visão consolidada de papéis, tiers,
handoffs e comandos relevantes do squad.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `squad_path` | string | Yes | Path do squad |
| `metadata_packet` | object | Yes | Saída de `squad-overview-metadata` |

## Workflow

### Step 1: Inventariar agents

Para cada arquivo em `agents/*.md`, extrair:

- nome/id
- papel
- título
- ícone
- `whenToUse`
- comandos principais
- tamanho aproximado

### Step 2: Classificar arquitetura

Determinar:

- orchestrator principal
- tiers implícitos ou explícitos
- especialistas puros vs coordenadores
- mapa básico de handoff

### Step 3: Preparar tabela de comandos

Emitir uma tabela com:

- comando
- descrição curta
- agente responsável
- delegação, se existir

## Output

```yaml
agents_packet:
  orchestrator: ""
  tier_map: {}
  agents: []
  command_table: []
  total_agent_lines: 0
  handoffs: []
```

## Acceptance Criteria

- [ ] Todos os agents do diretório foram considerados
- [ ] Tabela de comandos consolidada foi emitida
- [ ] Arquitetura de tiers e handoffs ficou explícita

## Related Documents

- `squad-overview.md` -- Task composta
- `squad-overview-minds.md` -- Próxima task

---

_Task Version: 1.0.0_
