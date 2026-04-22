# Task: Squad Overview — Generate

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `squad-overview-generate` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: squad-overview-generate
name: "Squad Overview — Generate"
category: documentation
agent: squad-chief
elicit: false
autonomous: true
description: "Compõe o markdown final do overview a partir dos pacotes analíticos já consolidados."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::squad_overview_generate
Output: artifact::squad_overview_generate
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Transformar os pacotes de análise em um documento final consistente, sem
placeholders e com seções aplicáveis ao tipo real do squad.

## Inputs

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `metadata_packet` | object | Yes | Saída de `squad-overview-metadata` |
| `agents_packet` | object | Yes | Saída de `squad-overview-agents` |
| `minds_packet` | object | Yes | Saída de `squad-overview-minds` |
| `structure_packet` | object | Yes | Saída de `squad-overview-structure` |
| `format` | string | No | `detailed` ou `compact` |

## Workflow

### Step 1: Selecionar seções aplicáveis

- Sempre incluir visão geral, time, estrutura, comandos, workflow e uso.
- Incluir DNA e especialistas apenas quando houver evidência real.
- Em `compact`, reduzir verbosidade, não cobertura.

### Step 2: Montar o markdown

Gerar:

- título e atributos
- tabelas de agents e comandos
- árvore do diretório
- fluxo de trabalho
- integrações, quality gates e métricas

### Step 3: Limpar placeholders

- Remover `{PLACEHOLDER}` remanescente
- Garantir coerência entre números e tabelas

## Output

```yaml
overview_document:
  title: "SQUAD {name} — Documentação Completa"
  markdown: ""
  sections: []
  estimated_lines: 0
```

## Acceptance Criteria

- [ ] Documento final não contém placeholders
- [ ] Todas as seções aplicáveis foram incluídas
- [ ] O output está pronto para gravação sem pós-processamento manual

## Related Documents

- `squad-overview.md` -- Task composta
- `squad-overview-write.md` -- Próxima task

---

_Task Version: 1.0.0_
