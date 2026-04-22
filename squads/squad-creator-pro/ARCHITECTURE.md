# Squad Creator Pro Architecture

## Visão Geral

`squad-creator-pro` é um upgrade-pack do `squad-creator`. Ele preserva o fluxo base de criação e upgrade de squads, e adiciona capacidades especializadas para:

- mind cloning e DNA extraction
- research-first agent creation
- workflow optimization e modernization
- workspace hardening e quality gates avançados

## Superfície Ativa

- Entrada principal: [`config.yaml`](./config.yaml)
- Workflows canônicos: [`workflows/`](./workflows)
- Tasks ativas: [`tasks/`](./tasks)
- Templates de contrato: [`templates/`](./templates)
- Runtime transient: `.aiox/squad-runtime/squad-creator-pro/`

## Modelo de Execução

- Executor formal do pack: `@squad-chief`
- Especialistas entram por delegação explícita, nunca como executor genérico
- O pack não escreve diretamente no workspace de negócios; ele endurece contrato, gera artefatos e prepara handoffs

## Contratos Estruturais

- `artifact_contracts` governam outputs tipados
- `journey_log` registra lifecycle events do pack
- `workspace_integration.level` permanece `read_only` no overlay pro
- Workflows exigem `sequence[].id` e `agent` concreto em cada step executável

## Referências

- Diagramas detalhados: [`docs/ARCHITECTURE-DIAGRAMS.md`](./docs/ARCHITECTURE-DIAGRAMS.md)
- Fluxo HITL: [`docs/HITL-FLOW.md`](./docs/HITL-FLOW.md)
- Pipeline de criação: [`docs/squad-creation-pipeline-workflow.md`](./docs/squad-creation-pipeline-workflow.md)
