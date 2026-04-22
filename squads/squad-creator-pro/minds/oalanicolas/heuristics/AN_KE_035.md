---
id: "AN_KE_035"
title: "CLI First Architecture"
mind: "oalanicolas"
type: "heuristics"
zone: "genialidade"
tags:
  - "Architecture"
  - "CLI"
  - "UI Hierarchy"
pipeline_instances:
  - "process-architecture"
  - "scaffolding"
cross_mind_map:
  convergent:
    - id: "PV_PA_019"
      title: "Deterministic Assignment (The Worker Rule)"
      mind: "pedro_valerio"
      resonance: "AN eleva CLI (interfaces lineares textuais sem variações estéticas) como superior ao UI para evitar abstrações mutáveis indesejadas que afetam RAGs. PV estipula formalmente que determinismo lógico exige um Worker isolado de UI/Agentes."
---

# AN_KE_035 - CLI First Architecture

**Type:** Architecture Definition Heuristic
**Phase:** 1 (Diagnostics)
**Agent:** @process-architect
**Pattern:** HO-PP-AN035

```yaml
sys_tension:
  tension_with: "AN_KE_073 (Parallel Subagents) pode fragmentar rastreabilidade linear CLI vs Observabilidade (dashboards) requer UI, mas CLI First exige ausência de UI como requisito"
  resolution: "CLI é mandatório para EXECUÇÃO (100%). UI é opcional e SOMENTE para visualização (consumir streams). Nunca para COMANDO."
```

## Purpose

Estabelecer a primazia absoluta da interface de linha de comando (CLI) como o cérebro das automações SINKRA. A interface gráfica (UI) não pode conter nenhuma inteligência ou lógica de negócio que não possa ser alcançada integralmente via CLI. Quando o servidor frontend cai, os processos críticos continuam. Se a lógica está presa num React Hook, o CEO fica refém do browser para rodar o mais simples dos squads.

## Configuration

```yaml
AN_KE_035:
  name: "CLI First Architecture"
  phase: 1
  zone: "genialidade"
  trigger: "Avaliando ou desenhando arquitetura de um novo agente, squad, ferramenta ou funcionalidade do SINKRA."

  weights:
    cli_headless_capability: 1.0
    ui_logic_coupling_risk: 1.0

  thresholds:
    ui_coupled_core_logic_tolerance: 0.0

  veto_conditions:
    - condition: "core_business_logic_requires_frontend_running_to_execute == true"
      action: "VETO - UI Parasitism. Extract core logic to CLI/Worker. The Dashboard consumes observability streams only."

  output:
    type: "decision"
    values: ["APPROVE_CLI_FIRST", "EXTRACT_TO_CLI", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "Parasitismo Crítico na UI (The Coward)"
    trigger: "O botão 'Executar Squad' numa interface Next.js contém parâmetros e lógica de roteamento que não são expostos em nenhuma CLI."
    manifestation: "O servidor frontend fica fora do ar durante a manutenção. O CEO não consegue rodar a validação do squad primário pois toda lógica de orquestração está acoplada ao React Hook `useSquadRunner()`."
    detection: "Inspeção de arquitetura detecta regras de negócio e condicionals operacionais dentro de React Hooks em vez de Workers ou CLI scripts."
    recovery: "Separar a Rule em pacote CLI headless. UI deve apenas chamar `node squad-runner.js --id X` via subprocess backend."

  - type: "misapplication"
    name: "CLI Puritanism (The Zealot)"
    trigger: "O time decide que NENHUMA lógica pode existir na UI, incluindo validação de formulário client-side."
    manifestation: "Toda validação de UX (formatos de email, campos obrigatórios) é processada via API round-trip, tornando a interface 3x mais lenta."
    detection: "Latência de formulário desnecessária. UX degradada por purismo."
    recovery: "CLI First se aplica a: business logic, orquestração de squads, pipelines. Não se aplica a: UX validation, client-side rendering, apresentação visual."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "CLI Headless Capability"
    weight: 1.0
    threshold: "=== TRUE"
    description: "A funcionalidade pode ser executada integralmente via CLI sem GUI em modo headless?"
  - metric: "UI Logic Coupling"
    weight: 1.0
    threshold: "=== 0"
    description: "Zero lógica de orquestração de squads ou rules de negócio vivem exclusivamente em React Hooks ou componentes de UI?"
```

## Decision Tree

```javascript
IF (Desenhando Nova Funcionalidade / Squad / Agent) {
  EVALUATE("A funcionalidade roda via `./squad.sh --param`?");
  
  IF (CLI_Headless_Capability === FALSE) {
    VETO("UI Parasitism Detectado");
    EXTRACT_TO_CLI("Refatorar lógica para Worker/Script CLI. UI = consumer only.");
  } ELSE IF (CLI_Works === TRUE) {
    PROCEED("Step 2: Build Observability Layer (streams, logs).");
    PROCEED("Step 3: Build UI optionally (only if UX adds value beyond CLI).");
    APPROVE_CLI_FIRST("Hierarquia CLI > Observability > UI respeitada.");
  }
}

NEVER("Amarrar a execução de qualquer squad ou lógica de negócio core à existência de um frontend em funcionamento.");
```

## Validation

✅ **Paradoxo identificado:** CLI First absolutismo vs. necessidade de UI para observabilidade.
✅ **Resolução:** Separação clara de responsabilidades — CLI para EXECUÇÃO (obrigatório), UI para VISUALIZAÇÃO (opcional).
✅ **Princípio preservado:** Sistema 100% funcional sem qualquer dependência de frontend.
