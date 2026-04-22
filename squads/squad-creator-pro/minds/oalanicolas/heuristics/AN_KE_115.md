---
id: "AN_KE_115"
title: "Task to Skill: The Right Question"
mind: "oalanicolas"
type: "heuristics"
zone: "genialidade"
tags:
  - "Skill Design"
  - "Workflow Architecture"
  - "Framework Design"
pipeline_instances:
  - "process-architecture"
  - "scaffolding"
cross_mind_map:
  convergent:
    - id: "PV_PA_013"
      title: "Task-First Primacy"
      mind: "pedro_valerio"
      resonance: "Ambos exigem que a task tenha inputs/outputs claros e independentes de quem a executa. PV define task pelo I/O (não pelo executor). AN define se a task pode se tornar skill pelo mesmo critério de I/O autossuficiente."
    - id: "PV_PA_004"
      title: "Zero-Cost Determinism (Worker First)"
      mind: "pedro_valerio"
      resonance: "PV usa I/O clarity para decidir se uma task vai para Worker. AN usa o mesmo critério de I/O standalone para decidir se uma task vira Skill. Mesmo teste, decisões diferentes mas complementares."
  tension:
    - id: "PV_PA_040"
      title: "Transparent Exchange Fallacy"
      mind: "pedro_valerio"
      divergence: "Ângulo de entrada inverso — não contradição. PV opera em execution time: 'o que auditar DENTRO do workflow ao trocar executor?' AN opera em design time: 'o que pode SAIR do workflow como skill?' São ortogonais: nunca se encontram no mesmo ponto de decisão. Premissa compartilhada: o workflow é o organismo primário que dita as regras."
      invalidates: false
---

# AN_KE_115 - Task to Skill: The Right Question

**Type:** Framework Design Heuristic
**Phase:** 1 (Diagnostics)
**Agent:** @process-architect
**Pattern:** HO-PP-AN115

## Purpose

A pergunta "skill vs squad?" é a pergunta errada. A pergunta certa é: "quando uma task deve virar skill?" A resposta: uma task vira skill quando ela é **standalone** — pode ser 100% realizada fora de um workflow, com inputs e outputs claros que não dependem de outras tasks. Se a task depende de outras tasks para ter sentido (inputs/outputs conectados), então não é a task que vira skill — **é o workflow inteiro que deve virar a skill**.

> **Cross-Mind:** PV_PA_013 chega ao mesmo critério pelo ângulo oposto — define task pelo I/O (não pelo executor). Ambos convergem: I/O autossuficiente = unidade atômica válida.

## Configuration

```yaml
AN_KE_115:
  name: "Task to Skill: The Right Question"
  phase: 1
  zone: "genialidade"
  trigger: "Decisão sobre quando transformar uma task em skill, ou quando o workflow inteiro deve ser encapsulado como skill."

  weights:
    correct_question_framing: 1.0
    standalone_dependency_check: 1.0

  thresholds:
    skill_vs_squad_false_dichotomy_tolerance: 0

  veto_conditions:
    - condition: "team_framing_decision_as_skill_vs_squad_instead_of_task_standalone_check == true"
      action: "VETO - Wrong Question. 'Não é skill vs squad. A pergunta certa é: quando uma task deve virar skill?' Check if task is standalone (clear I/O, no task dependencies)."

  output:
    type: "decision"
    values: ["TASK_BECOMES_SKILL", "WORKFLOW_BECOMES_SKILL", "KEEP_AS_TASK"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "Skill vs Squad Dichotomy (The Coward)"
    trigger: "Time debatendo 'devo criar uma skill ou um squad para isso?' sem avaliar se a task é standalone."
    manifestation: "Debate circular sem resposta. Tasks dependentes viram skills órfãs que só funcionam em contexto específico mas são tratadas como reutilizáveis. Quebra de contrato de I/O."
    detection: "Skill que exige que outra skill seja executada primeiro para ter input válido. Skill com dependência implícita não declarada."
    recovery: "Reframing: 'esta task tem inputs/outputs claros sem depender de outras tasks?' → SIM: task vira skill. NÃO: o workflow que contém as tasks deve virar skill."

  - type: "misapplication"
    name: "Everything is Standalone (The Zealot)"
    trigger: "Dev declara toda task como standalone e converte tudo em skills individuais."
    manifestation: "Skills que só funcionam juntas em sequência específica mas são registradas como independentes. Usuário invoca skill isolada e recebe erro por falta de contexto."
    detection: "Skill que, ao ser invocada sozinha, falha ou retorna resultado sem valor por falta de input de outra skill."
    recovery: "Teste de standalone: 'posso invocar esta skill em qualquer contexto, com inputs diretos do usuário, e obter output útil?' Se NÃO → não é standalone → workflow vira skill."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Standalone Check"
    weight: 1.0
    threshold: "=== EVALUATED before skill creation"
    description: "A task foi avaliada quanto à independência de inputs/outputs antes de ser promovida a skill?"
  - metric: "IO Clarity"
    weight: 1.0
    threshold: "=== CLEAR inputs and outputs without external task dependency"
    description: "A skill tem inputs e outputs 100% claros e autossuficientes, sem depender de outras tasks para operar?"
```

## Decision Tree

```javascript
IF (Decisão Sobre Transformar Task em Skill) {
  REFRAME("A pergunta errada é: 'skill vs squad?'");
  ASK("A pergunta certa é: 'esta task é standalone?'");

  CHECK_STANDALONE({
    "Test 1": "Inputs vêm DIRETAMENTE do usuário (não de output de outra task)?",
    "Test 2": "Outputs são úteis SEM precisar passar para outra task?",
    "Test 3": "Pode ser invocada em qualquer contexto e entregar valor por si só?"
    // Cf. PV_PA_013: task definida pelo I/O, executor é atributo transversal
  });

  IF (All_Tests_Pass) {
    TASK_BECOMES_SKILL("Task standalone → vira SKILL. I/O autossuficiente.");
  } ELSE {
    WORKFLOW_BECOMES_SKILL("Task tem dependências → o WORKFLOW inteiro deve virar a SKILL.");
    // Cf. PV_PA_040: se a task vive dentro de pipeline, auditar todo o organismo
  }
}

NEVER("Transformar task dependente em skill isolada. Se a task precisa de output de outra task para funcionar, é o workflow que encapsula ambas que deve virar skill.");
```
