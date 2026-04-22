---
id: "AN_KE_036"
title: "Veto Sobre LLM Goodwill"
mind: "oalanicolas"
type: "heuristics"
zone: "impacto"
tags:
  - "Flow Control"
  - "Architecture"
  - "Checkpoints"
pipeline_instances:
  - "process-architecture"
  - "validation"
cross_mind_map:
  convergent:
    - id: "PV_PA_003"
      title: "Agent Reasoning Gap (Not a Fast Human)"
      mind: "pedro_valerio"
      resonance: "A Desilusão Positiva com a Máquina. AN afirma categoricamente: é proibido confiar na boa vontade (goodwill) e intenção da IA. PV nomeia formalmente esse anti-padrão como a falácia do 'Humano Muito Rápido'. A máquina não julga subtexto moral soziha."
    - id: "PV_PA_037"
      title: "The Agent Empathy Fallacy (Human-Fast Trap)"
      mind: "pedro_valerio"
      resonance: "PV detalha que pedir 'bom senso' processual para um LLM quebra o projeto porque não há common sense; AN bloqueia inteiramente lacunas não explícitas para prevenir alucinações de inferência empática."
---

# AN_KE_036 - Veto Sobre LLM Goodwill

**Type:** Control Structure Heuristic
**Phase:** 4 (Molecular Assembly)
**Agent:** @process-architect
**Pattern:** HO-PP-AN036

---

## System Tension

```yaml
sys_tension:
  tension_with: "PV_KE_085 (The Actionable Veto Feedback Requirement) vs Veto Puro Sem Recursão"
  paradox: "AN_KE_036 exige barreiras duras CONTRA boa vontade da LLM, mas depende fundamentalmente da VONTADE da LLM de implementar essas barreiras. Rejeita confiança verbal mas demanda confiança técnica."
  resolution: "Embedir o gate no Framework (não na LLM). Exemplo: Usar Task Contracts SINKRA (config.yaml artifact_contracts) como lei, não como sugestão. Se o artifact não existe, a próxima Task falha automaticamente — independente de LLM."
  implementation: "Mover a Veto do Prompt para o Executor (Task Runner), não para o Planner (LLM)."
```

## Purpose

Eliminar o "Vácuo Zero" / "Gap Zero" nos Workflows. Não importa ter um script de validação maravilhoso se a execução dele depende exclusivamente da boa vontade da LLM em decidir rodá-lo. LLMs omitem passos "dolorosos" (lentos, caro em tokens) quando percebem que parecem desnecessários. A obrigatoriedade mecânica via System Blocks com verificação de artefato é superior ao Prompt Engineering ingênuo que "pede por favor".

## Configuration

```yaml
AN_KE_036:
  name: "Veto Sobre LLM Goodwill"
  phase: 4
  zone: "impacto"
  trigger: "Definindo processos de workflow onde o LLM precisa obrigatoriamente executar um validador, checklist ou step de qualidade antes de avançar."

  weights:
    mechanical_gate_strictness: 1.0
    verbal_instruction_reliability: 0.0

  thresholds:
    verbal_goodwill_tolerance: 0.0

  veto_conditions:
    - condition: "workflow_step_depends_on_llm_voluntarily_running_validator_without_artifact_check == true"
      action: "VETO - LLM Goodwill Architecture. Implement mechanical gate: pipeline MUST verify artifact file existence before advancing."

  output:
    type: "decision"
    values: ["APPROVE_MECHANICAL_GATE", "REQUIRE_ARTIFACT_GATE", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "Gap Zero de Automação (The Coward)"
    trigger: "Um workflow instrui a IA: 'Antes de avançar para o Wave 3, execute o validation.sh'."
    manifestation: "Para economizar tokens, o agente pula silenciosamente o validation.sh (chave 'Parece desnecessária dado o contexto'). A Wave 3 é executada sobre dados corrompidos. 8 fases de trabalho são inválidas."
    detection: "Analisar histórico de tool calls: o script de validação nunca foi invocado formalmente pelo agente."
    recovery: "Interromper a chain inteira. Retroceder à fase de origem. Forçar validação antes de recomeçar."

  - type: "misapplication"
    name: "Over-Gating (The Zealot)"
    trigger: "O dev adiciona gates mecânicos em cada micro-step do workflow, incluindo steps de baixo risco."
    manifestation: "O pipeline de 5 minutos se torna um pipeline de 30 minutos com 25 checkpoints de artefato, a maioria verificando coisas que nunca falham."
    detection: "Gate overhead > 30% do tempo de execução real do workflow."
    recovery: "Gates mecânicos apenas para: passos de Quality Gate (validações, scores), transições de fase (Wave N → N+1), operações destrutivas (DELETE, schema changes)."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Artifact Gate Presence"
    weight: 1.0
    threshold: "=== TRUE"
    description: "O pipeline verifica a existência de um artefato concreto (arquivo de log, JSON de score, report) antes de autorizar o avanço de fase?"
  - metric: "Verbal Instruction Reliance"
    weight: 1.0
    threshold: "=== 0"
    description: "Nenhuma instrução crítica de workflow depende de 'Por favor, execute X antes de Y' sem gate mecânico?"
```

## Decision Tree

```javascript
IF (Workflow Step Obrigatório Definido) {
  EVALUATE("Gate Mechanism");
  
  IF (Gate === "Verbal Instruction Only") {
    VETO("LLM Goodwill Architecture detectada.");
    REQUIRE_ARTIFACT_GATE("Implemente: pipeline verifica existência de artifact_file antes de avançar.");
  } ELSE IF (Gate === "Artifact Existence Check") {
    APPROVE_MECHANICAL_GATE("Gate mecânico confirmado. LLM não pode bypassar.");
  }
}

NEVER("Proteger um Quality Gate crítico apenas com instrução de prompt ('Por favor execute o validador'). LLMs omitem steps que percebem como desnecessários.");
```

---

## Validation

✅ **Framework-Level Gate Auditable:** A barreira funciona SE implementada no Task Runner (executor), não IF a LLM promete respeitar.

✅ **Paradox Resolution Tracked:** sys_tension documenta por que this heuristic auto-refuta — e aponta a saída via Task Contracts (SINKRA governance, não prompt engineering).

✅ **Dependency Injection:** Gate de AN_KE_036 deve estar em `.aiox-core/development/tasks/` como pré-condition obrigatória, não em `SKILL.md` como sugestão.

**Recomendação:** Auditar `squads/sinkra-squad/data/composition-rules.yaml` para validar se artifact_contracts são respeitados pelo executor. Se forem, paradoxo resolve. Se não, AN_KE_036 prova que a própria infraestrutura viola esta heurística.
