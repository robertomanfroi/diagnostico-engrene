---
task-id: etd-assemble-output
name: "ETD Final: Assemble Thinking DNA Output"
version: 1.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Montagem final requer síntese coerente de todas as fases anteriores"
estimated-time: 15 min
complexity: medium
parent_task: extract-thinking-dna

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
    - domain: "Area de expertise"
    - recognition_patterns_yaml: "Output de etd-recognition-patterns"
    - frameworks_yaml: "Output de etd-discover-frameworks"
    - heuristics_yaml: "Output de etd-extract-heuristics"
    - decision_architecture_yaml: "Output de etd-decision-architecture"
    - anti_patterns_yaml: "Output de etd-anti-patterns"
    - objection_handling_yaml: "Output de etd-objection-handling"
    - handoff_triggers_yaml: "Output de etd-handoff-triggers"

outputs:
  primary:
    - thinking_dna: "Bloco YAML completo para agent.md com todos os frameworks operacionais"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: etd-assemble-output
  task_name: 'ETD Final: Assemble Thinking DNA Output'
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 15m
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert a clonar''}'
  - '{''domain'': ''Area de expertise''}'
  - '{''recognition_patterns_yaml'': ''Output de etd-recognition-patterns''}'
  - '{''frameworks_yaml'': ''Output de etd-discover-frameworks''}'
  - '{''heuristics_yaml'': ''Output de etd-extract-heuristics''}'
  output:
  - '{''thinking_dna'': ''Bloco YAML completo para agent.md com todos os frameworks
    operacionais''}'
  action_items:
  - Executar os passos documentados no corpo da task
  acceptance_criteria:
  - Framework principal com 3+ steps claros
  - 5+ heurísticas de decisão documentadas
  - 2+ heurísticas de veto
  - Pipeline de decisão mapeado
  - 3+ anti-patterns identificados
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Operational
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# ETD Final: Assemble Thinking DNA Output

> **Objetivo:** Montar o bloco thinking_dna final a partir dos outputs de todas as fases.
>
> **Filosofia:** "Clone minds > create bots"

---

## Veto Conditions

| ID | Condition | Check | Result |
|----|-----------|-------|--------|
| VETO-AO-001 | Existing thinking_dna block in agent file must be backed up before modification | Check if target agent.md already contains a thinking_dna section | VETO - BLOCK. Create snapshot of current thinking DNA before overwriting. |
| VETO-AO-002 | All phases must have produced valid output before assembly | Verify all 7 input YAMLs are non-empty | VETO - BLOCK. Complete missing phases before assembling. |

---

## Step 1: Consolidate Phase Outputs

Colete os outputs de todas as 7 fases e monte o bloco unificado usando esta estrutura:

```yaml
# THINKING DNA - {MIND_NAME} | Domain: {DOMAIN} | Extracted: {DATE}
thinking_dna:
  primary_framework:
    name: "" | purpose: "" | steps: [] | when_to_use: "" | when_NOT_to_use: ""
  secondary_frameworks:
    - name: "" | purpose: "" | steps: [] | trigger: ""
  diagnostic_framework:
    questions: [] | red_flags: [] | green_flags: []
  heuristics:
    decision: [{ id, rule: "SE _ ENTAO _", rationale }]
    veto: [{ trigger, action: "PARE/REJEITE", reason }]
    prioritization: [{ rule, example }]
  decision_architecture:
    pipeline: [{ stage, action, frameworks?, criteria? }]
    weights: [{ criterion, weight: "alto|medio|baixo" }]
    risk_profile: { tolerance, risk_seeking: [], risk_averse: [] }
  anti_patterns:
    never_do: [{ action, reason }]
    common_mistakes: [{ mistake, correction }]
  recognition_patterns:
    instant_detection: [{ domain, pattern, accuracy }]
    blind_spots: [{ domain, what_they_miss }]
    attention_triggers: [{ trigger, response }]
  objection_handling:
    common_objections: [{ objection, response, tone }]
    pushback_triggers: [{ trigger, auto_response }]
    argumentation_style: { debate_preference, admission_willingness, recovery_when_wrong }
  handoff_triggers:
    limits: [{ domain, trigger_when, typical_response, to_whom }]
    self_awareness: { knows_limits: bool, defensive_about_gaps: bool }
```

**Nota:** Expanda cada campo ao preencher -- a notacao compacta acima e apenas referencia estrutural. O output final deve usar YAML completo e legivel.

---

## Step 2: Cross-Phase Consistency Check

Verifique coerência entre fases:
- Frameworks referenciados no pipeline de decisão existem?
- Anti-patterns são consistentes com heurísticas de veto?
- Handoff triggers não contradizem recognition patterns?

**Elicit:** Apresente o bloco completo e peça revisão final.

---

## Step 3: Quality Gate Final

- [ ] Framework principal com 3+ steps claros
- [ ] 5+ heurísticas de decisão documentadas
- [ ] 2+ heurísticas de veto
- [ ] Pipeline de decisão mapeado
- [ ] 3+ anti-patterns identificados
- [ ] 2+ recognition patterns (o que notam primeiro)
- [ ] 2+ objection responses documentadas
- [ ] 1+ handoff trigger identificado
- [ ] Todas as regras têm "rationale" (o PORQUE)

**Score mínimo:** 7/9 -> PASS

---

## Step 4: Insert Into Agent File

Cole o bloco `thinking_dna` no arquivo agent.md do expert.

**Pre-condition:** Se ja existir thinking_dna no agent.md, o backup deve ter sido criado (VETO-AO-001).

**Reference:** Para exemplo completo (Dan Kennedy), consulte a versao anterior deste arquivo em git history (v1.3.0).

## Task Anatomy

- **Executor:** Agent
- **Inputs:** mind_name; domain; recognition_patterns_yaml; frameworks_yaml; heuristics_yaml; decision_architecture_yaml; anti_patterns_yaml; objection_handling_yaml; handoff_triggers_yaml
- **Outputs:** Bloco YAML completo para agent.md com todos os frameworks operacionais
- **Completion Criteria:** All outputs produced and validated
- **Guardrails:** See Veto Conditions above

## Acceptance Criteria

- [ ] All veto conditions checked and none triggered
- [ ] Output artifact produced: Bloco YAML completo para agent.md com todos os frameworks operacionais
- [ ] Task output validated against quality standards
