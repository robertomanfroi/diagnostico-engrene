# AN_KE_038 - Gap de Reasoning = Processo Vago

**Type:** Process Maturity Heuristic
**Zone:** 🧠 0,8% Genialidade
**Agent:** @oalanicolas
**Pattern:** Automação vs Maturidade de Tooling
**Source:** [SOURCE: Padrão observado em múltiplas sessões — AN_KE_005 (Determinism First), runner-lib migration Epic 71, benchmark sinkra-map 2026-03-29. Princípio articulado por Pedro Valério no contexto de squad-creator: "eu de clonar mentes, o Pedro manja de processo, tasks, checklists" — sessão MMOS 1741b941]

## Purpose

Combater o auto-engano ao escalar modelos de IA caros. Quando a IA "erra", frequentemente o processo e os checklists são vagos demais — o upgrade de modelo mascara a inaptidão humana em roteirizar. Haiku com SOP rigorosa > Opus com instrução vaga.

## Configuration

```yaml
AN_KE_038:
  name: "Gap de Reasoning = Processo Vago"
  zone: "genialidade"
  trigger: "Quando um agente de IA falha repetidamente numa task e a tentação é trocar para um modelo mais caro."

  rule: |
    SE tentado a usar Opus/o3 para resolver algo simples
    ENTÃO pare e examine as instruções cruas da task.
    Modelos simples (Haiku) brilham com templates e checklists rigorosos.
    Conserte a receita antes de trocar a panela.

  sys_tension:
    tension_with: "AN_KE_050 (Inimigo Zero: Complexidade Inútil) — Escalação de custo/modelo mascara inaptidão humana em roteirizar. WIP>1 em tool stack antes de debugar processo."
    resolution: "Diagnóstico antes de upgrade: investir em SOP rigorosa first, model-flip only se SOP airtight + LLM still fails. Haiku + processo excelente > Opus + vaguidão."

  veto_condition:
    trigger: "Substituir engine (haiku→opus) na esperança que o modelo faça o design de processo que o dev não fez."
    action: "VETO — Audite o Task.yaml. Melhore a SOP com passos explícitos e templates."

  evidence:
    - "[SOURCE: AN_KE_005] Determinism First — Worker/Script > LLM quando precisão é requerida"
    - "[SOURCE: Epic 71] runner-lib migration: 8 runners estabilizados por SOPs melhores, não por modelos maiores"
    - "[SOURCE: benchmark 2026-03-29] Gemini 61/100 falhou não por reasoning, mas por output format — json-repair.py (Worker) resolveu"
    - "[SOURCE: sessão 1741b941] Pedro Valério reconhecido como especialista em processo/tasks/checklists — princípio validado pela divisão de competências"
```

## Decision Tree

```javascript
IF (llm_struggles_with_output_accuracy OR hallucinates_workflow_goal)
  IF (dev_suggests_increasing_model_parameters)
    THEN BLOCK_INCREASE
    THEN AUDIT_HUMAN_INSTRUCTIONS
      IF (instructions_lack_templates OR checklists_are_vague OR sop_is_weak)
        THEN REQUIRE_PROCESS_REWRITE ("Conserte a receita antes de trocar a panela.")
      ELSE
        // Processo airtight + LLM STILL fails = real reasoning gap
        THEN APPROVE_UPGRADE_TO_STRONGER_MODEL
```

## Failure Modes

### Queima de Tokens em Loops
- **Trigger:** Adotar Opus em todas as queries porque um runner falhou 3 vezes seguidas.
- **Manifestation:** Custo salta 10x. O problema original persiste porque era de formato, não de reasoning.
- **Detection:** Comparar logs de custo semanal com complexidade real da task.
- **Recovery:** Downgrade + reescrever SOPs com checklists determinísticos.
- **Prevention:** Exigir prova documentada de que Haiku foi devidamente instrumentalizado antes de aprovar upgrade.

## Integration with Workflow

```yaml
checkpoint:
  id: "reasoning-burnout-audit"
  heuristic: AN_KE_038
  phase: "Cost/Tier_Evaluation"
```

## Validation

**Paradoxo Identificado:** Investir em model upgrades caros mascara inaptidão humana em roteirizar processos. O upgrade não resolve o problema raiz (processo vago), apenas multiplica a queima de tokens.

**Critérios de Validação:**
- ✅ SOP auditada explicitamente antes de qualquer model flip (non-negotiable)
- ✅ Checklists determinísticos presentes no Task.yaml
- ✅ Templates de output definidos e testados com Haiku
- ✅ Se após SOP airtight LLM falha → upgrade aprovado
- ✅ Custo/benefício documentado para cada model-flip decision

**Resolved Tension:** Trade-off entre custo e qualidade é dissolvido por diagnóstico rigoroso — a resposta não é "modelo mais caro", é "processo mais rigoroso primeiro".
