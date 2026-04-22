---
id: "PV_KE_041"
title: "The Autovalidation Veto (Generation-Validation Split)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Quality Gates"
  - "Agent Architecture"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "PV_PA_009 (The Paradox of Self-Validation)"
  resolution: "Autovalidation Veto applies to high-stakes decisions requiring contextual judgment. Deterministic Workers with iron-clad coverage skip heavy quality gates to preserve velocity. The Split separates: deterministic tasks (exempt) vs heuristic-laden tasks (mandate disparate validation). Brand alignment, pricing, moral-weight decisions always require asymmetric review."
---

# PV_KE_041 - The Autovalidation Veto (Generation-Validation Split)

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:process-architect
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 3: Os 4 Executores / O princípio da Autovalidação]

## Purpose
A "Regra de Ouro" de quem gera não deve validar a si mesmo. Se um único executor (Humano ou Agent) gera uma peça e também carimba sua aprovação, o Quality Gate é falso (placebo burocrático). Este vetor isola alucinações cognitivas e erros narcísicos forçando uma assimetria estrutural e salvando Organisms de rodar no vazio com lixo em escala.

## Configuration
```yaml
PV_KE_041:
  name: "Autovalidation Veto"
  zone: "zone_0.8"
  trigger: "Instanciação de um Quality Gate onde origem e destino possuem a mesma entidade executora."
  evidence_threshold: "first_principles_inference"
  rule: |
    SE a task primária requer competências divergentes (gerar o código vs testar o código, ou escrever copy vs auditar brand-voice)
    ENTÃO você DEVE exigir `executor_type: validation_different_from_generation`.
  veto_condition:
    trigger: "Agent constrói a estratégia (briefing) e o mesmo Agent rodando o mesmo loop valida o escopo."
    action: "VETO - Autovalidação cega. Interceptar e forçar a validação via Clone de metodologia ou Humano sênior."
```

## Decision Tree
```javascript
IF (quality_gate_reached == TRUE)
  STEP_1: IDENTIFY generation executor
  STEP_2: IDENTIFY validation executor
    IF (generation_executor.entity_id == validation_executor.entity_id)
      -> REJECT workflow architecture. Force manual or disparate override.
    ELSE IF (generation_executor.type == 'Agent' && validation_executor.type == 'Clone' || 'Human')
      -> APPROVE architecture (Robust Generation-Validation Split).
NEVER: 
  Assumir que a velocidade da inteligência algorítmica dilui a necessidade secular do "Maker-Checker Principle" ou de ter "four eyes" nas decisões primárias da empresa.
```

## Failure Modes

### Misapplication / Excess: "A Burocracia Extrema"
- **Trigger:** Um time entende mal a regra e exige validações cruzadas até para tarefas onde não existe criatividade ou heurística.
- **Manifestation:** Um humano é forçado a revisar 5.000 tickets de suporte que um `Worker` determinístico triou por `if/else`, atrasando todo o pipeline em dias sob a desculpa de "precisa de 4 olhos".
- **Detection:** Operadores humanos reportando fadiga crônica avaliando flags binárias óbvias que as automações já sabiam (O Worker não precisava do humano pois ele nunca devia se autovalidar em coisas onde seu determinismo é de ferro).
- **Recovery:** Eliminar a trava de Quality Gate humana de Tasks onde o `executor_type == Worker`. Autovalidação não se aplica a Workflows determinísticos brutos com cobertura total.
- **Prevention:** Somente instanciar Quality Gates pesados para Atoms que dependam de julgamento contextual, estocasticidade (Agents) ou peso moral de falha.

### Omission / Failure to Activate: "A Confiança Cega"
- **Trigger:** Agência inteira visando super-velocidade; os painéis verdes Lean viciam a equipe na redução de FTEs (headcounts).
- **Manifestation:** O Worker constrói as listas de leads. O Agent manda e-mails, cria as propostas de alto ticket e aprova automaticamente usando sua métrica genérica de A.I. Os leads morrem por ausência de *brand alignment*. Ninguém do Board vê os e-mails enviados.
- **Detection:** KPIs técnicos dizem que a empresa processou 10.000 unidades em 4 horas (Sucesso Lean), mas o KPI de Faturamento despenca em 20% no trimestre decorrente de fechamentos abaixo do "Padrão Tático".
- **Recovery:** Interromper o `Organism` de Geração Massiva. Instalar imediatamente o Handoff Obrigatório: todo Batch deve repousar numa mesa esperando revisão amostral de Humano ou a barra de aço de um Clone calibrado na Empresa.
- **Prevention:** Todo pipeline novo gerado na equipe deve ser auditado no nível de Atoms para atestar explicitamente quem ocupa a cadeira de Originador (`primary`) e Validador (`reviewer`).

---

## Validation

**Paradox Identified:** The Autovalidation Veto demands asymmetric review to catch cognitive hallucinations and narcissistic errors. Yet the Velocity Paradox (PV_KE_026) pressures organizations to automate validation away for speed. The resolution is surgical: **deterministic execution (Workers, if/else trees) exempts itself from heavy gates**, but **heuristic-laden execution (Agents, brand decisions, pricing, moral-weight calls) demands mandatory disparate validation**. The distinction is not "Agent vs Human" but "Algorithm confidence vs Judgment Risk." A Worker with 99.9% deterministic coverage can self-validate. A pricing Agent that hallucinates brand misalignment cannot. This heuristic holds when applied to the right task type.

**Validation Criteria:**
- ✅ Used for high-stakes, judgment-laden tasks (brand, pricing, legal, strategic decisions)
- ✅ Enforces mandatory split between generator and validator roles
- ✅ Recovers from both excess (false bureaucracy on deterministic tasks) and omission (blind confidence in algorithmic output)
- ✅ Alignable with lean velocity when discrimination (deterministic vs heuristic) is applied precisely
- ⚠️ Requires explicit audit of task type at instantiation to avoid misapplication
