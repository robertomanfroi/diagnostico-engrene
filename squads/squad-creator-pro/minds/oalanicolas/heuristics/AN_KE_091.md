# AN_KE_091 - Conceptual Before Mechanical
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões mmos a8145c99, 017a1f24 — "calma, vamos planejar antes" repetido 2x na mesma sessão]

## Purpose

Entender CONCEITUALMENTE antes de executar MECANICAMENTE. Migrations sem entender o modelo conceptual = desastre. Código sem entender a arquitetura = retrabalho. A IA tende a executar imediatamente — o humano deve frear e exigir entendimento primeiro.

## Configuration

```yaml
AN_KE_091:
  name: "Conceptual Before Mechanical"
  zone: "genialidade"
  trigger: "IA propondo executar migration, refactor, ou mudança arquitetural significativa."

  rule: |
    SE mudança é arquitetural ou conceitual (não apenas cosmética)
    ENTÃO ENTENDER o modelo conceitual PRIMEIRO.
    Ler paper/doc/spec ANTES de escrever código.
    "antes de migrar precisamos entender conceitualmente"

  veto_condition:
    trigger: "Criar migration SQL antes de entender o modelo conceitual por trás."
    action: "VETO — 'calma vamos planejar antes de alterar qualquer coisa'"

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs. Complexidade de Parsing Conceitual"
    resolution: |
      Distinção crítica entre mudanças COSMÉTICA (alta velocidade aceitável) e
      ARQUITETURAIS (compreensão prévia obrigatória). A pressa mata a qualidade conceptual.
      Resolução: investir tempo inicial (conceptual) economiza retrabalho (execution).

  evidence:
    - "[SOURCE: sessão a8145c99] 'antes de fazer uma migração precisamos entender conceitualmente como vamos aplicar os tiers, eu escrevi um paper sobre isso, quero que leia antes de continuarmos'"
    - "[SOURCE: sessão 017a1f24] 'calma vamos planejar antes de alterar qualquer coisa' (dito 2x na mesma sessão)"
    - "[SOURCE: sessão 4af01fc6, mmos] 'podemos entao capturar uma documentacao que mereça ser lida antes de fazer uma nova view em db'"
```

## Decision Tree

```javascript
IF (proposed_change_is_architectural)
  STEP_1: STOP mechanical execution
    "calma vamos planejar antes de alterar qualquer coisa"
  STEP_2: UNDERSTAND conceptual model
    READ: paper/spec/doc if exists (AN_KE_082)
    IF (no doc exists) → DISCUSS conceptual model with human first
    MAP: how does the current conceptual model work?
  STEP_3: PLAN changes conceptually
    WHAT entities are affected?
    HOW do relationships change?
    WHAT breaks if we change this?
  STEP_4: ONLY THEN execute mechanically
    Migration/refactor/code follows conceptual understanding
  NEVER: write migration SQL without understanding the model behind it
```

## Failure Modes

### A Migration que Não Entendeu o Modelo
- **Trigger:** IA recebe "implementar tiers" e imediatamente escreve ALTER TABLE.
- **Manifestation:** Schema não reflete modelo conceitual do paper. Tiers mal-modelados.
- **Detection:** "calma vamos planejar antes" — dito 2x na mesma sessão (a8145c99, 017a1f24).
- **Prevention:** Ler paper/spec ANTES de escrever SQL. Entender conceito → DEPOIS implementar.

---

## ✓ Validation

**Paradoxo Identificado:** Velocidade de execução (pressão por delivery) vs. Compreensão conceitual profunda (qualidade arquitetural).

**Resolução Implementada:**
- Campo `sys_tension` adicionado ao YAML com referência cruzada e estratégia de resolução.
- Heurística confirma que investimento inicial em compreensão conceptual reduz retrabalho downstream.
- Aplicável a decisões arquiteturais e migrações de schema — não cosmético.
