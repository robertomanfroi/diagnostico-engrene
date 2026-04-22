# AN_KE_020 - Formato Do Artefato É o Contrato

**Type:** Decision Heuristic
**Zone:** 🚀 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Schema as Contract
**Source:** [SOURCE: Epic 70+71 — validation.log e score_card.yaml padronizados via reporting.sh, 3 formatos → 1]
**sys_tension:** (code_flexibility_vs_schema_rigidity, unified_schema_enforced_via_shared_emitters)

## Purpose

O formato do artefato de saída (log, score_card, state.json, progress.txt) é o contrato entre o runner e seus consumidores. Padronizar o formato é mais importante que padronizar o código.

## Configuration

```yaml
AN_KE_020:
  name: "Formato = Contrato"
  zone: "impacto"
  trigger: "Definindo outputs de pipeline/runner/processo"

  rule: |
    SE múltiplos scripts produzem artefatos consumidos por outros
    ENTÃO padronizar o SCHEMA do artefato (campos, tipos, formato)
    Código interno pode variar — o que importa é o output
    Dois scripts podem ter código totalmente diferente
    DESDE QUE produzam artefatos no mesmo schema

  evidence:
    - "validation.log: 3 formatos diferentes → 1 (Target/Type/Score/Verdict/Dims)"
    - "score_card.yaml: 3 schemas → 1 (validation/checks/dimensions/scores)"
    - "Qualquer ferramenta que lê score_card de qualquer runner sabe o schema"
    - "reporting.sh: emit_validation_log() + emit_score_card_yaml() = contrato"

  tension_with: "AN_KE_021 (Repair Layer Between Generator and Validator) — Schema rigidez vs flexibilidade de adaptação"
```

## Decision Tree

```javascript
IF (defining_pipeline_outputs)
  STEP_1: DEFINE output schema (fields, types, format)
    SCHEMA is the contract, not the code
  STEP_2: VALIDATE all producers emit same schema
    IF (producer_A.schema != producer_B.schema) → ALIGN schemas
  STEP_3: CODE is free to vary internally
    Two scripts with different code but same output schema = OK
  NEVER: standardize code but leave outputs inconsistent
```

## Failure Modes

### Os 3 Formatos de Score Card
- **Trigger:** validate-skill, validate-squad, sinkra-map each produce score cards in different formats.
- **Manifestation:** Consumer tool can't read score cards from different producers.
- **Detection:** 3 parsers needed for 3 producers. Should be 1 parser, 1 schema.
- **Prevention:** emit_score_card_yaml() as shared function. Schema = contract.

## Validation

**✓ Verified:** Schema standardization enforces contract invariants across heterogeneous producers.

**✓ Evidence:** reporting.sh emit_validation_log() + emit_score_card_yaml() demonstrate single schema consumable by N producers with M internal implementations (code free to vary, schema immutable).

**✓ Resolution:** Tension resolved via shared emitter functions — code flexibility achieved by centralizing schema contract, not duplicating it across producers.

**✓ Applied in:** validate-skill, validate-squad, sinkra-map (unified score_card.yaml schema, parallel codebases).
