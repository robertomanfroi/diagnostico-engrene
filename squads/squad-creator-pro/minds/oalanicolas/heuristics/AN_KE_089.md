# AN_KE_089 - Validate Phases Mirror Map Phases
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão sinkra-hub b3c022b9 — comparando validate vs map process phases]

## Purpose

Paridade arquitetural: se um processo tem N fases de MAPEAMENTO (sinkra-map), o processo de VALIDAÇÃO correspondente DEVE ter fases correspondentes. A validação não pode ser monolítica se o mapeamento é granular. Cada fase de map produz output verificável → cada fase precisa de validação correspondente. Alan detectou que validate tinha menos fases que map e pediu alinhamento: "deveriamos criar mais fases quebradas no validate como no map-process."

## Configuration

```yaml
AN_KE_089:
  name: "Validate Phases Mirror Map Phases"
  zone: "excelencia"
  trigger: "Processo tem map/generate com N fases mas validate/review com menos fases."

  sys_tension:
    tension_with: "AN_KE_050 (Inimigo Zero: Complexidade Inútil) vs Granularidade de Validação"
    resolution: "Equilibrio dinamico: validate DEVE ter fases correspondentes a map (AN_KE_089), mas apenas para outputs verificáveis. Fases que não produzem validação acionável são WIP — eliminar conforme AN_KE_050. Shared infra entre map/validate (logging, model routing) reduz overhead."

  rule: |
    SE processo tem map/generate com N fases granulares
    ENTÃO validate/review DEVE ter fases correspondentes (1:1 ou N:subset).
    Validação monolítica para mapeamento granular = gap de feedback.
    Cada fase de map produz output → cada output precisa de validation gate.
    BONUS: shared infra entre map e validate (logging, model routing) — AN_KE_100.

  veto_condition:
    trigger: "validate-process tem 2 fases para map-process com 7 fases."
    action: "VETO — 'deveriamos criar mais fases quebradas no validate como no map.' Alinhar granularidade."

  evidence:
    - "[SOURCE: sessão b3c022b9, sinkra-hub] 'deveriamos criar mais fases quebradas no validate como no map-process'"
    - "[CONTEXT] sinkra-map.sh tem 7 phases. validate-squad.sh inicialmente tinha 3 phases (structure, quality, deep). Alan pediu alinhamento."
    - "[CONTEXT] sessão 0f1fe148 descobriu que validate-skill, validate-squad e sinkra-map compartilham lógica (AN_KE_100)"
```

## Decision Tree

```javascript
IF (process_has_map_and_validate)
  STEP_1: COUNT phases
    map_phases = N (e.g., sinkra-map has 7)
    validate_phases = M

  STEP_2: CHECK alignment
    IF (M < N/2) → MISALIGNMENT: validate too coarse
      → ADD phases to validate to match map granularity
    IF (M ≈ N) → ALIGNED: good
    IF (M > N) → OVER-VALIDATION: validate more granular than necessary

  STEP_3: MAP correspondence
    FOR EACH map_phase:
      IDENTIFY: what output does it produce?
      ENSURE: a validate_phase checks that specific output
    FOR EACH validate_phase:
      ENSURE: it corresponds to at least 1 map_phase output

  STEP_4: SHARE infra (AN_KE_100 cross-tool)
    Logging → shared between map and validate
    Model routing → shared between map and validate
    Phase execution → shared between map and validate

  NEVER: monolithic validate for granular map
```

## Failure Modes

### O Validate que Score Sem Granularidade
- **Trigger:** validate-squad gives 1 score for entire squad, map-process has 7 phases.
- **Manifestation:** Score 45/100 — but which phases failed? No granularity to act on.
- **Detection:** validate output has 1 number. map output has 7 sections.
- **Prevention:** Break validate into phases mirroring map. Each phase gets its own score. Total = weighted average.

## Validation

**Paradoxo identificado:** A granularidade de MAPEAMENTO exige granularidade de VALIDAÇÃO (AN_KE_089), mas granularidade excessiva em validação aumenta overhead computacional (AN_KE_090).

**Resolução:** Validação deve ter N fases correspondentes a map, com execução paralela via shared infra (logging, model routing) para minimizar duplicação. Cada fase de validate valida exatamente 1 output de map. Agregação ocorre apenas em scoring final (weighted average por fase).

**Critério de sucesso:**
- ✓ validate_phases ≥ map_phases / 2
- ✓ Cada output de map tem correspondente em validate
- ✓ Shared infra reduce overhead (AN_KE_100)
- ✓ Feedback granular por fase (não monolítico)

---
**Validado em:** 2026-03-30 | **Status:** ✅ Refatorado com sys_tension e validação
