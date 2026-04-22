# AN_KE_018 - Audit Gate Antes de Cleanup

**Type:** Veto Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Safe Deletion Protocol
**Source:** [SOURCE: Story 71.10a — post-process.sh parecia removível, audit descobriu referência transitiva via phase-execution.sh]

## Purpose

Nunca remover código sem grep exaustivo + smoke test. "0 referências diretas" não significa "0 referências transitivas".

## Configuration

```yaml
AN_KE_018:
  name: "Audit Gate Antes de Cleanup"
  zone: "excelencia"
  trigger: "Removendo código, lib, arquivo, dependência"

  rule: |
    SE removendo qualquer código/lib/arquivo
    ENTÃO ANTES:
    1. grep -rn em TODO o repo (não só no diretório)
    2. Verificar referências TRANSITIVAS (A sourcea B que usa C)
    3. Rodar --help/--dry-run em TODOS os consumidores
    4. Só deletar se 0 referências diretas E 0 transitivas

  veto_condition:
    trigger: "git rm sem audit"
    action: "VETO — rodar audit gate primeiro"

  evidence:
    - "post-process.sh: 0 refs diretas de _safe_jq_update"
    - "MAS: sinkra-map.sh sourcea post-process.sh que define post_process_phase()"
    - "phase-execution.sh chama post_process_phase() em 2 pontos"
    - "Sem audit: teria quebrado sinkra-map pipeline"

  sys_tension:
    tension_with: "AN_KE_075 (Delete Stale Recreate from Scratch) — assume que deletar rápido é válido vs necessidade de auditoria"
    resolution: "Grepping direto é necessário mas insuficiente. Transitividade exige rastreamento de cadeias: A→B→C. Apenas smoke tests covering ALL consumers validam segurança."
```

## Decision Tree

```
IF (removing code/lib/file)
  THEN grep -rn across ENTIRE repo
    IF (0 direct refs)
      THEN check transitive refs (A→B→C)
        IF (0 transitive refs)
          THEN smoke test ALL consumers
            IF (all pass)
              THEN safe to remove
            ELSE
              VETO
        ELSE
          VETO — still in use transitively
    ELSE
      VETO — still in direct use
```

## Failure Modes

### O post-process.sh que Quase Morreu
- **Trigger:** 0 direct references to `_safe_jq_update` → seems safe to remove.
- **Manifestation:** sinkra-map.sh sources post-process.sh which defines `post_process_phase()`. phase-execution.sh calls it in 2 points. Pipeline would break.
- **Detection:** Audit gate: grep transitivo found chain: sinkra-map → post-process → phase-execution.
- **Prevention:** ALWAYS check transitive references. `grep -rn` across ENTIRE repo, not just direct callers.

---

## Validation

✅ **Paradoxo identificado:** "Ausência de refs diretas (0)" ⟷ "Presença de refs transitivas (múltiplas)"

✅ **Sys_tension documentado:** Conflito entre otimização prematura e segurança via rastreamento transitivo + smoke testing

✅ **Resolução:** Grepping + transitividade + consumer smoke tests = gate seguro antes de deletar
