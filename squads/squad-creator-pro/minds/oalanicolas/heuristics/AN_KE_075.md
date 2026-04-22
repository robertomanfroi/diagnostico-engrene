# AN_KE_075 - Delete Stale Recreate from Scratch
**Zone:** 🔥 20% Impacto | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão sinkra-hub 6c66eaf6 — limpeza e auditoria squad-creator-pro]

## Purpose

Counter-intuitive: quando artefato está desatualizado e o custo de atualizar > custo de recriar, DELETAR e recriar do zero. A tentação é "atualizar incrementalmente" — mas isso acumula cruft, inconsistências, e gera artefatos Frankenstein. A sessão 6c66eaf6 revela que Alan aplica isso em MÚLTIPLAS dimensões: (1) files desatualizados ("delete tudo que tiver desatualizado, melhor recriar do zero"), (2) organização questionável ("benchmarks dentro do squad-creator-pro? test-cases? isso precisa estar dentro dele? nao é sujeira?"), (3) documentação antiga ("tem mt documentacao que parece ser antiga tb de processos"). O princípio é mais profundo que file cleanup — é HYGIENE ORGANIZACIONAL: questionar a própria existência de cada artefato.

## Configuration

```yaml
AN_KE_075:
  name: "Delete Stale Recreate from Scratch"
  zone: "impacto"
  trigger: "Artefato desatualizado encontrado durante revisão, OU questionar se artefato deveria existir naquele local."

  rule: |
    SE artefato desatualizado E custo_atualizar > custo_recriar
    ENTÃO deletar e recriar do zero.
    SE artefato existe mas ninguém sabe POR QUE → questionar existência.
    SE artefato está no lugar errado ("precisa estar dentro dele?") → mover ou deletar.
    Manter stale = doc rot ativo contaminando contexto.
    Update incremental de artefato podre = Frankenstein.
    Delete + recreate from ground truth = consistência garantida.

  sys_tension:
    tension_with: "AN_KE_045 (Subtraction First Strategy) — Delete-from-Scratch approach é subtração radical vs preservação incremental. Porém: subtração de artefatos podres (>50% stale) garante higiene organizacional; em sistemas saudáveis, incrementalismo preserva contexto valioso. A tensão é: quando remover > consertarr."
    resolution: "Usar cost-threshold (0.3-0.5 ratio) como decisor. Abaixo = incremental. Acima = delete-recreate. Entre = preferir delete. Decisão baseada em métrica, não em preferência."

  veto_condition:
    trigger: "Fazendo patch incremental em artefato que: (a) está >50% desatualizado, (b) ninguém sabe pra que serve, ou (c) está no local errado."
    action: "VETO — 'delete tudo que tiver desatualizado, melhor recriar do zero.' Não faça Frankenstein. Questione a existência."

  evidence:
    - "[SOURCE: sessão 6c66eaf6, sinkra-hub] 'delete tudo que tiver desatualizado, melhor recriara do zero'"
    - "[SOURCE: sessão 6c66eaf6, sinkra-hub] 'O que são os benchmarks dentro do squad-creator-pro? test-cases? isso precisa estar dentro dele? nao é sujeira? tem mt documentacao que parece ser antiga tb de processos etc'"
    - "[META] Este upgrade de 11 cards (060-100) de 7L → ~60-80L é exemplo vivo desta heurística: stubs não foram patchados — foram deletados e recriados do zero"
```

## Decision Tree

```javascript
IF (stale_artifact_found)
  STEP_1: QUESTION existence first
    ASK: "isso precisa estar aqui? nao é sujeira?"
    IF (nobody knows why it exists) → DELETE without recreation
    IF (exists but in wrong place) → DELETE + recreate in correct location
    IF (exists with clear purpose but outdated) → proceed to Step 2

  STEP_2: EVALUATE update vs recreate
    cost_to_update = (lines_changed / total_lines) + (dependencies_broken / total_deps)
    IF (cost_to_update > 0.5 OR structure_changed) → DELETE and RECREATE from ground truth
    IF (cost_to_update < 0.3 AND structure_intact) → PATCH incrementally
    IF (between 0.3-0.5) → PREFER recreate (Frankenstein risk)

  STEP_3: BEFORE_DELETE
    HARVEST: valuable content that should survive (AN_KE_090 Template Harvesting)
    ARCHIVE: if artefato tem historical value (git history preserves)
    VERIFY: no active dependencies pointing to this artifact

  STEP_4: RECREATE from current ground truth
    SOURCE: current codebase state, not the old artifact
    FORMAT: current standards, not legacy format
    VALIDATE: new version against current reality
    NEVER: copy-paste from old artifact and "update" — starts from scratch

  THREE TRIGGERS of this heuristic:
    (1) FILE stale → "delete tudo desatualizado, melhor recriar do zero"
    (2) LOCATION wrong → "precisa estar dentro dele? nao é sujeira?"
    (3) DOCUMENTATION antiga → "mt documentacao que parece ser antiga de processos"
```

## Failure Modes

### O Frankenstein de Squad
- **Trigger:** Squad-creator-pro tem benchmarks, test-cases, e docs antigos acumulados de 6 meses de evolução.
- **Manifestation:** "O que são os benchmarks? test-cases? isso precisa estar dentro dele? nao é sujeira? tem mt documentacao que parece ser antiga"
- **Detection:** `ls -la` mostra arquivos com modified date > 60 days. Content não referenciado por nenhum script ativo.
- **Prevention:** Auditoria trimestral: para cada artefato perguntar "isso precisa existir? aqui? neste formato?" Se não → deletar.

## Validation

- ✅ **Paradoxo Identificado:** Tension entre incrementalismo (AN_KE_001) e delete-from-scratch (AN_KE_075) — resolvido via cost-threshold métrico
- ✅ **sys_tension** campo adicionado com tension_with e resolution explícitos
- ✅ **Decision Tree** fornece critério claro (0.3-0.5 cost ratio) para evitar decisões subjetivas
- ✅ **Failure Mode** exemplifica manifestação real em squad-creator-pro
- ✅ **Aplicabilidade:** Testado em upgrade 060-100 cards (stubs recriados, não patchados)
