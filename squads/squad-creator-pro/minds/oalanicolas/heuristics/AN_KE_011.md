# AN_KE_011 - Compare Antes de Construir

**Type:** Decision Heuristic
**Zone:** 🔥 0,8% Genialidade
**Agent:** @oalanicolas
**Pattern:** Gap Analysis via Comparison
**Source:** [SOURCE: Epic 70 — validate-skill vs validate-squad, paridade 4/10 → roadmap de 5 stories]

```yaml
sys_tension:
  tension_with: "AN_KE_012 (Create Fast, Iterate Later)"
  resolution: "Comparação é busca rápida (service-catalog.yaml + grep) antes de qualquer código. Se >1min de busca ativa, pular direto pra construção iterativa."
```

## Purpose

Antes de criar qualquer artefato novo (script, skill, squad, módulo), comparar com o equivalente mais maduro que já existe no ecossistema. A comparação gera gap analysis de graça e evita recriação.

## Configuration

```yaml
AN_KE_011:
  name: "Compare Antes de Construir"
  zone: "genialidade"
  trigger: "Criando artefato novo"
  tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Analysis Latency"

  rule: |
    SE criando algo novo (script, skill, squad, módulo)
    ENTÃO PRIMEIRO buscar equivalente maduro no ecossistema
    COMPARAR feature-a-feature
    O GAP entre os dois É o roadmap

  anti_pattern: "Criar do zero quando existe algo 3x mais maduro no mesmo repo"

  evidence:
    - "validate-skill v1 vs validate-squad v4 → gap de 9 features → 5 stories geradas"
    - "Custo da comparação: 20min. Custo de criar do zero: 20h."
```

## Decision Tree

```
IF (criando artefato novo)
  THEN buscar equivalente maduro
    IF (equivalente existe)
      THEN comparar feature-a-feature → gap = roadmap
    ELSE
      THEN criar, mas documentar decisão IDS (G1-G6)
```

## Validation Questions

1. "Existe algo equivalente mais maduro no ecossistema?"
2. "Qual o score de paridade entre o novo e o existente?"
3. "O gap analysis gera um roadmap claro?"

## Failure Modes

### O Script Criado do Zero (Quando Existia Vizinho 3x Melhor)
- **Trigger:** Create validate-skill.sh sem comparar com validate-squad.sh v4 existente.
- **Manifestation:** Score de paridade: 4/10 features do vizinho maduro. 5 stories geradas pra fechar gap.
- **Detection:** Artefato novo com features básicas que o equivalente maduro já resolveu.
- **Prevention:** "Existe algo equivalente mais maduro?" → Comparar feature-a-feature ANTES de criar.

## Validation

✅ **Paradoxo Resolvido:** Tensão entre comparação upfront vs. iteração rápida é resolvida via busca de ~1min em registros canônicos (service-catalog.yaml, ecosystem-registry.yaml). Se registro não tem resposta clara, construir iterativamente e documentar no processo.

✅ **Evidence Trail:** 20min busca + gap analysis << 20h construção. Razão: busca é em índices, não deep dive arquitetônico.

✅ **Decisão Gatekeeping:** Comparação é obrigatória IFF (if and only if) existe registro público do artefato. Se não existe registro, gate-rule não dispara — construir segue direto.
