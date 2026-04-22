# AN_KE_049 - Ship First, Doc Later

**Type:** Velocity Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Priorizar Execução sobre Documentação Prematura
**Source:** [SOURCE: Múltiplas sessões — padrão recorrente de Alan cortando README/docs prematuros]

## Purpose

Documentação prematura é desperdício quando o código ainda está mudando. Alan prioriza ENTREGAR funcionalidade e documentar DEPOIS. READMEs e docs extensos antes de código estável = retrabalho.

---

## 🔄 Systemic Tension (Paradoxo)

**Tension:** "Minimize doc overhead" ↔ "Handoffs/decisions MUST be documented NOW"

- **A-side (Minimize overhead):** READMEs, architecture docs, API specs DEFER até código estável (avoid churn).
- **B-side (Document critical flows):** Handoffs, decision logs, rules CREATE immediately (they ARE the guardrails that enable velocity).

**Resolution:** Classify docs at creation time—if type ∈ {handoff, decision_log, rule, governance}, CREATE. Else, DEFER to stability checkpoint.

## Configuration

```yaml
AN_KE_049:
  name: "Ship First, Doc Later"
  zone: "impacto"
  trigger: "IA propondo criar README, documentação extensa, ou parar pra documentar antes de terminar."

  sys_tension:
    tension_with: "AN_KE_029 (Survival by Documentation) — Ship velocity vs documentation as defense mechanism"
    resolution: "Classify doc type at birth. Handoffs/decisions/rules = CREATE NOW. READMEs/specs = DEFER to stability."

  rule: |
    SE no meio de implementação
    ENTÃO código funcional > documentação.
    README e docs DEPOIS que funciona.
    "nao precisa de readme, vamos avancar"

  veto_condition:
    trigger: "IA criando README de 200 linhas para feature que ainda não funciona."
    action: "VETO — Avance. Documente quando estiver estável."

  evidence:
    - "[SOURCE: sessão mentelendaria] 'nao precisa de readme, vamos avancar'"
    - "[SOURCE: sessão Hackathon-Hub] padrão recorrente de 'avance', 'avancar', 'proximo' cortando documentação"
    - "[SOURCE: sessão mmos 95be4920] 'essa parte nao quero: .claude/skills/ (auto-gerado, não deveria ser commitado)'"

  exceptions:
    - "Handoffs SÃO documentação crítica — sempre criar (AN_KE_029)"
    - "Decision logs SÃO críticos — documentar decisões na hora"
    - "CLAUDE.md rules — criar quando regra é descoberta"
```

## Decision Tree

```javascript
IF (ai_proposes_documentation)
  IF (feature_is_not_yet_working)
    THEN SKIP docs → focus on making it work
  ELSE IF (feature_works AND is_stable)
    THEN OK to document
  IF (doc_type == README AND code_is_changing)
    THEN DEFER — README will be outdated in 30 minutes
  IF (doc_type == handoff OR decision_log OR rule)
    THEN ALWAYS CREATE — these are time-sensitive
```

## Failure Modes

### O README Fantasma
- **Trigger:** IA cria README de 200 linhas descrevendo arquitetura que muda na próxima hora.
- **Manifestation:** README desatualizado em <1h. Pior que não ter README (doc rot).
- **Detection:** README contradiz código atual.
- **Recovery:** Deletar README desatualizado. Recriar quando estável.
- **Prevention:** Docs DEPOIS de estável. Handoffs e decisions SEMPRE.

## Integration with Workflow

```yaml
checkpoint:
  id: "ship-first-gate"
  heuristic: AN_KE_049
  phase: "Implementation / Documentation"
```

---

## ✅ Validation

| Critério | Status | Nota |
|----------|--------|------|
| **Paradoxo identificado** | ✓ | Tension: "minimize doc overhead" ↔ "document critical flows NOW" |
| **Resolução clara** | ✓ | Classificar doc type → handoffs/rules CREATE, others DEFER |
| **sys_tension field** | ✓ | Incluído com tension_with e resolution |
| **Exceções mapeadas** | ✓ | Handoffs, decision logs, CLAUDE.md rules sempre criam |
| **Failure mode coberto** | ✓ | O "README Fantasma" é prevenido pela rule de estabilidade |
| **Coerência interna** | ✓ | A-side (velocity) e B-side (guardrails) são complementares, não contraditórias |

**Validação:** AN_KE_049 resolve a aparente contradição através de classificação explícita de artefatos. Documentação tática (READMEs, specs) é adiada, mas documentação operacional (handoffs, decisões, regras) que SUSTENTA a velocidade é criada imediatamente. A tensão é gerida, não eliminada—é uma tradeoff consciente.
