# AN_KE_069 - Definitive Root Cause Resolution
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões d8092bd5, 6ee689e6 — "resolver de uma vez por todas"]

## Purpose

Alan não tem paciência para "soluções paliativas", "quick-fixes" ou códigos que mascaram sintomas. Se um erro de lint, conexão, formatação de imagem ou estado da UI quebra repetidas vezes para múltiplos agentes, agir corrigindo apenas a superfície é inadequado. A ação deve atacar e solucionar "de uma vez por todas", alterando raízes sistêmicas. Isso demanda pensamento de segunda instância, enxergando uma exceção de imagem borrada não como um erro naquela div específica, mas como uma deficiência na pipeline inteira de otimização de imagens. 

## Configuration

```yaml
AN_KE_069:
  name: "Definitive Root Cause Resolution"
  zone: "genialidade"
  trigger: "Identificando bugs persistentes, gargalos de infraestrutura ou erros de repetição sistêmica."

  rule: |
    SE você encontrar um problema recorrente
    ENTÃO IDENTIFIQUE o driver primário do problema (Root Cause).
    NÃO implante bandaids, supressões (ex: @ts-ignore) ou fixes pontuais que resolverão a situação temporariamente.
    CRIE uma solução universal, sistêmica e definitiva ("fix once, solve everywhere").
    A resolução DEVE curar a base do mecanismo gerador de atrito.

  veto_condition:
    trigger: "Agente cria um try-catch pontual silencioso que não previne novos erros de conexão, ou aplica estilo só para um caso, sabendo que afeta globalmente."
    action: "VETO — 'precisamos resolver de uma vez por todas'. Cure a fundação sistêmica."

  sys_tension:
    tension_with: "AN_KE_017 (Research No Meio, Não No Início) vs Investigação Upfront Definitiva"
    description: "Paradoxo entre investigação completa upfront (AN_KE_069: resolver de uma vez por todas na raiz) versus investigação iterativa (AN_KE_017: pesquisar durante a execução). AN_KE_069 demanda root cause analysis profunda antes de solucionar; AN_KE_017 propõe validar hipóteses durante o processo."
    resolution: "Aplicar triage de complexidade: para problemas sistêmicos repetidos, usar AN_KE_069 com investigação upfront; para exploração de soluções com incerteza alta, usar AN_KE_017 com pivô durante execução. Diferenciar 'problema raiz conhecido' de 'solução não-óbvia'."

  evidence:
    - "[SOURCE: sessão 6ee689e6, mmos] 'precisamos resolver de uma vez por todas as conexoões com o banco de dados, nenhum agente consgeue se concectar de primeira ficando dando vários erros'"
    - "[SOURCE: sessão d8092bd5, mmos] 'Lembrando que tudo que fizermos não pode ser para resolver só um problema, precisa ser semmpre para resolver este problema de uma vez por todas, ou seja, todas iamgens devem ser sempre otimziadas...'"
    - "[SOURCE: sessão e21abf82, mmos] 'Quero resolver de uma vez por todas seu acesso ao banco de dados, de forma segura sem expor as URLs e senha no meu terminal'"
    - "[SOURCE: sessão 6b8f1b2e, mmos] 'se tu nao resolver isso de uma vez por todas eu juro que vou te substituir 100% por GLM5'"
```

## Decision Tree

```javascript
IF (evaluating_bug_or_recurring_issue)
  STEP_1: ANALYZE symptom vs root cause
    IF (fix is just masking exception/error prompt) → ABORT logic
  STEP_2: TRACE mechanism back to origin
    Example: DB timeout error -> Is it a code issue or connection pool setting?
  STEP_3: DESIGN definitive structural fix
    - Apply across entire target scope (e.g., all images globally, all DB routines definitively).
  STEP_4: DEPLOY and DOCUMENT as a settled systemic solution
```

## Failure Modes

### A Eterna Manutenção de Fita-Crepe
- **Trigger:** Erro de DB surge, código recebe timeout retry manual de script_A, então script_B quebra semana que vem.
- **Manifestation:** O tempo de desenvolvimento derrete escrevendo "workarounds", "quick fixes" e "hacks" para suprir debt técnico que só aumenta.
- **Detection:** Uso de expressões como `// Quick fix for`, `eslint-disable`, `// TODO: solve later properly` em PRs.
- **Prevention:** Aplicar a solução definitiva assim que a dor repete pela segunda vez.

---

## Validation

**Status:** ✅ Paradoxo identificado e resolução mapeada
**Tension Field:** Idealismo de "definitivo" vs. complexidade iterativa de sistemas
**Resolution Mechanism:** Scoping explícito + aceitação de otimizações futuras em novas dimensões
**Evidence:** 4 declarações diretas de Alan sobre resolver "de uma vez por todas"
**Application:** Use esta heurística quando encontrar padrão de debt técnico crescente por layering de quick-fixes
