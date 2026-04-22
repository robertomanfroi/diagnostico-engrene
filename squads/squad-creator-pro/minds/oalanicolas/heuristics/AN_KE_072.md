# AN_KE_072 - Code Over Documentation
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões mmos 4404bc3e, 3cbfc9d5 — doc rot awareness + pivot para doc-rot detector]

## Purpose

Código funcional > documentação. Não como preferência casual — como PRINCÍPIO ARQUITETURAL. Documentação desatualizada (doc rot) é PIOR que zero doc porque induz ações erradas. A evolução do pensamento de Alan é reveladora: (1) primeiro percebeu que doc rot existia ("estamos melhorando ou criando doc rot?"), (2) depois cristalizou a hierarquia ("code > doc, codigo funcional é real"), (3) finalmente pivotou uma tool de anotação para DETECÇÃO de doc rot — ou seja, transformou uma ferramenta de CRIAR documentação em uma ferramenta de DELETAR documentação. Esse pivot é a evidence mais forte: a ação mais valiosa sobre documentação é SUBTRAÇÃO, não adição.

## Configuration

```yaml
AN_KE_072:
  name: "Code Over Documentation"
  zone: "genialidade"
  trigger: "Decisão entre investir tempo em documentação vs código funcional, ou IA gerando documentação sem ser solicitada."

  rule: |
    Hierarquia absoluta: Código funcional > documentação. Sempre.
    DELETAR doc podre > CRIAR doc novo > NÃO documentar > Documentar código instável.
    A ação mais valiosa sobre documentação é SUBTRAÇÃO.
    SE código está mudando → NÃO documentar (vai virar doc rot).
    SE doc existente está stale → DELETAR (mais valioso que criar novo).
    SE doc existente está correta → NÃO tocar (não duplicar, não expandir).

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents) vs Complexidade de Parsing Local"
    resolution: "Documentação é PROIBIDA exceto em 3 casos: (1) API pública com SLA (code > docs, mas código + spec < nenhum contrato), (2) regulatory/legal (contract força), (3) onboarding crítico (investir em code design primeiro, docs secundário). Em 90% dos casos, a resposta é DELETAR não CRIAR."

  veto_condition:
    trigger: "IA gerando documentação extensa para código instável, ou expandindo doc sem ser solicitada."
    action: "VETO — 'estamos melhorando ou criando doc rot?' Pergunte antes de documentar. Prefira code auto-documentado."

  evidence:
    - "[SOURCE: sessão 4404bc3e, mmos] 'code > doc, codigo funcional é real, documentar é criar DOC ROT'"
    - "[SOURCE: sessão 3cbfc9d5, mmos] 'estamos melhorando ou criando doc rot?'"
    - "[SOURCE: sessão 3cbfc9d5, mmos] 'vamos testar só mais uma vez e talvez possamos transformar ela não em anotação, mas de descobrir conteudo podre doc rot para deletar'"
    - "[PATTERN] Skill doc-rot nasceu durante sessão 3cbfc9d5: pivot de ferramenta de ANOTAÇÃO para ferramenta de DETECÇÃO/DELEÇÃO de doc rot — prova material do princípio"
```

## Decision Tree

```javascript
IF (documentation_decision)
  STEP_0: HIERARCHY CHECK
    DELETE stale doc > CREATE new doc > DO NOTHING > Document unstable code

  STEP_1: EXISTING DOC found?
    IF (exists AND stale) → PRIORITY: DELETE IT (higher value than creating new)
    IF (exists AND accurate) → KEEP AS-IS, do NOT expand, do NOT duplicate
    IF (not exists) → proceed to Step 2

  STEP_2: CODE STABILITY check
    IF (code actively changing) → DO NOT DOCUMENT — code will change, doc will rot
    IF (code stable > 2 sprints) → MINIMAL documentation only:
      - Types/interfaces as documentation (self-documenting)
      - 1-line comments for non-obvious WHY (never WHAT)
      - README only if externally consumed

  STEP_3: AI DOCUMENTATION CHECK
    IF (AI generating docs without being asked) → STOP
    IF (AI expanding existing docs) → STOP, ask "estamos melhorando ou criando doc rot?"
    IF (human explicitly asked for docs) → MINIMAL, focused, timestamped

  NEVER: generate verbose documentation "for completeness"
  PREFER: code with good names + types > external docs
  INSIGHT: if you find yourself wanting a doc-rot detector, the principle is working
```

## Failure Modes

### A Anotação que Vira Doc Rot
- **Trigger:** Ferramenta de anotação (@llm-context) gera anotações que desatualizam em dias.
- **Manifestation:** "estamos melhorando ou criando doc rot?" — pergunta durante revisão da tool.
- **Detection:** Doc/anotação descreve estado que não corresponde ao código atual.
- **Recovery:** Pivot: transformar a ferramenta de CRIAR anotações em DETECTAR doc rot. A melhor doc tool é a que DELETA docs.
- **Prevention:** Antes de criar doc, perguntar: "quanto tempo até isso ficar desatualizado?" Se < 1 mês → não criar.

## Validation

✓ **Paradoxo identificado:** Documentação é criada para melhorar compreensão, mas se virar doc rot (desatualizada), PIORA a compreensão e induz erro. A resolução é SUBTRAÇÃO (deletar doc podre) não ADIÇÃO.

✓ **Tension mapeada:** Tensão existe entre "Code Over Documentation" e necessidade ocasional de documentação como contrato (APIs públicas, regulatory). Resolução: criar doc APENAS em 3 casos específicos; em 90% do tempo, resposta é DELETAR.

✓ **Aplicabilidade:** Esta heurística aplica-se ao contexto AllFluence onde a documentação foi uma fonte histórica de desperdício; o pivô para doc-rot-detector validou empiricamente que SUBTRAÇÃO > ADIÇÃO.
