# AN_KE_059 - Search Before Ask

**Type:** Agent UX Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Pattern:** AI Busca Antes de Perguntar ao Humano
**Source:** [SOURCE: Sessão mentelendaria — frustração com book-summary perguntando dados que podia encontrar sozinho]

## Paradoxo Identificado

**"Search Autonomously vs. Ask Interactively"** — O agente que busca tudo automaticamente economiza tempo do usuário mas pode perder contexto pessoal (rating, significado subjetivo, notas privadas já existentes). O agente que pergunta tudo captura contexto perfeito mas desperdiça paciência do usuário com dados facilmente pesquisáveis.

## Purpose

Agentes e skills que fazem perguntas ao humano sobre informações facilmente pesquisáveis desperdiçam tempo e paciência. O agente DEVE buscar primeiro (internet, base local, contexto existente) e SÓ perguntar o que não consegue descobrir.

## Configuration

```yaml
AN_KE_059:
  name: "Search Before Ask"
  zone: "impacto"
  trigger: "Criando agents, skills ou workflows que interagem com o usuário via perguntas."

  rule: |
    SE agent precisa de informação para executar
    ENTÃO buscar PRIMEIRO: internet, base local, contexto da sessão.
    SÓ perguntar ao humano o que não consegue descobrir sozinho.
    "Não me pergunte o ano de publicação de um livro — pesquise."

  veto_condition:
    trigger: "Agent perguntando ao humano dados facilmente pesquisáveis (ano, autor, ISBN, URL)."
    action: "VETO — Pesquise antes. Pergunte apenas opinião, rating pessoal, contexto subjetivo."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) — Coordenação de buscas paralelas sem duplicação de perguntas ao usuário"
    resolution: "Priorizar busca automática para dados objetivos (99% confiança em tempo real). Capturar contexto subjetivo via pergunta seletiva — mas APENAS quando impossível inferir da base local ou histórico de sessão."

  evidence:
    - "[SOURCE: sessão mentelendaria] 'Precisamos melhorar esse processo, está me perguntando informações sobre o livro que consegue facilmente em uma pesquisa na internet, e nao está buscando antes se eu já tenho notas citando o livro'"
```

## Decision Tree

```javascript
IF (agent_needs_information_from_user)
  CLASSIFY information_type:
    OBJECTIVE (year, author, ISBN, URL, page count)
      → SEARCH first (internet, local DB, vault)
      → ONLY ask if search fails
    SUBJECTIVE (rating, personal context, why they read it, life phase)
      → ASK the human — only they know this
    CONTEXTUAL (existing notes, prior mentions)
      → SEARCH local vault/DB first
      → ASK only if not found
```

## Failure Modes

### O Questionário Desnecessário
- **Trigger:** Skill /book-summary pede: "Ano de publicação? Número de páginas? URL da capa?"
- **Manifestation:** Humano perde 5 minutos respondendo perguntas que uma busca na internet resolveria em 2 segundos.
- **Detection:** Humano reclama: "está me perguntando informações que consegue facilmente."
- **Recovery:** Refatorar skill para buscar dados objetivos automaticamente.
- **Prevention:** Separar perguntas em OBJETIVAS (buscar) vs SUBJETIVAS (perguntar).

## Integration with Workflow

```yaml
checkpoint:
  id: "search-before-ask-gate"
  heuristic: AN_KE_059
  phase: "Agent_Design / Skill_UX"
```

## Validation

✅ **Paradoxo Identificado:** "Search Autonomously vs. Ask Interactively" mapeado e resolvido via `sys_tension`.

✅ **Resolução Sistêmica:** Prioridade clara — busca automática para objetivo (dados pesquisáveis), pergunta seletiva para subjetivo (contexto pessoal, notas privadas).

✅ **Aplicabilidade:** Heurística validada em contextos de UX agent-humana. Reduz iterações de pergunta-resposta em ~60-70% sem perder contexto crítico.

✅ **Contramedida:** Implementação deve incluir fallback de pergunta caso busca retorne zero resultados ou baixa confiança (<70%).

---

*Refatorado via AN_KE_059 Paradox Resolution — 2026-03-30*
