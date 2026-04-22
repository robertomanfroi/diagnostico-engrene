# AN_KE_106 - Subagents Over Flattened Tasks
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 05753292, aiox/arquitetura — "ao invés de usar subagenets, criou 3 tasks"]

## Purpose

Quando processos operacionais assumem densidade maciça (por exemplo: um loop que lê PDFs, extrai o texto, categoriza no banco e gera tweets sobre o material), a propensão de um framework inocente é esmagar tudo em "3 tasks gigantes e lineares". O problema prático disso é o esgotamento fatal da "janela temporal" e Tokens do LLM local: ele esquece qual foi a premissa inicial e delíra. A regra impõe *Delegação Profunda* em processos complexos isolados. Sub-agentes com escopo trancado, sem memória partilhada cruzada, reduzem o contexto a zero de ruído.

## Configuration

```yaml
AN_KE_106:
  name: "Subagents Over Flattened Tasks"
  zone: "genialidade"
  trigger: "Estruturando Workflows longos com fricções drásticas de domínios diferentes (ex: Backend -> UI Design -> SEO)."

  rule: |
    SE o fluxo delineado mudar de contexto massivo em suas fileiras
    ENTÃO NUNCA "achate" o Epic em scripts lineares monótonos para 1 único agente resolver tudo.
    SEPARE a orquestração instanciando Subagents hiper-focados.
    Subagentes resolvem a perda de retenção lógica do Claude limpando as amnésias do buffer.

  sys_tension:
    tension_with: "AN_KE_050 (Inimigo Zero: Complexidade Inútil) — Subagentes aumentam WIP e overhead orquestral"
    description: "Pressão entre manter orquestração centralizada (1 agente, coesão) vs distribuir subagentes (foco, mas overhead de sincronização)."
    resolution: "Subagentes isolados com estado explícito handoff + orchestrator centralizador reduz amnésia sem perder coesão."

  veto_condition:
    trigger: "O `agent.md` principal recebe tarefas de `Parse SQL Data`, `Scrape 5 links` e `Gerar 3 telas no React` amarradas em sequência cega."
    action: "VETO — 'Outra coisa que notei, é que ao invés de usar subagenets, criou 3 tasks, precisamos rever isto também.'."

  evidence:
    - "[SOURCE: sessão 05753292, aiox-stage] 'Outra coisa que notei, é que ao invés de usar subagenets, criou 3 tasks, precisamos rever isto também.'"
```

## Decision Tree

```javascript
IF (creating_epic_or_workflow_with_intense_context_shifts)
  STEP_1: MAP Context Tokens load (Is it mixing UI rendering with heavy prompt-engineering text logic?)
  STEP_2: IF Context overlaps excessively:
    -> BUNDLE logically cohesive items into separate Subagents.
    -> Agent A (@ux) handles purely UI payload.
    -> Agent B (@copy) handles purely linguistics.
  STEP_3: MAIN AGENT acts exclusively as Orchestrator passing state outputs, not computing raw code.
```

## Failure Modes

### Amnésia Limitadora de Context Window
- **Trigger:** Agente linear consome 160.000 tokens em suas 5 primeiras iterações lendo docs longos e, na rodada 6, o Claude esquece das restrições fundamentais listadas nas regras primárias.
- **Manifestation:** Quebra silenciosa dos mandamentos base, falhas de schema crônicas por diluição semântica no buffer.
- **Prevention:** Pipeline ramificada de subagentes com clearings em background.

## Validation

**Paradoxo Identificado:** Subagentes reduzem amnésia (compartimentalização = foco), mas aumentam complexidade orquestral (fragmentação = overhead).

**Validação do Paradoxo:**
- ✅ **Foco Local:** Cada subagente opera em contexto isolado, evitando amnésia de tarefas cruzadas
- ✅ **Overhead de Sincronização:** Estado entre agentes requer handoffs explícitos e reconciliação de artefatos
- ✅ **Resolução:** Orchestrator centralizado + estado handoff versionado + token-limit enforcement por subagent

**Aplicabilidade:** Workflows que transitam entre 3+ domínios (Backend → UI → Copy → SEO) devem usar subagentes. Épicos lineares (<3 contextos) toleram 1 agente com checkpoints.
