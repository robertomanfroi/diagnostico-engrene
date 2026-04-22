# AN_KE_132 - Multi-Agent Collision Guard (Confira Antes de Avançar)

**Type:** Coordination Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Source:** [SOURCE: timestamp 1771209568, aiox-core] [SOURCE: timestamp 1771294538, forefy-prep-ahead] [SOURCE: timestamp 1773426281, aiox-stage]
**Tags:** [Multi-Agent, Coordination, Conflict, Git, Parallel]

## Purpose

Quando Alan opera multiplos agentes em paralelo (diferentes janelas/sessoes trabalhando no mesmo repositorio), ele exige que cada agente VERIFIQUE o estado atual antes de mutar qualquer arquivo. Isso porque outro agente pode ter alterado o mesmo arquivo segundos antes. Diferente de AN_KE_079 (Cross-Session Context Injection, onde o HUMANO injeta contexto manualmente), AN_KE_132 e sobre o AGENTE verificar proativamente se houve mudancas de outros agentes antes de agir. Alan grita "CONFIRA ANTES SE O OUTRO AGENTE NAO FEZ ISSO" quando detecta que um agente ignorou trabalho feito por outro. Esse pattern aparece em 4 projetos distintos (aiox-core, forefy-prep-ahead, aiox-stage, sinkra-hub) sempre no contexto de trabalho multi-janela.

## Configuration

```yaml
AN_KE_132:
  name: "Multi-Agent Collision Guard"
  zone: "impacto"
  trigger: "Agente prestes a modificar arquivo/recurso em repositorio onde outros agentes podem estar trabalhando simultaneamente."

  sys_tension:
    tension_with: "AN_KE_079 (Cross-Session Context Injection)"
    resolution: "AN_KE_079 e o humano como bridge de contexto entre sessoes. AN_KE_132 e o AGENTE verificando proativamente (git status, read file, check timestamp) antes de mutar. Um e humano→IA, outro e IA→filesystem. Complementares."

  rule: |
    SE ambiente tem multiplos agentes/janelas trabalhando em paralelo
    ENTAO antes de QUALQUER mutacao (edit, write, migration, schema change):
      (1) git status / git diff para verificar mudancas nao commitadas
      (2) Read do arquivo alvo para ver se conteudo mudou desde ultima leitura
      (3) Se outro agente ja fez a tarefa → NAO DUPLICAR
      (4) Se outro agente esta no meio → ESPERAR ou pedir ao humano
    SE detectar conflito → PARAR e reportar ao humano
    NUNCA assumir que o estado do arquivo e o mesmo de quando foi lido pela ultima vez

  veto_condition:
    trigger: "Agente modificando arquivo sem verificar se outro agente ja alterou."
    action: "VETO — 'CONFIRA ANTES SE O OUTRO AGENTE NAO FEZ ISSO'"

  evidence:
    - "[SOURCE: timestamp 1771209568, aiox-core] 'CONFIRA ANTES SE O OUTRO AGENTE NAO FEZ ISSO'"
    - "[SOURCE: timestamp 1771294538, forefy-prep-ahead] 'lembre-se que temos outros agentes trabalhando tb, precisa sempre conferir antes de avançar'"
    - "[SOURCE: timestamp 1773426281, aiox-stage] 'executa as 5 correcoes, comeca pelo state manager, mas considerando que tenho outro agente tentando fazer o mesmo entao leia antes, pois o arquivo pode ter sido alterado'"
    - "[SOURCE: timestamp 1774986738, sinkra-hub] 'confira antes o que foi feito, algumas coisas acredito que foram feita'"
    - "[SOURCE: timestamp 1771294601, forefy-prep-ahead] 'lembre-se que temos outros agentes trabalhando tb, precisa sempre conferir antes de avancar, crie um handoff par afazermos isso na proxima sessao, leia o .claude para entender coo fazer'"
```

## Decision Tree

```javascript
IF (about_to_mutate_file && multi_agent_environment)
  STEP_1: CHECK git status
    IF (uncommitted changes from other agent detected)
      → READ those changes before proceeding
      → ASSESS: does this overlap with my task?
  STEP_2: READ target file FRESH
    IF (file content differs from last read)
      → ANOTHER AGENT modified it
      → STOP and assess impact
  STEP_3: DECIDE action
    IF (other agent COMPLETED my task) → SKIP, report to human
    IF (other agent PARTIALLY completed) → BUILD ON their work, don't redo
    IF (potential CONFLICT) → STOP, report to human for arbitration
    IF (no overlap) → PROCEED with mutation
  NEVER: Assume file state from cache/memory
  NEVER: Overwrite another agent's recent work
  ALWAYS: git status before git add
```

## Failure Modes

### O Merge Cego
- **Trigger:** Agente A edita config.yaml. Agente B edita o mesmo config.yaml sem verificar.
- **Manifestation:** Agente B sobrescreve trabalho de Agente A. Informacao perdida. Human descobre ao revisar.
- **Detection:** Alan nota inconsistencia e grita "CONFIRA ANTES."
- **Prevention:** Read fresh antes de qualquer Write. Git status como primeiro passo de qualquer mutacao.

### O Trabalho Duplicado
- **Trigger:** Agente A completa task T. Agente B, sem verificar, comeca a mesma task T.
- **Manifestation:** Dois resultados conflitantes para a mesma task. Tempo desperdicado. Conflito de merge.
- **Detection:** Alan percebe duplicacao: "algumas coisas acredito que foram feitas."
- **Prevention:** Verificar se task ja foi feita por outro agente antes de iniciar. Handoff entre agentes quando possivel.
