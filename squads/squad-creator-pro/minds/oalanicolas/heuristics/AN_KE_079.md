# AN_KE_079 - Cross-Session Context Injection

```yaml
heuristic_id: AN_KE_079
name: "Cross-Session Context Injection"
zone: "excelencia"
agent: "@oalanicolas"
source: "sessões mmos 9c3ca5e9, 6484e8b6, 1ed77acc — trabalho paralelo multi-janela"
sys_tension:
  tension_with: "AN_KE_050 (Inimigo Zero: Complexidade Inútil) — overhead de consolidação + bridge humano em sessões paralelas"
  resolution: "Injeção de contexto APENAS para domínios que têm impacto direto. Não contaminar autonomia de sessões independentes. A decisão de 'é impactante?' fica com o humano, não com a IA."
```

**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões mmos 9c3ca5e9, 6484e8b6, 1ed77acc — trabalho paralelo multi-janela]

## Purpose

Quando trabalhando em múltiplas sessões paralelas, injetar contexto de uma sessão na outra PROATIVAMENTE. A IA não tem visibilidade cross-session — cada janela é um universo isolado. O humano é o bridge. Sem essa injeção: sessão A cria schema que sessão B não sabe, sessão B gera migrations que conflitam. Alan pratica isso sistematicamente: informa mudanças, pede consolidação para handoff, e verifica impacto cross-janela.

## Configuration

```yaml
AN_KE_079:
  name: "Cross-Session Context Injection"
  zone: "excelencia"
  trigger: "Trabalhando em múltiplas sessões Claude/Codex/Gemini em paralelo."

  rule: |
    SE fez trabalho em outra sessão que impacta a atual
    ENTÃO informar a IA proativamente:
      (1) O QUE mudou na outra sessão
      (2) COMO impacta o trabalho desta sessão
      (3) SE há conflitos potenciais (mesmo arquivo, mesmo schema)
    A IA não tem visibilidade cross-session. Você é o bridge.
    No final: consolidar para continuidade ("consolide tudo para continuar em outra sessão").

  veto_condition:
    trigger: "Duas sessões editando mesmo domínio sem informar uma sobre a outra."
    action: "VETO — Injetar contexto. 'o que acabei de fazer em outra sessão pode impactar seu trabalho.'"

  evidence:
    - "[SOURCE: sessão 9c3ca5e9, mmos] 'o que acabei de fazer em outra sessao e pode impactar/acelerar o seu trabalho e acho importante saber antes de continuar'"
    - "[SOURCE: sessão 6484e8b6, mmos] 'consolide tudo o que fez para continuar em outra sessao'"
    - "[SOURCE: sessão 1ed77acc, mmos] 'onde está toda esta documentacao? vou ir para outra janela com db-sage para conferir'"
    - "[SOURCE: sessão f5cce682, sinkra-hub] 'Você consegue rodar isso em outra janela/sessão sem depender desta?'"
```

## Decision Tree

```javascript
IF (working_in_multiple_sessions)
  BEFORE_SWITCHING:
    STEP_1: CONSOLIDATE current session state
      "consolide tudo o que fez para continuar em outra sessao"
    STEP_2: IDENTIFY cross-impact
      WHAT files changed? WHAT schema changed? WHAT decisions made?

  WHEN_ENTERING_NEW_SESSION:
    STEP_3: INJECT context from other session
      INFORM: "fiz X na outra sessão, pode impactar Y aqui"
      PROVIDE: specific files, changes, decisions

  ON_CONFLICT:
    IF (both sessions editing same file) → STOP one, sync, resume
    IF (both sessions changing schema) → STOP both, merge schema changes
    IF (decisions conflict) → surface to human for arbitration

  RELATED: AN_KE_099 (persist rules in config) — config files ARE cross-session context
```

## Failure Modes

### O Schema que Conflitou
- **Trigger:** Sessão A cria tabela X. Sessão B cria migration que assume X não existe.
- **Manifestation:** Migration falha em produção. "coluna já existe" ou "tabela não encontrada."
- **Detection:** Migration com erro de conflito em deploy.
- **Prevention:** Injetar contexto de mudanças de schema entre sessões. "fiz migrations na outra janela."

## Validation

**Paradoxo Identificado:** Quanto mais paralelo o trabalho, mais dependente a IA fica da injeção manual de contexto. A IA não consegue ver além de sua sessão, criando um gargalo de dependência do humano como "bridge" — justamente quando a paralelização deveria aumentar autonomia.

**Resolução:** A injeção de contexto NÃO é um problema a ser eliminado, mas uma PRÁTICA DELIBERADA. O humano decide o que é "impactante" — nem tudo merece ser comunicado cross-session. Sessões trabalhando em domínios independentes podem permanecer isoladas. A tensão resolve-se quando o humano ativa a injeção apenas para domínios com risco real de conflito.

**Checklist de Validação:**
- [ ] Mudança de schema? Informar otra sessão
- [ ] Mudança de arquivo compartilhado? Consolidar antes de trocar sessão
- [ ] Mudança de decisão arquitetural? Injetar contexto
- [ ] Mudança isolada (feature nova, sem deps)? Não contaminar outra sessão
- [ ] Ambiguidade sobre impacto? Perguntar ao humano antes de injetar
