# AN_KE_083 - Cross-Agent Awareness
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 851f99d8, aiox-stage — "Tem outro agente trabalhando"]

## Purpose

Você não está sozinho no repositório. O cenário AIOX é desenhado em modo *Multi-Player*, portanto, os agentes não devem atuar com arrogância de "singleton" ("sou a primeira coisa rolando aqui hoje"). Agentes podem, devem e vão entrar assincronamente preenchendo pedaços de um software enorme. Quando acordar em uma workspace, ou antes de sobrescrever uma estrutura greenfield perigosa com base no último input do chat, o Agente *deve ler fisicamente* as pastas adjacentes e se perguntar: "o outro Agente ou o usuário já adiantou isso agorinha?". Check de integridade temporal antes da cegueira de prompt.

## Configuration

```yaml
AN_KE_083:
  name: "Cross-Agent Awareness"
  zone: "excelencia"
  trigger: "Início de task em repositório grande após um intervalo, ou retomada de épicos de desenvolvimento."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Awareness Multi-Agente"
    resolution: "Equilibrar velocidade (30s check vs 5min audit) com coordenação: arquivo recente (< 5 min atrás) = SKIP rebuild; arquivo antigo (> 1h) ou ausente = PROCEED. Autonomia não é anarquia—é respeitar locks temporais."

  rule: |
    SE iniciar elaboração de assets novos de uma pipeline
    ENTÃO assuma que estamos num ambiente de inteligência paralela.
    PRIMEIRO confira se o asset já não foi gerado via file system / git log.
    Revisar > Reescrever as cegas.

  veto_condition:
    trigger: "Regerar um pacote de components UI inteiro sem verificar usando o comando ls/find se as pastas UI já ganharam os componentes nos últimos 5 commits por outro AI."
    action: "VETO — 'Tem outro agente trabalhando sempre revise pq algo ele pode já ter feito'."

  evidence:
    - "[SOURCE: sessão 851f99d8, aiox-stage] 'Tem outro agente trabalhando sempre revise pq algo ele pode já ter feito'"
    - "[SOURCE: sessão 341b50fe, aiox-stage] 'siga, mas sempre visando pq tenho outros agents trabalhando nisso tb e eels podem ter já feito'"
```

## Decision Tree

```javascript
IF (assigned_to_build_target_X)
  STEP_1: Assume another agent/human might have touched X recently.
  STEP_2: CHECK file existence (`view_file`, `list_dir`, `grep_search`).
  STEP_3: CHECK git history (`git log -n 5`) to trace recent modifications.
  STEP_4: IF (X partially built) -> APPEND and ENHANCE seamlessly instead of destroying.
  STEP_5: IF (X missing) -> PROCEED building.
```

## Failure Modes

### Overwrite Destrutivo do Agente Incoordenado
- **Trigger:** Agente Frontend e Agente Backend atuando no projeto. Backend gera tipos TS nos outputs. Frontend reconstrói tudo na cabeça usando uma versão sem consultar o folder target.
- **Manifestation:** Perda imediata do código que um modelo gastou 10min escrevendo.
- **Prevention:** Leitura obrigatória do destino de escrita das funções de criação antes do execute final.

---

## Validation

- [ ] **Paradoxo Identificado:** Tensão entre Autonomia Radical (AN_KE_001) e Awareness Multi-Agente (AN_KE_083) é resolvida via timing heurístico (5min/1h thresholds).
- [ ] **sys_tension Campo:** Completo com tension_with e resolution explícitos.
- [ ] **Decision Tree:** Aplicável em contextos de rebuild paralelo (UI components, schemas, assets).
- [ ] **Failure Mode Coverage:** Cobre o cenário crítico de overwrite entre Frontend/Backend.
- [ ] **Escalabilidade:** Heurística de timing funciona com N agents assincronamente.
