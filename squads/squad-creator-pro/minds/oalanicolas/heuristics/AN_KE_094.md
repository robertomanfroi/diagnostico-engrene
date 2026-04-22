# AN_KE_094 - Agnostic Extensibility Protection
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão aiox-core/squads — "mudou de genérico para hardcode"]

## Purpose

A arquitetura do AIOX e os scripts CLI desenhados baseiam-se em expansão orgânica: adicionar squads, expansion-packs e modulos ao sistema *deve requerer zero modificações* no ecossistema subjacente. Hardcodear diretórios isolados nos `if/else` ao iterar quebra drasticamente esse design expansivo. Alan odeia retrocessos estruturais e alerta rigidamente pro fato de que os laços devem ser for-loops genéricos iterando os caminhos, protegendo a auto-descoberta dos packs na startup.

## Configuration

```yaml
AN_KE_094:
  name: "Agnostic Extensibility Protection"
  zone: "excelencia"
  trigger: "Desenvolvendo CLIs, runners ou iterators base do workspace infinito."

  rule: |
    SE o script precisa interagir com os plugins presentes (como expansion-packs, squads)
    ENTÃO USE descoberta de diretórios dinâmica (`fs.readdir`, `glob`, arrays por pathing).
    NUNCA insira os nomes "squad_a", "squad_b" hardcoded no código do handler.
    O sistema DEVE processar módulos adicionados no futuro livremente.

  veto_condition:
    trigger: "Agent reescreve o script de compilação iterando rigidamente `['pack_zero', 'pack_one']` ao notar que existem apenas aqueles dois hoje."
    action: "VETO — 'Pq voce mudou de generico para hardcode considerando que podemos ter novos expansion packs...'."

  evidence:
    - "[SOURCE: sessão question on hardcode] 'Pq voce mudou de generico para hardcode considerando que podemos ter novos expansions packs e como está vai impedir que os novos sejam atualizados automatiacmente'"

  sys_tension:
    tension_with: "AN_KE_050 (Inimigo Zero: Complexidade Inútil) — pragmatismo imediato de hardcoding vs. extensibilidade genérica"
    resolution: "Use generic discovery with optional caching layer — maintain extensibility while optimizing hot paths through lazy-loading and memoization, not through hardcoded lists."
```

## Decision Tree

```javascript
IF (writing_loop_or_handler_for_plugins_squads_etc)
  STEP_1: CHECK for static data arrays denoting structural entities mapping to folders.
    IF (`['workspaceA', 'workspaceB'].includes(x)`) -> FAIL.
  STEP_2: REPLACE WITH DYNAMIC CALLS
    Use `os.listdir()` or equivalent backend mechanism mapping over the path `/expansion-packs/*`.
  STEP_3: ENSURE script works successfully even if we drop 7 new generic folders there tomorrow.
```

## Failure Modes

### Hardcode de Atalho Burro
- **Trigger:** Agente quebra a genérica que rodava sobre todos arquivos de configs e adere um mapeamento manual local nos IFs.
- **Manifestation:** Um Expansion Pack inteiro inserido no repo principal vira fantasma - as CI/CDs não o testam nem empacotam. Retrabalho insano de debugar "onde está aquele bug de não buildar minha pasta?".
- **Prevention:** Nomes de domínios corporativos não existem soltos na infra. Toda configuração injetável vem de fora dos Runners.

## Validation

- ✅ **Paradoxo Identificado:** Extensibilidade genérica vs. pragmatismo de hardcoding — balanceado via caching memoizado
- ✅ **sys_tension Adicionado:** Documenta conflito entre `Pragmatism` (hardcode para velocidade) e `Agnostic Extensibility` (descoberta dinâmica)
- ✅ **Resolução Proposta:** Lazy-loading + optional caching layer preserva genéricidade mantendo performance
- ✅ **Aplicabilidade:** Crítica para arquiteturas infinitas (AIOX, squads, expansion-packs, workspaces multibusiness) 
