# AN_KE_070 - Multi-IDE Sync Protocol
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 05e78370, aiox-stage — "vamos sincronizar sempre para claude"]

## Purpose

Alan utiliza um ecossistema complexo (Claude Code, Gemini, Roo, Cursor). Sempre que construímos scripts geradores ou `agents/workflows`, o design deve considerar portabilidade. Comandos globais (`/command`) e lógica de agente de profunda imersão funcionam de forma nativa apenas onde dão match absoluto (como no Claude CLI ou terminal de alta confianca), enquanto *nos outros* deve ser convertido apenas como *skills* (ferramentas passivas limitadas). Modificar em um significa propagar ao outro na medida da sua utilidade, garantindo sincronia transversal dos IDEs.

## Configuration

```yaml
AN_KE_070:
  name: "Multi-IDE Sync Protocol"
  zone: "excelencia"
  trigger: "Modificando scripts, agentes ou comandos CLI que impactam configurações dos IDEs AI."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Centralização Sequencial do Sync"
    resolution: "Centralizar em Claude Code como source-of-truth para commands/agents. Expor via skills em outros IDEs. Skills são conversas assincrónicas; commands são sincronizações CLI. Não gerar conflito de ativação: uma feature = um ponto de entrada + múltiplas formas de consumo."

  rule: |
    SE você criar ou atualizar commands ou skills para a base principal
    ENTÃO DEVE sincronizar transversalmente respeitando o ecossistema local.
    Claude Code recebe os pesos pesados (commands e agents).
    Gemini/Roo e outros recebem versões em formato de skill.
    O AIOX DEVE estar alinhado transversalmente.

  veto_condition:
    trigger: "Agente cria um feature amarrado estritamente ao framework Gemini que destrói as dependências do Claude Code, sem gerar skill isolada."
    action: "VETO — 'nos outros todos precisa ser apenas skill'."

  evidence:
    - "[SOURCE: sessão 05e78370, aiox-stage] 'vamos sincronizar sempre para claude /command e /agents, nos outros apenas o que eles tem compatibilidade, até onde sei nos outros todos precisa ser apenas skill'"
```

## Decision Tree

```javascript
IF (creating_or_updating_workflow_agent_skill)
  STEP_1: IDENTIFY execution context (Is this heavy orchestration or basic capability?)
  STEP_2: For CLAUDE CODE (Core Orchestration):
    -> Save as complex agent/command
  STEP_3: For GEMINI / ROO / OTHERS (Task Execution):
    -> Map strictly as a Skill, preventing incompatible IDE crashes.
  STEP_4: Verify git sync status across workspaces.
```

## Failure Modes

### Quebra Incompatível de IDE
- **Trigger:** Configurações ou comandos do Cursor copiam cegamente hooks de CLI do Claude.
- **Manifestation:** Todos os IDEs paralelos perdem compatibilidade e dão erro ao renderizar custom skills.
- **Detection:** Analisar arquivos `manifest.json` ou configs locais de `.gemini`/`.claude`.
- **Prevention:** Isolar implementações passivas (skills) de implementações ativas (commands/activators).

## Validation

**✓ Paradoxo Identificado:** Sincronização transversal vs. Isolamento por IDE (Cada IDE pressiona por customização nativa; sincronização exige compatibilidade universal)

**✓ Resolução Aplicada:** Hierarchy clara — Claude Code = authority (source-of-truth); Outros IDEs = skill-based consumers (async, compatible)

**✓ Enforcement:** Before pushing any command/agent update, verify via ide-sync validator:
```bash
node .aiox-core/infrastructure/scripts/ide-sync/index.js validate --strict
```

**✓ Mapped Tensions:** Connected heuristics (AN_KE_018, AN_KE_042) document complementary principles
