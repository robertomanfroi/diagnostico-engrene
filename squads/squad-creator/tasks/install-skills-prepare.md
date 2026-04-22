# Task: Prepare Skill Surface Installation Environment

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `install-skills-prepare` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: install-skills-prepare
name: "Prepare Skill Surface Installation Environment"
category: squad-installation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Detectar IDEs instaladas no projeto, validar estrutura do squad,
  criar diretórios de destino por IDE e resolver conflitos de arquivos
  existentes antes da escrita. Consolida as fases de discovery e
  conflict resolution em um único átomo de preparação.
worker_script: "scripts/sync-ide-skills.py"
accountability:
  human: squad-operator
  scope: review_only
domain: Operational
```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::install_skills_prepare
Output: artifact::install_skills_prepare
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Preparar o ambiente de instalação antes que qualquer skill de ativação seja escrita.
Este átomo é responsável por toda a lógica de pré-execução: detectar quais IDEs estão
configuradas no projeto, validar que o squad-alvo possui a estrutura mínima necessária
(config.yaml, agents/), criar os diretórios de destino em cada IDE detectada, escanear
por conflitos de arquivos existentes e resolver a estratégia de overwrite.

A separação desta fase garante que o átomo de escrita (`install-skills-write`) receba
um plano de execução determinístico, sem ambiguidades sobre destinos ou conflitos.

**Worker Script:** `scripts/sync-ide-skills.py`

## Prerequisites

- [ ] Squad-alvo existe em `squads/{squad_name}/`
- [ ] Pelo menos uma IDE configurada ou fallback aceito pelo operador
- [ ] Permissão de escrita nos diretórios de IDE do projeto

## Inputs

```yaml
inputs:
  squad_name:
    type: string
    required: true
    description: >
      Nome do squad a ser instalado. Deve corresponder a um diretório
      existente em squads/{squad_name}/ com config.yaml e agents/.

  force:
    type: boolean
    required: false
    default: false
    description: >
      Se true, sobrescreve todos os arquivos existentes sem confirmação.
      Se false, detecta conflitos e solicita resolução interativa.

  ide:
    type: enum
    required: false
    values: [claude, cursor, windsurf, gemini, antigravity, codex]
    description: >
      Se fornecido, restringe a instalação a uma única IDE.
      Se omitido, detecta automaticamente todas as IDEs configuradas.
```

## Workflow

### Step 1: Detect Installed IDEs

Escanear o diretório raiz do projeto procurando por 5 diretórios de configuração
de IDE conhecidos. Cada diretório presente indica uma IDE ativa.

```yaml
ide_detection:
  scan_targets:
    - ide: claude_code
      config_dir: ".claude/"
      description: "Anthropic Claude Code"
    - ide: codex
      config_dir: ".codex/"
      description: "OpenAI Codex CLI"
    - ide: gemini
      config_dir: ".gemini/"
      description: "Google Gemini CLI"
    - ide: antigravity
      config_dir: ".antigravity/"
      description: "Antigravity AI"
    - ide: cursor
      config_dir: ".cursor/"
      description: "Cursor IDE"

  detection_method: "directory_exists_check"
  output: "detected_ides[] — lista de IDEs encontradas com paths confirmados"
```

**Lógica:** Para cada entrada em `scan_targets`, verificar se o diretório existe
na raiz do projeto. Se `--ide` foi fornecido explicitamente, ignorar a detecção
automática e usar somente a IDE especificada.

### Step 2: IDE Detection Fallback

Se nenhuma IDE for detectada no Step 1, oferecer opções ao operador em vez de
abortar silenciosamente.

```yaml
fallback_options:
  trigger: "detected_ides.length == 0 AND ide_param == null"
  prompt: "Nenhuma IDE detectada. Escolha uma opção:"
  options:
    - id: baseline
      label: "Instalar para Claude Code (baseline recomendado)"
      action: "set detected_ides = [claude_code]"
    - id: specific
      label: "Escolher uma IDE específica"
      action: "elicit ide_choice from supported list"
    - id: all
      label: "Instalar para todas as IDEs suportadas"
      action: "set detected_ides = ALL_SUPPORTED"
    - id: cancel
      label: "Cancelar instalação"
      action: "abort with exit_code 0"
```

**Regra:** Se `elicit: false` (modo autônomo), aplicar fallback `baseline`
automaticamente sem prompt.

### Step 3: Validate Squad Structure

Verificar que o squad-alvo possui a estrutura mínima exigida para instalação.

```yaml
squad_validation:
  checks:
    - id: V-SQ-001
      check: "squads/{squad_name}/config.yaml exists"
      severity: blocking
      on_fail: "HALT — squad inexistente ou corrompido"

    - id: V-SQ-002
      check: "squads/{squad_name}/agents/ directory exists"
      severity: blocking
      on_fail: "HALT — squad não possui agents publicáveis"

    - id: V-SQ-003
      check: "config.yaml parseable as valid YAML"
      severity: blocking
      on_fail: "HALT — config.yaml com sintaxe inválida"

    - id: V-SQ-004
      check: "config.yaml contains pack.name and pack.version"
      severity: warning
      on_fail: "WARN — metadata incompleta, prosseguir com defaults"

    - id: V-SQ-005
      check: "agents/ contains at least 1 .md file"
      severity: blocking
      on_fail: "HALT — nenhum agent publicável encontrado"

  parse_fields:
    - "pack.name → squad_display_name"
    - "pack.version → squad_version"
    - "activation.shortcuts[0] → slashPrefix (extract prefix)"
    - "agents[].id → publishable_agent_ids"
```

**Output:** `squad_metadata` com name, version, slashPrefix e lista de agents.

### Step 4: Create Per-IDE Directory Structures

Criar a árvore de diretórios de destino para cada IDE detectada.

```yaml
directory_creation:
  destination_map:
    claude_code: ".claude/skills/{slashPrefix}/{agent}/SKILL.md"
    codex: ".codex/skills/{slashPrefix}/"
    gemini: ".gemini/agents/{slashPrefix}/"
    antigravity: ".agents/workflows/{slashPrefix}/"
    cursor: ".cursor/rules/"

  action: "mkdir -p for each detected IDE using slashPrefix from squad_metadata"
  idempotent: true
  output: "directories_created[] — lista de diretórios criados ou já existentes"
```

**Guardrail:** Nunca criar diretórios para IDEs que não foram detectadas no Step 1
(exceto se selecionadas explicitamente via fallback).

### Step 5: Detect Existing Activation Files

Escanear os diretórios de destino por arquivos que já existem e que seriam
sobrescritos pela instalação.

```yaml
conflict_detection:
  for_each: "agent in publishable_agents"
  for_each_ide: "ide in detected_ides"
  check: "destination_path(agent, ide) already exists?"
  output:
    conflicts:
      - agent_id: "{agent-id}"
        ide: "{ide-name}"
        target_path: "{full path}"
        existing_size: "{bytes}"
        existing_modified: "{timestamp}"
```

### Step 6: Resolve Conflicts

Determinar a estratégia de escrita para cada conflito detectado.

```yaml
conflict_resolution:
  strategy_matrix:
    - condition: "no conflicts detected"
      resolution: "PROCEED — nenhum conflito"
    - condition: "force == true"
      resolution: "OVERWRITE_ALL — sobrescrever todos sem confirmação"
    - condition: "force == false AND conflicts.length > 0"
      resolution: "PROMPT_USER"
      options:
        - id: overwrite_all
          label: "Sobrescrever todos os existentes"
        - id: skip_existing
          label: "Pular existentes, instalar apenas novos"
        - id: cancel
          label: "Cancelar instalação"

  autonomous_fallback:
    when: "elicit == false AND force == false AND conflicts exist"
    action: "skip_existing — modo seguro, não sobrescreve sem --force"
```

## Output

```yaml
output:
  prepare_result:
    status: "READY | ABORTED"
    detected_ides:
      - ide: "claude_code"
        config_dir: ".claude/"
        target_dir: ".claude/skills/{slashPrefix}/"
    squad_metadata:
      name: "{pack.name}"
      version: "{pack.version}"
      slashPrefix: "{resolved prefix}"
      publishable_agents:
        - id: "{agent-id}"
          source: "squads/{squad_name}/agents/{agent-id}.md"
    directories_created:
      - ".claude/skills/{slashPrefix}/"
      - ".codex/skills/{slashPrefix}/"
    conflicts:
      - agent_id: "{agent-id}"
        ide: "{ide-name}"
        target_path: "{path}"
        resolution: "overwrite | skip | create"
    resolution_strategy: "OVERWRITE_ALL | SKIP_EXISTING | NO_CONFLICTS"
    agents_to_install:
      - id: "{agent-id}"
        per_ide:
          - ide: "claude_code"
            action: "create | overwrite | skip"
            target: "{target path}"
```

## Acceptance Criteria

- [ ] IDEs detectadas corretamente a partir dos diretórios do projeto
- [ ] Fallback oferecido quando nenhuma IDE detectada
- [ ] Squad validado com todas as checks V-SQ-001 a V-SQ-005
- [ ] Metadata do squad extraída (name, version, slashPrefix, agents)
- [ ] Diretórios de destino criados para cada IDE detectada
- [ ] Conflitos detectados e resolução determinada antes do output
- [ ] Output contém plano completo para a fase de escrita
- [ ] Modo autônomo (elicit: false) funciona sem interação humana

## Veto Conditions

- **VETO-INSTALL-001:** Sobrescrever arquivos existentes sem confirmação quando `force == false`
  - Trigger: tentativa de overwrite sem resolução explícita
  - Action: HALT, solicitar confirmação ou --force

- **VETO-INSTALL-002:** Validação de estrutura do squad falhou
  - Trigger: qualquer check blocking (V-SQ-001 a V-SQ-003, V-SQ-005) falhou
  - Action: HALT, reportar check específica que falhou

- **VETO-INSTALL-003:** IDE explícita inválida
  - Trigger: `--ide` fornecido com valor fora do enum suportado
  - Action: HALT, listar IDEs válidas

## Error Handling

```yaml
error_handling:
  squad_not_found:
    - log: "Squad '{squad_name}' não encontrado em squads/"
    - action: HALT
    - suggestion: "Verifique o nome do squad ou execute *create-squad primeiro"

  config_parse_error:
    - log: "Erro ao parsear config.yaml do squad"
    - action: HALT
    - suggestion: "Verifique a sintaxe YAML do config.yaml"

  directory_permission_error:
    - log: "Sem permissão para criar diretórios de IDE"
    - action: HALT
    - suggestion: "Verifique as permissões do diretório do projeto"

  resume:
    - re-run full task (stateless)
```

## Related Documents

- `install-skills.md` — Orchestrator (átomo principal)
- `install-skills-write.md` — Next phase (escrita de arquivos)
- `install-skills-finalize.md` — Final phase (validação e relatório)
- `workflows/wf-install-skills.yaml` — Worker wrapper
- `scripts/sync-ide-skills.py` — Worker script canônico

---

_Task Version: 1.0.0_
_Last Updated: 2026-03-27_
