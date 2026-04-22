# Task: Sync IDE Skills

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `sync-ide-skills` |
| **Version** | `3.1.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: sync-ide-skills
name: "Sync IDE Skills"
category: utility
agent: squad-chief
elicit: false
autonomous: true
description: "Atom único para sincronizar components do squad com as superfícies de IDE usando o worker determinístico de sync."
worker_script: "scripts/sync-ide-skills.py"
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::sync_ide_skills
Output: artifact::sync_ide_skills
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Sincronizar agents individuais ou squads inteiros para IDEs suportadas,
tratando parsing, resolução de aliases, descoberta de destinos, execução e
verificação como passos internos do mesmo Atom. O critério de término é binário:
os arquivos de destino esperados existem e o relatório final foi emitido.

## Inputs

```yaml
inputs:
  type:
    type: enum
    required: true
    values: [agent, squad]
  name:
    type: string
    required: true
  squad:
    type: string
    required: false
  ide:
    type: enum
    required: false
    values: [claude, cursor, windsurf, gemini, antigravity, codex]
  dry_run:
    type: boolean
    required: false
    default: false
  force:
    type: boolean
    required: false
    default: false
  verbose:
    type: boolean
    required: false
    default: false
  output:
    type: enum
    required: false
    default: text
    values: [text, json]
```

## Workflow / Steps

### Step 1: Parse & Normalize Request

- Validar `type` contra `agent|squad`
- Normalizar flags (`dry_run`, `force`, `ide`, `verbose`, `output`)
- Resolver `name` e `squad` quando o componente exigir contexto de squad
- Serializar o pedido de sync em um payload único

```yaml
normalized_request:
  type: "agent | squad"
  name: "{component_name}"
  squad: "{resolved_squad_or_null}"
  active_ides: ["claude", "cursor"]
  dry_run: true | false
  force: true | false
```

Blocking checks:
- tipo inválido
- `name` vazio
- `agent` sem `squad` resolvível
- IDE pedida explicitamente, mas não suportada

### Step 2: Load Effective Sync Configuration

- Ler `.aiox-sync.yaml` quando existir
- Fazer fallback para `config.yaml` do squad quando necessário
- Resolver `slashPrefix`/alias efetivo
- Resolver IDEs ativas e comportamento de log
- Congelar a configuração efetiva antes de tocar filesystem

```yaml
sync_config:
  squad_alias: "{slashPrefix}"
  active_ides: ["claude", "cursor", "codex"]
  destination_map:
    claude: ".claude/skills/{squad_alias}/{agent}/SKILL.md"
    codex: ".codex/skills/{squad_alias}/"
```

### Step 3: Resolve Source, Targets & Conflicts

- Localizar arquivos-fonte reais
- Calcular destinos por IDE
- Detectar sobrescritas
- Aplicar política de `--force`
- Produzir um plano explícito de sync antes da execução

Rules:
- `agent` sincroniza um arquivo de `agents/`
- `squad` sincroniza todos os agents publicáveis do squad
- tasks, workflows, checklists e templates permanecem dentro de `squads/`

```yaml
sync_plan:
  sources:
    - "squads/{squad}/agents/{agent_id}.md"
  targets:
    - ide: "claude"
      path: ".claude/skills/{squad_alias}/{agent_id}/SKILL.md"
      exists: true | false
      overwrite_required: true | false
```

### Step 4: Execute Canonical Worker

```bash
python3 squads/squad-creator/scripts/sync-ide-skills.py {type} {name} [flags...]
```

Execution guarantees:
- `dry_run` não escreve
- `force` permite overwrite
- o worker é a fonte única de transformação por IDE
- não existe lógica paralela de cópia fora do worker

### Step 5: Verify Outputs & Emit Final Report

- Confirmar que os arquivos esperados existem
- Validar que cada IDE recebeu o artefato correto
- Consolidar status por IDE
- Emitir `sync_report`

Verification checks:
- arquivo esperado foi criado/atualizado
- destination root bate com alias do squad
- `dry_run=true` não criou arquivos
- falhas por IDE ficaram explícitas

## Output

```yaml
sync_report:
  status: "PASS | FAIL"
  request:
    type: "agent | squad"
    name: "{name}"
    squad: "{squad}"
  synced_files:
    - path: ".claude/skills/{slashPrefix}/{agent_id}/SKILL.md"
      ide: "claude"
      status: "created | updated | skipped"
  conflicts:
    - path: "..."
      resolution: "overwrite | skipped | blocked"
  failures:
    - ide: "cursor"
      reason: "destination missing"
  dry_run: true | false
```

## Acceptance Criteria

- [ ] Pedido validado e normalizado
- [ ] Alias e destinos resolvidos
- [ ] Worker canônico executado
- [ ] Arquivos esperados verificados
- [ ] `sync_report` emitido

## Veto Conditions

- Tipo inválido
- Fonte não encontrada
- Conflito sem `--force`
- Falha do worker script
- Arquivos de saída ausentes após execução

## Commands

```yaml
commands:
  squad: "*sync squad {squad_name}"
  agent: "*sync agent {agent_name}"
  dry_run: "*sync squad {squad_name} --dry-run"
```

## Examples

```bash
*sync squad copy
*sync squad copy --dry-run
*sync agent copy-chief --squad copy
```

## Related Documents

- `workflows/wf-sync-ide-skills.yaml`
- `scripts/sync-ide-skills.py`
- `install-skills.md`

---

_Task Version: 3.1.0_
