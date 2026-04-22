# Task: Install Skills

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `install-skills` |
| **Version** | `3.1.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: install-skills
name: "Install Squad Skills"
category: squad-installation
agent: squad-chief
elicit: false
autonomous: true
description: "Atom único para instalar as skills publicáveis de um squad nas IDEs suportadas usando o worker canônico de sync."
worker_script: "scripts/sync-ide-skills.py"
accountability:
  human: squad-operator
  scope: review_only
domain: Operational
```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::install_skills
Output: artifact::install_skills
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Instalar os agents publicáveis de um squad nas superfícies de IDE suportadas.
Validação do squad, resolução de aliases, cálculo de destinos, overwrite policy,
execução do worker, verificação e relatório final são tratados como passos
internos do mesmo Atom porque compartilham o mesmo executor real, o mesmo
worker determinístico e o mesmo critério de término operacional.

**Worker Script:** `scripts/sync-ide-skills.py`

## PRO DETECTION

> At execution time, check if `squads/squad-creator-pro/config.yaml` exists.
> If YES and `pro_mode=true`, pro enhancements are surfaced within the internal
> steps of this Atom.
> If NO, continue with this base version.

## Inputs

```yaml
inputs:
  squad_name:
    type: string
    required: true
  force:
    type: boolean
    required: false
    default: false
  dry_run:
    type: boolean
    required: false
    default: false
  ide:
    type: enum
    required: false
    values: [claude, cursor, windsurf, gemini, antigravity, codex]
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

## Internal Steps

### Step 1: Resolve Request, Squad and Effective IDE Set

- Validar `squads/{squad_name}/config.yaml`
- Confirmar que o squad tem diretório `agents/`
- Carregar `.aiox-sync.yaml` quando existir
- Resolver `slashPrefix`/alias efetivo do squad
- Resolver IDEs-alvo a partir de `--ide` explícito ou `active_ides`

```yaml
effective_request:
  squad: "{squad_name}"
  squad_alias: "{slashPrefix}"
  ide_source: "explicit --ide | .aiox-sync.yaml | DEFAULT_CONFIG"
  target_ides:
    - claude
    - codex
  publishable_components:
    type: agent
    count: 5
```

Supported IDE surfaces:

```yaml
destination_map:
  claude: ".claude/skills/{prefix}-{agent}/SKILL.md"  # depth-2 flat naming (scanner constraint)
  cursor: ".cursor/rules/"
  windsurf: ".windsurf/commands/{slashPrefix}/"
  gemini: ".gemini/agents/{slashPrefix}/"
  antigravity: ".agents/workflows/{slashPrefix}/"
  codex: ".codex/skills/{slashPrefix}/"
```

Blocking checks:
- squad inexistente
- `config.yaml` ausente
- `agents/` ausente
- nenhum agent publicável encontrado
- IDE explícita inválida

### Step 2: Resolve Targets and Overwrite Policy

- Calcular o destino de cada agent em cada IDE-alvo
- Verificar se o arquivo de destino já existe
- Congelar a política de escrita antes da execução
- Preparar um `sync_plan` explícito

Overwrite policy:
- destino inexistente: criar
- destino existente + `force=false`: marcar como `skipped`
- destino existente + `force=true`: sobrescrever

Guardrails:
- publicar apenas `agents/`
- não publicar `tasks/`, `templates/`, `checklists/` ou `workflows/`
- manter o alias do squad consistente em todos os destinos

```yaml
sync_plan:
  agents:
    - id: copy-chief
      source: "squads/copy/agents/copy-chief.md"
      targets:
        - ide: claude
          path: ".claude/skills/copy/copy-chief/SKILL.md"
          exists: true
          resolution: "overwrite | skipped"
        - ide: codex
          path: ".codex/skills/Copy/copy-chief.md"
          exists: false
          resolution: "create"
```

### Step 3: Execute Canonical Worker

```bash
python3 squads/squad-creator/scripts/sync-ide-skills.py squad {squad_name} [flags...]
```

Execution guarantees:
- `dry_run` não escreve arquivos
- `force` controla overwrite
- `ide` restringe o target set a uma IDE específica
- o worker é a fonte única de transformação por IDE
- `cursor` converte `.md` para `.mdc`
- `squad` publica somente os agents do squad

### Step 4: Verify Outputs and Emit Installation Report

- Confirmar coverage de agents esperados por IDE
- Verificar paths de destino e alias do squad
- Confirmar que `dry_run=true` não criou arquivos
- Confirmar ausência de vazamento de artefatos internos
- Emitir `installation_report`

Verification checks:
- quantidade de agents instalada por IDE
- paths de destino corretos
- nenhum diretório indevido foi publicado
- falhas e `skips` ficaram explícitos
  - output final contém before/after e próximos passos

## Output

```yaml
installation_report:
  status: "PASS | FAIL | PARTIAL"
  squad: "{squad_name}"
  squad_alias: "{slashPrefix}"
  target_ides:
    - claude
    - codex
  per_ide:
    - ide: claude
      created: 5
      skipped: 0
      errors: 0
    - ide: codex
      created: 4
      skipped: 1
      errors: 0
  leaked_artifacts: []
  next_steps:
    - "/{slashPrefix}:{entry_agent}"
    - "*help"
```

Human-readable report must include:
- resumo por IDE
- before/after agregado
- arquivos criados, sobrescritos e pulados
- warnings e failures
- próximos comandos de ativação

## Veto Conditions

- Estrutura do squad inválida
- Nenhum agent publicável encontrado
- Worker falhou
- Arquivos esperados ausentes após execução
- Leak de artefatos fora do skill surface

## Error Handling

```yaml
error_handling:
  execution_failure:
    - log failure context
    - halt install
    - report to human
  resume:
    - re-run full task (stateless worker flow)
```

## Acceptance Criteria

- [ ] Squad validado antes da instalação
- [ ] Targets e alias resolvidos antes da escrita
- [ ] Worker canônico executado
- [ ] Agents esperados publicados nas IDEs-alvo
- [ ] `installation_report` emitido com before/after e próximos passos
- [ ] Nenhum artefato fora do skill surface foi publicado indevidamente

## Worker Script Interface

```bash
python3 squads/squad-creator/scripts/sync-ide-skills.py squad {name}
python3 squads/squad-creator/scripts/sync-ide-skills.py squad {name} --ide codex
python3 squads/squad-creator/scripts/sync-ide-skills.py squad {name} --dry-run
python3 squads/squad-creator/scripts/sync-ide-skills.py squad {name} --force
python3 squads/squad-creator/scripts/sync-ide-skills.py squad {name} --output json
python3 squads/squad-creator/scripts/sync-ide-skills.py squad {name} --verbose
```

## Related

| Command | Purpose |
|---------|---------|
| `*install-skills {name}` | Install squad skills to IDEs |
| `*create-squad {name}` | Create a new squad |
| `*validate-squad {name}` | Validate squad before installation |
| `*sync squad {name}` | Publish squad skills directly |

| Reference | File |
|-----------|------|
| Worker Wrapper | `workflows/wf-install-skills.yaml` |
| Worker Script | `scripts/sync-ide-skills.py` |
| Sync Atom | `tasks/sync-ide-skills.md` |

---

_Task Version: 3.1.0_
_Last Updated: 2026-03-27_
