# Task: Write IDE Skill Surface Files

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `install-skills-write` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: install-skills-write
name: "Write IDE Skill Surface Files"
category: squad-installation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Ler os agents do squad, converter para formatos específicos de cada IDE
  e escrever os arquivos de skill surface nos diretórios de destino. Gera também
  um README.md por IDE documentando as skills instaladas. Conflitos já
  foram resolvidos na fase prepare — esta fase executa o plano de escrita
  de forma determinística.
worker_script: "scripts/sync-ide-skills.py"
accountability:
  human: squad-operator
  scope: review_only
domain: Operational
```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::install_skills_write
Output: artifact::install_skills_write
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Executar a conversão e escrita dos arquivos de skill surface do squad nas superfícies de
IDE detectadas. Este átomo recebe o plano de execução determinístico da fase
`install-skills-prepare` e executa-o sem ambiguidades: lê os agents-fonte,
aplica as transformações específicas de cada IDE e escreve os arquivos nos
diretórios de destino já criados.

A separação da escrita garante que toda lógica de decisão (quais IDEs, quais agents,
qual estratégia de overwrite) já foi resolvida. Este átomo é pura execução — lê,
converte, escreve, registra.

**Worker Script:** `scripts/sync-ide-skills.py`

## Prerequisites

- [ ] `install-skills-prepare` concluído com `status: READY`
- [ ] Diretórios de destino criados (via prepare)
- [ ] Conflitos resolvidos com estratégia determinada
- [ ] Squad agents acessíveis em `squads/{squad_name}/agents/`

## Inputs

```yaml
inputs:
  - name: prepare_output
    type: object
    required: true
    source: install-skills-prepare
    description: >
      Output completo da fase de preparação contendo: detected_ides,
      squad_metadata (name, version, slashPrefix, publishable_agents),
      directories_created, conflicts com resoluções, resolution_strategy
      e agents_to_install com ações por IDE.

  - name: squad_name
    type: string
    required: true
    description: "Nome do squad (propagado do orchestrator)"

  - name: dry_run
    type: boolean
    required: false
    default: false
    description: >
      Se true, simula a escrita sem criar arquivos.
      Útil para validação prévia do plano de execução.

  - name: verbose
    type: boolean
    required: false
    default: false
    description: "Se true, emite log detalhado por arquivo processado."
```

## Workflow

### Step 1: Read Source Agent Files

Carregar e parsear cada arquivo de agent do squad para extração de metadata,
seções de conteúdo e princípios operacionais.

```yaml
read_agents:
  source_dir: "squads/{squad_name}/agents/"
  file_pattern: "*.md"
  parse_strategy:
    - extract_yaml_frontmatter: "Se presente, extrair metadata YAML"
    - extract_title: "Primeira linha H1 como título do agent"
    - extract_sections:
        - "Identity / Persona"
        - "Commands / Capabilities"
        - "Methodology / Principles"
        - "Quality Criteria"
        - "Handoffs / Synergies"
    - extract_activation: "Buscar padrão de ativação (slash command, @mention)"

  output:
    parsed_agents:
      - id: "{agent-id}"
        source_path: "squads/{squad_name}/agents/{agent-id}.md"
        title: "{extracted title}"
        sections: "{map of section_name → content}"
        metadata: "{frontmatter if present}"
        raw_content: "{full file content as fallback}"

  error_handling:
    unparseable_file:
      action: "WARN — usar raw_content como fallback"
      continue: true
    empty_file:
      action: "SKIP — registrar em failures"
      continue: true
```

### Step 2: Convert to IDE Format

Aplicar templates de conversão específicos para cada IDE-alvo. Cada IDE tem
requisitos distintos de formato, metadata e estrutura.

```yaml
ide_conversion_templates:
  claude_code:
    format: "Markdown (SKILL.md com frontmatter)"
    structure: |
      ---
      name: "{agent-id}"
      description: "{one-line desc}"
      ---

      # {agent_title}

      {full agent content — preservar todas as seções}
    notes: "Preservar conteúdo completo no formato canonical de slash skill."

  codex:
    format: "Markdown (.md) — SKILL.md simplified"
    structure: |
      # {agent_title}

      {condensed agent content — foco em instruções e capabilities}

      ## Commands
      {commands list}
    notes: >
      Condensar para formato skill. Remover seções de handoff/synergy
      que não se aplicam ao Codex. Manter instruções operacionais.

  gemini:
    format: "Markdown (.md) com YAML metadata block"
    structure: |
      ---
      name: "{agent-id}"
      squad: "{squad_name}"
      version: "{squad_version}"
      ---

      # {agent_title}

      {full agent content}
    notes: "YAML frontmatter obrigatório. Conteúdo completo preservado."

  antigravity:
    format: "Markdown (.md) com YAML metadata block"
    structure: |
      ---
      workflow: "{agent-id}"
      squad: "{squad_name}"
      version: "{squad_version}"
      ---

      # {agent_title}

      {full agent content}
    notes: "Similar ao Gemini. Usar 'workflow' como chave principal."

  cursor:
    format: "Markdown (.md) com referência .cursorrules"
    structure: |
      # {agent_title}

      > Cursor Rule: This agent is part of the {squad_name} squad.
      > Activate with: @{agent-id}

      {full agent content}

      ## .cursorrules Reference

      Add to your .cursorrules file:
      ```
      @{agent-id} — {one-line description}
      ```
    notes: "Incluir instrução de integração com .cursorrules."
```

**Regra de conversão:** Sempre preservar o conteúdo operacional do agent.
A conversão adapta formato e metadata, nunca remove funcionalidade.

### Step 3: Write Converted Commands

Para cada combinação agent x IDE, gerar o arquivo convertido e escrevê-lo
no diretório de destino.

```yaml
write_execution:
  for_each_agent: "agent in prepare_output.agents_to_install"
  for_each_ide: "ide_target in agent.per_ide"
  logic:
    - check: "ide_target.action"
      if_skip: "Registrar em skipped[], prosseguir"
      if_create_or_overwrite: "Aplicar template, escrever arquivo"

    - convert: "Apply ide_conversion_templates[ide] to agent"
    - target_path: "ide_target.target from prepare_output"

    - write_file:
        dry_run_check: "Se dry_run == true, registrar mas não escrever"
        actual_write: "Write converted content to target_path"
        on_success: "Registrar em files_written[]"
        on_failure: "Registrar em failures[], continue to next"

  cursor_special:
    note: >
      Para Cursor, o worker converte .md para .mdc quando aplicável.
      O script sync-ide-skills.py aplica esta transformação
      automaticamente para targets cursor.

  guardrails:
    - "Publicar APENAS agents/ — NUNCA tasks/, templates/, checklists/ ou workflows/"
    - "Manter slashPrefix consistente em todos os destinos"
    - "Não criar arquivos em IDEs não detectadas"
    - "Não escrever se dry_run == true"
```

### Step 4: Generate Per-IDE README

Criar um README.md em cada diretório de IDE documentando as skills instaladas,
ativação e versão do squad.

```yaml
readme_generation:
  for_each_ide: "ide in detected_ides"
  target: "{ide_target_dir}/README.md"
  template: |
    # {squad_display_name} — Skill Surfaces ({ide_name})

    **Squad:** {squad_name}
    **Version:** {squad_version}
    **Installed:** {timestamp}
    **Agent Count:** {agents_installed_count}

    ## Available Slash Skills

    | Agent | Activation | Description |
    |-------|---------|-------------|
    {for each agent: | {agent_title} | `/{slashPrefix}:{agent-id}` | {one-line desc} |}

    ## Activation

    Use the slash skill to activate any agent:
    ```
    /{slashPrefix}:{agent-id}
    ```

    ## Re-installation

    To update these skills:
    ```
    *install-skills {squad_name}
    ```

    ---
    _Generated by squad-creator install-skills pipeline_

  skip_if: "dry_run == true"
  output: "readmes_written[] — lista de READMEs gerados"
```

## Output

```yaml
output:
  write_result:
    status: "COMPLETE | PARTIAL | DRY_RUN"
    files_written:
      - agent_id: "{agent-id}"
        ide: "{ide-name}"
        target_path: "{path}"
        action: "created | overwritten"
        bytes: "{file size}"
    files_skipped:
      - agent_id: "{agent-id}"
        ide: "{ide-name}"
        target_path: "{path}"
        reason: "conflict_skip | dry_run"
    readmes_written:
      - ide: "{ide-name}"
        path: "{readme path}"
    failures:
      - agent_id: "{agent-id}"
        ide: "{ide-name}"
        error: "{error message}"
    summary:
      total_agents: "{count}"
      total_ides: "{count}"
      total_files_written: "{count}"
      total_files_skipped: "{count}"
      total_readmes: "{count}"
      total_failures: "{count}"
```

## Acceptance Criteria

- [ ] Todos os agents do squad lidos e parseados corretamente
- [ ] Conversão aplicada por IDE usando template específico
- [ ] Arquivos escritos nos diretórios corretos por IDE
- [ ] Arquivos com `action: skip` não foram escritos
- [ ] `dry_run == true` não criou nenhum arquivo no filesystem
- [ ] README.md gerado para cada IDE com lista de agents
- [ ] Failures registrados mas não bloqueantes (continue on error)
- [ ] Apenas agents/ publicados — nenhum task/template/checklist vazou
- [ ] Cursor targets convertidos para .mdc quando aplicável

## Veto Conditions

Nenhuma condição de veto nesta fase — todos os conflitos foram resolvidos em
`install-skills-prepare`. Se a preparação emitiu `status: READY`, esta fase
executa o plano sem decisões adicionais.

Exceção: se o filesystem torna-se inacessível durante a escrita (disk full,
permissions revoked), a fase registra failures e reporta `status: PARTIAL`.

## Error Handling

```yaml
error_handling:
  file_write_error:
    - log: "Falha ao escrever {target_path}: {error}"
    - action: "Registrar em failures[], continuar próximo agent/IDE"
    - note: "Um arquivo falhando não bloqueia os demais"

  agent_parse_error:
    - log: "Falha ao parsear {source_path}: {error}"
    - action: "WARN — tentar usar raw_content como fallback"
    - fallback_fail: "Registrar em failures[], skip agent"

  template_error:
    - log: "Template de conversão falhou para IDE {ide}: {error}"
    - action: "Registrar em failures[], skip IDE for this agent"

  dry_run_mode:
    - note: "Todos os passos executam exceto a escrita física"
    - output: "Mesmo formato, com action: 'dry_run' em todos os files"

  resume:
    - re-run full task (stateless — lê prepare_output novamente)
```

## Related Documents

- `install-skills.md` — Orchestrator (átomo principal)
- `install-skills-prepare.md` — Previous phase (detecção e resolução)
- `install-skills-finalize.md` — Next phase (validação e relatório)
- `workflows/wf-install-skills.yaml` — Worker wrapper
- `scripts/sync-ide-skills.py` — Worker script canônico

---

_Task Version: 1.0.0_
_Last Updated: 2026-03-27_
