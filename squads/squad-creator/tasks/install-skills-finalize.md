# Task: Finalize Skill Surface Installation and Generate Report

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `install-skills-finalize` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: install-skills-finalize
name: "Finalize Skill Surface Installation and Generate Report"
category: squad-installation
agent: squad-chief
elicit: false
autonomous: true
description: >
  Validar que a instalação foi bem-sucedida, verificar consistência
  cross-IDE, sincronizar o índice de skills e gerar o relatório final
  de instalação com before/after, comandos disponíveis e próximos passos.
worker_script: "scripts/sync-ide-skills.py"
accountability:
  human: squad-operator
  scope: review_only
domain: Operational
```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::install_skills_finalize
Output: artifact::install_skills_finalize
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Validar e finalizar o processo de instalação de skills de ativação. Este átomo executa após
a fase de escrita (`install-skills-write`) e é responsável por: verificar que
todos os arquivos esperados foram criados corretamente, validar consistência entre
as diferentes IDEs, garantir que o índice de skills está sincronizado para
discoverability, e produzir o relatório final de instalação.

O relatório final é o artefato principal desta fase — ele serve como confirmação
para o operador e como registro de auditoria da instalação. Sem este relatório,
a instalação não é considerada completa.

**Worker Script:** `scripts/sync-ide-skills.py`

## Prerequisites

- [ ] `install-skills-write` concluído com `status: COMPLETE | PARTIAL`
- [ ] `install-skills-prepare` output disponível (para referência cruzada)
- [ ] Arquivos de skill escritos nos diretórios de destino

## Inputs

```yaml
inputs:
  - name: write_output
    type: object
    required: true
    source: install-skills-write
    description: >
      Output completo da fase de escrita contendo: files_written,
      files_skipped, readmes_written, failures e summary com contagens.

  - name: prepare_output
    type: object
    required: true
    source: install-skills-prepare
    description: >
      Output da fase de preparação contendo: detected_ides,
      squad_metadata, directories_created, agents_to_install.
      Usado para referência cruzada na validação.

  - name: squad_name
    type: string
    required: true
    description: "Nome do squad (propagado do orchestrator)"

  - name: output_format
    type: enum
    required: false
    default: text
    values: [text, json]
    description: "Formato do relatório final: texto legível ou JSON estruturado."
```

## Workflow

### Step 1: Per-IDE Validation

Verificar que cada IDE recebeu os arquivos esperados e que os arquivos
estão válidos e completos.

```yaml
per_ide_validation:
  checks:
    - id: V-IDE-001
      name: "Agent Count Match"
      description: >
        Verificar que o número de agents instalados por IDE corresponde
        ao esperado. Considerar skips e failures na contagem.
      logic: |
        for each ide in detected_ides:
          expected = count(agents_to_install where action != 'skip')
          actual = count(files_written where ide == current_ide)
          failures = count(failures where ide == current_ide)
          assert actual + failures == expected
      severity: "ERROR se mismatch sem justificativa"

    - id: V-IDE-002
      name: "YAML Syntax Valid"
      description: >
        Para arquivos que contêm blocos YAML (frontmatter ou activation),
        verificar que a sintaxe YAML é válida e parseável.
      logic: |
        for each file in files_written:
          if file contains YAML block:
            parse YAML block
            assert no parse errors
      severity: "WARNING — arquivo funcional mas com YAML malformado"

    - id: V-IDE-003
      name: "No Leaked Artifacts"
      description: >
        Verificar que nenhum arquivo de task, template, checklist ou
        workflow do squad foi publicado nos diretórios de IDE.
        Somente agents devem estar presentes.
      logic: |
        for each ide_dir in directories_created:
          scan all files in ide_dir
          assert none match patterns:
            - "*task*", "*template*", "*checklist*"
            - "*workflow*", "*pipeline*"
            - "config.yaml", "*.yaml" (exceto README)
      severity: "CRITICAL — leak de artefatos internos"

  output:
    validation_results:
      - ide: "{ide-name}"
        checks:
          - id: "V-IDE-001"
            status: "PASS | FAIL | WARN"
            details: "{explanation if not PASS}"
```

### Step 2: Cross-IDE Consistency Check

Comparar as listas de agents entre IDEs para garantir que todas as IDEs
receberam o mesmo conjunto de agents (respeitando skips individuais).

```yaml
cross_ide_consistency:
  logic: |
    agent_sets = {}
    for each ide in detected_ides:
      agent_sets[ide] = set(files_written where ide == current_ide).agent_ids

    # Verificar que todas as IDEs têm o mesmo set de agents
    # (excluindo agents que falharam em IDEs específicas)
    base_set = agent_sets[first_ide]
    for each ide in remaining_ides:
      diff = symmetric_difference(base_set, agent_sets[ide])
      if diff not empty:
        check failures[] for justification
        if not justified: flag as inconsistency

  output:
    consistency:
      status: "CONSISTENT | INCONSISTENT"
      per_ide_agent_count:
        - ide: "claude_code"
          agents: ["agent-1", "agent-2", "agent-3"]
          count: 3
        - ide: "codex"
          agents: ["agent-1", "agent-2"]
          count: 2
      inconsistencies:
        - agent_id: "{agent-id}"
          present_in: ["claude_code"]
          missing_from: ["codex"]
          reason: "write failure — {error}"
```

### Step 3: Skill Resolution and Discoverability

Verificar que as skills instaladas são descobríveis através dos mecanismos
de ativação de cada IDE.

```yaml
skill_resolution:
  checks:
    - id: S-DISC-001
      name: "Claude Code Command Index"
      description: >
        Verificar que `.claude/skills/{slashPrefix}/{agent}/SKILL.md` está indexado
        e que a sintaxe de ativação `/{slashPrefix}:{agent-id}` funciona.
      ide: claude_code
      check: "Directory exists AND contains expected SKILL.md files"

    - id: S-DISC-002
      name: "Activation Syntax Correctness"
      description: >
        Verificar que o slashPrefix no conteúdo dos arquivos corresponde
        ao slashPrefix real do squad em config.yaml.
      check: |
        for each file in files_written:
          if file contains slashPrefix reference:
            assert slashPrefix == squad_metadata.slashPrefix

    - id: S-DISC-003
      name: "README Discoverability"
      description: >
        Verificar que cada IDE com agents instalados tem um README.md
        que lista todos os agents e suas formas de ativação.
      check: "README.md exists in each IDE target directory"

  output:
    discoverability:
      status: "DISCOVERABLE | PARTIAL | UNDISCOVERABLE"
      activation_commands:
        - command: "/{slashPrefix}:{agent-id}"
          ide: "claude_code"
          status: "available"
```

### Step 4: Generate Summary Report

Produzir o relatório final de instalação em formato humano-legível e/ou JSON.

```yaml
report_generation:
  sections:
    - section: "Installation Summary"
      content: |
        Squad: {squad_name} v{squad_version}
        Status: {PASS | FAIL | PARTIAL}
        Date: {timestamp}
        IDEs: {detected_ides count} detected, {ides_with_installs count} installed

    - section: "Cross-IDE Table"
      format: "markdown table"
      content: |
        | IDE | Agents Installed | Skipped | Failures | Status |
        |-----|-----------------|---------|----------|--------|
        | {ide} | {count} | {count} | {count} | {PASS/PARTIAL/FAIL} |

    - section: "Before/After Diff"
      content: |
        ### Before Installation
        - Files in IDE dirs: {before_count}

        ### After Installation
        - Files in IDE dirs: {after_count}
        - New files: {created_count}
        - Overwritten: {overwritten_count}
        - Skipped: {skipped_count}

    - section: "Available Slash Skills"
      content: |
        ### Activation Skills
        {for each agent:}
        - `/{slashPrefix}:{agent-id}` — {agent title}

        ### Squad Commands
        - `*help` — Show available commands
        - `*install-skills {squad_name}` — Re-install squad skills

    - section: "Next Steps"
      content: |
        1. Test activation: `/{slashPrefix}:{entry_agent}`
        2. View help: `*help`
        3. Check README in each IDE directory

    - section: "Warnings"
      content: |
        {if failures: list each failure with agent, IDE, error}
        {if inconsistencies: list cross-IDE inconsistencies}
        {if leaked artifacts: CRITICAL — list leaked files}

  output_formats:
    text:
      target: "stdout (human-readable)"
      template: "Sections rendered as markdown with headers"
    json:
      target: "stdout (structured JSON)"
      template: |
        {
          "status": "PASS|FAIL|PARTIAL",
          "squad": "{squad_name}",
          "version": "{squad_version}",
          "per_ide": [...],
          "validation": {...},
          "activation_skills": [...],
          "warnings": [...]
        }
```

## Output

```yaml
output:
  finalize_result:
    status: "PASS | FAIL | PARTIAL"
    verification:
      per_ide_validation:
        - ide: "{ide-name}"
          v_ide_001: "PASS | FAIL"
          v_ide_002: "PASS | WARN"
          v_ide_003: "PASS | CRITICAL"
      cross_ide_consistency: "CONSISTENT | INCONSISTENT"
      discoverability: "DISCOVERABLE | PARTIAL"
    report:
      format: "text | json"
      content: "{rendered report}"
    summary:
      squad: "{squad_name}"
      version: "{squad_version}"
      slashPrefix: "{prefix}"
      ides_installed: "{count}"
      total_agents_installed: "{count}"
      total_files_created: "{count}"
      total_files_skipped: "{count}"
      total_failures: "{count}"
      leaked_artifacts: []
      warnings: []
    installation_report:
      status: "PASS | FAIL | PARTIAL"
      squad: "{squad_name}"
      squad_alias: "{slashPrefix}"
      target_ides:
        - "{ide-name}"
      per_ide:
        - ide: "{ide-name}"
          created: "{count}"
          skipped: "{count}"
          errors: "{count}"
      leaked_artifacts: []
      next_steps:
        - "/{slashPrefix}:{entry_agent}"
        - "*help"
```

## Acceptance Criteria

- [ ] Per-IDE validation executada com checks V-IDE-001 a V-IDE-003
- [ ] Cross-IDE consistency check identifica inconsistências entre IDEs
- [ ] Skill resolution verifica discoverability das slash skills
- [ ] Relatório final contém: resumo, cross-IDE table, before/after, slash skills, next steps
- [ ] Formato text renderizado como markdown legível
- [ ] Formato JSON renderizado como estrutura parseável
- [ ] Leaked artifacts detectados e reportados como CRITICAL
- [ ] Warnings e failures listados explicitamente no relatório
- [ ] `installation_report` no formato esperado pelo orchestrator

## Veto Conditions

- **VETO-FINAL-001:** Leaked artifacts detectados (V-IDE-003 CRITICAL)
  - Trigger: arquivos de task/template/checklist encontrados em diretórios de IDE
  - Action: STATUS = FAIL, relatório inclui lista de arquivos vazados
  - Remediation: "Remova os arquivos vazados e re-execute *install-skills"

- **VETO-FINAL-002:** Zero agents instalados em todas as IDEs
  - Trigger: total_files_created == 0 AND total_files_skipped == 0
  - Action: STATUS = FAIL, relatório indica instalação vazia
  - Remediation: "Verifique o output de install-skills-write"

- **VETO-FINAL-003:** Validação per-IDE falhou em todas as IDEs
  - Trigger: todas as IDEs com V-IDE-001 FAIL
  - Action: STATUS = FAIL, relatório detalha falhas por IDE

## Error Handling

```yaml
error_handling:
  validation_error:
    - log: "Erro durante validação per-IDE: {error}"
    - action: "Registrar check como FAIL, continuar validação"
    - note: "Validação parcial é melhor que nenhuma validação"

  report_generation_error:
    - log: "Erro ao gerar relatório: {error}"
    - action: "Fallback para relatório mínimo (status + counts)"
    - note: "Sempre emitir pelo menos o status da instalação"

  file_access_error:
    - log: "Erro ao acessar {path} durante validação: {error}"
    - action: "Registrar como WARN, continuar com arquivos acessíveis"

  resume:
    - re-run full task (stateless — lê write_output e prepare_output)
```

## Related Documents

- `install-skills.md` — Orchestrator (átomo principal)
- `install-skills-prepare.md` — First phase (detecção e resolução)
- `install-skills-write.md` — Previous phase (escrita de arquivos)
- `workflows/wf-install-skills.yaml` — Worker wrapper
- `scripts/sync-ide-skills.py` — Worker script canônico

---

_Task Version: 1.0.0_
_Last Updated: 2026-03-27_
