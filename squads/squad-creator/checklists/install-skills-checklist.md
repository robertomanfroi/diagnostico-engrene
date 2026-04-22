# Install Skills Checklist

```yaml
checklist:
  id: install-skills-checklist
  version: 1.0.0
  created: 2026-03-26
  purpose: "Validate slash skill installation and IDE sync for squad activation"
  mode: blocking
  task_reference: tasks/install-skills.md
```

---

## Pre-Installation Requirements

```yaml
pre_install:
  - id: squad-validated
    check: "Target squad passes squad-checklist.md validation"
    type: blocking
    validation: "Squad has PASS or CONDITIONAL PASS from squad-checklist.md"

  - id: config-has-entry-agent
    check: "Squad config.yaml declares entry_agent"
    type: blocking
    validation: "config.yaml contains entry_agent field pointing to existing agent"

  - id: config-has-slash-prefix
    check: "Squad config.yaml declares slashPrefix in camelCase"
    type: blocking
    pattern: "^[a-z]+([A-Z][a-z]+)*$"

  - id: agents-have-commands
    check: "All agents to be installed have a commands section"
    type: blocking
    validation: "Each agent .md file contains commands: or ## Commands section"
```

---

## IDE Detection

```yaml
ide_checks:
  - id: ide-detected
    check: "Target IDE is identified (Claude Code, Cursor, Windsurf, etc.)"
    type: blocking
    supported_ides: ["claude-code", "cursor", "windsurf"]

  - id: ide-command-path-exists
    check: "IDE command directory exists or can be created"
    type: blocking
    paths:
      claude-code: ".claude/skills/{prefix}-{agent}/"
      cursor: ".cursor/commands/{squad-name}/"
      windsurf: ".windsurf/commands/{squad-name}/"

  - id: ide-skill-path-exists
    check: "IDE skill directory exists or can be created"
    type: recommended
    paths:
      claude-code: ".claude/skills/{prefix}-{agent}/"
```

---

## Conflict Detection

```yaml
conflict_checks:
  - id: no-command-name-collision
    check: "No existing command files will be overwritten without confirmation"
    type: blocking
    validation: "For each agent, .claude/skills/{prefix}-{agent}/SKILL.md does not exist OR user confirms overwrite"

  - id: no-slash-prefix-collision
    check: "Squad slashPrefix does not collide with existing squads"
    type: blocking
    validation: "No other squad in .claude/skills/ uses same prefix"

  - id: no-skill-collision
    check: "No existing skill will be overwritten without confirmation"
    type: recommended
    validation: "For each skill, .claude/skills/{prefix}-{skill}/SKILL.md does not exist OR user confirms"
```

---

## Skill Surface Generation

```yaml
command_file_checks:
  - id: chief-command-written
    check: "Entry agent (chief) slash skill written to IDE activation directory"
    type: blocking
    validation: ".claude/skills/{prefix}-{agent}/{entry-agent}/SKILL.md exists"

  - id: all-agents-written
    check: "All squad agents have corresponding slash skills"
    type: recommended
    validation: "For each agent in agents/, a skill file exists in .claude/skills/{prefix}-{agent}/{agent}/SKILL.md"

  - id: command-format-valid
    check: "Command files follow IDE-specific format requirements"
    type: blocking
    validation: |
      Claude Code: Markdown file with activation instructions
      Cursor: .md file with cursor-compatible format
      Windsurf: .md file with windsurf-compatible format

  - id: command-references-agent
    check: "Each command file correctly references the source agent definition"
    type: blocking
    validation: "Command file contains path to squads/{squad}/agents/{agent}.md"
```

---

## Skill Sync

```yaml
skill_checks:
  - id: skills-index-updated
    check: "Skills index file reflects newly installed commands"
    type: recommended
    validation: ".claude/skills/ index includes new squad entries"

  - id: skill-activation-works
    check: "Skill can be activated via /{squad-name}:{agent-name} syntax"
    type: blocking
    validation: "Invoking /{squad-name}:{entry-agent} loads the agent correctly"

  - id: codex-skill-synced
    check: "Codex skill file created if .codex/ directory exists"
    type: recommended
    validation: ".codex/skills/{entry-agent}/SKILL.md exists (if .codex/ present)"
```

---

## Verification

```yaml
verification_checks:
  - id: activation-test
    check: "Entry agent activates without errors via slash skill"
    type: blocking
    validation: "/{squad-name}:{entry-agent} loads persona, commands, and dependencies"

  - id: help-command-works
    check: "*help command returns valid output listing available commands"
    type: blocking
    validation: "*help after activation returns formatted command list"

  - id: dependencies-resolve
    check: "All agent dependencies resolve to existing files from IDE root"
    type: blocking
    validation: "Every path in dependencies[] resolves from project root"

  - id: data-files-accessible
    check: "Referenced data files are accessible from command context"
    type: recommended
    validation: "Data files in data/ can be read by the activated agent"
```

---

## Report Generation

```yaml
report_checks:
  - id: install-report-generated
    check: "Installation report summarizes what was installed and any issues"
    type: recommended
    fields: ["squad_name", "agents_installed", "commands_created", "conflicts_found", "verification_status"]

  - id: report-includes-activation
    check: "Report includes activation instructions for the user"
    type: recommended
    validation: "Report contains example slash skill activation"
```

---

## Scoring

| Score | Result | Action |
|-------|--------|--------|
| 100% Blocking | PASS | Skill surfaces installed and verified |
| 90%+ Blocking | CONDITIONAL | Usable with minor gaps documented |
| <90% Blocking | FAIL | Fix installation issues before use |

---

**Created:** 2026-03-26
**Task Reference:** tasks/install-skills.md
