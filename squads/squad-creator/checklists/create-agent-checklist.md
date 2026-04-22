# Create Agent Checklist

```yaml
checklist:
  id: create-agent-checklist
  version: 1.0.0
  created: 2026-02-10
  purpose: "Validate agent creation process completeness"
  mode: blocking
  task_reference: tasks/create-agent.md
```

---

## Pre-Creation Requirements

```yaml
pre_creation:
  - id: research-complete
    check: "Research phase completed before agent creation"
    type: blocking
    validation: "mind_research.md or equivalent exists"

  - id: mind-identified
    check: "Target mind/expert identified with verifiable work"
    type: blocking
    validation: "mind_name is real person with documented methodologies"

  - id: sources-collected
    check: "Minimum 5 sources collected and classified"
    type: blocking
    validation: "sources_inventory.yaml exists with >= 5 sources"
```

---

## Phase 0: Context Validation

```yaml
context_checks:
  - id: squad-exists
    check: "Target squad exists at squads/{squad_name}/"
    type: blocking
    validation: "ls squads/{squad_name}/ succeeds"

  - id: tier-classification
    check: "Agent tier (0, 1, 2, 3) determined based on role"
    type: blocking
    validation: "tier in [0, 1, 2, 3]"

  - id: no-duplicate
    check: "Agent with same id doesn't already exist"
    type: blocking
    validation: "squads/{squad_name}/agents/{agent_id}.md doesn't exist"
```

---

## Phase 1: DNA Extraction

```yaml
dna_extraction:
  - id: voice-dna-complete
    check: "Voice DNA extracted with 10+ power words"
    type: blocking
    validation: "voice_dna.yaml contains >= 10 power_words"

  - id: thinking-dna-complete
    check: "Thinking DNA extracted with primary framework"
    type: blocking
    validation: "thinking_dna.yaml contains primary_framework with 3+ steps"

  - id: citations-present
    check: "DNA includes citations [SOURCE: page/minute]"
    type: recommended
    validation: "grep '[SOURCE:' returns >= 15 matches"

  - id: signature-phrases
    check: "5+ signature phrases documented"
    type: blocking
    validation: "signature_phrases count >= 5"
```

---

## Phase 2: Agent Structure

```yaml
structure_checks:
  - id: min-lines
    check: "Agent file has 300+ lines"
    type: blocking
    validation: "wc -l {file} >= 300"

  - id: all-levels-present
    check: "All 6 levels present (Identity, Operational, Voice, Quality, Credibility, Integration)"
    type: blocking
    validation: "grep for all level headers"

  - id: persona-complete
    check: "Persona has role, style, identity, focus"
    type: blocking
    sections: ["role", "style", "identity", "focus"]

  - id: core-principles
    check: "5-9 core principles defined"
    type: blocking
    min: 5
    max: 9

  - id: commands-defined
    check: "Commands section with *help and *exit"
    type: blocking
    required: ["*help", "*exit"]
```

---

## Phase 3: Quality Assurance

```yaml
quality_checks:
  - id: output-examples
    check: "3+ complete output examples"
    type: blocking
    min: 3
    fields: ["task", "input", "output"]

  - id: anti-patterns
    check: "5+ never_do anti-patterns documented"
    type: blocking
    min: 5

  - id: handoff-defined
    check: "Handoff triggers and targets defined"
    type: blocking
    validation: "handoff_to has >= 1 entry"

  - id: objection-algorithms
    check: "3+ objection responses documented"
    type: recommended
    min: 3
```

---

## Phase 4: Smoke Test

```yaml
smoke_test:
  - id: domain-knowledge
    check: "Agent demonstrates domain expertise when asked"
    type: blocking
    prompt: "Explain your primary framework"
    validates: ["Uses power_words", "Uses signature_phrases"]

  - id: decision-making
    check: "Agent applies documented heuristics"
    type: blocking
    prompt: "How would you approach [domain scenario]?"
    validates: ["Applies framework", "Shows conviction"]

  - id: objection-handling
    check: "Agent responds to challenges appropriately"
    type: blocking
    prompt: "I disagree with your approach because..."
    validates: ["Recognizes objection", "Maintains position"]
```

---

## Phase 5: CC-Compatible Schema Validation

```yaml
cc_schema_checks:
  - id: cc-tools-defined
    check: "Agent defines tools array (allowlist) or explicitly inherits from squad default"
    type: recommended
    validation: "YAML frontmatter has 'tools:' field OR config.yaml defines squad default tools"
    examples:
      - "tools: [Read, Edit, Write, Grep, Glob, Bash]"
      - "tools: [Agent, TaskStop, SendMessage, SyntheticOutput, Read, Grep]"
    notes: "Workers typically restrict to file tools. Leaders need Agent/SendMessage."

  - id: cc-disallowed-tools
    check: "Agent defines disallowedTools if role has operations that MUST be blocked"
    type: recommended
    validation: "If agent is a worker: disallowedTools includes Agent, TaskStop, AskUserQuestion"
    examples:
      - "disallowedTools: [TaskOutput, ExitPlanMode, EnterPlanMode, AskUserQuestion]"
    notes: "BR-AGENT-005: Workers must not have TeamCreate or AskUserQuestion."

  - id: cc-permission-mode
    check: "Agent specifies permissionMode (default | plan | bypassPermissions)"
    type: blocking
    validation: "permissionMode is one of: default, plan, bypassPermissions, acceptEdits, dontAsk"
    default: "default"
    notes: "Workers in headless pipeline MUST be 'default' or 'bypassPermissions'. 'plan' for review agents."

  - id: cc-max-turns
    check: "Agent sets maxTurns if task is time-bounded (prevents infinite loops)"
    type: recommended
    validation: "Integer > 0. Workers: 50-100. Leaders: 100-200. Unbounded tasks: omit."
    examples:
      - "maxTurns: 50   # worker, single-phase task"
      - "maxTurns: 200  # leader, multi-phase coordination"

  - id: cc-hooks-valid
    check: "Agent hooks field references valid lifecycle events if automation is needed"
    type: recommended
    validation: "Hook events must be from the 27-event catalog (17 CC-native + 10 AIOX-specific)"
    valid_events: [PreToolUse, PostToolUse, Stop, SessionStart, UserPromptSubmit, PreCompact,
                   SubagentStart, SubagentStop, TeammateIdle, TaskCompleted, Notification,
                   PermissionRequest, PostToolUseFailure, ConfigChange, WorktreeCreate,
                   WorktreeRemove, SessionEnd, PreSquadActivation, PostSquadActivation,
                   PreTaskExecution, PostTaskExecution, PreHandoff, PostHandoff,
                   PreCommit, PostCommit, PipelineStart, PipelineEnd]

  - id: cc-flat-roster
    check: "Worker agents do NOT attempt to spawn sub-agents (BR-AGENT-041)"
    type: blocking
    validation: "If role=worker: Agent tool NOT in tools array. 'swarm.role: worker' confirmed."
    notes: "BR-AGENT-041: Teammates cannot spawn teammates. Flat roster. No hierarchy in swarm."
```

---

## Scoring

| Score | Result | Action |
|-------|--------|--------|
| 100% Blocking | PASS | Proceed with integration |
| 80%+ Blocking | CONDITIONAL | Document gaps, proceed |
| <80% Blocking | FAIL | Fix issues, re-run checklist |

---

**Created:** 2026-02-10
**Task Reference:** tasks/create-agent.md
