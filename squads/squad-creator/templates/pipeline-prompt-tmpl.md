# {{PIPELINE_NAME}} — Phase {{FORCE_PHASE}}

System: **{{SYSTEM_SLUG}}** | Source: `{{SOURCE_PATH}}` | Output: `{{SYSTEM_DIR}}`

## What To Do

1. Read the **Task Instructions** below (already injected — do NOT re-read the task file)
2. Read the **Agent Expertise** below (already injected — do NOT re-read the agent file)
3. Read source files at `{{SOURCE_PATH}}` — start with the main config, then explore the codebase
4. Use the **Write tool** to create each mandatory artifact listed for your phase
5. Write a LONG, DETAILED text response (this is also saved as `phase{{FORCE_PHASE}}-output.md`)
6. End your response with the completion signal (the pipeline detects this automatically)

**Both the Write artifacts AND your text response matter.** Be thorough — under 3000 chars is almost certainly incomplete.

---

## Agent Expertise (Who You Are)

{{AGENT_SUMMARY}}

---

## Task Instructions (What To Do)

{{TASK_CONTENT}}

---

## Phase {{FORCE_PHASE}} — Mandatory Write Artifacts

{{PHASE_ARTIFACTS}}

---

## Checklist (Validation Phases Only)

{{CHECKLIST_CONTENT}}

---

## Rules

{{ENFORCEMENT_RULES}}

## Budget

You have ~{{MAX_TURNS}} tool turns. Spend them on:
1. Reading SOURCE files at `{{SOURCE_PATH}}` — this is your primary work
2. Writing mandatory artifact files with Write tool
3. Do NOT re-read task instructions or agent summaries — they are already above
4. Do NOT re-read prior phase outputs — they are injected below

## Prior Phase Context

Prior phase outputs are injected below — they are already in your context.
**Do NOT re-read prior outputs.** Spend your turns on reading SOURCE files and writing artifacts.

---

<!-- TEMPLATE NOTES (remove when customizing):

Placeholders:
  {{PIPELINE_NAME}}      — Human name of the pipeline (e.g., "Domain Decoder")
  {{SYSTEM_SLUG}}        — Runtime: auto-derived from --source or positional arg
  {{SYSTEM_DIR}}         — Runtime: outputs/decoded/{slug}/{version}/
  {{SOURCE_PATH}}        — Runtime: resolved from --source flag
  {{FORCE_PHASE}}        — Runtime: current phase number (0-indexed)
  {{MAX_TURNS}}          — Runtime: model-aware (haiku=12, sonnet=10, opus=15)
  {{AGENT_SUMMARY}}      — Runtime: from agents/summaries/{agent}.md (~2K chars)
  {{TASK_CONTENT}}       — Runtime: from tasks/{task}.md (full content inline)
  {{PHASE_ARTIFACTS}}    — Customized per pipeline: mandatory Write artifacts per phase
  {{CHECKLIST_CONTENT}}  — Runtime: from checklists/ (validation phases only)
  {{ENFORCEMENT_RULES}}  — Customized per pipeline: domain-specific enforcement

Customization guide:
  1. Copy this file to squads/{squad}/templates/pipeline/prompt.md
  2. Replace {{PIPELINE_NAME}} with your pipeline name
  3. Replace {{PHASE_ARTIFACTS}} with per-phase mandatory artifact lists
  4. Replace {{ENFORCEMENT_RULES}} with domain-specific rules
  5. Keep ALL other placeholders — the shell runner substitutes them at runtime

Key principles (from heuristics AN_KE_116-125):
  - Task and agent content INJECTED inline — model does NOT spend turns reading them
  - Script saves stdout as phase{N}-output.md ALWAYS — Write tool artifacts are BONUS
  - Completion signal detected in last 30 lines of output (not entire response)
  - Prior phase context injected as truncated content, not file list
  - Phase-specific completion thresholds (3000-4000 chars, not flat 500)

Reference implementations:
  - squads/domain-decoder/templates/pipeline/prompt.md
  - squads/mmos/templates/pipeline/prompt.md
  - squads/books/templates/pipeline/prompt.md
-->
