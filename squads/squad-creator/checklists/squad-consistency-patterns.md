# Squad Consistency Patterns Checklist

```yaml
checklist:
  id: squad-consistency-patterns
  version: 1.0.0
  created: 2026-03-23
  purpose: "Validate that a squad has the 5 consistency patterns for reliable output quality"
  mode: recommended
  note: "These patterns are recommended, not blocking. Squads function without them, but output consistency improves significantly when implemented."
```

---

## Consistency Checks

```yaml
consistency_checks:
  - id: vocabulary-mappings
    check: "Domain vocabulary mappings file exists"
    type: recommended
    validation: "data/{squad}-mappings.yaml exists with >= 4 tables and >= 15 entries per table"
    template: "templates/squad-mappings-tmpl.yaml"
    rationale: |
      Without canonical vocabulary, each agent translates vague terms differently.
      "Card" means one thing to one agent and something else to another.
      A shared mappings file ensures consistent interpretation across all agents.
    implementation: |
      1. Copy templates/squad-mappings-tmpl.yaml to squads/{squad}/data/{squad}-mappings.yaml
      2. Fill 4 tables with domain-specific translations (min 15 entries each)
      3. Register in config.yaml under data: section

  - id: context-gate
    check: "Chief agent enforces context loading before generation"
    type: recommended
    validation: "Chief agent contains a context gate rule that HALTs without loaded context"
    rationale: |
      Agents that generate output without domain context produce inconsistent,
      hallucinated, or generic results. A context gate ensures the required
      workspace data is loaded before any generation task executes.
    implementation: |
      Add to the chief agent's rules/operational section:

      - "Context gate: Before any generation task, verify domain context is loaded
         from workspace/businesses/{business}/{squad_namespace}/. If context is not
         loaded, HALT and suggest the appropriate setup command. Generation without
         context produces inconsistent output."

  - id: edit-first-rule
    check: "Chief agent prefers editing over full regeneration"
    type: recommended
    validation: "Chief agent contains edit-first decision tree with at least 3 branches"
    rationale: |
      Full regeneration wastes tokens, loses context, and often produces worse
      results than targeted edits. The Stitch principle: "Prefer edit for targeted
      adjustments over full re-generation."
    implementation: |
      Add to the chief agent's rules/operational section:

      - "Edit-first principle: When output is rejected, evaluate before regenerating.
         Branch 1: If [core structure] is fundamentally wrong, regenerate with improved input.
         Branch 2: If issue is localized (specific element), edit ONLY that element.
         Branch 3: If issue is general style/tone, adjust style keeping structure intact.
         Rule: Editing is ALWAYS preferable to regeneration."

  - id: generation-tasks-reference
    check: "Generation tasks reference vocabulary mappings in prerequisites"
    type: recommended
    validation: "Tasks that produce creative output mention mappings or vocabulary in prerequisites"
    rationale: |
      Even if the chief knows about mappings, individual task definitions should
      reference them so agents executing tasks independently also benefit.
    implementation: |
      Add to the prerequisites section of generation tasks:

      - "Vocabulary: Consult data/{squad}-mappings.yaml for canonical terminology."

  - id: config-registration
    check: "Mappings file registered in config.yaml"
    type: recommended
    validation: "config.yaml contains data: section with mappings entry (id, name, format, description)"
    rationale: |
      Registration in config.yaml enables CLI discovery, validation scripts,
      and automated squad health checks to verify the mappings file exists.
    implementation: |
      Add to config.yaml:

      data:
        - id: {squad}-mappings
          name: "{Squad} Mappings — Canonical Vocabulary"
          format: yaml
          description: "Translates vague requests into professional terminology."
```

---

## Scoring

```yaml
scoring:
  total_checks: 5
  passing_threshold: 3
  ratings:
    5_of_5: "Full consistency — all patterns implemented"
    3_or_4: "Good consistency — core patterns in place"
    1_or_2: "Partial — squad functions but output quality varies"
    0: "No consistency patterns — output is ad-hoc"
```

---

## Reference Implementations

```yaml
reference_squads:
  - squad: aiox-design
    score: 5/5
    note: "First squad to implement all 5 patterns. Gold standard."
  - squad: aiox-copy
    score: 4/5
    note: "Had brief-protocol and copy-gate before this framework. Added mappings and edit-first."
  - squad: brand
    score: 3/5
    note: "Context gate, edit-first, and mappings. No separate enhance-prompt task (chief handles it)."
  - squad: movement
    score: 2/5
    note: "Context gates on manifestador and estrategista. No mappings (uses MI Completo as vocabulary)."
  - squad: hormozi
    score: 2/5
    note: "Context gates on chief, offers, pricing, scale. No separate mappings file."
  - squad: storytelling
    score: 3/5
    note: "Mappings, edit-first, framework-first routing. No explicit context gate (workspace-first handles it)."
```
