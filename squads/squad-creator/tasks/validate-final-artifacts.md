# Task: Validate Final Artifacts

**Task ID:** validate-final-artifacts
**Execution Type:** Hybrid (Deterministic checks + Agent for semantic quality)
**Domain:** `Operational`
**Purpose:** Validate final squad outputs only, not intermediate artifacts
**Orchestrator:** @squad-chief
**Mode:** Blocking quality gate
**Model:** `Sonnet` (final artifact semantic quality assessment)
**Haiku Eligible:** NO -- final quality adjudication requires contextual reasoning

**Accountability:** `human: squad-operator | scope: full`

## Cardinal Rule

```
Validate final deliverables, not process traces.
A squad passes only if final artifacts are production-ready.
```

---


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
agent: squad-chief
Input: request::validate_final_artifacts
Output: artifact::validate_final_artifacts
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Final Targets

```yaml
required_artifacts:
  - config.yaml
  - agents/*.md
  - tasks/*.md
  - workflows/*.yaml
  - README.md
  - .claude/skills/*/{entry_agent}/SKILL.md
  - .codex/skills/{entry_agent}/SKILL.md

optional_but_scored:
  - checklists/*.md
  - templates/*
  - data/*
```

---

## Hard Gates

1. `Structure Gate` (blocking)
- All required files exist.
- Entry agent is valid and referenced.
- No broken internal path references.

2. `Execution Gate` (blocking)
- At least one runnable workflow exists.
- Task references resolve to existing files.
- No circular phase dependency in workflows.

3. `Quality Gate` (blocking)
- `validate-squad` score >= 7.0.
- No critical security findings.
- No veto condition triggered.

4. `Chief Activation Gate` (blocking)
- Chief slash skill exists in `.claude/skills/*/{entry_agent}/SKILL.md`.
- Chief Codex skill exists in `.codex/skills/{entry_agent}/SKILL.md`.

5. `Usability Gate` (warning)
- README includes activation and example commands.
- At least one end-to-end example path.

---

## Output

```yaml
final_artifact_report:
  result: PASS | CONDITIONAL | FAIL
  score: 0-10
  blocking_failures:
    - id: "..."
      reason: "..."
  warnings:
    - "..."
  recommended_fixes:
    - "..."
  schema_ref: squads/squad-creator/config/workflow-yaml-schema.yaml

```

---

## Success Criteria

- All blocking gates pass.
- Report generated at `.aiox/squad-runtime/squad-validation/{squad_name}/final-artifacts.yaml`.
