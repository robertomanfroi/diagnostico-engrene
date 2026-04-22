# Dry Run Report: traffic-masters absorve _traffic

Date: 2026-03-09
Mode: dry-run (analysis only, no writes in squads/traffic-masters)
Sources: `squads/traffic-masters`, `squads/_traffic`
Target (planned): `squads/traffic-masters`

## Evidence Snapshot

### Inventory
- traffic-masters: agents 16, tasks 18, workflows 1, templates 6, checklists 4, data 9, scripts 5, skills 36
- _traffic: agents 9, tasks 11, workflows 8, templates 1, checklists 8, data 38, scripts 0, skills 0
- estimated merged volume (sum - basename collisions):
  - agents 25, tasks 29, workflows 9, templates 7, checklists 12, data 47, scripts 5, skills 36
- basename collisions detected: none across agents/tasks/workflows/templates/checklists/data/scripts/skills

### Quality Signals
- `validate-squad.sh traffic-masters --quick --json`: score 7/10 (conditional)
- `validate-squad.sh _traffic --quick --json`: score 7/10 (conditional)
- workflow contract scan (`validate_workflow_contracts.cjs --squads traffic-masters,_traffic`):
  - traffic-masters: 1 workflow, 1 error, 2 warnings
  - _traffic: 8 workflows, 8 errors (all missing top-level `workflow:` schema)

### Orchestrator Surface
- `traffic-masters-chief`: 11 commands
- `traffic-chief` (_traffic): 34 commands
- overlap: `*help`, `*diagnose`, `*scale`

## Decision Matrix (keep / merge / discard)

| Category | traffic-masters | _traffic | Decision | Rationale |
|---|---|---|---|---|
| Canonical target | Exists and operational | Legacy squad | KEEP target as `traffic-masters` | Better governance + workspace integration contract already defined |
| Manifest schema | `config.yaml` + `squad.yaml` present | only `config.yaml` (no `squad.yaml`) | KEEP target manifest style | `traffic-masters` closer to canonical contract |
| Orchestrator agent | `traffic-masters-chief.md` | `traffic-chief.md` | KEEP target + MERGE command coverage | Keep canonical identity; absorb missing operational commands as aliases/routing |
| Specialist agents | 16 elite minds | 9 operational agents | KEEP target, DISCARD direct import of source agents | Avoid duplicate agent topology; absorb operational logic via tasks/workflows |
| Workflows | 1 (invalid contract today) | 8 (all invalid contract today) | MERGE with normalization only | High tactical value, but must be converted to required workflow schema first |
| Tasks | 18 strategic/ops | 11 tactical ops | MERGE selective | Many useful tactical tasks in _traffic complement target coverage |
| Checklists | 4 | 8 | MERGE selective | _traffic adds pre-launch, quality gates, andromeda checklist depth |
| Templates | 6 | 1 | MERGE selective | `dream-100-worksheet.yaml` is additive |
| Data: rules | limited rules in target | 14 rule files | MERGE (high priority) | Strong operational ruleset by campaign type |
| Data: strategies | few KB docs | 4 strategy docs | MERGE selective | Good strategic references, align naming and provenance |
| Data: benchmarks/reference | compact | extensive references | MERGE selective | Useful benchmark/reference corpus |
| Data: runtime feedback | not dominant | `dados-reais.yaml`, `feedback-vendas.yaml` | DISCARD direct import | Runtime/client-specific signals should not enter canonical static KB |
| Scripts/skills | 5 scripts + 36 skills | none | KEEP target | No source assets to merge |

## File-Level Proposed Actions

### Workflows (_traffic -> traffic-masters/workflows)
Status: MERGE_AFTER_NORMALIZE (schema conversion required)
- wf-create-campaign.yaml
- wf-daily-optimization.yaml
- wf-dream-100-campaign.yaml
- wf-launch-campaign.yaml
- wf-lead-magnet-pipeline.yaml
- wf-paid-ads-campaign.yaml
- wf-story-seguidores.yaml
- wf-weekly-production.yaml

### Tasks (_traffic)
Status: MERGE
- apply-rules.md
- assemble-ads.md
- competitor-research.md
- create-meta-campaign.md
- generate-hooks.md
- generate-report.md
- generate-visual-report.md
- pull-metrics.md
- schedule-optimization.md

Status: DISCARD_DIRECT_IMPORT (merge ideas only)
- plan-campaign.md (overlaps with target create/diagnose flow)
- audit-account.md (overlaps with existing audit tasks; too shallow as standalone)

### Data (_traffic)
Status: MERGE
- rules/*.yaml (all)
- strategies/*.md (all)
- references/*.md + references/*.yaml (all, after curation)
- benchmarks/benchmarks-brasil-2025.yaml
- torriani-metrics.yaml (merge with provenance + naming normalization)

Status: DISCARD_DIRECT_IMPORT
- benchmarks/dados-reais.yaml
- benchmarks/feedback-vendas.yaml

### Checklists / Templates (_traffic)
Status: MERGE_SELECTIVE
- checklists/*.md (all candidates; validate overlap before final copy)
- templates/dream-100-worksheet.yaml

## Risks and Mitigations

1. Workflow contract failures in both squads
- Risk: importing invalid workflow schema increases lint/test friction.
- Mitigation: convert each merged workflow to canonical `workflow:` contract before enabling.

2. Command surface inflation in orchestrator
- Risk: too many commands degrade routing quality.
- Mitigation: map source commands to grouped aliases and keep primary command set small.

3. Data provenance drift
- Risk: benchmark/reference files may mix static guidance with runtime-specific data.
- Mitigation: separate static KB from runtime feedback; keep runtime data outside canonical squad data.

## Governance Block

```yaml
governance_check:
  protocol: squads/squad-creator/protocols/ai-first-governance.md
  canonical_sources_checked:
    - path: squads/traffic-masters/config.yaml
      status: implemented
    - path: squads/traffic-masters/squad.yaml
      status: implemented
    - path: squads/_traffic/config.yaml
      status: implemented
    - path: squads/_traffic/agents/traffic-chief.md
      status: implemented
    - path: squads/traffic-masters/agents/traffic-masters-chief.md
      status: implemented
  evidence:
    - claim: inventory and collision analysis completed
      source: shell inventory commands (2026-03-09)
    - claim: workflow contract risk mapped for both squads
      source: infrastructure/scripts/squads/validate_workflow_contracts.cjs report
    - claim: quick validation scores captured for both squads
      source: squads/squad-creator-pro/scripts/validate-squad.sh --quick --json
  contradictions_found: []
  unresolved_items:
    - final alias map for orchestrator commands
    - exact normalized filenames for converted workflows
    - rollout strategy for deprecating `_traffic` after merge
```
