<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-extract-dna
  task_name: Extract DNA Mental
  status: pending
  responsible_executor: Agent
  execution_type: Hybrid
  estimated_time: 30m
  domain: Operational
  input:
  - Consultar a seção de inputs no corpo da task
  output:
  - Consultar a seção de outputs no corpo da task
  action_items:
  - Source Assessment (40% do tempo)
  - Layer Extraction
  - Document Voice DNA
  - Document Thinking DNA
  - Generate Report
  acceptance_criteria:
  - 8 camadas mapeadas
  - Fontes classificadas (ouro vs bronze)
  - Trindade identificada (Playbook + Framework + Swipe)
  - Voice DNA documentado
  - Thinking DNA documentado
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: full
  escalation_priority: medium
```
<!-- SINKRA_TASK_METADATA:END -->

<!-- SINKRA_CONTRACT:START -->
```yaml
sinkra_contract:
  Domain: Tactical
  atomic_layer: Atom
  executor: Agent
  pre_condition: "inputs, dependências e artefatos prévios resolvidos antes de iniciar a execução."
  post_condition: "output principal gerado, validado e pronto para handoff da próxima fase."
  performance: "executar dentro do SLA declarado, registrar erro explicitamente e escalar via handoff sem falha silenciosa."
```
<!-- SINKRA_CONTRACT:END -->


# Task: Extract DNA Mental

**Task ID:** an-extract-dna  
**Version:** 3.1.0  
**Purpose:** compor a extração de DNA mental em fases atômicas de curadoria, camadas, voice, thinking e report

## Canonical Workflow

- `squads/squad-creator-pro/workflows/wf-extract-dna.yaml`

## Atomic Sub-Tasks

- `an-extract-dna-source-assessment.md`
- `an-extract-dna-layer-extraction.md`
- `an-extract-dna-voice-dna.md`
- `an-extract-dna-thinking-dna.md`
- `an-extract-dna-report.md`

## Inputs

- `mind` ou `target` do clone é obrigatório
- `sources/` e `data/an-source-tiers.yaml` alimentam a curadoria
- contexto adicional só enriquece a extração, sem alterar a sequência canônica

## Preconditions

- [ ] `squads/squad-creator-pro/workflows/wf-extract-dna.yaml` existe
- [ ] as 5 subtasks atômicas existem
- [ ] a extração só prossegue se `source_map` e `curadoria_score` forem produzidos na fase 1

## Execution Sequence

```text
[1] an-extract-dna-source-assessment
[2] an-extract-dna-layer-extraction
[3] an-extract-dna-voice-dna
[4] an-extract-dna-thinking-dna
[5] an-extract-dna-report
OUTPUT: dna_extraction_report + voice_dna_preview + thinking_dna_preview
```

## Output

```yaml
output:
  delegated_workflow: "squads/squad-creator-pro/workflows/wf-extract-dna.yaml"
  source_map: {}
  curadoria_score: 0
  voice_dna_preview: {}
  thinking_dna_preview: {}
  dna_extraction_report: {}
```

## Acceptance Criteria

- [ ] 8 camadas são mapeadas nas subtasks de extração
- [ ] fontes são classificadas como ouro vs bronze com score de curadoria
- [ ] voice DNA e thinking DNA são documentados separadamente
- [ ] o report final inclui `fidelity_estimate` e `next_steps`
- [ ] o wrapper não reimplementa localmente as 5 fases
