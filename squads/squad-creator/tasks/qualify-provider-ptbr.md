# Task: PT-BR Quality Test for Cross-Provider Qualification

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `qualify-provider-ptbr` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: qualify-provider-ptbr
name: "PT-BR Quality Test for Cross-Provider Qualification"
category: qualification
agent: squad-chief
elicit: false
autonomous: true
description: >
  Tests the candidate model's Portuguese quality using 3 structured prompts
  (technical writing, framework extraction, voice consistency). Opus evaluates
  results on fluency, accuracy, and completeness. Conditional phase -- skipped
  when task is not pt_br_critical or skip_pt_br is true. Corresponds to Phase 4
  of wf-cross-provider-qualification.yaml.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::qualify_provider_ptbr
Output: artifact::qualify_provider_ptbr
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Validate that the candidate model can produce natural, accurate Brazilian
Portuguese at a level acceptable for the pipeline. Models that translate
rather than think natively in PT-BR fail this gate.

## Prerequisites

- [ ] `qualify-provider-compare` completed successfully
- [ ] Condition met: NOT skip_pt_br AND task.pt_br_critical

## Inputs

| Parameter | Type | Required | Source |
|-----------|------|----------|--------|
| `task_name` | string | Yes | From pipeline |
| `candidate_model` | string | Yes | From pipeline |
| `skip_pt_br` | boolean | No | Default: false |
| `pt_br_critical` | boolean | Yes | From cross_provider_candidates |

## Condition

```yaml
execute_if: "NOT skip_pt_br AND pt_br_critical"
skip_output:
  ptbr_verdict: "SKIPPED"
  ptbr_overall: null
```

## Workflow

### Step 1: Execute PT-BR prompts

Run 3 test prompts via LLM Router:

```yaml
pt_br_test_prompts:
  - id: ptbr_1
    name: "Technical Writing"
    prompt: |
      Escreva uma documentacao tecnica de 500 palavras sobre arquitetura de microsservicos.
      Inclua: definicao, beneficios, desafios, e quando usar.
      Use linguagem tecnica mas acessivel.
    eval_criteria: [fluency, accuracy, completeness]

  - id: ptbr_2
    name: "Framework Extraction"
    prompt: |
      Dado o seguinte texto sobre metodologia de vendas:
      "O fechamento acontece quando voce elimina todas as objecoes do cliente.
      Primeiro, identifique a objecao real. Depois, concorde parcialmente.
      Por fim, apresente uma perspectiva diferente que resolve a objecao."
      Extraia o framework em formato YAML com: nome, etapas, e quando aplicar.
    eval_criteria: [understanding, structure, no_hallucination]

  - id: ptbr_3
    name: "Voice Consistency"
    prompt: |
      Voce e Pedro Valerio, especialista em processos e automacao.
      Sua filosofia e: "Se o executor consegue errar, o processo esta errado."
      Responda a pergunta: "Como voce abordaria a criacao de um novo workflow?"
      Mantenha sua voz e perspectiva consistentes.
    eval_criteria: [voice_match, philosophy_applied, natural_pt_br]
```

Each result saved to `test-cases/cross-provider/{task_name}/{candidate_model}/ptbr-{id}.yaml`.

### Step 2: Evaluate PT-BR quality

Opus evaluates each output on a 1-10 scale for fluency, accuracy, and completeness.

**Overall PT-BR Score** = average of all individual scores.

### Step 3: PT-BR verdict

```yaml
verdict_rules:
  - condition: "ptbr_overall < 7.0"
    verdict: "NOT_QUALIFIED"
    veto: CPQ_VC_005
  - condition: "ptbr_overall >= 7.0 AND ptbr_overall < 8.0"
    verdict: "ACCEPTABLE"
  - condition: "ptbr_overall >= 8.0"
    verdict: "QUALIFIED"
```

## Output

```yaml
ptbr_output:
  ptbr_scores: []
  ptbr_overall: 0.0
  ptbr_verdict: "QUALIFIED|ACCEPTABLE|NOT_QUALIFIED|SKIPPED"
```

## Veto Conditions

```yaml
veto_conditions:
  - id: CPQ_VC_005
    trigger: "PT-BR quality score < 7.0/10"
    action: "BLOCK - Model not qualified for PT-BR"
```

## Acceptance Criteria

- [ ] All 3 PT-BR prompts executed (or phase skipped with reason)
- [ ] Opus evaluation completed with per-prompt scores
- [ ] Overall score calculated and verdict assigned
- [ ] Veto applied if score below 7.0

## Related Documents

- `wf-cross-provider-qualification.yaml` -- Parent workflow
- `qualify-provider-compare.md` -- Previous task in pipeline
- `qualify-provider-report.md` -- Next task in pipeline

---

_Task Version: 1.0.0_
_Extracted from: wf-cross-provider-qualification.yaml v1.0 (Phase 4)_
