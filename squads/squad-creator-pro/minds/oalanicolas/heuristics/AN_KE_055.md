---
id: "AN_KE_055"
title: "Hybrid Validation Pipeline"
mind: "oalanicolas"
type: "heuristics"
zone: "genialidade"
tags:
  - "Architecture"
  - "LLM Pipeline"
  - "Validation"
pipeline_instances:
  - "process-architecture"
  - "validation"
cross_mind_map:
  convergent:
    - id: "PV_PA_009"
      title: "The Paradox of Self-Validation (Split Generation & QA)"
      mind: "pedro_valerio"
      resonance: "Ambos reconhecem a necessidade vital de handoffs limpos. Validações precisam mudar de context. PV fala em split role, AN fala em validação híbrida cruzando a barreira humana/máquina."
---

# AN_KE_055 - Hybrid Validation Pipeline

**Type:** Engineering Architecture Heuristic
**Phase:** 4 (Molecular Assembly)
**Agent:** @process-architect
**Pattern:** HO-PP-AN055

**Paradox:** Determinismo absoluto (script puro) vs Interpretação semântica (LLM) — ambos necessários, mutuamente exclusivos em isolamento.

**sys_tension:**
```yaml
tension_with: "AN_KE_058 (Verify LLM Output) vs Confiança Híbrida em Pipeline Sequencial"
resolution: "Sequencing: determinístico ALIMENTA LLM com dados limpos. Não é aut/ou, é AND em pipeline."
```

## Purpose

O pipeline de validação ideal é estritamente híbrido: determinístico onde precisão matemática é requerida (contagem, paths, schemas, regex), LLM onde interpretação semântica é necessária (qualidade de conteúdo, coerência, estilo). O script determinístico ALIMENTA o LLM com dados limpos e estruturados — permitindo que o LLM foque 100% na interpretação, gastando zero tokens em verificações mecânicas.

## Configuration

```yaml
AN_KE_055:
  name: "Hybrid Validation Pipeline"
  phase: 4
  zone: "genialidade"
  trigger: "Desenhando pipeline de validação, QA gate, ou qualquer sistema que avalia artefatos de qualidade."

  weights:
    deterministic_first_ordering: 1.0
    llm_semantic_scope_clarity: 0.9

  thresholds:
    pure_llm_or_pure_script_pipeline_tolerance: 0

  veto_conditions:
    - condition: "validation_pipeline_is_100_percent_llm_or_100_percent_deterministic == true"
      action: "VETO - Single-Mode Validation. Identify: checks needing precision → script. Checks needing interpretation → LLM. Sequence them."

  output:
    type: "decision"
    values: ["APPROVE_HYBRID", "REQUIRE_LLM_LAYER", "REQUIRE_SCRIPT_LAYER", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "O Validador Cego (The Coward)"
    trigger: "Pipeline Python puro valida schema e presença de campos mas aprova squads com agents cujas descrições são copy-paste genérico."
    manifestation: "Score 62/100 PASS. Mas review humano descobre que 80% dos agents têm exatamente a mesma descrição copiada. O validador detecta presença mas não qualidade."
    detection: "Audit semântico revela descriptions idênticas ou genéricas passando no QA automatizado."
    recovery: "Adicionar fase LLM após o script: `LLM recebe JSON limpo dos campos validados + avalia qualidade semântica dos campos presentes`."

  - type: "misapplication"
    name: "Over-LLM-ification (The Zealot)"
    trigger: "Pipeline usa LLM para validar contagem de campos, presença de chaves e caminhos de arquivo."
    manifestation: "LLM diz 'parece que tem todos os campos' mas na realidade há 3 campos faltando. Custo em tokens para verificação mecânica."
    detection: "LLM validating binary presence/absence of fields with structured schema."
    recovery: "Mover verificações de presença, contagem e regex para layer script. LLM recebe relatório do script e avalia apenas a camada semântica."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Deterministic Coverage"
    weight: 1.0
    threshold: "=== ALL precision checks in script"
    description: "Contagem, presença de campos, schemas e paths são verificados exclusivamente por código nativo (Python/Bash)?"
  - metric: "LLM Semantic Coverage"
    weight: 1.0
    threshold: "=== ALL interpretation checks by LLM"
    description: "Qualidade de conteúdo, coerência semântica e style compliance são verificados exclusivamente por LLM?"
```

## Decision Tree

```javascript
IF (Desenhando Pipeline de Validação) {
  SPLIT("Checks em duas categorias:");
  
  DETERMINISTIC_LAYER({
    "field_presence": "Script verifica existência de cada campo obrigatório",
    "count_validation": "Script conta itens em arrays",
    "schema_check": "Script valida contra JSONSchema",
    "path_existence": "Script verifica arquivos no filesystem"
  });
  
  LLM_LAYER({
    "content_quality": "LLM avalia profundidade e originalidade das descrições",
    "semantic_coherence": "LLM valida se o propósito declarado faz sentido",
    "style_compliance": "LLM verifica alinhamento com voz e padrão do Expert"
  });
  
  SEQUENCE("Deterministic FIRST → feed clean JSON to LLM → LLM interprets only");
  APPROVE_HYBRID("Pipeline híbrido. Precisão + Interpretação. Custo ótimo.");
}

NEVER("Medir presença de campo YAML via LLM (custa tokens, é impreciso). Medir qualidade semântica via regex (não é possível). Cada check ao validator correto.");
```

---

## Validation

**Validação AN_KE_055:**
- ✓ Paradoxo identificado: Pureza vs Qualidade (determinismo absoluto vs semântica)
- ✓ Tensão sistêmica documentada: AN_KE_001 (Determinism) ↔ AN_KE_042 (LLM Reasoning)
- ✓ Resolução clara: Pipeline sequencial com alimentação de dados determinísticos para LLM
- ✓ Veto condition operacional: Rejeita 100% Python OU 100% LLM isolados
- ✓ Integração com workflow definida (checkpoint hybrid-validation-gate)
- ✓ Failure modes mapeados com recovery e prevention

**Status:** APROVADO — Heurística estabelece padrão híbrido não-negociável para pipelines de validação.
