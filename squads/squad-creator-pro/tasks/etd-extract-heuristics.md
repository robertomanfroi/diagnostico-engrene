---
task-id: etd-extract-heuristics
name: "ETD Phase 3: Extract Heuristics (SE/ENTÃO + Vetos + Priorities)"
version: 1.0.0
execution_type: Agent
model: Opus
haiku_eligible: false
model_rationale: "Heuristic extraction requires deep pattern recognition across multiple sources"
estimated-time: 20 min
complexity: medium
parent_task: extract-thinking-dna

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
    - domain: "Area de expertise"
    - sources: "Fontes validadas com metodologia documentada"
    - recognition_patterns: "Output de etd-recognition-patterns"
    - frameworks: "Output de etd-discover-frameworks"

outputs:
  primary:
    - heuristics_yaml: "Bloco YAML com heurísticas no formato SE/ENTÃO/NUNCA"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: etd-extract-heuristics
  task_name: 'ETD Phase 3: Extract Heuristics (SE/ENTÃO + Vetos + Priorities)'
  status: pending
  responsible_executor: Agent
  execution_type: Agent
  estimated_time: 20m
  domain: Operational
  input:
  - "{'mind_name': 'Nome do expert'}"
  - "{'sources': 'Fontes validadas'}"
  - "{'recognition_patterns': 'Output Phase 1'}"
  - "{'frameworks': 'Output Phase 2'}"
  output:
  - "{'heuristics_yaml': 'Bloco YAML com heurísticas SE/ENTÃO/NUNCA'}"
  action_items:
  - Extrair regras de decisão (SE condição → ENTÃO ação)
  - Extrair vetos (NUNCA + trigger + consequência)
  - Extrair prioridades (entre A e B, expert escolhe qual)
  - Classificar por Pareto ao Cubo (0,8% genialidade, 4% excelência, 20% impacto, 80% descartar)
  - Validar rastreabilidade com [SOURCE:]
  acceptance_criteria:
  - 8+ heurísticas extraídas
  - 100% no formato SE/ENTÃO/NUNCA
  - 100% com [SOURCE:] rastreável
  - Zero inferências sem marcação [INFERRED]
  - Pareto ao Cubo aplicado (classificação por zona)
  - 2+ veto conditions documentadas
  output_persistence: transient_output
  accountable_id: Human:Squad_Operator
  accountability_scope: review_only
```
<!-- SINKRA_TASK_METADATA:END -->

# ETD Phase 3: Extract Heuristics

## Purpose

Extrair as regras de decisão (heurísticas) que o expert usa para decidir em situações recorrentes.
Diferente de frameworks (estruturas formais) e recognition patterns (sinais de reconhecimento),
heurísticas são atalhos mentais no formato SE/ENTÃO que o expert aplica intuitivamente.

## Scope

**O que extrair:**
- Decision heuristics: "SE X acontece → ENTÃO faço Y"
- Veto heuristics: "NUNCA faço Z quando W"
- Prioritization heuristics: "Entre A e B, sempre A porque..."
- Timing heuristics: "QUANDO X, é hora de Y"
- Risk heuristics: "SE risco > threshold → ação defensiva"

**O que NÃO extrair:**
- Frameworks formais (etd-discover-frameworks já cobriu)
- Padrões de reconhecimento (etd-recognition-patterns já cobriu)
- Conhecimento genérico ("seja disciplinado", "planeje antes de agir")

## Extraction Method

### Step 1: Scan Sources com Perguntas-Guia

Para cada fonte OURO, aplicar:

```
1. "Em que PONTO EXATO o expert decidiu X? O que mudou?"
2. "Que regra o expert aplica que é CONTRAINTUITIVA?"
3. "Quando o expert RECUSA uma oportunidade aparentemente boa, qual é o critério?"
4. "Que ERRO gerou uma regra permanente?"
5. "Onde o expert DISCORDA do consenso do mercado?"
```

### Step 2: Formatar como SE/ENTÃO/NUNCA

Cada heurística DEVE ter:

```yaml
- id: "H-{DOMAIN}-NNN"
  name: "Nome descritivo"
  type: "decision|veto|prioritization|timing|risk"
  rule: |
    SE {condição observável}
    ENTÃO {ação específica}
    NUNCA {anti-pattern}
  source: "[SOURCE: {livro/entrevista}, {página/minuto}]"
  confidence: "ALTA|MEDIA"
  zone: "genialidade|excelencia|impacto"  # Pareto ao Cubo
```

### Step 3: Aplicar Pareto ao Cubo

Classificar cada heurística:
- **0,8% Genialidade** — contraintuitiva + comprovada + única deste expert
- **4% Excelência** — guardrail valioso que previne erro caro
- **20% Impacto** — boa prática com evidência
- **80% Descartar** — qualquer expert diria, genérico

**Teste de Distintividade:** "200 experts neste domínio diriam a mesma coisa?"
Se sim → 💩 descartar. Se não → manter.

### Step 4: Validar Rastreabilidade

- 100% das heurísticas DEVEM ter `[SOURCE:]` com página/minuto
- Inferências marcadas `[INFERRED]` — nunca apresentar como fato
- Heurísticas com confidence ALTA requerem 2+ fontes independentes

## Output Format

```yaml
heuristics:
  total: N
  by_zone:
    genialidade: N
    excelencia: N
    impacto: N
    descartadas: N
  items:
    - id: "H-{DOMAIN}-001"
      name: "..."
      type: "decision"
      rule: |
        SE ...
        ENTÃO ...
        NUNCA ...
      source: "[SOURCE: ...]"
      confidence: "ALTA"
      zone: "genialidade"
    # ... more items
```

## Veto Conditions

- Heurística sem `[SOURCE:]` → BLOCK
- Heurística genérica (200 experts diriam) → DISCARD
- Menos de 8 heurísticas extraídas → fontes insuficientes, buscar mais
- Inferência apresentada como fato → BLOCK

## Related Tasks

- `an-extract-heuristics.md` — task genérica do @oalanicolas para extração standalone
- `an-extract-session-heuristics.md` — extração de heurísticas de sessões de trabalho
- `etd-discover-frameworks.md` — predecessor (frameworks → heurísticas)
- `etd-decision-architecture.md` — successor (heurísticas → decision architecture)

---

_Task Version: 1.0.0_
