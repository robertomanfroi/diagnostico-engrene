---
task-id: an-assess-sources-collect
name: "Collect Sources for Assessment"
version: 1.0.0
execution_type: Hybrid
model: Haiku
model_rationale: "Source collection is elicitation + cataloging. No deep semantic judgment needed."
haiku_eligible: true
estimated-time: 10 min
complexity: low

inputs:
  required:
    - mind_name: "Nome do expert a clonar"
  optional:
    - sources_dir: "Caminho para diretorio com fontes ja baixadas"

outputs:
  primary:
    - raw_sources_list: "Lista catalogada de todas as fontes com tipo, URL, duracao"

elicit: true
---
<!-- SINKRA_TASK_METADATA:START -->
```yaml
sinkra_task_metadata:
  task_id: an-assess-sources-collect
  task_name: Collect Sources for Assessment
  status: pending
  responsible_executor: '@oalanicolas'
  execution_type: Hybrid
  estimated_time: 10m
  domain: Operational
  input:
  - '{''mind_name'': ''Nome do expert a clonar''}'
  - '{''sources_dir'': ''Caminho para diretorio com fontes ja baixadas''}'
  output:
  - '{''raw_sources_list'': ''Lista catalogada de todas as fontes com tipo, URL, duracao''}'
  action_items:
  - Elicit Sources from User
  - Apply Source Granularity Rules (CRITICAL)
  - Catalog Each Source
  acceptance_criteria:
  - Todas as fontes listadas pelo usuario catalogadas
  - Cada fonte e uma UNIDADE COMPLETA (nao fragmentos)
  - Tipo, URL e duracao registrados para cada fonte
  - Nenhum livro dividido em capitulos ou video em segmentos
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


# Task: Collect Sources for Assessment

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `an-assess-sources-collect` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `@oalanicolas` |
| **Execution Type** | `Hybrid` |

## Metadata

- **Parent Task:** `an-assess-sources` (orchestrator stub)
- **Sequence:** Phase 1 of 4
- **Previous Task:** None
- **Next Task:** `an-assess-sources-score`

## Purpose

Coletar e catalogar todas as fontes disponiveis para avaliacao de um expert, aplicando a regra de granularidade Trinity FONTE (uma unidade completa de conteudo = uma fonte).

## Prerequisites

- `mind_name` fornecido pelo usuario
- Fontes disponiveis (listadas pelo usuario ou em diretorio local)

## Inputs

| Input | Required | Description |
|-------|----------|-------------|
| `mind_name` | Yes | Nome do expert a clonar |
| `sources_dir` | No | Caminho para diretorio com fontes baixadas |

## Workflow / Steps

### Step 1: Elicit Sources from User

Perguntar ao usuario:
- "Liste TODOS os materiais que voce tem dessa pessoa"
- Tipos: videos, podcasts, livros, posts, stories, comentarios, entrevistas, cursos

### Step 2: Apply Source Granularity Rules (CRITICAL)

```yaml
source_granularity:
  principle: "Trinity FONTE = uma UNIDADE COMPLETA de conteudo"

  # O que conta como UMA fonte (avaliar como unidade unica)
  one_source_equals:
    livro: "O LIVRO INTEIRO (nao capitulos separados)"
    video: "O VIDEO INTEIRO (nao segmentos)"
    podcast: "O EPISODIO INTEIRO (nao trechos)"
    entrevista: "A ENTREVISTA INTEIRA (nao perguntas)"
    curso: "O CURSO INTEIRO (nao modulos)"
    post: "O POST INTEIRO (cada post = 1 fonte)"
    thread: "A THREAD INTEIRA (nao tweets individuais)"

  # ANTI-PATTERNS - NUNCA FACA ISSO
  never_do:
    - "NAO divida livros em capitulos separados"
    - "NAO divida videos em segmentos"
    - "NAO trate secoes de livro como fontes diferentes"
    - "NAO avalie partes de um todo separadamente"

  # EXEMPLOS CORRETOS vs INCORRETOS
  examples:
    correto:
      - "Livro '$100M Offers' -> 1 fonte (avaliar livro inteiro)"
      - "Entrevista Tom Bilyeu -> 1 fonte (avaliar entrevista inteira)"
      - "Podcast Episode #47 -> 1 fonte"

    incorreto:
      - "Capitulo 6 de Offers -> NAO (e parte de um livro)"
      - "Secoes I-II de Leads -> NAO (e parte de um livro)"
      - "Minutos 0-30 do video -> NAO (e parte de um video)"

  rationale: |
    O usuario BAIXA e PROCESSA fontes no nivel de SOURCE (livro, video, episodio).
    A prioridade de extracao e por SOURCE, nao por capitulo.
    Se um LIVRO e Crown Jewel, todo o livro tem prioridade - nao apenas 1 capitulo.
```

### Step 3: Catalog Each Source

For each source, record:

```yaml
raw_sources_list:
  mind: "{nome}"
  total_sources: {n}
  sources:
    - name: "{fonte}"
      type: "{video|podcast|livro|post|curso|entrevista}"
      url: "{link se disponivel}"
      duration: "{duracao/paginas}"
      has_local_file: true|false
```

## Output

```yaml
raw_sources_list:
  mind: "{nome}"
  total_sources: 0
  sources: []
```

## Acceptance Criteria

- [ ] Todas as fontes listadas pelo usuario catalogadas
- [ ] Cada fonte e uma UNIDADE COMPLETA (nao fragmentos)
- [ ] Tipo, URL e duracao registrados para cada fonte
- [ ] Nenhum livro dividido em capitulos ou video em segmentos

## Veto Conditions

| ID | Condition | Result |
|----|-----------|--------|
| VETO-AS-001 | `mind_name` must be provided | BLOCK |
| VETO-AS-002 | Source fragmentation detected (chapters as separate sources) | BLOCK — merge into single source |

## Related Documents

| Document | Relationship |
|----------|-------------|
| `an-assess-sources.md` | Parent orchestrator |
| `an-assess-sources-score.md` | Next phase (25-checkpoint scoring) |
| `data/an-source-tiers.yaml` | Tier definitions reference |
