# Task: Command-Task-Artifact Traceability Map (Autonomous)

## Contrato SINKRA

Domain: `Strategic`

responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- sujeitos, fontes e artefatos upstream conforme `Inputs`
Saida:
- artefatos de benchmark em `docs/bench/`
Checklist:
- `checklists/bench-quality-checklist.md`
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata
```yaml
id: bench-traceability
name: "AIOX Traceability Map"
category: benchmark
agent: bench-analyst
elicit: false
autonomous: true
estimated_duration: "10-15min"
description: "Map every AIOX command to its executing task and output artifacts with confidence scoring"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Produce a complete traceability chain: Command → Task → Artifact.
Identifies unmapped commands (gaps) and low-confidence mappings requiring validation.

## Reference

See `docs/bench/bmad/aiox-command-task-artifact-traceability-deep.md` for output format example.

---

## Step 1: Load Agent Command Inventory

```
ACTION: Read("docs/bench/appendix-aiox-agent-command-inventory.json")
IF not found: Execute bench-inventory first
STORE: agents[] with their commands[]
```

---

## Step 2: Load Task Catalog

```
ACTION: Glob(".aiox-core/development/tasks/*.md")
STORE: task_files[]

For EACH task_file (read first 40 lines):
  ACTION: Read(task_file, limit=40)
  EXTRACT:
    - id (from metadata YAML)
    - name
    - category
    - agent (default executor)
    - outputs/creates (if documented)
    - key phrases from description

STORE: tasks_catalog[] = [
  { "id": "create-doc", "name": "Create Document", "agent": "pm", "aliases": ["create-doc", "doc-out"], "outputs": ["created_file", "validation_report"] },
  ...
]
```

---

## Step 3: Match Commands to Tasks

For EACH agent in agents[]:
  For EACH command in agent.commands[]:

```
MATCHING ALGORITHM (in priority order):

1. EXACT MATCH (confidence: 1.0)
   command_name == task_id
   Example: "document-project" → task "document-project.md"

2. ALIAS MATCH (confidence: 0.95)
   command_name matches known alias in task metadata
   Example: "research-prompt" → task "create-deep-research-prompt.md"

3. TASK-DEPENDENCY MATCH (confidence: 0.95)
   command appears in agent.dependencies.tasks[]
   Example: agent lists "create-doc.md" → command "create-prd" maps to it

4. SEMANTIC MATCH (confidence: 0.7-0.89)
   command_name has strong word overlap with task name
   "create-competitor-analysis" ≈ "create-doc" (with template=competitor-analysis)

5. NO MATCH (confidence: 0)
   Command has no plausible task mapping
   Mark as GAP

CLASSIFY:
  high: confidence >= 0.9
  medium: confidence 0.7-0.89
  low: confidence < 0.7
  gap: no match
```

---

## Step 4: Extract Artifacts Per Task

For HIGH and MEDIUM confidence matches:

```
ACTION: Read(matched_task_file)
EXTRACT output artifacts:
  - Grep for "creates:", "output:", "OUTPUT:", "generates:"
  - Grep for file path patterns (docs/, .aiox-core/, outputs/)
  - Grep for "Write(" patterns in step instructions

STORE: artifacts[] per command mapping
```

---

## Step 5: Generate Traceability Report (MD)

```markdown
# AIOX {version} - Rastreabilidade Comando -> Task -> Artefato

Data: {today}

## Escopo
Mapeamento detalhado de comandos dos agentes AIOX para tasks executaveis e artefatos de saida.
Fonte: .aiox-core/development/agents/*.md, .aiox-core/development/tasks/*.md

## Cobertura
- Comandos analisados: {total}
- Mapeados (top match): {mapped}
- Nao mapeados: {gaps}
- High confidence: {high_count}
- Medium confidence: {medium_count}
- Low confidence: {low_count}
- Cobertura funcional (sem utilitarios): {functional_mapped}/{functional_total} ({pct}%)

## Regras de Confianca
- high: match por alias conhecido, nome exato ou evidencia direta
- medium: similaridade nominal forte
- low: similaridade fraca, exige validacao manual

## Agente: {agent_id}

- High-confidence mappings: {count}
- Gaps (sem match): {count}

| Comando | Task alvo | Score | Artefatos principais |
| --- | --- | ---: | --- |
| `{command}` | `{task}` | {score} | {artifacts} |

Gaps prioritarios (validar execucao real):
- `{unmapped_command_1}`
- `{unmapped_command_2}`

{repeat for each agent}
```

**OUTPUT:** Write `docs/bench/{competitor}/aiox-command-task-artifact-traceability-deep.md`

---

## Step 6: Generate Traceability Data (JSON)

```json
{
  "generatedAt": "<ISO-8601>",
  "method": "autonomous-command-task-matching",
  "coverage": {
    "total_commands": 276,
    "mapped": 168,
    "unmapped": 108,
    "high_confidence": 81,
    "medium_confidence": 63,
    "low_confidence": 24
  },
  "agents": [
    {
      "id": "analyst",
      "mappings": [
        {
          "command": "create-project-brief",
          "task": "create-doc",
          "confidence": 0.95,
          "confidence_level": "high",
          "artifacts": ["created_file", "validation_report"]
        }
      ],
      "gaps": ["research-deps", "extract-patterns"]
    }
  ]
}
```

**OUTPUT:** Write `docs/bench/{competitor}/appendix-command-task-artifact-traceability.json`

---

## Outputs

| File | Format |
|------|--------|
| `aiox-command-task-artifact-traceability-deep.md` | MD |
| `appendix-command-task-artifact-traceability.json` | JSON |

## Verification

- [ ] Every agent from inventory is covered
- [ ] Every command attempted for mapping
- [ ] High-confidence matches spot-checked (3 random)
- [ ] Gap list reviewed for false negatives
- [ ] JSON parseable
