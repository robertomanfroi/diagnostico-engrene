# {COMPETITOR} vs AIOX {AIOX_VERSION} - Comparativo Profundo (Privado)

Data: {DATE}
Escopo: comparacao tecnica profunda de agentes, workflows e capacidades operacionais
Status: documento privado local (nao comitar)

## Fontes (oficiais)

- {COMPETITOR} repo: {REPO_URL}
- {COMPETITOR} docs: {DOCS_URL}
- AIOX local:
  - `.aiox-core/development/agents/`
  - `.aiox-core/development/workflows/`
  - `.aiox-core/development/tasks/`

## Metodo de comparacao

1. {COMPETITOR}: {SOURCE_METHOD}
2. AIOX: extraido diretamente dos YAML embutidos nos agentes e YAML de workflows locais
3. Mapeamento feito em 3 niveis:
   - Equivalente forte
   - Equivalente parcial
   - Sem equivalente direto

## Inventario real atual

### {COMPETITOR}

| Componente | Quantidade |
|------------|------------|
| Agents | {COMP_AGENTS} |
| Workflows | {COMP_WORKFLOWS} |
| Tasks/Commands | {COMP_TASKS} |
| Templates | {COMP_TEMPLATES} |

**Agentes:**
{COMP_AGENT_LIST}

**Workflows:**
{COMP_WORKFLOW_LIST}

### AIOX {AIOX_VERSION}

| Componente | Quantidade |
|------------|------------|
| Agents | {AIOX_AGENTS} |
| Workflows | {AIOX_WORKFLOWS} |
| Tasks | {AIOX_TASKS} |
| Commands | {AIOX_COMMANDS} |
| Templates | {AIOX_TEMPLATES} |

**Agentes locais:**
{AIOX_AGENT_LIST}

**Workflows locais:**
{AIOX_WORKFLOW_LIST}

## Matriz 1:1 - Agentes

| {COMPETITOR} agent | AIOX equivalente | Nivel | Diferencas principais |
| --- | --- | --- | --- |
{AGENT_MATRIX_ROWS}

## Matriz 1:1 - Workflows

| {COMPETITOR} workflow | AIOX equivalente | Nivel | Diferencas principais |
| --- | --- | --- | --- |
{WORKFLOW_MATRIX_ROWS}

## Gaps AIOX (sem equivalente em {COMPETITOR})

{AIOX_DIFFERENTIALS}

## Gaps {COMPETITOR} (sem equivalente em AIOX)

{COMPETITOR_DIFFERENTIALS}

## Leitura objetiva

{OBJECTIVE_READING}

## Recomendacoes

{RECOMMENDATIONS}
