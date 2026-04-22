# {COMPETITOR} -> AIOX {AIOX_VERSION} Migration Playbook

Data: {DATE}
Status: documento privado local (nao comitar)

## Objetivo

Fornecer migracao de baixo risco para times que ja operam {COMPETITOR} e querem adotar AIOX sem perder capacidade operacional.

## Premissas

- {PREMISSA_1}
- {PREMISSA_2}
- {PREMISSA_3}

---

## Mapeamento de agentes (pratico)

| {COMPETITOR} | AIOX alvo | Acao de migracao |
| --- | --- | --- |
{AGENT_MIGRATION_ROWS}

## Mapeamento de workflows core

| {COMPETITOR} | AIOX | Status |
| --- | --- | --- |
{WORKFLOW_MIGRATION_ROWS}

## Traducao de comandos (nucleo)

Observacao: comandos podem variar entre versoes {COMPETITOR}; usar esta tabela como baseline operacional.

### {AGENT_1}

| {COMPETITOR} (esperado) | AIOX |
| --- | --- |
{AGENT_1_COMMAND_ROWS}

### {AGENT_2}

| {COMPETITOR} (esperado) | AIOX |
| --- | --- |
{AGENT_2_COMMAND_ROWS}

### {AGENT_3}

| {COMPETITOR} (esperado) | AIOX |
| --- | --- |
{AGENT_3_COMMAND_ROWS}

### {AGENT_4}

| {COMPETITOR} (esperado) | AIOX |
| --- | --- |
{AGENT_4_COMMAND_ROWS}

## Mapeamento de artefatos

| Artefato {COMPETITOR} | Artefato AIOX equivalente |
| --- | --- |
{ARTIFACT_MIGRATION_ROWS}

---

## Estrategia de migracao em 4 ondas

### Onda 1: Compatibilidade minima

1. {WAVE_1_STEP_1}
2. {WAVE_1_STEP_2}
3. {WAVE_1_STEP_3}

### Onda 2: Paridade operacional

1. {WAVE_2_STEP_1}
2. {WAVE_2_STEP_2}
3. {WAVE_2_STEP_3}

### Onda 3: Ganhos AIOX

1. {WAVE_3_STEP_1}
2. {WAVE_3_STEP_2}
3. {WAVE_3_STEP_3}

### Onda 4: Otimizacao e governanca (continuo)

1. {WAVE_4_STEP_1}
2. {WAVE_4_STEP_2}
3. {WAVE_4_STEP_3}

---

## Checklists de risco (anti-perda)

### Checklist tecnico

- [ ] Todos os agentes core mapeados e testados
- [ ] Workflows core validados em projeto piloto
- [ ] Quality gates obrigatorios ativados
- [ ] Paridade por IDE validada
- [ ] Hooks ativados quando aplicavel

### Checklist de processo

- [ ] Time conhece diferenca entre `aiox-master` e `devops`
- [ ] Squad sabe quando usar agentes especializados
- [ ] Fluxo de QA loop documentado
- [ ] Criterios de "done" alinhados com gate QA

---

## Gaps esperados durante migracao

1. {GAP_1}
2. {GAP_2}
3. {GAP_3}

## Backlog recomendado de fechamento de gap

1. {BACKLOG_1}
2. {BACKLOG_2}
3. {BACKLOG_3}

## Conclusao

{CONCLUSION}
