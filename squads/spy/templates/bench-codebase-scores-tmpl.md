# Benchmark Pratico - {COMPETITOR} vs AIOX ({SCENARIO_COUNT} Cenarios)

Data: {DATE}

## Metodo

- Benchmark {METHOD_TYPE}: **{METHOD_DESCRIPTION}**.
- Cenarios: {SCENARIOS_LIST}.
- {METHOD_DISCLAIMER}

## Medicoes executadas (AIOX)

- validate:parity: {PARITY_RESULT}
- {ACTIVATION_METRICS}

## Resultado por cenario

{FOR_EACH_SCENARIO}
### {SCENARIO_NAME}

| Eixo | AIOX | {COMPETITOR} | Delta (AIOX-{COMPETITOR}) |
| --- | ---: | ---: | ---: |
| Delivery Control | {AIOX_CONTROL} | {COMP_CONTROL} | {DELTA_CONTROL} |
| QA Strength | {AIOX_QA} | {COMP_QA} | {DELTA_QA} |
| Automation Index | {AIOX_AUTO} | {COMP_AUTO} | {DELTA_AUTO} |
| Orchestration Depth | {AIOX_DEPTH} | {COMP_DEPTH} | {DELTA_DEPTH} |
| Drift Risk (menor melhor) | {AIOX_DRIFT} | {COMP_DRIFT} | {DELTA_DRIFT} |

Metrica estrutural observada:

- AIOX: steps={AIOX_STEPS}, agents={AIOX_AGENTS}, outputs={AIOX_OUTPUTS}, decision_points={AIOX_DECISIONS}
- {COMPETITOR}: steps={COMP_STEPS}, agents={COMP_AGENTS}, outputs={COMP_OUTPUTS}, decision_points={COMP_DECISIONS}
{END_FOR_EACH}

## Leitura objetiva

{OBJECTIVE_READING}

## Arquivos gerados

{GENERATED_FILES_LIST}
