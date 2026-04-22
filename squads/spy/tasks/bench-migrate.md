# Task: Migration Playbook Generation (Autonomous)

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
id: bench-migrate
name: "Migration Playbook"
category: benchmark
agent: bench-analyst
elicit: false
autonomous: true
estimated_duration: "10-15min"
description: "Generate step-by-step migration guide from competitor framework to AIOX"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

For teams currently using a competing framework, produce a practical migration playbook
that maps every concept, command, and workflow to AIOX equivalents.

## Prerequisites

- Agent command matrix exists: `docs/bench/{competitor}/{competitor}-vs-aiox-agents-command-matrix.md`
- Workflow matrix exists: `docs/bench/{competitor}/{competitor}-vs-aiox-workflow-step-matrix.md`
- If neither exists, run `bench-quick-compare` first

## Reference

See `docs/bench/bmad/bmad-to-aiox-migration-playbook-deep.md` for output format.

---

## Step 1: Load Comparison Data

```
ACTION: Read("docs/bench/{competitor}/{competitor}-vs-aiox-agents-command-matrix.md")
EXTRACT: agent mapping table, paridade scores, gaps

ACTION: Read("docs/bench/{competitor}/{competitor}-vs-aiox-workflow-step-matrix.md")
EXTRACT: workflow mapping table, AIOX differentials

ACTION: Read("docs/bench/{competitor}/{competitor}-vs-aiox-comparativo-completo.md")
EXTRACT: inventory counts, objective reading
```

---

## Step 2: Build Agent Migration Map

For EACH competitor agent with AIOX equivalent:

```markdown
| {Competitor} | AIOX alvo | Acao de migracao |
| --- | --- | --- |
| `{comp_agent}` | `{aiox_agent}` | {migration action: "migracao direta" or specific adaptation needed} |
```

Rules:
- Paridade 5/5 → "migracao direta"
- Paridade 4/5 → "migracao direta, notar: {difference}"
- Paridade 3/5 → "adaptar: {what needs changing}"
- Paridade 2/5 or 1/5 → "substituir por: {aiox alternative} + {workaround}"
- Sem equivalente → "sem equivalente direto, emular via: {suggestion}"

---

## Step 3: Build Command Translation Table

For EACH agent pair, map commands:

```markdown
### {Agent Name}

| {Competitor} (esperado) | AIOX |
| --- | --- |
| `*{comp_command}` | `*{aiox_command}` |
```

Rules:
- Same name → direct mapping
- Different name, same purpose → map with note
- No equivalent → "sem equivalente (emular via {suggestion})"

---

## Step 4: Build Workflow Migration Map

```markdown
| {Competitor} | AIOX | Status |
| --- | --- | --- |
| `{comp_workflow}` | `{aiox_workflow}` | equivalente forte / parcial / sem arquivo nominal |
```

---

## Step 5: Build Artifact Migration Map

```markdown
| Artefato {Competitor} | Artefato AIOX equivalente |
| --- | --- |
| {comp_artifact} | {aiox_artifact} (via `{command}`) |
```

---

## Step 6: Design Migration Waves

```markdown
## Estrategia de migracao em 4 ondas

### Onda 1: Compatibilidade minima (1-2 dias)
1. Definir mapeamento de agentes na equipe
2. Fixar workflow core equivalente
3. Treinar comandos base

### Onda 2: Paridade operacional (2-4 dias)
1. Validar quality gates
2. Rodar um ciclo greenfield e um brownfield completo
3. Ajustar diferencas de nomenclatura

### Onda 3: Ganhos AIOX (3-7 dias)
1. Introduzir agentes exclusivos AIOX ({list})
2. Adotar workflows exclusivos ({list})
3. Ativar automacao adicional

### Onda 4: Otimizacao e governanca (continuo)
1. Medir throughput e taxa de retrabalho
2. Padronizar handoffs
3. Customizar squad para dominio
```

---

## Step 7: Generate Risk Checklists

```markdown
## Checklists de risco

### Checklist tecnico
- [ ] Todos os agentes core mapeados e testados
- [ ] Workflows core validados em projeto piloto
- [ ] Quality gates obrigatorios ativados
- [ ] Paridade por IDE validada

### Checklist de processo
- [ ] Time conhece diferencas de nomenclatura
- [ ] Fluxo de QA documentado
- [ ] Criterios de "done" alinhados com gate QA

## Gaps esperados durante migracao
{list from comparison data}

## Backlog recomendado de fechamento de gap
{actionable items}
```

---

## Step 8: Write Output

**OUTPUT:** Write `docs/bench/{competitor}/{competitor}-to-aiox-migration-playbook-deep.md`

Full structure:
1. Objetivo
2. Premissas
3. Mapeamento de agentes (pratico)
4. Mapeamento de workflows core
5. Traducao de comandos (nucleo)
6. Mapeamento de artefatos
7. Estrategia de migracao em 4 ondas
8. Checklists de risco
9. Gaps esperados
10. Backlog de fechamento
11. Conclusao

---

## Outputs

| File | Format |
|------|--------|
| `{competitor}-to-aiox-migration-playbook-deep.md` | MD |

## Verification

- [ ] Every competitor agent has migration path
- [ ] Every core command has translation
- [ ] Waves are actionable (not generic)
- [ ] Risk checklists are specific to this competitor
- [ ] Gap backlog has concrete items
