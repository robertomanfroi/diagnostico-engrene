# Task: Bench Report — Load Evidence

## Contrato SINKRA

Domain: `Strategic`

task: benchReportLoadEvidence()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- `output_dir`
- artefatos upstream do benchmark
Saida:
- evidence bundle validado
Checklist:
- checar presença dos artefatos obrigatórios
- detectar inconsistências antes da síntese
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-report-load-evidence
parent_task: bench-report
category: benchmark-report-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Carrega e valida o pacote de evidências antes da síntese executiva."
```

## Steps

1. Carregar matrix, score, gap e deep artifacts relevantes.
2. Validar presença e consistência básica dos números.
3. Montar evidence bundle normalizado.
4. Registrar faltas ou discrepâncias.

## Acceptance Criteria

- evidence bundle completo
- discrepâncias explicitadas
- síntese downstream não depende de dados implícitos

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
