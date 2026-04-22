# Task: Bench Matrix — LLM

## Contrato SINKRA

Domain: `Tactical`

task: benchMatrixLLM()
responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- `inventory_a`
- `inventory_b`
- `output_dir`
Saida:
- matriz llm JSON/MD
Checklist:
- comparar specs, benchmarks e capabilities
- explicitar vantagem por dimensão
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata

```yaml
id: bench-matrix-llm
parent_task: bench-matrix
category: benchmark-matrix-atom
agent: bench-analyst
elicit: false
autonomous: true
description: "Constrói a matriz comparativa para modelos de linguagem."
```

## Steps

1. Comparar contexto, preço, cutoff e outputs.
2. Comparar benchmarks disponíveis e capacidades.
3. Sinalizar vantagem de A, B, empate ou desconhecido.
4. Persistir matriz final em JSON + MD.

## Acceptance Criteria

- specs e capabilities cobertas
- benchmarks citados com fonte
- lacunas marcadas como `unknown`, nunca inventadas

---

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
