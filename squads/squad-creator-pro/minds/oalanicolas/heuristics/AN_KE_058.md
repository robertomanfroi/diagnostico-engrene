# AN_KE_058 - Verify LLM Output

**Type:** Data Quality Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Sanity Check + Verificação Externa
**Source:** [SOURCE: Sessões mmos 8872d121, c46a77a7, 5e996e85 — problemas com dados inventados e quantidades absurdas]

## Purpose

LLMs inventam dados, inflam quantidades e apresentam ficção como fato. Dois mecanismos de defesa: (1) sanity check numérico — se output >> esperado, algo está errado; (2) verificação externa — pesquisar na internet antes de confiar.

## Configuration

```yaml
AN_KE_058:
  name: "Verify LLM Output"
  zone: "impacto"
  trigger: "LLM gerando dados factuais, extraindo informações, ou produzindo quantidades."
  sys_tension:
    tension_with: "AN_KE_025 (Determinism Over LLM) — Verificação externa delegada ao LLM reintroduz dependência do mesmo agente que fabricou os dados. Solução: usar MCPs (Exa, scrapling) ou fontes primárias em vez de LLM para validação."
    resolution: "Desacoplar: (1) sanity check por humano o sistema automatizado independiente; (2) verificación externa por MCP (Exa, scrapling) o consulta manual a fuentes primarias, NUNCA LLM."

  rule: |
    SE LLM gera dados factuais ou extrai informação
    ENTÃO dois checks obrigatórios:
    1. SANITY CHECK: output é proporcional ao input? (12 QAs ≠ 1000+ fragmentos)
    2. VERIFICAÇÃO EXTERNA: pesquisar internet para confirmar fatos críticos (via MCP ou fonte primária, NÃO via LLM).
    SE quantidade >> esperada → algo está errado, investigar antes de aceitar.

  veto_condition:
    trigger: "Aceitar dataset gerado por LLM sem sanity check ou verificação externa independente."
    action: "VETO — Verificar proporção input/output (critério humanizado) e confirmar fatos em fonte primária (MCP ou pesquisa manual)."

  evidence:
    - "[SOURCE: sessão 8872d121] 'sempre faça pesquisas na internet para confirmar a veracidade'"
    - "[SOURCE: sessão c46a77a7] 'tem algo mt errado nao deveria ser possivel extrair tantos fragmentos de apenas 12 qa'"
    - "[SOURCE: sessão 5e996e85] 'use multiplos agentes em paralelo para este preenchimento e sempre pesquise na internet se tiver alguma dúvida, precisamos ter dados confiáveis nesse dataset'"
```

## Decision Tree

```javascript
IF (llm_generates_factual_data OR extracts_quantities)
  STEP 1: SANITY_CHECK
    IF (output_count / input_count > expected_ratio)
      THEN FLAG — "Quantidade desproporcional ao input"
      THEN INVESTIGATE before accepting
  STEP 2: EXTERNAL_VERIFY (for critical facts)
    IF (data_will_be_used_in_production OR customer_facing)
      THEN REQUIRE internet search verification
    IF (internal_only AND non_critical)
      THEN sanity check is sufficient
```

## Failure Modes

### O Dataset Inflado
- **Trigger:** LLM extrai "fragmentos de conhecimento" de 12 QAs e produz 1.292 entradas.
- **Manifestation:** Banco inflado com dados duplicados, inventados ou extrapolados.
- **Detection:** Proporção input/output absurda (12→1292 = 107x).
- **Recovery:** Purge + re-extração com limites explícitos.
- **Prevention:** Sanity check antes de persistir: "12 QAs × ~10 fragmentos max = ~120. Se >200, investigar."

## Integration with Workflow

```yaml
checkpoint:
  id: "llm-output-verification-gate"
  heuristic: AN_KE_058
  phase: "Data_Extraction / Dataset_Building"
```

## Validation

✓ **Paradoxo identificado:** Confiança circular em LLM para verificar dados gerados pelo LLM.
✓ **Resolução documentada:** Desacoplar verificação externa para MCPs (Exa, scrapling) ou fontes primárias.
✓ **sys_tension adicionado:** Descreve a tensão e oferece caminho de resolução.
✓ **Implementação:** Sanity check humanizado + verificação externa independente = defense-in-depth.
