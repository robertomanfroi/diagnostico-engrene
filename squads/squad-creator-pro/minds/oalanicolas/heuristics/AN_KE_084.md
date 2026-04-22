# AN_KE_084 - Foundation Complete Before Building
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão mmos 22650c09 — completar base antes de avançar]

## Purpose

Completar uma camada 100% antes de construir a próxima. Drivers e tools 100% ANTES de correlações. Schema 100% ANTES de seeds. Base instável = tudo em cima treme.

## Configuration

```yaml
AN_KE_084:
  name: "Foundation Complete Before Building"
  zone: "excelencia"
  trigger: "Projeto multi-camada onde camada N+1 depende de camada N."

  rule: |
    SE projeto tem camadas de dependência (schema → seeds → UI → tests)
    ENTÃO completar camada N a 100% ANTES de começar N+1.
    "eu quero preparar antes 100% o drivers e tools, e depois começar as correlações"

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs sequência mandatória de camadas"
    resolution: "100% completude na camada atual significa: schema validado + drivers testados + correlações mapeadas. 'Aproveitar dados existentes' refere-se a reutilizar estruturas já 100% completas, nunca a usar camadas parcialmente prontas. A transição entre camadas é binária: camada N = 100% (gate passa) ou camada N < 100% (gate falha, não avança)."

  evidence:
    - "[SOURCE: sessão 22650c09] 'eu quero preparar antes 100% o drivers e tools, e depois começar as correlações, antes de avançar no resto'"
    - "[SOURCE: sessão 77b3afff] 'a ideia é nao criar nenhuma nova coluna muito menos tabela, vamos primeiro aproveitar esses dados'"
```

## Decision Tree

```javascript
IF (project_has_dependency_layers)
  STEP_1: IDENTIFY layer order
    L0: Schema/Data model → MUST be 100% before L1
    L1: Seeds/Sample data → MUST be 100% before L2
    L2: Backend logic → MUST be 100% before L3
    L3: UI/Frontend → builds on stable backend
  STEP_2: VALIDATE current layer completeness
    IF (current_layer < 100%) → COMPLETE it first
    IF (current_layer = 100%) → proceed to next
  NEVER: start L3 while L1 is still 80%
  PREFER: aproveit existing data before creating new columns/tables
```

## Failure Modes

### O UI que Treme
- **Trigger:** Frontend built on schema that keeps changing.
- **Manifestation:** Every schema change breaks 3 UI components. Constant rework.
- **Detection:** > 2 schema changes AFTER UI started. Frontend PR requires backend PR.
- **Prevention:** "preparar 100% drivers e tools primeiro, depois começar correlações."

## Validation

**Checklist para garantir camada N a 100% antes de avançar:**

- [ ] Schema: Todas as tabelas definidas, tipos validados, constraints aplicadas
- [ ] Drivers: APIs/funções de acesso testadas e funcionando 100%
- [ ] Correlações: Relacionamentos entre entidades mapeados e validados
- [ ] Seeds: Dados de teste ou iniciais carregados e verificados
- [ ] Tests: Cobertura mínima 80% da camada atual
- [ ] Gate Review: Aprovação explícita (não implícita) para avançar à camada N+1

**Paradoxo Resolvido:** "Completude antes de avançar" ≠ "nunca reutilizar". Significa: estruturas prontas + validadas + testadas = seguras para reutilizar. Aproveitar existente = reuso controlado de camadas 100% completas, não de WIP.
