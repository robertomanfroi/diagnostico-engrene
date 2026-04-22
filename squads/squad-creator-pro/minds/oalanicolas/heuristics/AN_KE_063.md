# AN_KE_063 - Full Document Context Requirement
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: 17+ instâncias cross-project (mmos, aiox-core, sinkra-hub) — "leia tudo antes"]

## Purpose

A regra imperativa "nunca leia pela metade" reflete a intolerância a erros causados por falta de escopo. LLMs tipicamente tentam otimizar tokens lendo fragmentos (e.g., `Read 50 lines`), agindo precipitadamente sobre informações parciais. Alan exige que o contexto COMPLETO seja absorvido ANTES de qualquer implementação (seja um design, uma task list, ou um arquivo de código). Metade do conhecimento = decisões erradas = retrabalho. O investimento de tempo (ou tokens) inicial na leitura completa previne a miopia de contexto que gera regressões.

## Configuration

```yaml
AN_KE_063:
  name: "Full Document Context Requirement"
  zone: "excelencia"
  trigger: "Quando solicitado para ler um arquivo, revisar documentação ou antes de iniciar uma alteração baseado em arquivos de referência."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Complete contextual understanding"
    resolution: "Invest upfront in complete reading (higher token cost) to prevent costly rework and misalignment (exponential cost increase). Full context first, optimize later."

  rule: |
    SE você precisar ler um documento ou arquivo
    ENTÃO LER na sua integridade (100%), do início ao fim.
    NUNCA usar leitura paginada parcial para iniciar as modificações.
    SE o arquivo for grande, LER TUDO primeiro, depois processar e planejar.
    Ler documento pela metade resulta em agir sobre pressupostos incorretos.

  veto_condition:
    trigger: "Agente lê apenas as primeiras 50 linhas de um arquivo e começa a propor ou realizar modificações."
    action: "VETO — 'O que eu falei de nunca ler uma rquivo pela metade? leia eles na integrridade'."

  evidence:
    - "[SOURCE: sessão 06009677, mmos] 'Como fazemos voce SEMPRE ler o documento inteiro, nunca em hipose alguma ler s/o um pedaço dele?'"
    - "[SOURCE: sessão 1d8402a1, mmos] 'O que eu falei de nunca ler uma rquivo pela metade? Read(components/ui/optimized-image.tsx) ⎿  Read 50 lines'"
    - "[SOURCE: sessão 1340ec7d, mmos] 'Leia tudo antes de continuar alterações'"
    - "[SOURCE: sessão 64375ac7, aiox-core] 'eu já tinha feito isso tem certeza que tem falha nele? leia tudo antes de reescrecer'"
    - "[SOURCE: sessão f6e6396a, aiox-core] 'Leia 100% TODOs os 20 documentos antes de qualquer coisa'"
```

## Decision Tree

```javascript
IF (task_requires_reading_file_or_document)
  STEP_1: CHECK file size and intention
  STEP_2: READ file to end (100% completeness)
    IF (agent reads partial chunk) → REJECT partial state
    THEN CONTINUE reading until EOF
  STEP_3: ANALYZE full context
  STEP_4: ONLY THEN start planning or executing changes
    IF (modification proposed before EOF) → STOP, finish reading
```

## Failure Modes

### O Arquiteto Apressado
- **Trigger:** Arquivo de `optimized-image.tsx` é aberto, agente vê as props iniciais e já altera as tipagens, quebrando dependências nas últimas linhas que não foram lidas.
- **Manifestation:** "O que eu falei de nunca ler uma rquivo pela metade?"
- **Detection:** Analisar tool call `Read` ou `view_file` que tem limite de linhas e nenhuma chamada subsequente completando o arquivo.
- **Prevention:** Obrigatório ler do registro inicial até a linha final antes de editar.

## Validation

**Paradoxo Identificado:**
O custo imediato (tokens consumidos na leitura completa) parece mais alto, mas o custo real (rework, regressões, erros cascata) é exponencialmente maior quando contexto é parcial. Alan executa a heurística "leia tudo primeiro" porque reconhece que otimização pré-matura de tokens leva a otimização sub-ótima de resultados.

**Critério de Conformidade:**
- ✅ Agent reads entire file before proposing changes
- ✅ No partial-view tool calls followed by Edit/modifications without completing the read
- ✅ Full context analyzed before any planning decision
- ✅ Token investment in complete reading prevents rework cycles

**Escalação:**
Se agente violar (partial read → immediate modification), ativar veto_condition e retornar à leitura integral.
