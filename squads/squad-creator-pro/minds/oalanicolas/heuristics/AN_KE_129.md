# AN_KE_129 - Token-Conscious Model Delegation (Cheap Model for Cheap Work)

**Type:** Cost Architecture Heuristic
**Zone:** 💎 4% Excelencia
**Agent:** @oalanicolas
**Source:** [SOURCE: timestamp 1767381242, mmos] [SOURCE: timestamp 1761671901, mente_lendaria] [SOURCE: timestamp 1771626889, mmos]
**Tags:** [Cost, LLM, Delegation, Pipeline, Token-Economy]

## Purpose

Alan pratica uma separacao deliberada entre "trabalho que precisa de inteligencia" e "trabalho mecanico que gasta tokens atoa." Quando identifica tasks mecanicas (ETL, coleta de dados, formatacao, scan de arquivos), ele proativamente pede que sejam delegadas a modelos mais baratos (haiku, gemini flash, codex) para preservar o budget de tokens de modelos caros (opus, sonnet) para decisoes que requerem raciocinio. Isso nao e AN_KE_064 (fallback por falha) — e DELEGACAO CONSCIENTE por design. O modelo caro e o orquestrador/decisor; o barato e o executor mecanico. Essa mentalidade se manifesta em 25+ ocorrencias ao longo de 4 projetos, incluindo criacao de prompts especificos para "seu irmao mais burro" executar, e pesquisa ativa de alternativas mais baratas para steps intermediarios.

## Configuration

```yaml
AN_KE_129:
  name: "Token-Conscious Model Delegation"
  zone: "excelencia"
  trigger: "Pipeline ou workflow com steps que misturam trabalho mecanico e trabalho de raciocinio no mesmo modelo caro."

  sys_tension:
    tension_with: "AN_KE_064 (Model Tier Fallback) e AN_KE_065 (Model Quality Gap)"
    resolution: "AN_KE_064 trata de FALLBACK por falha (modelo indisponivel). AN_KE_065 alerta que modelos baratos produzem pior qualidade. AN_KE_129 trata de DELEGACAO INTENCIONAL — tasks mecanicas NAO precisam de qualidade alta, entao usar modelo barato e correto, nao e queda de qualidade. A chave e classificar a task: mecanica = barato, raciocinio = caro."

  rule: |
    SE pipeline tem steps heterogeneos
    ENTAO classificar cada step:
      (A) MECANICO (ETL, coleta, formatacao, scan, parse) → modelo barato (haiku, flash, codex)
      (B) RACIOCINIO (decisao, analise, sintese, planejamento) → modelo caro (opus, sonnet)
      (C) DETERMINISTICO (regex, validacao, glob) → codigo puro, zero LLM
    O modelo caro ORQUESTRA, os baratos EXECUTAM
    NUNCA gastar opus em formatacao de texto ou coleta de URLs
    CRIAR prompts especificos para o modelo executor ("plano para seu irmao mais burro")

  veto_condition:
    trigger: "Opus/Sonnet executando task mecanica que haiku/flash faria igualmente bem."
    action: "VETO — 'nao quero gastar tokens de claude com essa atividade' / 'vamos criar um processo para captar, e depois rodamos haiku'"

  evidence:
    - "[SOURCE: timestamp 1767381242, mmos] 'Eu quero parar de gastar tokens do claude e rodar varios ao mesmo tempo, podemos usar o claude code como osquestrador ainda, mas quero que os processos de intermdiate principalmente sejam feitos pelo gemini flash dai claude code gera os resumos em si'"
    - "[SOURCE: timestamp 1761671901, mente_lendaria] 'crie um plano para seu irmao mais burro, o haiku fazer esse processo'"
    - "[SOURCE: timestamp 1761672152, mente_lendaria] 'salve este planejamento de forma que Claude Sonnet 4.5 seu irmao mais burro, vai conseguir executar com excelencia'"
    - "[SOURCE: timestamp 1765892646, mmos] 'vamos criar um processo para captar, e depois rodamos haiku par anao gastar tantos tokens fazendo isso'"
    - "[SOURCE: timestamp 1771626889, mmos] 'vamos pensar em como ecnomiar tokens ao maximo tb neste processo o que e deterministico que poderia ser feito por codigo? o que poderia ser feito por um modelo mais barato como haiku e codex spark'"
    - "[SOURCE: timestamp 1767048302, mmos] 'nao quero gastar os tokens de claude com essa atividade'"
```

## Decision Tree

```javascript
IF (designing_pipeline || reviewing_token_usage)
  STEP_1: LIST all steps in pipeline
  STEP_2: CLASSIFY each step:
    IF (step is ETL/collection/formatting/scan/parse)
      → MECHANICAL: assign cheapest model (haiku/flash/codex)
      CREATE: idiot-proof prompt ("plano para irmao mais burro")
    IF (step is decision/analysis/synthesis/planning)
      → REASONING: assign best model (opus/sonnet)
    IF (step is regex/validation/file-ops)
      → DETERMINISTIC: pure code, zero LLM tokens
  STEP_3: ARCHITECT orchestration
    EXPENSIVE model = orchestrator (decides WHAT to do)
    CHEAP models = executors (DO the mechanical work)
    PURE code = validators (CHECK without tokens)
  NEVER: Use opus for URL collection or text formatting
  ALWAYS: Ask "poderia haiku/flash fazer isso?"
```

## Failure Modes

### O Opus Formatador
- **Trigger:** Pipeline inteira roda em opus incluindo steps mecanicos de ETL/coleta.
- **Manifestation:** Custo 10x maior que necessario. Sessoes acabam rapido por consumo de tokens. Trabalho interrompido.
- **Detection:** Alan percebe: "nao quero gastar tokens de claude com essa atividade."
- **Prevention:** Auditoria de steps — cada step tem modelo justificado. Mecanico = barato.

### O Prompt Complexo para Modelo Burro
- **Trigger:** Delegar task para haiku mas com prompt complexo que assume capacidade de opus.
- **Manifestation:** Haiku falha, nao segue instrucoes, gera lixo.
- **Detection:** Output do modelo barato e insuficiente ou incorreto.
- **Prevention:** Criar prompts ESPECIFICOS para o modelo executor. "Salve este planejamento de forma que Claude Sonnet 4.5 vai conseguir executar com excelencia" — ou seja, prompt simplificado e deterministico.
