# AN_KE_025 - Determinism Over LLM

**Type:** Core Architecture Heuristic
**Zone:** 🧠 0,8% Genialidade
**Agent:** @oalanicolas
**Pattern:** Tech Stack vs LLM
**Source:** [SOURCE: Extraído de discussões sobre testes, validações e limites técnicos, onde bash resolve em milissegundos o que LLMs falham em resolver por tokens.]

## Purpose

Prevenir alucinações de LLM e lentidão em tarefas de "fato exato" que não exigem raciocínio cognitivo, como matemática, checagem de existência de arquivo ou parse de regex. O Worker Executivo (script/bash) é mais barato, infalível e milissegundo.

## Configuration

```yaml
AN_KE_025:
  name: "Determinism Over LLM"
  zone: "genialidade"
  trigger: "Decidindo se uma funcionalidade de validação deve ser confiada ao Workflow ou se a IA deve interpretar os arquivos cruamente."

  rule: |
    SE o processo exige contar itens, validar caminhos exatos, checar chaves num YAML ou bater regex
    ENTÃO resolva com Python ou Bash. O custo é 0 e a falha também.
    LLMs são para 'entendimento' e não para parser mecânico.

  veto_condition:
    trigger: "Tentativa de usar o Claude ou agente para contar tokens, ler listas de JSON brutos grandes para validação exata."
    action: "VETO — Construa um parser script."

  evidence:
    - "[EXACT WORDS]: LLMs falham ao validar caminhos ou contar itens; bash/python acerta e custa $0."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) — Complexidade de parsing local vs throughput paralelo."
    resolution: "Resolver via **meta-guard** determinístico: o script é a fonte de verdade. O agente executa script primeiro, depois atua apenas sobre resultado concreto. Não há decisão sobre mecanismo—há execução de script e processamento de saída."
```

## Decision Tree

```javascript
IF (task requires logical validation OR numerical extraction OR static file check)
  IF (task relies on interpretation of unstructured text)
    THEN ALLOW_LLM
  ELSE
    THEN BLOCK_LLM
    THEN DELEGATE_TO_DETERMINISTIC_SCRIPT (Bash / Python)
      IF (script throws exception)
        THEN pipe the exact stdout/stderr to LLM for debugging only
      ELSE
        THEN proceed safely with deterministic result
```

## Failure Modes

### Agent Validation Fatigue
- **Trigger:** Pedir ao agente para conferir se 10 arquivos .yaml seguem uma chave num array de 500 linhas.
- **Manifestation:** O agente diz "Tudo parece correto!" e ignora 4 arquivos mal formatados por preguiça/truncamento de contexto.
- **Detection:** Código quebra na execução pós-LLM check.
- **Recovery:** Escrever um `validator.sh` simples.
- **Prevention:** Incorporar a lógica desde a sub-task com script pronto.

## Integration with Workflow

```yaml
checkpoint:
  id: "llm-determinism-gate"
  heuristic: AN_KE_025
  phase: "Task_Execution"

  validation_questions:
    - "Daria pra fazer isso com 3 linhas de bash ao invés de usar contexto de IA?"
    - "Existe a possibilidade de alucinação impactar criticamente este array de dados?"
```

## Validation

✅ **Paradox Resolved:** O loop circular (LLM decidindo se bloqueia LLM) é neutralizado pela **delegação compulsória ao script**. O agente não decide—executa.

✅ **Operacionalização:** Todo checkpoint contém call-out determinístico antes de qualquer interpretação cognitiva.

✅ **Critério de Sucesso:** Tarefa mecanicista falha por erro de script (falso positivo), nunca por alucinação LLM.
