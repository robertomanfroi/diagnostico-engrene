# AN_KE_039 - Checkpoint Categórico de Modelos Mentais

**Type:** Context Protection Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Forçamento Dinâmico na Janela de Contexto
**Source:** [SOURCE: Extraído de "Mega Handoffs" apontando um erro drástico onde o LLM simplesmente esquecia tudo o que havia aprendido nas SOPs.]

## Purpose

Modelos mentais gravados numa wiki global morrem no esquecimento se não forem evocados. Durante tarefas profundas (coding, strategy design), os Agentes tenderem a agir de fábrica. Obrigar a evocação dos modelos da base destrava o verdadeiro valor do DNA intelectual preservado naquele projeto.

## Configuration

```yaml
AN_KE_039:
  name: "Checkpoint Categórico de Modelos Mentais"
  zone: "excelencia"
  trigger: "Estruturando tarefas sequenciais longas onde o risco de perda de aderência ao DNA do expert é elevado (Amnésia por contexto cheio)."

  rule: |
    SE há Agentes assumindo posições chave de raciocínio onde a filosofia interna de Alan (e experts copiados) importam
    ENTÃO institua um 'Checkpoint Gate'. O sistema deve obrigar fisicamente o Agente a acionar a "Leitura do Modelo Mental / Heurísticas de Base" periodicamente na execução em cascata.

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Sequencialismo de Validação"
    resolution: "Checkpoints devem ler modelos mentais ANTES de engulir grandes volumes de dados externos. Limitar tokens de entrada antes do checkpoint, não depois."

  veto_condition:
    trigger: "Criar um batch iterativo de 50 ações em background que rodam à revelia dos princípios de design originais documentados no root."
    action: "VETO — Insira micro-consultas (forcing functions) à base lógica dentro das Phases estipuladas."

  evidence:
    - "[EXACT WORDS]: Problema descoberto: Modelos mentais estão SOLTOS das tasks. Próxima sessão: Criar checkpoints dentro das tasks que FORÇAM consulta aos modelos mentais."
```

## Decision Tree

```javascript
IF (large_continuous_task OR executing_generative_work_sequence)
  IF (task_does_not_contain_read_heuristics_command)
    THEN BLOCK_EXECUTION
    THEN INJECT_CHECKPOINT ("No Passo 4, antes da síntese, invoque/analise o arquivo 'oalanicolas.md' mental_models para afinar escolhas de design.")
      IF (checkpoint successfully enforces LLM to context-load the file)
        THEN proceed to Step 5 (Generation with mental overlay)
  ELSE
    // Explicit grounding ensures high-fidelity output
    THEN ALLOW
```

## Failure Modes

### A Diluição por Token Overload
- **Trigger:** Ao pesquisar grandes quantidades de sites da web via Firecrawl no meio da pesquisa.
- **Manifestation:** Depois de ler 20 mil palavras de concorrentes banais, a IA responde exatamente igual a eles, sem qualquer resquício do gênio socrático e da personalidade do framework do autor. A entropia diluiu sua voz no mar de tokens inúteis consumidos pela API.
- **Detection:** Leitura da revisão mostra que está medíocre e "corporate-friendly".
- **Recovery:** Parar, evocar a diretiva de DNA ("Lembre-se da regra: 40% da voz é conflito com opiniões óbvias") e gerar a síntese novamente.
- **Prevention:** Veto-Gates ao longo do Workflow exigindo o preenchimento de templates "Estou Honrando o Mental Model XXX?".

## Integration with Workflow

```yaml
checkpoint:
  id: "mental-models-grounding"
  heuristic: AN_KE_039
  phase: "Continuous_Sprints / Synthesis"
```

## Validation

- ✅ Paradoxo Identificado: Forçar evocação de modelos mentais vs. dilui-los via token overload
- ✅ Resolução: Pré-filtrar entrada antes de aplicar checkpoints (evita amplificar o problema)
- ✅ Implementação: Adicionar limite de tokens-de-entrada ao Decision Tree (Step 0)
- ✅ Monitoramento: Detectar quando recovery é necessário via sinais de "output corporativo"
