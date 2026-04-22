---
id: "PV_KE_087"
title: "The Automation Tipping Point Guardrail (PV_PM_001 Elimination)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Workflow Design"
  - "Execution Standards"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "PV_PA_017 (Variance as a Feature) vs Guardrails Rigorosos"
  resolution: "Guardrails rigorosos aplicam-se APENAS a AUTOMATE/DELEGATE; julgamento humano em KEEP_MANUAL preserva discernimento natural sem cartilha mecânica."
---

# PV_KE_087 - The Automation Tipping Point Guardrail (PV_PM_001 Elimination)

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:workflow-designer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 14: Fase 4 - Workflows / Checkpoint PV_PM_001]

## Purpose
Matar pela raiz a febre da Automação Irresponsável e da Burocracia Fóssil. Esta heurística (Checkpoint PV_PM_001) intercepta processos antes que virem fluxos operacionais (Phase 4), e testa o Guardrail da Automação (Se você quer criar uma automação, ela possui pré-condição explícita, pós-condição explícita, error handling em nível estrutural e fallback?). Além disso, a heurística exige o expurgo (ELIMINATE) de Tasks que rodem menos de 2 vezes no mês ou não justifiquem o investimento cognitivo. O Output mais valioso do PV_PM_001 não é Automatizar, é Excluir; a task não automatiza nem retrocede para o Humano: desaparece do sistema.

## Configuration
```yaml
PV_KE_087:
  name: "Ruthless Tipping Point & Elimination"
  zone: "zone_0.8"
  trigger: "Fase 4 (Workflows) do pipeline SINKRA. Quando o Workflow Designer transforma atribuições de Executores (Fase 3) em Sequências de Ações Reais e Automações (Workflows)."
  evidence_threshold: "structural_logic"
  rule: |
    O Checkpoint PV_PM_001 DEVE avaliar toda Automação proposta em três eixos:
    1. Frequência Operacional: Task <= 2x mês com impacto não crítico? (ELIMINATE)
    2. Guardrails (Pre, Post, Error, Fallback): Estão zerados ou dúbios? (VETO - Automação Mística Bloqueada).
    3. Padronização >= 0.7: O input/output é repetível?
    O Output do PV_PM_001 bifurca a realidade em 4 nós canônicos e estritos:
      a) AUTOMATE (Worker): Deterministico, Volume+, Guardrails+.
      b) DELEGATE (Agent): Contextual, Volume M, Guardrails+.
      c) KEEP_MANUAL (Human): Julgamento Crítico Insbstituível.
      d) ELIMINATE: Remoção Físca, Extirpação Histórica da Task Existente.
```

## Decision Tree
```javascript
IF (evaluating_a_task_for_operationalization_via_workflow)
  STEP_1: EXAMINE its frequency and impact.
  STEP_2: EVALUATE the explicit definition of 'How it breaks' (Guardrails).
    IF (Frequency is 1x / year AND Impact doesn't justify maintaining an explicit robotic route)
      -> ELIMINATE: The task is Fossil Bureaucracy. Delete from the process.
    IF (Workflow states 'Agent generates report', but contains NO limits, NO rejection criteria, and NO strict JSON format)
      -> VETO: 'Automation without guardrails is a wish, not a workflow.' Halts the phase 4. Return to designer.
    IF (Task is Deterministic, High Volume, and Full Guardrails present)
      -> AUTOMATE: Hand off to Worker.
NEVER:
  Automatizar uma tarefa apenas "para não ter que fazer". Automação exige contrato (Guardrails). Sem contrato explícito, é muito mais barato e seguro manter um humano falho (KEEP_MANUAL), que pelo menos tem bom senso natural, do que invocar um autômato burro cego sem trilho de escape que destruirá uma base de dados inteira se a API externa cair e ele não tiver um fallback.
```

## Failure Modes

### Misapplication / Excess: "O Fundamentalismo do Guardrail Micro"
- **Trigger:** O Time aplica a heurística PV_PM_001 a tarefas Humano-only altamente subjetivas ("Conversar com a Equipe de Criação por 15min"), exigindo `error handling` algorítmico num bate-papo, `retry logic` mental e rejeitando a Workflow com base em burocracia desmedida.
- **Manifestation:** Todos os `KEEP_MANUAL` humanos agora precisam de uma cartilha mecânica gigantesca e o PV_PM_001 bloqueia interações vitais informais. O Mapeamento tranca porque a criatividade e a negociação (Human) foram avaliadas pelo mesmo prisma de um Endpoint REST.
- **Detection:** Reclamações que a empresa virou uma "Tirania Robótica" onde ninguém consegue preencher as `pre-conditions` de um Telefonema.
- **Recovery:** Os Guardrails Severos (Error handling literal, retry logic de N vezes, fallback estrutural algorítmico) são EXIGÊNCIAS INEGOCIÁVEIS APENAS PARA `AUTOMATE (Worker)` e `DELEGATE (Agent/Clone)`. O julgamento humano (`KEEP_MANUAL`) usa as proteções do Nível de Organismo e o discernimento natural Humano.

### Omission / Failure to Activate: "O Processo Lixão e o Robô Surto"
- **Trigger:** A Equipe ignora o modo `ELIMINATE` e o Módulo de `Guardrails` (Automação Mística), construindo fluxos para a Nuvem recheados de Nodes que não checam as Post-conditions.
- **Manifestation:** A empresa continua rodando Tasks irrelevantes do Século Passado (Fóssil Burocrata) que ocupam banda, mas que acabaram virando Automações Caras rodando só 1x ao ano e gerando erros silenciosos sempre que a API muda. Ou, pior: O Workflow do Worker roda de forma falha, a API dá Timeout, ele não tem Retry, o cliente recebe um email quebrado, ninguém é notificado, não há fall-back e o Workflow finge que concluiu.
- **Detection:** Perdas processuais dramáticas causadas por "Erro Silencioso" num fluxo zumbi que o time esqueceu de pôr `alert_on_failure` porque o Checkpoint (PV_PM_001) da Fase 4 foi passado por Bypass.
- **Recovery:** Auditar todos os Workflows em produção. Se existir um `Worker` ou `Agent` executando no Mapeamento sem os campos algorítmicos e lógicos de `Pre-conditions` e `Fallback/Error Handling` explicitamente digitados, a Automação deve ser sumariamente suspensa (Suspende Operação) até ser adequada ou realocada para Humano.

---

## Validation

**Paradoxo Central (sys_tension):** A heurística PV_KE_087 traz uma tensão estrutural entre dois imperativos aparentemente contraditórios:
- **Tese:** Automação requer guardrails rigorosos (pré-condições, pós-condições, error handling, fallback), senão é "automação mística" — uma bomba-relógio.
- **Antítese:** Aplicar a mesma lógica algorítmica a trabalho humano criativo/contextual (telefonemas, negociações, conversas) transforma a organização em "tirania robótica" onde o discernimento natural fica preso em cartilhas mecânicas inúteis.

**Resolução:** O Checkpoint PV_PM_001 diferencia **modos de execução**:
1. **AUTOMATE** (Worker) → Guardrails RIGOROSOS (algorítmicos)
2. **DELEGATE** (Agent/Clone) → Guardrails ESTRUTURAIS (lógicos)
3. **KEEP_MANUAL** (Human) → Proteções do Nível de Organismo (discernimento natural)
4. **ELIMINATE** → Remoção física (não resolvível via automação)

A heurística é válida quando: (a) diferencia claramente os modos, (b) aplica rigor apenas a AUTOMATE/DELEGATE, (c) preserva flexibilidade humana em KEEP_MANUAL, e (d) força o expurgo radical (ELIMINATE) de tarefas fósseis que consomem banda sem ROI justificável.
