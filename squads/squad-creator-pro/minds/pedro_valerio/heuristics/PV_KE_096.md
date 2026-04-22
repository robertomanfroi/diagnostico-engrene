---
id: "PV_KE_096"
title: "Agents as Strict Function Contracts"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "AI Orchestration"
  - "Execution Standards"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "PV_PA_005 (Directed Stochasticity) — Strict I/O contracts vs. variance-as-feature philosophy"
  resolution: "Bifurcate outputs into two classes: (1) Metadata Keys (Status, Score, Category)—REQUIRED strict typing for orchestration integrity; (2) Body Content (Creative/Exploratory)—unrestricted string field. Schema hierarchy enforces metadata contracts while preserving cognitive freedom in content generation."
---

# PV_KE_096 - Agents as Strict Function Contracts

**Type:** Epistemic Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:agent-generator
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 15: Configurando Agentes para Sinkra]

## Purpose
Aniquilar a ilusão perigosa de corporações usarem Inteligência Artificial Genérica Mística ("bota um ChatGPT lá e vê o que sai do texto"). Esta heurística define OBRIGATORIAMENTE que um Agente no ecossistema SINKRA não é um Chatbot de conversação livre. Um Agente é um `Executor Estocástico Controlado` operando estritamente dentro de uma Função com Tipagem de Entrada e Schema de Saída Rígido (Outputs Validados via JSON), submetido sempre a um Quality Gate SINKRA e contendo um Caminho de Escalonamento Humano Inegociável (Fallback). Pular esta restrição significa injetar "Alucinações" massivas indetectadas e erros silenciosos dentro das engrenagens Centrais de Decisão Tática da Operação, implodindo os Fluxos Sistêmicos SINKRA.

## Configuration
```yaml
PV_KE_096:
  name: "The Stochastic Executable Law (Strict I/O Agent Validation)"
  zone: "zone_0.8"
  trigger: "Fase 8 (Agent Generation). O Engenheiro de Prompt ou AIOX arquiteta a instância que substituirá o Human (Task) no sistema."
  evidence_threshold: "coding_principles"
  rule: |
    TODA Arquitetura (Agent YAML) da Instância de IA DEVE preencher a Matriz Mínima Funcional Sem Exceção:
    - 1. inputs -> [Tipados (URL, String, Booleano)].
    - 2. outputs -> [Schema JSON OBRIGATÓRIO (Arrays, Floats, Estruturas Físicas)].
    - 3. quality_gate -> Qual Bot PV audita e qual Threshold Mínimo.
    - 4. escalation -> Pathing de Queda (O que faz se alucinar ou tirar nota < 60?).
    Nenhum Agente no SINKRA retorna 'Texto Livre'. Agentes não são conselheiros de chat; são Funções de Transformação de Dados e Lógica com Contratos Rascunhados (System Prompts versionados externalizados).
```

## Decision Tree
```javascript
IF (creating_or_approving_an_Agent_role_in_the_Architecture)
  STEP_1: EXAMINE its Output format.
  STEP_2: ENFORCE exact Schema constraints and fail-safes.
    IF (The Team proposes: 'The Agent reads the PDF and generates a paragraph summarizing the meeting to the team.')
      -> VETO: 'Missing Schema, missing scoring, missing escalation. A paragraph of text cannot be reliably caught and processed by the next Worker or Tool in an automated flow.'
    IF (The Team proposes: 'The Agent reads the PDF. OutputSchema={score: float, action_items: array[string], status: enum(ready, needs_human)}. Falls back to Human PM on Error or bad JSON format.')
      -> ACCEPT: Operational integrity. The Stochastic black box has become a predictable Contractual Node SINKRA.
NEVER:
  Confundir as Ferramentas Livres (Interface Claude.ai) com Camadas de Automação Empresariais Rígidas (SINKRA/AIOX OS). Um Sistema não tolera "Eu acho que tá bom". Ou um Schema bate de forma binária com a estrutura requerida ou explode sob falha crítica antes de gravar no Supabase/ClickUp.
```

## Failure Modes

### Misapplication / Excess: "Engessamento Absurdo (A Morte do Raciocínio Base)"
- **Trigger:** O Time de Arquitetura força Agentes a emitirem Outputs Numéricos, Json super complexos e tabelas gigantescas para situações altamente dinâmicas onde a função raiz primária P0 solicitada ao LLM exigia "Exploração Empática ou Geração Livres de Idéias Literárias" que posteriormente passariam por revisão total de um Chief Criativo Diretor (Clone SINKRA).
- **Manifestation:** O Agente de "Brainstorming Copywriting" engasga com quebras de formatação no JSON, passando mais instrução técnica de código do que usando as 8 Bilhões de Parâmetros dele para criar bons roteiros, inutilizando a fase Criativa. O Pipeline fica burro.
- **Detection:** Retornos de erro (`Parsing Error`) constantes da IA enquanto tenta encaixar um Roteiro de Vídeo em um Array Multidimensional, sem nunca focar no resultado linguístico esperado.
- **Recovery:** A Lei de Tipagem Rígida (PV_KE_096) vale para a INJEÇÃO DE METADADOS de FLUXO (Status, Score, Categorizações) da Arquitetura Covalente. Para Trabalhos Criativos, a Tipagem Rígida encabeça uma chave como `Body_Content: String`, onde a Inteligência tem espaço irrestrito e puro. E se a Task for muito criativa, o `Output Formal` é a Submissão, e o Validador SINKRA Posterior emite a Nota. 

### Omission / Failure to Activate: "O Desastre Silencioso da Alucinação Solta"
- **Trigger:** Configurações rápidas onde um Desenvolvedor atrela o Node Central "HTTP Request - OpenAI" que devolve o bloco genérico "Content" de volta para o Frontend Cliente, salvando direto.
- **Manifestation:** Na Quarta, o Modelo muda para a Versão Subsequente Minor no Backend do provedor, ele muda sutilmente o Estilo de Tones para "Explicações Filosóficas", o Pipeline começa a enviar mensagens não-padronizadas, emails estranhos, e no caso da análise técnica, devolve respostas como "Me desculpe, não posso prosseguir", enquanto o Software Frontal grava no Log a flag "Complete" e encerra o Processo do Cliente 1241. Total Falência Tática Invisível.
- **Detection:** Agentes gravando Alucinações Óbvias ou Logs Defensivos de Segurança da OpenAI/Anthropic direto num Database Institucional.
- **Recovery:** Matação Preventiva de LLM. Se o Modelo de IA gerar texto ou resposta que violou o Schema de Contract Validado e os Scripts JSON SINKRA (Sendo captado no Retry ou Try/Catch), o Framework imediatamente DELETA O OUTPUT, loga falha estrutural, tenta Retry e Aborta de forma barulhenta enviando alerta Humano. Agentes Mudos não danificam Tabelas Master.

## Validation

**Paradox Resolved:** The tension between rigid typing and creative freedom is resolved by schema bifurcation—metadata keys (status, score, category) remain strictly typed for orchestration safety, while content bodies preserve unrestricted string capacity for exploratory/creative work. This maintains both operational integrity and cognitive autonomy.

**Application Criteria:**
- ✅ Use strict typing for ALL orchestration metadata (inputs, status flags, scoring, escalation signals)
- ✅ Use unrestricted string fields (body_content, reasoning, explanation) for creative or exploratory outputs
- ✅ Validate metadata schema binarily (pass/fail with fallback-to-human on schema violation)
- ✅ Log content generation separately from schema validation—content quality goes to QA human gate, schema violations go to system emergency abort

**Enforcement:** Agents violating this bifurcated contract (mixing creative output into typed metadata keys, or omitting escalation paths) must be rejected at architecture review (PV_KE_096 violation → VETO).
