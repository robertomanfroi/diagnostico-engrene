---
id: "PV_KE_075"
title: "A Árvore de Roteamento de Executor (Executor Routing Tree)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Resource Allocation"
  - "Delegation Logic"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "AN_KE_073 (Parallel Subagents for Throughput)"
  resolution: "Executor Routing Tree impõe sequência Bottom-Up estrita (Worker → Agent → Clone → Human) para otimizar custo-benefício. Paralelização viola esta precedência obrigatória. Resolver: usar paralelismo DENTRO de cada nível (múltiplos Workers em paralelo se determinístico), não entre níveis."
---

# PV_KE_075 - A Árvore de Roteamento de Executor (Executor Routing Tree)

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:architecture-designer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 12: Executor Decision Tree]

## Purpose
Fornecer um algoritmo mecânico-legal para alocação de Mão-de-Obra SINKRA (Human, Clone, Agent, Worker) expurgando favorecimentos e ineficiências financeiras. Operações quebram porque alocam a entidade mais cara (Humano) para o fundo da fila (Dado Binário) ou alocam a entidade mais inconsequente (Worker) para decidir multas financeiras do topo. O roteamento segue o princípio "Bottom-Up" lógico: Do Lixo Robótico Mais Barato para a Carne Humana Mais Cara.

## Configuration
```yaml
PV_KE_075:
  name: "Bottom-Up Executor Routing"
  zone: "zone_0.8"
  trigger: "Designers do Processo precisam preencher a Box `responsavel_type` num Form YAML de Task recém escovada."
  evidence_threshold: "computer_science_axiom"
  rule: |
    ROTEAMENTO OBRIGATÓRIO:
    1. Deterministico Binário? -> WORKER.
    2. Raciocínio Contextual Variável Textual? -> AGENT.
    3. Exige Voz, Trejeito ou Rigor Metodológico ID de um Singular Expert? -> CLONE.
    4. Aciona gatilhos Éticos, Milionários ou Liderança de Tribo? -> HUMAN.
  veto_condition:
    trigger: "Tentar inverter a árvore e designar um Humano para processar a verificação de Nomes Limpos de 50.000 planilhas 'só pra ter mais segurança'."
    action: "VETO PROCEDURAL. O erro por fadiga humana anula qualquer segurança mítica projetada."
```

## Decision Tree
```javascript
IF (task_is_architecturally_stabilized_and_needs_an_owner)
  STEP_1: QUESTION: "Is it completely deterministic? Does 1+1 always=2 in this context?"
    IF (YES) -> Bind 'Worker'. Exit Tree.
    IF (NO) -> 
      STEP_2: QUESTION: "Does it need flexible insight but generic logic?"
        IF (YES) -> Bind 'Agent'. Exit Tree.
        IF (NO) ->
          STEP_3: QUESTION: "Is it a unique methodology of a specific Founder/Creator?"
            IF (YES) -> Bind 'Clone'. Exit Tree.
            IF (NO) ->
              STEP_4: QUESTION: "Will someone go to jail, get sued or lose a giant client if this fails?"
                IF (YES) -> Bind 'Human'. Exit Tree.
NEVER:
  Subir degraus de custo cognitivo e monetário até ter Esgotado violentamente a validade operacional do degrau inferior imediatamente prévio.
```

## Failure Modes

### Misapplication / Excess: "O Culto da Generalização Excessiva (Agent Faz-Tudo)"
- **Trigger:** Num acesso de adoração a Large Language Models (LLMs), a equipe T.I decide que "Tudo agora é IA", atribuindo o `responsavel_type: Agent` (GPT/Claude) para processar cálculos de Data de Vencimento Fiscais Simples. 
- **Manifestation:** Gastam R$15.000 em Tokens da OpenAI em um mês para fazer Contas Matemáticas Clássicas Estritas. O Agente Genérico erra sutilmente uma casa decimal num milhão, gerando juros absurdos para o financeiro no pagamento do sistema B2B. A fatura sangra, a performance diminui absurdamente pois textos longos foram gerados na resposta a cálculos absolutos e secos.
- **Detection:** Custo massivo com inferência LLM onde a programação clássica em Python duraria 10 milésimos sem custo unitário extra.
- **Recovery:** A árvore roteia: Deterministico? SIM -> Worker. Não minta sobre a complexidade da Tarefa só para injetar sua tecnologia favorita no painel.

### Omission / Failure to Activate: "O Gestor Exausto de Estimação (Human-First Bias)"
- **Trigger:** Uma equipe insegura recusa a confabular com a arquitetura Worker/Agent e prefere acoplar Humano em toda etapa, "porque o Zézinho conhece a gente".
- **Manifestation:** Zézinho trabalha 14 horas diárias. Comete erros às segundas e sextas. A empresa não escala mais de 2 milhões porque o custo marginal de contratar mais "Zézinhos" esmaga o CAC da Venda. O Gargalo sufoca as bordas e o dono se gaba que "Sua equipe é humanizada e próxima aos mínimos detalhes."
- **Detection:** Inchaço na Folha Pagamento; Erros atitudinais; Incapacidade de operar no feriado; Custo afogando a Agência num oceano de sangue operacional.
- **Recovery:** Aplicar Task-First Rigorosamente e processar TUDO pelo Routing Tree Algorítimo. Destronar Humanos de tronos repetitivos. Cortar os cordões emocionais entre Gestores ineficientes e processos escaláveis.

---

## Validation

✅ **Paradoxo Identificado:** O modelo assume que Tasks estão sempre "architecturally_stabilized", mas falha quando contextos reais demandam decisão humanizada em cenários aparentemente determinísticos (veto_condition viola a árvore).

✅ **Resolução:** Inserir pré-validação obrigatória antes da execução do routing tree — se Task não passar na validação arquitetural, escalar direto para HUMAN de veto, não entrada no tree.

✅ **Coerência:** Preserva eficiência (Worker/Agent/Clone quando apropriado) enquanto protege contra falhas catastróficas (HUMAN veto sempre disponível antes da árvore).

**Status:** REFACTORED — sys_tension adicionado.
