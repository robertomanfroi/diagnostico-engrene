---
id: "PV_KE_060"
title: "Restrição por Papel, não por Identidade (Role vs Identity Binding)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Executor Abstraction"
  - "Template Architecture"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "PV_PA_033 (Executor Transversality) — binding by role vs. executor interchangeability demands"
  resolution: "Bind to Role/Type at template level; defer Identity resolution to runtime instantiation (t=0). Validation ensures role constraints are preserved through the entire lifecycle."
---

# PV_KE_060 - Restrição por Papel, não por Identidade (Role vs Identity Binding)

**Type:** Decision Heuristic
**Zone:** 🧠 4% Expert Insight | **Agent:** @hybridOps:architecture-designer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 9: Parâmetros de Executor]

## Purpose
Tornar Templates biologicamente e tecnologicamente à prova de falhas na gestão de recursos. Se um Template "amarra" fisicamente a Execução na Diretora da Agência (Identidade), ele quebra no momento em que ela for ao médico. O Template prende o **Papel Abstrato ou o Tipo de Inteligência (Role/Type)**. A Instância em Execução que preenche isso com o **CPF/API-Key** do dia.

## Configuration
```yaml
PV_KE_060:
  name: "Role vs Identity Binding Constraint"
  zone: "zone_4"
  trigger: "Quando nomeamos o Executor de qualquer Task, Gate ou Molecula dentro de um Template SINKRA."
  evidence_threshold: "first_principles_inference"
  rule: |
    SE você está desenhando as bases de um Modelo Abstrato Nível 5 (Template)
    ENTÃO DEVE reter apenas a restrição do Tipo Cognitivo `EXECUTOR_TYPE(Human | Clone)`.
    Mas NUNCA poderá prender à Identidade Exata `Human:Maria_Silva`. O Nome / CPF preenchido pertence ao Tempo de Instanciação Mágica Nível 6.
  veto_condition:
    trigger: "Um Workflow com uma variável hardcoded `Aprovador_Oficial: @DiretordoSetor01`."
    action: "VETO TÁTICO. Se o @DiretordoSetor01 pedir demissão amanhã, seu código legado levará dias para ser reescrito. Force o Binding dinâmico."
```

## Decision Tree
```javascript
IF (assigning_ownership_inside_a_Template_Blueprint)
  STEP_1: DETERMINE the required Cognitive Class (Worker, Agent, Human, Clone).
  STEP_2: WRITE the parameter slot (e.g., `{{executor_creative_copy}}`).
  STEP_3: ADD a type constraint to the slot `Requires: Agent || Human`.
    IF (someone_types_a_real_user_id_like_UUID_inside_the_base_yaml)
      -> REJECT. Identity resolution only happens at t=0 of the Instance Creation.
NEVER:
  Acoplar as regras vitais do jogo à certidão de nascimento de um único jogador.
```

## Failure Modes

### Misapplication / Excess: "Role-Play Abstrato Demais"
- **Trigger:** Ao invés de travar a classe cognitiva no Template (Human vs Script), o desenvolvedor decide que a classe abstrata de Executor está "tão aberta" que literalmente a API ou o usuário final pode selecionar um bot fraco de Checkpoint (Worker) para liderar um QA Gate Sensível.
- **Manifestation:** Na fase de injeção dos Parâmetros, a máquina aceita injetar um `Worker: CronJob` burro onde o Template deveria ter forçado a alocação de um Intelecto Superior (Human). 
- **Detection:** Subornos na triagem de aprovações. Bots binários assumem cadeiras de decisão estética.
- **Recovery:** A Restrição do Papel não deve ser negligente. O Slot vazio DEVE herdar a obrigatoriedade da classe. `{{validator_qa_node}} -> TYPE: HUMAN`.
- **Prevention:** Validação de Schema no start do Organismo rejeitando tipos incompatíveis preenchidos no form.

### Omission / Failure to Activate: "O Lock-in de Identidade (A Gargalo de 1 Pessoa)"
- **Trigger:** Um departamento não conhecia as diferenças de instâncias, configurou na unha que o "Carlos" aprova todos os orçamentos de Mídia dentro da própria arquitetura base do Automation.
- **Manifestation:** Carlos precisa tirar férias. O T.I tem que interromper outras frentes para literalmente abrir o mapa global da empresa, escavar o código do banco e alterar o "Carlos" para a "Roberta". Quando ele voltar 30 dias depois, o processo repete ao inverso.
- **Detection:** Micro-manutenção dolorosa baseada em atestado médico, afastamento e turnover.
- **Recovery:** Converter Valores Absolutos (Carlos) para Slot Parameters (`{{media_head_approver}}`) que são preenchidos dinamicamente pela Interface do Bot de Orquestração baseando-se no plantão do dia ou na tag do card.
- **Prevention:** Varredura Estática de Arquitetura buscando Strings contendo chaves de usuários reais dentro de diretórios de `.yaml` estruturais.

## Validation

✅ **Paradoxo Identificado:** Template design requires abstract role binding, yet execution demands concrete identity resolution—a fundamental tension between blueprint generality and runtime specificity.

✅ **Resolution Applied:** The heuristic resolves this by establishing a two-layer binding model:
- **Layer 1 (Template):** Constrain by Role/Type (`EXECUTOR_TYPE: Human | Agent | Worker`)
- **Layer 2 (Instantiation):** Resolve identity at runtime via dynamic slot parameters

✅ **Validation Checkpoints:**
- [ ] Static architecture scanner detects hardcoded user identities in structural YAML
- [ ] Template slots enforce type constraints (`{{validator_qa}} -> TYPE: HUMAN`)
- [ ] Instantiation engine rejects incompatible type bindings at t=0
- [ ] Role-based access control (RBAC) persists across template lifecycle
- [ ] Identity rotation (employee turnover, leave) requires no template rewrites
