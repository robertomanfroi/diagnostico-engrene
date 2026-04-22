---
id: "PV_KE_094"
title: "The 5 Mandatory OS Fields (Metadata Anchor)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Implementation Phase"
  - "Data Governance"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "PV_KE_045 (Declarative Behavior Token) — Rigid Metadata Mandates vs Fluid Behavior Extensibility"
  resolution: "5 fields are immutable foundation; domain extensions wrap them without replacing the core tuple"
---

# PV_KE_094 - The 5 Mandatory OS Fields (Metadata Anchor)

**Type:** Infrastructure Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:clickup-engineer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 15: Configurando o ClickUp para Sinkra / Passo 2]

## Purpose
Garantir a rastreabilidade total de Meta-Linguagem do SINKRA dentro do Sistema Operacional visual (ClickUp, Jira). Esta heurística (Commandment) obriga a implementação de exatos 5 Campos Customizados Tipados em toda Raiz de Sistema, imutáveis e globais. Um card/task no ClickUp sem a marcação SINKRA (`executor_type`, `phase`, `sinkra_primitive`, `guardrail_status`, `quality_gate_result`) retrograda de Unidade Operacional rastreável para um "Post-it Digital inútil". Estes 5 parâmetros são a ligação matemática que acopla a camada abstrata da Ferramenta de YAML à camada prática da Interface Gráfica, permitindo filtragens exatas e acionamentos robóticos perfeitos por Views, Agentes e Trabalhadores Autônomos.

## Configuration
```yaml
PV_KE_094:
  name: "Sinkra Metadata Anchor Constraint"
  zone: "zone_0.8"
  trigger: "Fase 7 - Implementation. O Arquiteto ou ClickUp Engineer formata os Arrays de Meta-Dados da Instância Base do Software de Gestão."
  evidence_threshold: "structural_logic"
  rule: |
    TODA Tarefa/Workflow no Sistema Operacional Front-End DEVE carregar os 5 Atributos:
    1. executor_type (Dropdown) -> Human, Agent, Worker, Clone.
    2. phase (Number/Dropdown) -> 1 a 9 (Estágio da arquitetura).
    3. sinkra_primitive (Dropdown) -> Atom, Molecule, Organism, Template, Instance.
    4. guardrail_status (Checkbox) -> Flag Boolean de auditoria de restrição.
    5. quality_gate_result (Dropdown) -> APPROVE, REVIEW, VETO, N/A.
    Se a Ferramenta Visual não suportar tipagem rígida, não a utilize para operar Organismos Complexos. Se um Card SINKRA descer para produção sem estar plotado por estas 5 coordenadas, suspenda a automação atrelada.
```

## Decision Tree
```javascript
IF (mapping_SINKRA_YAML_constructs_into_a_Frontend_Task_Tracker)
  STEP_1: EXAMINE the Custom Fields / Columns implementation.
  STEP_2: ENFORCE the Basic Universal Tuple.
    IF (The Team proposes: 'We just need Assignee, Priority, and Due Date. Let\\'s skip the Primitive dropdown.')
      -> VETO: If you don't know the Primitive, you don't know its behavior rules, nesting rights, or transition physics. If you don't have executor type, Automations cannot filter by Agent triggers. You lose SINKRA OS completely.
    IF (The Team adds 40 specific client fields but anchors them along with the 5 SINKRA Fields at the Domain Level Space.)
      -> ACCEPT: The 5 fields are the minimum, universal standard. Expansions are allowed per domain context, but the foundation remains.
NEVER:
  Delegar o registro SINKRA de uma Tarefa Operacional para uma `Description` text livre ou `Sub-Taggings` caóticos soltos (Labels não tipados). A filtragem lógica na camada Banco de Dados/OS exige Variáveis Severas. Sem elas, seus Workers tentarão inferir strings em YAML Livre, e a precisão afunda.
```

## Failure Modes

### Misapplication / Excess: "O Campo Intrusivo Não Negocial"
- **Trigger:** A Equipe exige dezenas de preenchimentos obrigatórios manuais no `Create Task` de uma plataforma, bloqueando Operadores (Humans) com os 5 Campos Técnicos quando o Frontend SINKRA poderia herdar tudo via Templates (Fase 6 - Passo 6).
- **Manifestation:** Humanos precisam preencher exaustivamente "Isto é um Atom!", "Sou Fase 4!" sempre que criarem a Tarefa de uma Sub-Célula Tática no Board. Rejeição fortíssima da Equipe pela repetição insana. O software vira um poço de micro-burocracia, e ninguém preenche as Tasks novas.
- **Detection:** Reclamações severas de lentidão na operação, e campos técnicos do SINKRA preenchidos aleatoriamente como "qualquer coisa" só para passar a condição do Front-End.
- **Recovery:** Os 5 campos OBRIGATÓRIOS (PV_KE_094) devem vir **PRÉ-PREENCHIDOS VIA TEMPLATES** de Instanciamento (ClickUp Template, Automations On-Create). O Humano operando a ponta do funil raramente digita a meta-linguagem SINKRA. Ele preenche os Dados Táticos. A Automação carrega as 5 âncoras para rastreio estrutural (Blackbox para Humano na Criação, Transparente para Worker/Audit).

### Omission / Failure to Activate: "O Frankenstein de Labels Coloridos"
- **Trigger:** A Equipe tenta implementar a Hierarquia Primitiva (Níveis SINKRA) usando tags fofinhas coloridas sem Tipagem Estrita e sem Padronização ou escopos numéricos, mesclando "Agent" com "High Priority" com "Molecule" no mesmo mar de Labels.
- **Manifestation:** O Backend Automação (Worker / N8N) precisa buscar dados por filtro de Tag no OS. Duas tags chamam "AGENT" e "Agent", e "Agnt". O Webhook não acha o alvo. O Worker não dispara porque não consegue dar um match Booleano ou Enum estrito no Array de Custom Fields soltos. O Sistema paralisa, silencioso, até a panela de pressão explodir e o time de Operações ficar correndo atrás do painel tentando entender quem quebrou.
- **Detection:** Scripts rodando `Search_Field` sem retorno com logs vazios e processos em "In Progress" interminável.
- **Recovery:** A Lei dos Custom Fields de Alta Coesão (PV_KE_094). As Fases (F1-F9), Executores Orgânicos e Tipologias Primitivas NUNCA HABITAM NO ESPAÇO CAÓTICO DOS LABELS MISTOS E LIVRES. OBRIGATÓRIO (MUST): Criação de Dropdowns Fechados (Enum Strict) na Camada Nativa (ClickUp/Jira/Notion).

## Validation

✅ **Paradox Identified:** Tension between immutable universal mandate (5 fields) and permissible domain-specific extensions.
✅ **Resolution Applied:** Core tuple (5 fields) is inviolable foundation. Domain extensions are satellite fields, not replacements.
✅ **System Tension Recorded:** `sys_tension` block captures duality for orchestration and decision trees.
