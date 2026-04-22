---
id: "PV_KE_093"
title: "The Domain Namespace Priority (Anti-Client Folder)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Implementation Phase"
  - "Process Governance"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "AN_KE_073 (Parallel Subagents for Throughput) — Sequential Domain Hierarchy vs. Concurrent Multi-Customer Processing"
  resolution: "Use Domain-First Architecture (Strategic > Tactical > Operational) as root structure, then apply intelligent filtering and custom views at the client/product level to preserve clean separation of concerns while delivering customer visibility when needed"
---

# PV_KE_093 - The Domain Namespace Priority (Anti-Client Folder)

**Type:** Organizational Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:clickup-engineer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 15: Configurando o ClickUp para Sinkra / Passo 1]

## Purpose
Estabelecer a primazia arquitetural do Espaço de Trabalho (Workspace Hierarchy). Esta heurística impõe que a Camada 1 (Sistema de Gestão, ex: ClickUp Spaces) deve ser subdividida OBRIGATORIAMENTE por Nível de Domínio (Estratégico, Tático, Operacional) e NUNCA por "Clientes", "Equipes Departamentais" ou "Produtos". Organizar o ambiente por Cliente mistura na mesma tela/pasta a Meta Visão (Estratégico) com Operações Robotizadas (Worker), destruindo a filtragem, obliterando os dashboards analíticos e fundindo níveis de abstração incompatíveis. O Workspace limpo é um espelho do Domínio, não da fatura comercial.

## Configuration
```yaml
PV_KE_093:
  name: "Strict Domain-Level Workspaces"
  zone: "zone_0.8"
  trigger: "Fase 7 - Implementation. O ClickUp Engineer (ou equivalente) configura o Workspace Raiz da organização SINKRA no Gerenciador de Tarefas."
  evidence_threshold: "structural_logic"
  rule: |
    O Top-Level Container (Space, Board Raiz) DEVE refletir o Domínio SINKRA:
    - [DOMAIN] Estratégico -> Decisões, Planejamento C-Level, Metas Macroeconômicas (Predomínio Human).
    - [DOMAIN] Tático -> Coordenação, Campanhas, Arquitetura Middle-Man (Misto Human/Agent).
    - [DOMAIN] Operacional -> Produção em Massa, Execuções (Predomínio Worker/Agent).
    Se o Cliente X requerer pastas, ele terá Projetos (Instâncias) dentros do Domínio Tático/Operacional.
    Se o Workspace contiver Espaços Misturados ("Cliente A", "Marketing", "TI Dúvidas"), a abstração ruiu. A Visão SINKRA implodiu e dashboards se tornarão inúteis.
```

## Decision Tree
```javascript
IF (structuring_the_hierarchical_Spaces_of_a_Task_OS_like_ClickUp_or_Jira)
  STEP_1: EXAMINE the Root Node categorization philosophy of the Team.
  STEP_2: ENFORCE Domain Supremacy.
    IF (The Team proposes: 'We create 1 Space per Customer so the Account Manager can see everything associated with Nike.')
      -> VETO: Organizing by Customer throws Strategic alignment tasks, tactical planning, and 10,000 operational robotic tasks into the same visual bucket. Dashboards lie. Executive views break.
    IF (The Team proposes: 'We create 3 Spaces: Strategic, Tactical, and Operational. We tag the customer in the Custom Field of the Instances.')
      -> ACCEPT: Architectural integrity. Perfect Filtering. Cross-Customer aggregation is possible.
NEVER:
  Organizar um ecossistema operacional pelas fronteiras sociais/comerciais (Produto/Time/Cliente). Ecossistemas de Alta Tensão SINKRA são estruturados pela Gravidade da Física Processual (O Nível de Abstração: Pensar x Gerenciar x Executar).
```

## Failure Modes

### Misapplication / Excess: "O Fundamentalismo das Gavetas Vagas"
- **Trigger:** A Equipe força a taxonomia "Estratégico/Tático/Operacional" literal como ÚNICAS 3 Listas/Namespaces na Empresa Global, não permitindo sequer Lógicas Sub-Diretoriais sensatas nas Instâncias, jogando 5.000 projetos diários de 15 BUs numa Mesma Lista chamada "Operacional Geral", matando a UI/UX da Ferramenta.
- **Manifestation:** O Workspace Tático exibe gargalos inenarráveis de Lentidão Front-End porque todos os Nodes de todas as Células (RH, Vendas, Infra) despencam numa vala comum sem Subdivisão de Pastas SINKRA (Primitivo de Template/Célula).
- **Detection:** Reclamações que a categorização rigorista de Domínios impossibilitou achar a Tarefa X do Squad Y no meio da vala "Operacional".
- **Recovery:** A Restrição do Domínio (PV_KE_093) governa o NODE RAIZ (ClickUp Space, Notion Root Database). A hierarquia secundária (Folders, Project Tags) OBRIGATORIAMENTE desce à particularidade das Squads/Produtos/Clientes. A Ferramenta Mapeia assim: `Space [Domínio] -> Folder [Template/Unidade] -> List [Instância Agrupadora] -> Task [Atom/Molecule]`.

### Omission / Failure to Activate: "O Desastre do 'Workspace Por Cliente'"
- **Trigger:** Agências de Marketing ou Consultorias antigas migrando para SINKRA e insistindo "O jeito que a gente sempre fez foi criar uma Área no Trello para cada Cliente novo que entra."
- **Manifestation:** A Diretoria tem Visão Fragmentada (Silos Obscuros). Se a empresa fechar com 80 clientes, ela terá 80 Namespaces diferentes, com Custom Fields diferentes porque nenhum herda a Meta-Regra. Um relatório C-Level de "Mostre todos os Gargalos Operacionais da Fase de Criação" cruza-clientes torna-se IMPOSSÍVEL ou requer planilheiros de Excel consolidando CSVs na madrugada.
- **Detection:** Multiplicação descontrolada de Paineis. O Arquiteto não sabe nem "Onde" aplicar a regra de Automação de Cópia X, pois ela precisa ser replicada 80 vezes. A manutenibilidade despencou à zero.
- **Recovery:** O `Process-Mapper` em parceria com o `ClickUp-Engineer` tranca Criações Radicais. Re-Estrutura Base `(Domínio > Unidade)`. Configura View Customizada Agregadora: "Account Manager Nike View", onde um Filtro Inteligente puxe TODAS as tasks do Domínio Tático/Operacional taggeadas com "Cliente: Nike", gerando a exata ilusão de "Organização por Cliente" no Front-End sem sujar a Arquitetura limpa SINKRA no Back-End (Data Base OS).

## Validation

✅ **Paradox Identified:** Domain-First Architecture (enforced abstraction) vs. Customer-Centric Visibility (commercial reality). The heuristic resolves this tension by separating concerns: structure follows domain logic at the root (Spaces), commercial perspective is layered through Views and intelligent filtering (Custom Fields, Tags).

✅ **Architectural Integrity:** The principle maintains SINKRA's core mandate—clean separation between thinking (Strategic), managing (Tactical), and executing (Operational)—while providing Account Managers the visual experience they need without architectural compromise.

✅ **Scalability Proof:** This pattern scales from 5 to 500+ customers without multiplying complexity at the workspace root; custom Views multiply, not Spaces.
