---
id: "PV_KE_046"
title: "Governança Cross-Process (Composição Dentro, Governança Entre)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Domain Modeling"
  - "System Architecture"
pipeline_instances:
  - "sinkra-master"
sys_tension:
  tension_with: "PV_KE_043 (A Primazia do Atributo) — Task-First local autonomy conflicts with Cross-Process entity governance requirements."
  resolution: "Tiered governance rule: Root & High-Weight Derived Entities (People, Companies, Orders) use Cross-Process centralization. Low-Impact Ephemeral Entities (local to single Organism) use Local Field Declaration with explicit scope boundaries."
---

# PV_KE_046 - Governança Cross-Process (Composição Dentro, Governança Entre)

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:architecture-designer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 4: Além dos 6 Níveis: A Dimensão Cross-Process]

## Purpose
A ilusão de silos modulares: Quando três processos da empresa mapeiam o que é um "Cliente" separadamente, ocorrem fissuras sistêmicas. Projetos tem "Cliente" com 12 campos. Financeiro tem "Cliente" com 6. Esta heurística resolve a colisão determinando que Organisms (Processos) aplicam composição estrita *verticalmente*, mas confiam na dimensão *ortogonal* (Domain Model Central / Registro de Entidades) para tratar dados que transcendem seus recintos.

## Configuration
```yaml
PV_KE_046:
  name: "Cross-Process Governance (Domain Registry Sovereignty)"
  zone: "zone_0.8"
  trigger: "Um novo processo ou automação precisa utilizar pacotes de dados de Entidades Core do negócio (Lead, Cliente, Projeto, Fatura)."
  evidence_threshold: "system_design_axiom"
  rule: |
    SE uma entidade vai ser transitada num Organism
    ENTÃO é VETADO declarar o modelo de campos dessa Entidade isoladamente no próprio processo.
    A Entidade deve apontar a sua raiz referencial para o DM (Domain Model / Registro de Entidades) centralizado da empresa.
  veto_condition:
    trigger: "Um fluxograma modela 'Abertura de Projeto' e define ali na interface que o 'Cliente' vai ter apenas Nome e Email."
    action: "VETO ESTRUTURAL. Processos não são donos de Entidades. Processos operam Ciclos de Vida e Atoms. O Dicionário de Entidades é ortogonal e absoluto."
```

## Decision Tree
```javascript
IF (mapping_entity_in_workflow)
  STEP_1: CHECK Domain Model (Registro Central de Entidades)
    IF (entity_exists_in_Domain_Model == TRUE)
      -> ACCEPT: Use foreign key reference (ex: `DM-001: Cliente`).
    IF (entity_exists_in_Domain_Model == FALSE)
      -> HALT workflow design.
      -> ACTION: Declare the new Root or Derived Entity in the centralized Domain Model first. Then resume design.
NEVER:
  Considerar a Governança Transversal como um "Sétimo Nível Composicional". Não contém Tasks. É uma infraestrutura de roteamento e dicionário universal, paralela à pirâmide executiva.
```

## Failure Modes

### Misapplication / Excess: "O Dicionário Burocrático Extremo"
- **Trigger:** O Arquiteto leva a regra ao extremo em uma startup pequena, tentando formalizar `Registro Central` para dados efêmeros locais de automação.
- **Manifestation:** Um processo isolado de "Coleta de Brindes" demora semanas pra ir pro ar pois estão esperando a revisão no "Registro Central de Entidades" formal parar aprovar a criação da entidade "Tamanho de Camiseta". 
- **Detection:** Velocidade de entrega desaba. Overhead para processos Táticos de Nível 4 (Workspace L4).
- **Recovery:** Isenção Local. A regra diz: "Se a Entidade é compartilhada em *múltiplos* processos, Governança Central". Se só vive em um Organism e seu impacto não cruza fronteiras, permita `Local Field Declaration`. 
- **Prevention:** Aplicar a régua da gravidade: Root Entities (Pessoas, Empresas) e Derived de alto peso (Pedidos, Projetos, Contratos) usam "Cross-Process Rule".

### Omission / Failure to Activate: "A Fragmentação Monstro (Frankenstein de Dados)"
- **Trigger:** Velocidade brutal e falta de SINKRA Chief Architect ditando centralização.
- **Manifestation:** Financeiro cria o form de onboarding com 12 campos obrigatórios de endereço fiscal. O Comercial, focado em vendas, usa seu próprio funil CRM e cadastra apenas o CNPJ. Quando a automação empurra o fechamento para "Projetos", a API detona a bomba de `Missing Keys`.
- **Detection:** Ninguém confia no Pipeline CPT (Customer Path). Erros crônicos de Payload Invalid nos Webhooks centrais. Equipes discutindo qual departamento está "certo".
- **Recovery:** Freeze Operacional. Auditoria de todas as definições da entidade "Cliente", construção do arquivo DM e exigência de refatoração para garantir as fronteiras (Constraints) universais para criar, ler e mudar status da entidade com o "Lifeycle Map".
- **Prevention:** Jamais escalar de 2 squads pra 4 squads sem instituir a camada formal ortogonal 1 e 2 (Registro Central e Lifecycle Maps).

---

## Validation

**Paradox Identified:** The heuristic embodies a fundamental tension between **Local Autonomy** (processes composing freely within their boundaries) and **Global Coherence** (entities must be governed centrally to prevent fragmentation).

**Resolution Pattern Applied:** The paradox is resolved through a **Tiered Governance Framework**:
1. **Root & High-Weight Entities** (People, Companies, Orders) → Mandatory Cross-Process Governance
2. **Ephemeral, Low-Impact Entities** (Shirt Sizes, Local Workspace Data) → Permitted Local Declaration with explicit scope boundaries

**Validation Logic:** The heuristic is validated by its ability to distinguish between entities that *transcend processes* (governed) and entities that *live within one process* (autonomous), preventing both excessive centralization overhead and chaotic fragmentation.

**Status:** ✅ Coherent and Applicable
