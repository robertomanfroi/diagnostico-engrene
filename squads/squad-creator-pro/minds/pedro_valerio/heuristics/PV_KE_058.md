---
id: "PV_KE_058"
title: "A Dicotomia da Configuração (Configurable vs Customizable)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Template Architecture"
  - "Orchestration Hierarchy"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "PV_KE_059 (O Dogma dos Invariantes Estruturais) - Flexibilidade operacional (injeção de parâmetros) vs Integridade estrutural (invariantes de processo)"
  resolution: "Permitir mutação de Parâmetros (SLA, Executor, Threshold) mantendo blocos estruturais (Fases, Gates) imutáveis. Criar Non-Template Organisms isolados se a estrutura deve mudar."
---

# PV_KE_058 - A Dicotomia da Configuração (Configurable vs Customizable)

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:architecture-designer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 9: A Distinção Fundamental]

## Purpose
Estabelecer o abismo absoluto entre escalar operações via **Templates** rígidos e destruir a operação permitindo que usuários gerem cópias flexíveis (Customização). "Configurável" significa que os valores das variáveis mudam dentro de um escopo predefinido fechado. "Customizável" significa que o usuário muda a estrutura em si. A SINKRA proíbe a segunda.

## Configuration
```yaml
PV_KE_058:
  name: "Configurable vs Customizable Axiom"
  zone: "zone_0.8"
  trigger: "O cliente ou equipe de Atendimento solicita 'remover uma etapa de aprovação' de um Pipeline apenas para aquele cliente específico."
  evidence_threshold: "process_absolutism_law"
  rule: |
    SE você instanciar um Modelo Operacional (Template)
    ENTÃO você PODE alterar Parâmetros de Identidade (Cliente), Threshold (SLA) ou Executor (João vs Maria).
    MAS você é PROIBIDO de remover, adicionar ou remanejar Blocos Estruturais (QA Gates, Fases). 
  veto_condition:
    trigger: "Um Scrum Master tenta deletar o QA Gate do Board de um Cliente Vip pois ele confia no time de entrega."
    action: "VETO ESTRUTURAL. Customizar não é um direito operacional. Se a estrutura deve mudar, cria-se um Non-Template Organism isolado."
```

## Decision Tree
```javascript
IF (team_requests_to_adapt_a_pipeline_for_a_use_case)
  STEP_1: EVALUATE the requested change.
    IF (they_want_to_change_SLA_hours_or_assignee)
      -> ACCEPT: Pass parameters to the Template instance.
    IF (they_want_to_skip_Phase_3_or_remove_the_Compliance_Gate)
      -> REJECT: "This breaks the structural invariant. The Template cannot be customized. We can adjust the Gate's harshness threshold, but not delete the Gate."
NEVER:
  Confundir flexibilidade de Parâmetros com licença para mutilar a espinha dorsal de um processo.
```

## Failure Modes

### Misapplication / Excess: "Templates Gessados e Inúteis"
- **Trigger:** Travar todos os valores matemáticos dentro do próprio código do Template, impedindo a injeção de configurações externas.
- **Manifestation:** O Template dita que o prazo sempre será "8 horas" e o Executor é sempre "O Joãozinho". Como resultado, o Template serve apenas para o projeto A e fica inutilizável no projeto B.
- **Detection:** A empresa tem "1 Template," mas a adoção da ferramenta é zero porque não atende as minúcias logísticas de outras equipes.
- **Recovery:** Abstrair Valores Dinâmicos em Parâmetros `{}`, mantendo trancado no código apenas Esqueletos Geométricos (Setas e Posições do fluxo).
- **Prevention:** Um Template obrigatoriamente tem Variáveis Injetáveis. Se não tem, ele é apenas um Organismo fantasiado de Template (Anti-Pattern 2).

### Omission / Failure to Activate: "O Frankenstein dos 14 Pipelines"
- **Trigger:** Ao fechar novos clientes, a equipe copia o Pipeline original do ClickUp e adapta livremente deletando cartões e criando colunas que acham legais pro novo contexto.
- **Manifestation:** Em 6 meses a agência tem 14 processos diferentes rodando para fazer a "mesma" entrega. Ninguém sabe onde treinar o novo funcionário. Se ocorre uma melhoria de segurança no processo principal, as copias ficam esquecidas e falham com o cliente.
- **Detection:** Um C-Level pede um relatório de Gargalo Nacional e percebe que as bases de métricas são incompatíveis entre Contas.
- **Recovery:** Destruir os Frankenstein e refatorar em 1 Único Template PAI, repassando o contexto de variação como meros Payload Parameters.
- **Prevention:** A replicação de Board nunca será permitida sem o engessamento mecânico de estrutura imposto pela camada de Template da SINKRA.

---

## Validation

✓ **Paradox Identified:** Flexibilidade de configuração (necessária para escalar) vs Rigidez estrutural (necessária para manutenibilidade)

✓ **Resolution Applied:** Arquitetura em 2 camadas
  - Camada 1 (Mutável): Parâmetros, SLAs, Executores, Thresholds
  - Camada 2 (Imutável): Blocos estruturais, Fases, Gates, Invariantes

✓ **Anti-patterns Mapped:** 2 falhas críticas documentadas (Gessamento + Replicação Desordenada)

✓ **Enforcement Mechanism:** Veto estrutural via Template Engine da SINKRA
