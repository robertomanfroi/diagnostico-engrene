---
id: "PV_KE_059"
title: "O Dogma dos Invariantes Estruturais (The 4 Un-parameterizables)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Template Architecture"
  - "Governance"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "PV_KE_058 (A Dicotomia da Configuração)"
  resolution: "Implementar guardrails de veto irreversível (imutável em runtime) para os 4 invariantes, com auditoria e alertas para tentativas de contorno. Permitir parametrização apenas em camadas de infraestrutura isolada (ex: plataforma de notificação do Handoff), nunca na existência/ativação do próprio Handoff."
---

# PV_KE_059 - O Dogma dos Invariantes Estruturais (The 4 Un-parameterizables)

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:architecture-designer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 9: O Que NUNCA é Parâmetro]

## Purpose
Blindar a integridade das instâncias de Template definindo o que **jamais** pode se tornar uma variável injetada. Quando analistas ganham poder de parametrizar restrições estruturais críticas (como quantidade de checagens de qualidade), a governança colapsa disfarçada sob a falsa promessa de flexibilidade.

## Configuration
```yaml
PV_KE_059:
  name: "The 4 Un-parameterizables"
  zone: "zone_0.8"
  trigger: "Na declaração de variáveis configuráveis de um Blueprint ou Template YAML."
  evidence_threshold: "process_absolutism_law"
  rule: |
    Quatro elementos NUNCA podem virar parâmetros no sistema SINKRA:
    1. A sequência de fases cronológicas.
    2. A presença de QA Gates.
    3. A obrigatoriedade de Checkpoints de pré-condição.
    4. A estrutura de Handoff explícita.
  veto_condition:
    trigger: "Criar uma variável do tipo `incluir_qa_gate: true/false` ou `numero_de_gates: 0|1|2` num template base."
    action: "VETO ARQUITETURAL. Você não pode dar a um operador logístico a chave para desligar a barreira de segurança primária da corporação."
```

## Decision Tree
```javascript
IF (creating_parameter_fields_for_a_Template)
  STEP_1: REVIEW the proposed parameter list.
    IF (parameter determines if a security/quality node Exists or Not)
      -> REJECT. Existence is non-negotiable Structure.
    IF (parameter determines the harshness (threshold) of the security/quality node)
      -> ACCEPT. Values and Thresholds are configurations.
NEVER:
  Deixar o usuário da máquina de produção decidir quantos componentes de freio de emergência a fábrica vai instalar naquele dia.
```

## Failure Modes

### Misapplication / Excess: "O Extremismo da Camisa de Força"
- **Trigger:** Configurar todos os mínimos detalhes, como qual o texto do e-mail ou o caminho exato do URL interno num sistema fixo, como invariantes intocáveis.
- **Manifestation:** O workflow envelhece mal. Um mês depois, a empresa troca o Slack pelo Teams, mas como a ferramenta de Handoff estava fisicamente embutida e trancada como "Invariável intocável", a engrenagem para de funcionar, forçando a deleção da raiz.
- **Detection:** Dificuldade extrema de mudar pequenos pormenores na operação diária.
- **Recovery:** Separar corretamente a Variável (Parâmetro) da Barreira Abstrata (Estrutura Invariável). O "Handoff Existir" é invariável; a "Plataforma de Notificação" do Handoff é parâmetro.
- **Prevention:** Somente conceitos fundamentais de integridade Lógica, Sequencial, Transferência e Validação merecem o selo do Dogma dos Invariantes.

### Omission / Failure to Activate: "O Template Desossado (Bypass Silencioso)"
- **Trigger:** Num acesso de pressão ágil do Sprint, a área de Marketing implora que a área Tech libere um "botãozinho de desligar o QA de revisão para posts urgentes".
- **Manifestation:** A Tech cria a variável booleana de Skip-QA no Payload. Um mês depois, todos os gestores ativam a variável para todas as instâncias só para ganhar velocidade artificial no Painel, publicando lixo.
- **Detection:** Taxa absurda de entregas falhas, e ao olhar os logs do sistema, os QA Gates marcam que a rotina foi "Pulada com sucesso".
- **Recovery:** Expurgar parâmetros mutáveis de nós de arquitetura estrutural essenciais.
- **Prevention:** Uma linha no código ou template que tem a semântica `IF (Handoff_Required == True)` está fundamentalmente violando o estatuto de templates corporativos da SINKRA.

---

## Validation

**Paradox Identified:** A heurística proclama que certos elementos (QA Gates, Checkpoints, Handoff) NUNCA podem ser parametrizados, mas reconhece na seção de "Omission" que operações sob pressão sistematicamente parametrizam-nos de todos os modos, criando um hiato entre o **ideal dogmático** e a **realidade pragmática**.

**System Tension:** Rigidez absoluta vs. Flexibilidade operacional

**Resolution Applied:** Guardrails imutáveis em runtime (não em design) com auditoria e alertas, permitindo parametrização apenas em camadas isoladas de infraestrutura, nunca na existência/ativação dos invariantes principais.

**Applicability:** ✓ Aplica-se a arquitetura de Templates, Blueprints e processos críticos governados por SINKRA v3.1+.
