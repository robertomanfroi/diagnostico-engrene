---
id: "PV_PA_038"
title: "Clone Liability Threshold & Handoff"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Clone Architecture"
  - "Accountability"
pipeline_instances:
  - "quality-control"
sys_tension:
  - tension_with: "AI Autonomy vs Legal Liability"
    resolution: "Split Decision — Clone suggests (95% fidelity), Human executes Signatory Handoff (0% Clone liability)"
---

# PV_PA_038 - Clone Liability Threshold & Handoff

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:process-architect
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 3: Os 4 Executores]

## Purpose
A arquitetura do Clone atinge 95% de fidelidade metodológica ao replicar a personalidade, heurísticas e voz de marca do fundador. Porém, o Clone possui rigorosamente 0% de Accountability Legal ou Moral. Esta heurística blinda processos operacionais garantindo que a delegação extrema da inteligência não se converta em terceirização fatal de risco não-provisionado.

## Configuration
```yaml
PV_PA_038:
  name: "Clone Liability Threshold"
  zone: "zone_0.8"
  trigger: "Clone operando num decision node de alta consequência."
  evidence_threshold: "first_principles_inference"
  rule: |
    SE o Clone atuar sobre outputs ou liberações com peso contratual, financeiro (> tolerância do budget), ou representação jurídica final
    ENTÃO quebre a task de liberação em duas:
      Action_1 (Clone): Analisa coerência metodológica e sugere score de aprovação.
      Action_2 (Human): Executa o Handoff de liberação comercial/jurídica (1-click approval).
  veto_condition:
    trigger: "Tentativa de automatizar envio de contratos comerciais ou aprovação de fundos maciços via Clone 100% autônomo."
    action: "VETO absoluto. O humano deve manter o status de Signatory (Signatário) no Quality Gate subsequente."
```

## Decision Tree
```javascript
IF (clone_output_is_ready_for_release)
  STEP_1: ANALYZE domain threat level
    IF (requires_legal_signature || exposes_capital_risk_above_P0)
      -> HALT pipeline; TRIGGER Human Signatory Handoff.
    ELSE IF (is_internal_draft_or_safe_copy)
      -> PROCEED with standard automated release.
NEVER: 
  Confundir "Automação com Voz de Especialista" com "Substituto Moral do Especialista". A lei processa indivíduos, não matrizes estocásticas.
```

## Failure Modes

### Misapplication / Excess: "O Gargalo do Especialista Paranóico"
- **Trigger:** A diretoria lê sobre os riscos e exige assinaturas para e-mails cotidianos.
- **Manifestation:** Medo da responsabilidade algorítmica faz Pedro Valério voltar a aprovar tudo ("Ah, vou ler pessoalmente as propostas antes de ir pro Lead frio").
- **Detection:** O tempo de resposta de e-mails cai de volta para o nível 100% humano (3 dias), destruindo o benefício de escala que o Clone trazia.
- **Recovery:** Definir fronteiras matemáticas no SLA. "Até $5.000 em negociação fria, Clone autoriza os touchpoints e templates. Acima disso, Humano revisa."
- **Prevention:** Aplicar um "Visto Operacional" para tasks menores e um "Visto Estratégico" só pras tarefas maiores na State Machine (Nível 4).

### Omission / Failure to Activate: "A Assinatura Sombra"
- **Trigger:** Deslumbre com a performance impecável nas primeiras 50 iterações do Clone na agência matriz.
- **Manifestation:** O Clone ganha bypass (Fast-track) pro cliente final. Ele redige propostas complexas contratuais e dispara os anexos sem ninguém ler.
- **Detection:** Um cliente liga reclamando que o contrato prometia entregas irrealistas que a equipe não suporta e que o Clone redigiu livremente baseado num contexto cruzado.
- **Recovery:** Interrupção total do Pipeline em Produção. Voltar o Organism para o modo Sandbox. Instalar o Quality Gate "Human Approval Node" travando o disparo externo.
- **Prevention:** A arquitetura do sistema sempre ter um `Status-Atom` em estado "WAITING_FOR_SIGNATURE" como pré-condição inquebrável para envio de PDF ou transferências financeiras.

## Validation

✅ **Paradoxo Identificado:** Clone com 95% fidelidade metodológica + 0% accountability legal cria tension between automation capability and legal responsibility.

✅ **Resolução Implementada:** Split Decision pattern — Clone provides suggestions (advisory layer), Human retains Signatory role (accountability layer).

✅ **Critério Testável:** Todos os outputs com peso contratual/financeiro devem passar por WAITING_FOR_SIGNATURE status antes de liberação.

✅ **Proteção Jurídica:** Handoff explícito registra que Clone não assina — reduz exposição a litígios de decisões automatizadas.
