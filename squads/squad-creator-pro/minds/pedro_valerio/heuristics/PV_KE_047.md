---
id: "PV_KE_047"
title: "Governança Preventiva (Reserved Tokens)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Version Control"
  - "Governance"
pipeline_instances:
  - "sinkra-master"
sys_tension:
  tension_with: "AN_KE_043 (Zero Achismos) vs Preventive Framework Evolution Planning"
  description: "A necessidade de formalizar tokens futuros (prevenção) vs risco de acumular tokens inutilizados (cemitério de intenções)"
  resolution: "TTL obrigatório em RESERVED tokens com limpeza automática ao fim da Major Version alvo. Limite máximo: 2 versões à frente. Auditoria trimestral de ratio Active:Reserved."
---

# PV_KE_047 - Governança Preventiva (Reserved Tokens)

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:architecture-designer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 5: Tokens Reservados — Governança de Evolução]

## Purpose
Evolução de infraestrutura não é "agrupar novidades de surpresa". Quando um framework cresce agressivamente (versão 3.2 para 3.3), invenções "ad-hoc" de Tokens criam caos semântico em produção. A técnica de Tokens Reservados (`status: RESERVED`) é a fundação para estabelecer um território conceitual antes da sua respectiva implementação técnica, ancorando o design system preventivamente contra entropia (onde times inventam nomes não-oficiais pros mesmos dados).

## Configuration
```yaml
PV_KE_047:
  name: "Preventive Governance via RESERVED Tokens"
  zone: "zone_0.8"
  trigger: "O Chief Architect prevê que o framework requererá uma funcionalidade global nova num futuro de curto/médio prazo (Ex: Cross-process Trigger Registry)."
  evidence_threshold: "framework_evolution_axiom"
  rule: |
    SE existe um conceito estrutural planejado para as próximas versões do framework
    ENTÃO é MANDATÓRIO declarar os IDs formais e as chaves no Registry agora mesmo sob `status: RESERVED` e `target_version: vx.x`, contendo o Rationale.
  veto_condition:
    trigger: "Desenvolvedores ou squads usando tokens não-rastreados em Produção."
    action: "VETO DRACONIANO. Lixo de esquema (Shadow definitions) corrompe o C-Level. Somente tokens no estado 'ACTIVE' podem operar."
```

## Decision Tree
```javascript
IF (identifying_future_system_requirement)
  STEP_1: FORMALIZE the intended architecture for the token.
  STEP_2: INJECT it into the Central Configuration YAML as:
    status: "RESERVED"
    target_version: "v3.3"
  STEP_3: SYSTEM ENFORCES blockage of execution holding reserved keys.
    IF (engineer_attempts_to_use_it_now)
      -> BLOCK compile/validation. Display warning: "Token reserved for future version."
NEVER:
  Entregar novidades conceituais da noite pro dia na corporação, forçando migração "surpresa" sem ter assentado as balizas arquiteturais meses antes na cara dos times.
```

## Failure Modes

### Misapplication / Excess: "O Cemitério de Intenções (Over-booking)"
- **Trigger:** Arquitetos em modo visionário excessivo criam 450 tokens RESERVED projetando 5 anos no futuro de todas as features possíveis baseadas em delírios teóricos.
- **Manifestation:** O arquivo de Registry pesa 3MB textuais com chaves que ninguém tem certeza se entrarão na documentação. Pessoas evitam criar chaves porque "tá tudo super lotado de lixo inativo e engessado".
- **Detection:** Ratio absurdo de Tokens Active vs Reserved (ex: 200 Activos para 600 Reserved parados há mais de 6 meses).
- **Recovery:** Limpeza de higiene. Tokens RESERVED têm prazo de validade (TTL - *Time to Live*). Se o roadmap não bate a meta no lançamento da *Major Version* especificada, descarte-o impiedosamente.
- **Prevention:** Use "target_version" explicitamente para a MESMA ou PRÓXIMA Major/Minor version. Nunca planejar na neblina profunda (> 2 versões).

### Omission / Failure to Activate: "O Fogo de Palha (Ad-Hoc Evolution Chaos)"
- **Trigger:** Cultura startup 100% "Agile Mova Rápido e Quebre Coisas", sem formalização de evolução SINKRA.
- **Manifestation:** Sai um release de inovação de processos cruzados. Três gerentes diferentes adaptam seus ClickUps/sistemas na mesma semana. O primeiro os chama de `[Cross_Trig]`, o segundo os chama de `Hook_ID`, e os da tech os chamam de `x_process_hook`. O painel central quebra a governança.
- **Detection:** Múltiplas convenções concorrendo nativamente contra a espinha dorsal de um processo novo na mesma empresa.
- **Recovery:** Puxão severo do C-Level na auditoria geral. Estabelecimento forçado de um único Dicionário (Migration forçada gerando downtime pro negócio se re-alinhar). Perda tremenda de faturamento diário.
- **Prevention:** Lançamento pré-oficial do "Chassi Vazio" (Registry com Tokens RESERVADOS). Quando virarem "ATIVOS", todo o vocabulário das squads já está unificado sem gastar código.

---

## Validation

**✓ Tensions Acknowledged:** A heurística equilibra preventivismo (evitar caos semântico ad-hoc) com pragmatismo (não criar cemitério de tokens obsoletos).

**✓ Paradox Resolution:** TTL obrigatório força limpeza periódica, removendo tokens não-ativados na janela-alvo. Limite de 2 versões futuras impede planejamento especulativo excessivo.

**✓ Enforceability:** Sistema bloqueia tokens RESERVED em tempo de compilação. Auditoria trimestral valida ratio Active:Reserved para detecção precoce de over-booking.

**Status:** ✅ **Ready for Production** | Testada contra cenários extremos de growth acelerado (v3.1→v3.3) em SINKRA-hub.
