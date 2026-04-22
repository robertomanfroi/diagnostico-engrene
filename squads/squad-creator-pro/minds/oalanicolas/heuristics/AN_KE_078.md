# AN_KE_078 - Names Not IDs as Identity
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão sinkra-hub ee0a7008 — migração squad-creator-pro, identidade de founders]

## Purpose

Quando artefatos representam PESSOAS reais (founders, experts, agents), usar nomes reais — não anonimizar com IDs, slugs, ou roles genéricos. Pessoas são DNA do sistema, não recursos intercambiáveis. Alan exige que o sistema reflita identidade: "eles são parte do DNA." Isso se aplica a minds no squad-creator-pro (oalanicolas, pedro-valerio, thiago-finch), agents no CODEOWNERS, e qualquer artefato que represente decisões de pessoas reais.

## Configuration

```yaml
AN_KE_078:
  name: "Names Not IDs as Identity"
  zone: "excelencia"
  trigger: "Criando artefato que representa pessoa real: mind, agent, CODEOWNER, founder profile."
  sys_tension:
    tension_with: "AN_KE_034 (Ghostwriting/Autorship) — rastreabilidade de DNA vs anonimização de privacidade em clones."
    resolution: "Critério administrativo: se pessoa é nomeada em CODEOWNERS ou squad-creator-pro/agents/, usa nome real (DNA). Se é cliente/prospect, anonimiza (privacidade)."

  rule: |
    SE artefato representa PESSOA real (founder, expert, mentor, agent)
    ENTÃO usar nome/username real, não anonimizar.
    Pessoas-chave são DNA do sistema — identidade é design, não dados.
    EXCEÇÃO: dados sensíveis de terceiros (clientes, leads) → anonimizar.
    REGRA: internos = nomes reais. Externos = proteção de privacidade.

  veto_condition:
    trigger: "Substituindo nomes de founders/experts por IDs genéricos ('founder_1', 'expert_A')."
    action: "VETO — 'nao devemos anonimizar, eles sao parte do DNA.' Use nomes reais para internos."

  evidence:
    - "[SOURCE: sessão ee0a7008, sinkra-hub] 'nao devemos anonimizar, eles sao parte do DNA'"
    - "[CONTEXT] Diretórios minds/ em squad-creator-pro usam nomes reais: oalanicolas/, pedro-valerio/, thiago-finch/"
    - "[CONTEXT] CODEOWNERS usa 3 founders por nome para aprovação de paths shared"
```

## Decision Tree

```javascript
IF (creating_artifact_representing_person)
  STEP_1: CLASSIFY person
    IF (internal: founder, expert, team member) → USE real name/username
    IF (external: client, lead, prospect) → ANONYMIZE for privacy
    IF (public figure: expert being cloned) → USE real name (they're the product)

  STEP_2: APPLY naming
    Directories: minds/oalanicolas/ (not minds/founder_001/)
    Agents: @pedro-valerio (not @agent_02)
    CODEOWNERS: real GitHub usernames
    Heuristic cards: AN_KE_NNN by @oalanicolas

  NEVER: anonymize internal team members — they ARE the system
  NEVER: use real names for external client data — privacy first
```

## Failure Modes

### O Clone Sem Nome
- **Trigger:** Building mind-cloning system with anonymous IDs for all personas.
- **Manifestation:** System loses the "who" — decisions traced to "mind_47" instead of the person who made them.
- **Detection:** Artefatos usam IDs onde deveriam usar nomes. `grep -r "founder_\|expert_\|mind_[0-9]" minds/`
- **Prevention:** Names for DNA, IDs for data. Founders and experts ARE the identity of the system.

## Validation

✅ **Paradoxo resolvido:** Tensão entre "nomes para rastreabilidade DNA" (internos) e "anonimização para privacidade" (externos) → **Critério administrativo como fonte de verdade.** Se CODEOWNERS ou squad-creator-pro declaram a pessoa, usa-se nome real. Clientes/prospects → anonimizar por padrão, exceto se expressamente autorizado em contrato L1-strategy/legal.
