# AN_KE_105 - Architectural KISS Challenge
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão aiox-core/arquitetura — "comparou com a esrtutura atual"]

## Purpose

A Síndrome do Over-Engineering ataca desenvolvedores e IAs quando recebem um domínio novo. A primeira intuição irresponsável de um Agente é modelar do zero uma "Nova Arquitetura Robusta", construindo castelos no backend com enums inéditos. O desafio KISS do Alan barra a ansiedade arquitetural. A regra prescreve que o Agente é rigorosamente obrigado a provar que a infraestrutura anterior DE FATO falhou em atender ao novo escopo, analisando a composição das classes/dados existentes *antes de rascunhar qualquer nova interface.*

## Configuration

```yaml
AN_KE_105:
  name: "Architectural KISS Challenge"
  zone: "genialidade"
  trigger: "Proposta de recriação de tabelas, grandes epics de novas arquiteturas ou design de domínios (DDD)."

  sys_tension:
    tension_with: "AN_KE_106 (Subagents Over Flattened Tasks) — parallelization drives architectural complexity vs KISS simplicity"
    resolution: "Distinguish between legacy reuse patterns (apply KISS) and truly novel contexts (require evidence that existing cannot adapt). Use IDS Principles gates G1-G6 to evaluate fit before deciding REUSE vs CREATE."

  rule: |
    SE você arquitetar uma estrutura inteiramente nova (novas rotas UI, novos Schemas)
    ENTÃO OBRIGATÓRIA A ETAPA: Defender a "Inutilização do Antigo".
    Avalie o que pode ser reusado das views/pipelines legadas no projeto.
    NÃO aplique soluções mastodônticas antes de atestar a completa derrocada de um design MVP anterior.

  veto_condition:
    trigger: "Agente sugere criar 4 `tables` PostgreSQL e GraphQL routes pra gerir eventos sem consultar a estrutura atual EventSourcing presente."
    action: "VETO — 'Está aplicando KISS? analisou se essa arquitetura toda é REALMENTE necessária? comparou com a estrutura atual para entender o que pode ser aprovaitado dela?'."

  evidence:
    - "[SOURCE: histórico manual] 'Está aplicando KISS? analisou se essa arquitetura toda é REALMENTE necessária? comparou com a esrtutura atual para entender o que pode ser aprovaitado dela? isso tudo precisa estar de forma nativa na sua tast de domain'"
```

## Decision Tree

```javascript
IF (designing_brand_new_component_or_data_pipeline)
  STEP_1: PAUSE construction logic.
  STEP_2: QUERY existing counterparts (`search_web`, `grep_search`).
  STEP_3: CHECK: How much of the existing data payloads solve 80% of our need?
  STEP_4: EJECT newly created files IF simple prop-overriding on legacy architecture resolves the epic.
  STEP_5: BUILD ONLY the delta requirements.
```

## Failure Modes

### Over-Engineering Delusion
- **Trigger:** Agente decide recriar um módulo UI de Cartões Psicográficos inteiro usando `recharts` puro, ignorando totalmente a livraria `shadcn/ui` que estava gerindo os `Cards` da dashboard ao lado.
- **Manifestation:** O projeto enche de bibliotecas redundantes (Moment + DateFNS, Shadcn + Radix Puro + Headless).
- **Prevention:** O Desafio de Simplicidade Inicial (KISS Challenge).

---

## Validation

**Paradoxo Identificado:** Conservadorismo arquitetural vs. Inovação necessária — O heurístico proíbe criar novos quando o antigo poderia servir, mas contextos genuinamente novos exigem estruturas adaptadas.

**Resolução:** Aplicar avaliação por gates (IDS Principles G1-G6) para distinguir entre:
1. **Legacy Reuse Patterns** (KISS applies): Estrutura existente pode ser reconfigurada com 80%+ cobertura → REUSE/ADAPT
2. **Genuinely Novel Contexts** (CREATE justified): Análise prova incompatibilidade estrutural → CREATE com documentação

**Aplicação:** Toda proposta de arquitetura nova DEVE passar por:
- G1 (Existe?) + G2 (Funciona sem modificação?)
- Se SIM → REUSE (segue KISS Challenge)
- Se NÃO → G3-G6 (avaliar adaptabilidade, compatibilidade, manutenibilidade)
- CREATE é autorizado apenas se G3-G6 validarem impossibilidade de adaptação
