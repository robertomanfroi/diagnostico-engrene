---
id: "PV_KE_085"
title: "The Actionable Veto Feedback Requirement (Anti-Cruelty)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Feedback Loops"
  - "Execution Standards"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  - tension_with: "PV_KE_051 (O Veto da Falsa Ação) vs Structured Actionability"
    resolution: "Complete 5-key contract in structured format (YAML matrix, ≤3 lines per key). Verbose explanation detached in optional 'context' field, activated only if reviewer requests it."
---

# PV_KE_085 - The Actionable Veto Feedback Requirement (Anti-Cruelty)

**Type:** Standard Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:qa-architect
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 13: Feedback Loops / VETO Não é Dead-End]

## Purpose
Exterminar Checkpoints opacos institucionais. Vedar um processo (VETO) sem fornecer instrução de remediação rastreável e específica é *crueldade administrativa* travestida de controle de qualidade. Esta heurística obriga que qualquer Veto no SINKRA seja, por definição de tipo rígido, uma "Exceção Rica" que guie o Designer de volta à trilha. Um Checkpoint sem feedback algorítmico e mensurável não é um Checkpoint, é uma "opinião institucionalizada". O VETO SINKRA diz: Falhou Aqui, Por causa Deste Número, Corrija Fazendo Alpha, Beta e Gamma.

## Configuration
```yaml
PV_KE_085:
  name: "Cruelty-Free Veto Contract"
  zone: "zone_0.8"
  trigger: "Sempre que uma flag VETO ou REVIEW saltar em um Checkpoint Heurístico ou META_AXIOMA."
  evidence_threshold: "data_types"
  rule: |
    Todo VETO ou REVIEW emitido DEVE conter o contrato algorítmico de 5 chaves preenchido:
    1. Score: O valor numérico que causou o problema.
    2. Threshold: O valor mínimo esperado.
    3. Dimensão/Falha: Referência formal no modelo.
    4. Causa Raiz de Negócio: Por que quebrou estruturalmente no Mundo Real.
    5. Ação Recomendada: Comando atômico operacional (Task level) do que deve ser digitado/projetado para ser Aprovo na resubmissão.
    Se um Checkout do Pipeline lançar erro como "Processo fraco" ou "Não Atende ao Padrão", ele mesmo quebrou seu Contrato Quality Gate.
```

## Decision Tree
```javascript
IF (a_QA_system_or_Heuristic_detects_a_breach)
  STEP_1: COMPILE the Actionable Payload BEFORE returning false.
    SCORE = 5.8
    THRESHOLD = 6.0
    DIMENSION = Risk_Management
    CAUSE = 'Tasks enviarPagamento sem retry logic'
    ACTION = 'Adicionar error_handling: retry(3) e alert_on_failure(true)'
  STEP_2: RETURN the full payload.
    IF (The reviewer says: 'It feels unaligned. Reject.')
      -> AUTO-FIX / DENY THE REJECT. "Opinions without metric vectors cannot halt deterministic pipelines."
NEVER:
  Confundir o ato de encontrar defeitos processuais com a habilidade de resolver fluxos. Um VETO calado apenas recicla confusão; O VETO parametrizado induz a uma correção cirúrgica num tempo T previsível.
```

## Failure Modes

### Misapplication / Excess: "O Detalhismo Obstrutivo Oculto"
- **Trigger:** Checkpoints fornecem payloads de feedback gigantescos (3 páginas) e prolixos (filosofia da qualidade) a cada vírgula errada que emitem num VETO.
- **Manifestation:** O Time perde mais tempo lendo os tratados do Bot de Veto do que apenas abrindo o código e aplicando a correção. Feedback longo mascara a ação concreta no fundo do YAML.
- **Detection:** Reclamações que a burocracia do feedback superou a própria complexidade da Task originadora.
- **Recovery:** Aja como Míssil, não como Conferência. O Feedback do Veto Actionable DEVE ser conciso. `Acao_recomendada: Adicionar error_handling: retry no nó Zyx`. Simples, 3 linhas. Nenhuma lição de moral atrelada. Use `Fail-Fast` visual e mecânico.

### Omission / Failure to Activate: "A Caixa Preta Rejeitadora"
- **Trigger:** Checkpoints mal configurados (Anti-Pattern 1 e 5) dão "FAIL" ou "VETO" usando Strings hardcoded opacas do tipo `feedback: Processo não atende critérios.`
- **Manifestation:** Frustração profunda do arquiteto, retrabalho por tentativa-e-erro "na base do chute", estresse de equipe. Resultado clássico: os designers tentam adivinhar o que a Máquina ou a Gerência quer, alterando coisas irrelevantes ao redor do nó problemático, atrasando cronogramas do Masterplan.
- **Detection:** Multiplas iterações `(Submete -> Veto -> Submete -> Veto)` com zero progresso no Score, e as pessoas enviando mensagens como "Me fala logo o que é pra mudar que eu mudo!".
- **Recovery:** Forçar a Validação Estrutural da Própria Arquitetura de QA. No SINKRA, um Checkpoint que retorna uma string opaca não é executável, e seu Output é dropado (considerando a arquitetura do próprio Node de QA inválida). O Contrato do VETO com a matriz de 5 Chaves é um forte Data Type Obrigatório.

---

## Validation

**Compliance Checklist:**
- ☑ Every VETO contains Score, Threshold, Dimension, Cause, Action (5-key matrix)
- ☑ Action is operationally atomic (single task or command, ≤3 lines)
- ☑ Feedback payload is compact YAML, not prose (Fail-Fast principle)
- ☑ Optional verbose context field does NOT block pipeline execution
- ☑ Tension resolved: structured completeness + concise delivery via matrix format

**Paradox Resolution:** The 5-key contract provides completeness (no blind rejections), while YAML matrix structure + optional context field ensures conciseness (missiles, not conferences). Paradox dissolved by separating mandatory signal from optional narrative.
