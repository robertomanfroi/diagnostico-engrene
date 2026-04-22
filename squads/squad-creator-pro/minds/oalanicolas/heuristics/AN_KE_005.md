---
id: "AN_KE_005"
title: "Determinism First (Code > LLM)"
mind: "oalanicolas"
type: "heuristics"
zone: "excelencia"
tags:
  - "Architecture"
  - "Reliability"
  - "Performance"
pipeline_instances:
  - "process-architecture"
  - "system-scaling"
cross_mind_map:
  convergent:
    - id: "PV_PA_004"
      title: "Zero-Cost Determinism (Worker First)"
      mind: "pedro_valerio"
      resonance: "Convergência total. AN prioriza determinismo puro (Code > LLM). PV declara a prioridade de Workers (scripts RPA) para cenários totalmente booleanos sem contexto subjetivo para poupar API tokens. Mesmo axioma tático, linguagem direcionalmente distinta."
    - id: "PV_PA_019"
      title: "Deterministic Assignment (The Worker Rule)"
      mind: "pedro_valerio"
      resonance: "PV formaliza a regra tática Worker para lógicas exatas sem variância. AN advoga por Determinism First. Aplicação exata do mesmo princípio técnico no planejamento."
  tension:
    - id: "PV_PA_005"
      title: "Directed Stochasticity (Variance as a Feature)"
      mind: "pedro_valerio"
      divergence: "PV argumenta que a variância estocástica é o core power do LLM e deve ser gerenciada a jusante (post-generation), não limitada em pre-generation. AN prioriza o corte da variância antes dela acontecer substituindo IA por Código sempre que possível. Focam em extremidades operacionais opostas (onde usar versus onde evitar)."
      invalidates: false
---

# AN_KE_005 - Determinism First (Code > LLM)

**Type:** Architecture Heuristic
**Phase:** 4 (Molecular Assembly)
**Agent:** @process-architect
**Pattern:** HO-PP-AN005

## Purpose

Castrar a preguiça técnica do dev ou do Agente Orquestrador. Obrigar o uso estrito de limites matemáticos e computacionais em vez de delegar operações rígidas de validação e controle a Grandes Modelos de Linguagem (LLMs). Raciocínios são estocásticos. Delegar uma validação determinística de tipagem ou Regex a um LLM por luxo tecnológico é suicídio operacional, lentidão agressiva e queima injustificável de tokens. Code > LLM.

## Configuration

```yaml
AN_KE_005:
  name: "Determinism First"
  phase: 4
  zone: "excelencia"
  trigger: "Estruturando lógicas de roteamento estrito, contadores validadores, scrapers ou parsers de JSON/YAML."

  weights:
    immutability_enforcement: 1.0
    token_conservation: 1.0

  thresholds:
    llm_math_tolerance: 0.0

  veto_conditions:
    - condition: "using_llm_for_strict_type_checking_or_regex_parsing == true"
      action: "VETO - Delírio Tecnológico. Stop using probabilistic stochastic engines to hammer nails. Use Native Code (Worker)."

  output:
    type: "decision"
    values: ["APPROVE_NATIVE_WORKER", "SHIFT_TO_LLM_SEMANTICS", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "misapplication"
    name: "Computational Stupidity / LLM Math (The Zealot)"
    trigger: "Obrigar o LLM a fazer contagem matemática complexa de tokens, strings ou cruzar objetos relacionais em JSON."
    manifestation: "O desenvolvedor diz 'Seja muito rigoroso, garanta que não perca nenhuma linha' no system_message do Agent. O pipeline quebra de madrugada porque o LLM esqueceu uma vírgula (erro de complacência estatística)."
    detection: "Scripts Python que mandam payloads inteiros para a API da Anthropic apenas para reformatá-los como um `.csv`."
    recovery: "Extirpar o LLM da cadeia matemática/sintática final. Inserir blocos rígidos de Pydantic, Zod TypeScript ou Bash regex nativos."

  - type: "omission"
    name: "Over-Engineering the Soup (The Paranoiac)"
    trigger: "Escrever rotinas de Regex gigantescas e indecifráveis para tentar adivinhar nuances complexas de interpretação humana."
    manifestation: "O dev escreve 900 linhas de Regex em Node para tentar fisgar sentimentos de humor abstrato ou ironia em um chat de suporte. A engine falha miseravelmente diante de sarcasmo real."
    detection: "Expressões Regulares contendo 40 ORs tentado abraçar variações sintáticas fluidas."
    recovery: "Aceitar a limitação do Código Rígido contra nuvem semântica. Se envolve humor ou dialeto caótico, MATE o Regex e substitua por apenas 1 call barata e veloz via LLM Haiku / Flash."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Immutability Distinction"
    weight: 1.0
    threshold: "=== TRUE"
    description: "Essa operação tem apensa UMA forma matemática correta de se resolver? (Se SIM = Extirpar LLM, Usar Script Rígido)."
  - metric: "Semantic Requirement"
    weight: 1.0
    threshold: "=== TRUE"
    description: "O sucesso desta operação demanda interpretação de ruído não estruturado, nuances, empatia ou criatividade? (Se SIM = Extirpar Script Rígido, Chamar Agente LLM)."
  - metric: "Zero-Cost Execution"
    weight: 0.9
    threshold: "=== TRUE"
    description: "Essa validação poderia ser executada em 5ms usando Zod ou Regex nativos de graça?"
```

## Decision Tree

```javascript
IF (O input exige contagem de caracteres estrita, formatação tipográfica, ou validação de YAML/JSON schema) {
  VETO("LLM Prompt Dependency");
  ASSIGN("EXECUTOR_TIER = NATIVE_WORKER (Bash / TypeScript / Python)");
} ELSE IF (O loop engloba interpretação semântica da massa de dados, nuances emocionais ou síntese abstrata) {
  ASSIGN("EXECUTOR_TIER = SEMANTIC_AGENT (Claude Haiku / Gemini Flash)");
}

NEVER("Pedir por favor a um robô bilionário de Linguagem Neural que ordene um array de números em ordem alfabética.");
```
