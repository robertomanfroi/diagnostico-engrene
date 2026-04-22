---
id: "AN_KE_040"
title: "Agnosticização Mandatória em Infra"
mind: "oalanicolas"
type: "heuristics"
zone: "excelencia"
tags:
  - "Architecture"
  - "Portability"
  - "Infrastructure"
pipeline_instances:
  - "process-architecture"
  - "system-scaling"
cross_mind_map:
  convergent:
    - id: "PV_PA_033"
      title: "Executor Transversality"
      mind: "pedro_valerio"
      resonance: "Padrão de Infraestrutura Limpa: Módulos Core do Hub SINKRA (como Service Bus) não ligam se são de AIOX ou Synkra. PV eleva isso ao status de Executor Universal: 'se mudar o agente e a tela não muda, sua infra é transversal de fato'."
    - id: "PV_PA_011"
      title: "Optimization Interchangeability (Process Extinction)"
      mind: "pedro_valerio"
      resonance: "Ao modularizar tudo, você alcança o cenário apontado por PV onde modelos de custo alto podem ser sacados e executores baratos instalados na engrenagem sem tocar no fluxo inteiro."
---

# AN_KE_040 - Agnosticização Mandatória em Infra

**Type:** Architecture Standard Heuristic
**Phase:** 2 (Structural Assembly)
**Agent:** @process-architect
**Pattern:** HO-PP-AN040

**sys_tension:**
- **tension_with:** AN_KE_070 (Multi-IDE Sync Protocol) vs Agnóstico Completo de Infra
- **resolution:** Agnóstico máximo + test matrix mínima (3 contextos: local, Docker, cloud). Cobertura > Genericidade quando há conflito.

## Purpose

Prevenir a criação de scripts de infraestrutura (parsers, validadores, pipelines genéricos, deployers compartilhados) que contêm nomes de projetos específicos hardcoded ("MMOS", "AIOX", `/Users/<username>`). Scripts de infraestrutura nasceram para servir N repositórios e N clientes. Quando não são agnósticos, morrem na primeira mudança de contexto — tornando-se dívida técnica imóvel.

## Configuration

```yaml
AN_KE_040:
  name: "Agnosticização Mandatória em Infra"
  phase: 2
  zone: "excelencia"
  trigger: "Criando utilitários compartilhados, pipelines raiz, bash scripts genéricos ou qualquer script que atue fora do escopo restrito de um Squad."

  weights:
    dynamic_argument_usage: 1.0
    literal_path_or_name_contamination: 1.0

  thresholds:
    hardcoded_project_name_tolerance: 0
    hardcoded_local_path_tolerance: 0

  veto_conditions:
    - condition: "infrastructure_script_contains_literal_project_name_or_local_user_path == true"
      action: "VETO - Infrastructure Lock-in. Replace all literals with dynamic arguments ($PROJECT_ROOT, $CLIENT_ID) passed by the caller."

  output:
    type: "decision"
    values: ["APPROVE_AGNOSTIC", "REQUIRE_PARAMETRIZATION", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "Works on My Machine Syndrome (The Coward)"
    trigger: "Alan empacota a infraestrutura fantástica do projeto MMOS para distribuir como ferramenta pública 'SuperAgentes'."
    manifestation: "Todos os pipelines morrem com Pathing Error. Os scripts contêm `cd mmos` e chamadas a `PROJECT_ROOT=/Code/sinkra-hub`. Zero portabilidade."
    detection: "Sentry mostrando erros de path em bloco para novos usuários. Arquivo funciona localmente, quebra em qualquer outro ambiente."
    recovery: "Grep global para caminhos `/Users/`, nomes literais de projeto, substituindo por `${PROJECT_ROOT:-$(pwd)}`. Teste em Docker limpo."

  - type: "misapplication"
    name: "Over-Parametrization (The Zealot)"
    trigger: "Dev parametriza absolutamente tudo, incluindo valores que nunca variam (ex: versão do protocolo, encoding charset)."
    manifestation: "Script de 20 linhas exige 15 argumentos de CLI para rodar, sendo 12 deles constantes imutáveis de domínio."
    detection: "README do script tem mais linhas de argumento documentation que o script em si."
    recovery: "Distinguir: Variável de Contexto (path, client_id, project_name) = argumento dinâmico. Constante de Protocolo (encoding=UTF8, schema_version=1.2) = hardcoded é OK."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Path Agnosticism"
    weight: 1.0
    threshold: "=== 0 literal paths"
    description: "Zero caminhos absolutos de usuário (/Users/<username>/) ou projeto (/Code/mmos) estão hardcoded no script?"
  - metric: "Dynamic Arguments"
    weight: 1.0
    threshold: "=== TRUE"
    description: "O script aceita PROJECT_ROOT, CLIENT_ID e equivalentes como argumentos $1/$2 ou env vars para operar em qualquer contexto?"
```

## Decision Tree

```javascript
IF (Criando Script de Infraestrutura Compartilhada) {
  SCAN("Literal paths e project names: /Users/, /Code/mmos, AIOX, <agent_owner>");
  
  IF (Literals_Found > 0) {
    VETO("Infrastructure Lock-in detected.");
    REQUIRE_PARAMETRIZATION("Substituir literals por: PROJECT_ROOT=$1, CLIENT_ID=$2, ou env var.");
  } ELSE {
    SIMULATE("Docker limpo. Rodar script com args dinâmicos apenas.");
    IF (Test_Passes === TRUE) {
      APPROVE_AGNOSTIC("Script agnóstico. Portável para qualquer cliente.");
    }
  }
}

NEVER("Criar scripts de infraestrutura que referenciam literalmente o nome do projeto atual, caminhos de máquina local ou identidades de cliente.");
```

## Validation

**Checklist de Conformidade AN_KE_040:**

- [ ] Script/utilitário não contém strings literais de projeto (MMOS, AIOX, AllFluence, etc.)
- [ ] Paths não são absolutos hardcoded (`/Users/<username>`, `/Code/...`)
- [ ] Todos os paths críticos são argumentos dinâmicos ou variáveis de ambiente
- [ ] Testado em pelo menos 3 contextos: local filesystem, Docker container, cloud (S3/GCS)
- [ ] Documentation descreve como chamar e quais env vars são obrigatórios
- [ ] Código de infra NUNCA assume a máquina do autor — assume apenas Node.js 18+ e bash/sh
- [ ] Gate validado antes de merge em `.aiox-core/infrastructure/`
