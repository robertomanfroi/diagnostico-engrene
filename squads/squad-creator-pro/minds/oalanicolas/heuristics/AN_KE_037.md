---
id: "AN_KE_037"
title: "Single Source of Truth (Business)"
mind: "oalanicolas"
type: "heuristics"
zone: "excelencia"
tags:
  - "Architecture"
  - "Data Governance"
  - "Knowledge Management"
pipeline_instances:
  - "process-architecture"
  - "scaffolding"
---

# AN_KE_037 - Single Source of Truth (Business)

**Type:** Architecture Standards Heuristic
**Phase:** 2 (Structural Assembly)
**Agent:** @process-architect
**Pattern:** HO-PP-AN037

---

**YAML Metadata:**
```yaml
AN_KE_037:
  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) — Centralização absoluta no Workspace vs. Paralelização operacional que exige acesso distribuído (squads precisam ler Supabase, /docs, código simultaneamente)"
    resolution: "Workspace como SSOT canônico para config/estratégia L0-L1; cache distribuído (Supabase) para R/O operacional; validação periódica de drift"
```

## Purpose

Evitar deriva existencial e desalinhamento multi-agente. Ter as definições corporativas vitais (ICP, Persona, Missão, Tech Stack) espalhadas em `/docs`, `/supabase`, Notion, arquivos root de squads e repositórios paralelos cria múltiplas fontes parcialmente atualizadas que eventualmente divergem. A única fonte aceita para consulta corporativa deve ser o `workspace/` root centralizado, blindado e versionado.

## Configuration

```yaml
AN_KE_037:
  name: "Single Source of Truth (Business)"
  phase: 2
  zone: "excelencia"
  trigger: "Buscando ou armazenando dados operacionais corporativos: ICP, Missão, Persona de Marca, AI Strategy ou Tech Stack oficial."

  weights:
    workspace_centralization: 1.0
    peripheral_storage_risk: 1.0

  thresholds:
    business_data_outside_workspace_tolerance: 0

  veto_conditions:
    - condition: "business_identity_data_stored_in_squad_directory_or_docs_instead_of_workspace == true"
      action: "VETO - SSOT Violation. Move data to workspace/ root. Squads are consumers, never owners of business identity."

  output:
    type: "decision"
    values: ["APPROVE_WORKSPACE_STORAGE", "MIGRATE_TO_WORKSPACE", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "Desalinhamento Ideológico Multi-Agente (The Coward)"
    trigger: "Squad de Email Marketing copia a Persona do Notion enquanto o Squad de Design a lê de `/docs/brand.md`."
    manifestation: "O Email é gerado para 'programadores sêniors de startups' enquanto o layout do site foi montado para 'executivos C-Level de médias empresas'. Esquizofrenia de branding."
    detection: "Revisão de marketing aponta divergência inexplicável de tom e target entre os outputs da semana."
    recovery: "Migração forçada de todas as refs de identidade para workspace/ root. Re-run de todos os squads consumidores dessa semana."

  - type: "misapplication"
    name: "Workspace Over-centralization (The Zealot)"
    trigger: "Dev move até arquivos de runtime operacional (logs, temp states) para dentro do workspace/."
    manifestation: "Workspace/ vira um dump geral de 500 arquivos misturando dados estratégicos com lixo operacional temporário."
    detection: "Workspace/ com arquivos de log e temp JSON misturados a YAML de identidade."
    recovery: "Separar estritamente: workspace/ = dados imutáveis de identidade de negócio. `/outputs/`, `/tmp/` = dados efêmeros operacionais."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Workspace Centralization"
    weight: 1.0
    threshold: "=== 1 source"
    description: "Apenas 1 local no repositório contém a definição canônica de ICP, Persona e Missão da empresa?"
  - metric: "Squad Consumer Pattern"
    weight: 1.0
    threshold: "=== TRUE"
    description: "Todos os squads que precisam de dados de identidade buscam exclusivamente via path referência ao workspace/ root?"
```

## Decision Tree

```javascript
IF (Buscando ou Armazenando Dados de Identidade Corporativa) {
  EVALUATE("Localização do storage");
  
  IF (Storage_Location !== "workspace/") {
    VETO("SSOT Violation.");
    MIGRATE_TO_WORKSPACE("Centralizar em workspace/{business-slug}/L0-identity/ ou L1-strategy/.");
  } ELSE {
    APPROVE_WORKSPACE_STORAGE("Dado de identidade no workspace/ canônico.");
  }
}

NEVER("Armazenar ICP, Persona ou Tech Stack oficial hardcoded dentro de pastas de squad ou /docs/. Squads são consumidores, nunca donos de identidade corporativa.");
```

---

## Validation

**Paradox Identified:** Centralização absoluta (SSOT único no Workspace) conflita com realidade operacional de 60+ squads que precisam acessar dados em múltiplas camadas (Supabase, /docs/brands, código).

**Resolution Approach:**
- ✅ **Camada Canônica (L0-L1):** Workspace = SSOT inviolável (persona, missão, structure)
- ✅ **Camada Operacional (L2-L4):** Supabase + /docs como cache validado, sincronizado periodicamente com Workspace
- ✅ **Validação de Drift:** Checklist `ssot-business` dispara reconciliação se detiver divergências >10%

**Critical Implication:** Sem esta tensão resolvida explicitamente, o risco é: centralizadores criarão lock-in insustentável; descentralizadores criarão caos de múltiplas verdades. Solução: **Hub-and-Spoke com single source of truth referencial, não operacional.**
