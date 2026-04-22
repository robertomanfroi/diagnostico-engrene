# Changelog - Squad Creator

Todas as alterações notáveis no squad-creator serão documentadas aqui.

---

## [6.0.0] - 2026-04-04

### Fusão Kaizen — Ecosystem Mode Integrado

**Story**: EPIC-108 (STORY-108.1 → STORY-108.5)
**Tipo**: Structural fusion + SINKRA-native certification

#### Adicionado

- **Ecosystem Mode**: Observabilidade contínua do ecossistema absorvida do squad kaizen
  - Agente `ecosystem-analyst` (squads/squad-creator-pro/agents/ecosystem-analyst.md) — distilação das 7 inteligências kaizen em 6 lentes internas
  - 8 tasks migradas do kaizen com header de provenance `migrated_from: kaizen`:
    - `detect-gaps.md` — Lente 4: Capability Gap Analysis
    - `performance-dashboard.md` — Lente 2: Performance Monitoring
    - `update-radar.md` — Lente 5: Technology Radar
    - `cost-analysis.md` — Lente 6: Cost & ROI
    - `generate-recommendations.md` — Síntese para `*analyze` e `*report`
    - `self-improve.md` — Meta-lente: auto-auditoria do ecossistema
    - `audit-output-quality.md` — Complemento qualitativo de `*qa-after-creation`
    - `auto-healing-gate.md` — Pré-condição de qualidade para `*analyze`
  - 3 workflows migrados do kaizen:
    - `wf-ecosystem-analysis.yaml` — Pipeline completo de análise (6 fases)
    - `wf-weekly-report.yaml` — Cadência semanal de relatório
    - `wf-self-improve.yaml` — Loop de meta-melhoria
  - Novos comandos no squad-chief: `*analyze`, `*topology`, `*performance`, `*bottleneck`, `*gaps`, `*radar`, `*cost`, `*report`
  - Templates de saída: `ecosystem-health-tmpl.md`, `gap-analysis-tmpl.md`, `performance-dashboard-tmpl.md`, `tech-radar-tmpl.md`, `weekly-report-tmpl.md`
  - Artifact contracts para todos os artefatos de observabilidade
  - Domínio `Observability` adicionado ao `domain_model`
  - Entities: `EcosystemHealthReport`, `CapabilityGapAnalysis`, `TechRadarReport`

- **fusion_provenance**: Registro completo da fusão com kaizen (ADRs 108.1-001, 108.1-002, 108.2-001, 108.2-002, 108.2-003)
- **sinkra_native: true**: Certificação SINKRA-native v6.0.0 (score: 9.5)

#### Alterado

- `config.yaml`: versão 5.x → 6.0.0, novos campos `fusion_provenance`, `sinkra_native`, domínio `Observability`
- `composition_mapping`: adicionadas moléculas `mol-ecosystem-analysis` e `mol-weekly-cadence`; organismos `org-ecosystem-analysis`, `org-weekly-report`, `org-self-improve`
- `activation.shortcuts`: adicionado `/squadCreator:ecosystem-analyst`
- `process_token_contract`: tokens_declared 29 (estável — kaizen não declarava tokens novos)
- `metadata.base_stats`: tasks 139 (absorção kaizen), workflows 24+ (3 novos)
- README.md: seção Ecosystem Mode adicionada

#### ADRs Registrados

- `ADR-108.1-001`: Kaizen agents NÃO absorvidos individualmente — inteligência destilada em ecosystem-analyst
- `ADR-108.1-002`: Kaizen minds arquivados — preservados como ghost layer temporário (STORY-108.6 pendente)
- `ADR-108.2-001`: Ecosystem-analyst com 6 lentes internas (não 6 agentes)
- `ADR-108.2-002`: 8 tasks kaizen absorvidas integralmente
- `ADR-108.2-003`: Tiers isolados garantem independência criação vs observabilidade

---

## [4.0.0] - 2026-02-24

### Base/Pro Architecture Split (SCPRO Epic)

- **SCPRO.1:** Complete dependency mapping and asset classification (53 tasks → 20 base + 33 pro)
- **SCPRO.2:** Restructure base with pro detection
  - Rewrite squad-chief.md (1779→1011 lines) with silent pro detection at boot
  - Rewrite 6 base tasks: create-squad, create-agent, discover-tools, upgrade-squad, install-skills, validate-squad
  - Simplify 2 base workflows: create-squad.yaml (353→280 lines), validate-squad.yaml (new, 222 lines)
  - Stage 33 pro tasks, 17 pro workflows, 3 specialist agents to _staging/
- **SCPRO.3:** Create squads/squad-creator-pro/ upgrade pack
  - config.yaml with type: upgrade-pack, enhances: squad-creator, v3.1.0
  - Migrate all pro assets from _staging/ with path reference updates (143 refs)
  - Feature manifest: mind-cloning, research, advanced-creation, optimization, model-routing, quality, maintenance, strategy
- **SCPRO.4:** Unify entry points
  - .claude/agents/squad-creator.md → loads squad-chief persona directly
  - .claude/agents/squad-chief.md → deprecation redirect
  - Remove legacy Claude command surface for SquadCreator (37 files, third copy eliminated)
- **SCPRO.5:** Dual-mode testing, degradation verification, final audit
  - All 53 tasks accounted for: 20 base + 33 pro, zero duplication
  - Registry migrated to {registry_path}
  - Zero broken references, all YAML valid

### Alterado
- Version: 3.1.0 → 4.0.0
- config.yaml: metadata.type = "base", metadata.pro_detection = true
- Single activation path: @squad-creator (no separate @squad-chief)

---

## [3.2.1] - 2026-02-04

### Adicionado
- **T3-DOC: Changelog separation check**
  - Verifica se tasks >= v2.0.0 têm CHANGELOG.md separado
  - Referencia HO-DP-001 do best-practices.md
  - Peso: 1 ponto no score de Documentation

---

## [3.2.0] - 2026-02-04

### Adicionado
- **T2-TOOL-001: Tool Registry Validation**
  - Valida `tool-registry.yaml` se squad usa tools/MCPs externos
  - Verifica se tools declaradas são acessíveis
  - Alerta se tools não documentadas no README

- **T3-OPT: Optimization Opportunities Check**
  - Identifica tasks Agent que poderiam ser Worker (economia de custo)
  - Referencia `executor-decision-tree.md` (Q1-Q6)
  - Fornece projeção econômica (estimativa de economia mensal)
  - Apenas informacional, não bloqueia

- **T4H-EX: Executor Decision Tree Validation** (Hybrid squads)
  - Valida campo `execution_type` nas tasks
  - Verifica aplicação correta do decision tree Q1-Q6
  - Confirma que tasks Worker têm scripts
  - Confirma que tasks Hybrid têm `human_checkpoint`
  - Valida fallback chain definido
  - Peso: 35% do score Hybrid (REQUIRED)

### Alterado
- Ajustados pesos TIER 3: 20% cada (era 25%)
- Ajustados pesos TIER 4 Hybrid para acomodar executor validation
- Atualizada tabela Quick Reference com novos componentes
- Adicionadas referências a `executor-decision-tree.md`, `tool-registry.yaml`, `optimize.md`

---

## [3.1.0] - 2026-02-02

### Corrigido
- Minor fixes e clarificações

---

## [3.0.0] - 2026-02-01

### Adicionado
- Detecção de tipo de squad (Expert/Pipeline/Hybrid)
- Sistema de validação em 4 tiers
- Prompt quality, pipeline coherence, checklist actionability checks
- Coverage ratio checks
- Type-specific veto conditions

### Alterado
- `voice_dna`/`objection_algorithms` agora são contextuais (não obrigatórios para todos)
- Alinhamento com `squad-checklist.md` v3.0

---

## [2.0.0] - 2026-01-15

### Alterado
- Abordagem de validação qualitativa
- Checks baseados em princípios

---

## [1.0.0] - 2025-12-01

### Adicionado
- Task inicial de validação
