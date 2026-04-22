# Task: Classify Tools by Category and Relevance

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `discover-tools-classify` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Agent` |

## Metadata

```yaml
id: discover-tools-classify
name: "Classify Tools by Category and Relevance"
category: discovery
agent: squad-chief
elicit: false
autonomous: true
description: >
  Searches official and community MCP repositories for servers matching
  identified capability gaps. Classifies findings by source type, domain
  relevance, and quality signals. Corresponds to Phase 1 search steps
  of the original discover-tools pipeline.
accountability:
  human: squad-operator
  scope: review_only
domain: Operational

```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::discover_tools_classify
Output: artifact::discover_tools_classify
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Execute structured searches across MCP sources (official repos, directories,
GitHub community) to discover candidate tools for each prioritized gap.
Classify each finding by source authority, domain fit, and basic quality signals.

## Prerequisites

- [ ] `discover-tools-scan` completed successfully
- [ ] Scan output available at `.aiox/squad-runtime/discovery/{domain}/scan-results.yaml`
- [ ] WebSearch/EXA tool available for research
- [ ] WebFetch tool available for page analysis

## Inputs

| Parameter | Type | Required | Source |
|-----------|------|----------|--------|
| `scan_output` | object | Yes | Output from `discover-tools-scan` |
| `domain` | string | Yes | Passed through from pipeline |
| `use_cases` | list | Yes | Passed through from pipeline |
| `budget_tier` | enum | No | `"free_only"`, `"low_cost"`, `"enterprise"` |

## Workflow

### Step 1: Search Official MCP Repositories

```yaml
official_mcp_search:
  # URLs centralizadas em data/tool-discovery-sources.yaml → sources.mcp
  sources_ref: "data/tool-discovery-sources.yaml#sources.mcp.priority_1_official"

  search_queries:
    - "MCP server {domain}"
    - "Model Context Protocol {use_case}"
    - "{domain} anthropic MCP"

  for_each_result:
    extract:
      - name
      - description
      - capabilities
      - installation
      - requirements
      - last_updated
      - stars
      - issues_count
```

### Step 2: Search GitHub for Community MCPs

```yaml
github_mcp_search:
  queries:
    - query: "topic:mcp-server {domain}"
      type: "topic"
    - query: "mcp server {domain} in:readme"
      type: "code"
    - query: "model context protocol {use_case}"
      type: "repositories"

  filters:
    - stars: ">= 10"
    - updated: "within 6 months"
    - has_readme: true
    - has_license: true

  for_each_result:
    validate:
      - has_installation_docs: true
      - has_usage_examples: true
      - compatible_with_claude: true
```

### Step 3: Classify Findings

For each discovered tool, assign:

```yaml
classification:
  source_type: "official|directory|community"
  domain_relevance: "direct|adjacent|tangential"
  capability_match:
    - gap_id: "{capability}"
      match_strength: "full|partial|weak"
  quality_signals:
    has_readme: true/false
    has_license: true/false
    has_examples: true/false
    recently_updated: true/false
    star_count: N
```

Deduplicate tools found across multiple sources (prefer official source).

## Output

```yaml
classify_output:
  total_found: N
  by_source:
    official: N
    directory: N
    community: N
  by_relevance:
    direct: N
    adjacent: N
    tangential: N
  classified_tools:
    - name: ""
      source_url: ""
      source_type: ""
      domain_relevance: ""
      capabilities_matched: []
      quality_signals: {}
      install_command: ""
```

Output file: `.aiox/squad-runtime/discovery/{domain}/classified-tools.yaml`

## Acceptance Criteria

- [ ] At least 3 MCP sources searched
- [ ] Results validated, not just listed
- [ ] Each finding classified by source type and domain relevance
- [ ] Duplicates removed with source preference applied
- [ ] Only gaps from `external_search_scope.required` + justified optional searched

## Veto Conditions

```yaml
veto_conditions:
  - id: "VETO-CLASSIFY-001"
    condition: "No scan_output available or scope unverified"
    trigger: "Before search begins"
    block_behavior: "BLOCK classification; require scan task first"
```

## Related Documents

- `discover-tools.md` -- Orchestrator (parent task)
- `discover-tools-scan.md` -- Previous task in pipeline
- `discover-tools-evaluate.md` -- Next task in pipeline

---

_Task Version: 1.0.0_
_Extracted from: discover-tools.md v3.0 (Phase 1, Steps 1.1-1.2)_
