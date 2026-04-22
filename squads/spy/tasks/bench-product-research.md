# Task: Product Research

## Contrato SINKRA

Domain: `Tactical`

responsavel: bench-analyst
atomic_layer: Atom
Entrada:
- sujeitos, fontes e artefatos upstream conforme `Inputs`
Saida:
- artefatos de benchmark em `docs/bench/`
Checklist:
- `checklists/bench-quality-checklist.md`
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

## Metadata
```yaml
id: bench-product-research
name: "Product Research"
category: benchmark-product
agent: bench-analyst
elicit: true
autonomous: false
estimated_duration: "12-18min"
description: "Research product features, pricing, integrations, and user reviews for comparison"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Research a software product by collecting its features, pricing tiers, integrations,
user experience reputation, and community reviews. Produces a structured inventory JSON
used as input for the universal comparison pipeline.

This task is the **product-specific** implementation of the inventory phase.
Data is collected from product websites, review platforms, and public documentation.

## Prerequisites

- [ ] Product identified (name, URL)
- [ ] Comparison type confirmed as `product`
- [ ] Internet access available for web research

## Inputs

```yaml
inputs:
  subject_name:
    type: string
    required: true
    description: "Product identifier (e.g., 'notion', 'obsidian', 'linear', 'jira')"

  product_url:
    type: string
    required: false
    description: "Official product website URL"

  output_dir:
    type: string
    required: false
    description: "Override output directory"
```

## Data Collection Protocol

```
PROTOCOL: DOCS_AND_REVIEWS_FIRST
METHODS: WebSearch, WebFetch
NEVER: Assume features without verification, use outdated pricing
ALWAYS: Cite source for every claim, note date of data collection
```

---

## Step 1: Identify Product

```
ACTION: WebSearch("{subject_name} official website product")
ACTION: WebFetch(product_url) if provided
EXTRACT:
  - Full product name
  - Company / organization
  - Category (project management, note-taking, CRM, etc.)
  - Founded / launch date
  - Target audience
  - Tagline / value proposition

STORE: identity = {
  name: "<full name>",
  company: "<organization>",
  category: "<category>",
  launch_date: "<date or 'unknown'>",
  target_audience: "<description>",
  tagline: "<value prop>",
  url: "<official URL>"
}
```

---

## Step 2: Collect Core Features

```
ACTION: WebSearch("{subject_name} features list capabilities")
ACTION: WebFetch("{product_url}/features") if accessible
EXTRACT:
  - Feature categories (e.g., collaboration, automation, reporting)
  - Key features per category
  - Unique differentiators
  - Feature depth assessment

STORE: features = {
  categories: [
    {
      name: "<category>",
      features: ["feature1", "feature2"],
      depth: "<basic|moderate|deep>"
    }
  ],
  unique_capabilities: ["<differentiator1>", "<differentiator2>"],
  total_feature_count: <estimated count>,
  source: "<URL>"
}
```

---

## Step 3: Collect Pricing

```
ACTION: WebSearch("{subject_name} pricing plans")
ACTION: WebFetch("{product_url}/pricing") if accessible
EXTRACT:
  - Plan names and prices
  - Free tier (features, limits)
  - Per-user or flat pricing model
  - Annual vs monthly pricing
  - Enterprise pricing
  - Usage limits per tier

STORE: pricing = {
  model: "<per-user|flat|usage-based|hybrid>",
  currency: "USD",
  plans: [
    {
      name: "<plan name>",
      price_monthly: <number or "custom">,
      price_annual: <number or "custom">,
      key_features: ["<feature>"],
      limits: "<description>"
    }
  ],
  free_tier: {
    available: <boolean>,
    features: ["<feature>"],
    limits: "<description>"
  },
  enterprise: "<custom pricing|contact sales|listed price>",
  source: "<URL>",
  as_of_date: "<date>"
}
```

---

## Step 4: Collect Integrations

```
ACTION: WebSearch("{subject_name} integrations API marketplace")
ACTION: WebFetch("{product_url}/integrations") if accessible
EXTRACT:
  - API availability (REST, GraphQL, etc.)
  - Webhook support
  - Integration marketplace / app store
  - Key integrations (Slack, GitHub, Zapier, etc.)
  - SDK/client libraries
  - Plugin/extension system

STORE: integrations = {
  api: {
    available: <boolean>,
    type: "<REST|GraphQL|both>",
    documentation: "<URL or 'undocumented'>"
  },
  webhooks: <boolean>,
  marketplace: {
    available: <boolean>,
    app_count: <number or "unknown">
  },
  key_integrations: ["Slack", "GitHub", "Zapier"],
  sdk_languages: ["JavaScript", "Python"],
  plugin_system: <boolean>,
  source: "<URL>"
}
```

---

## Step 5: Collect User Experience Data

```
ACTION: WebSearch("{subject_name} UX review onboarding experience")
EXTRACT:
  - Onboarding quality reputation
  - UI/UX design reputation
  - Learning curve assessment
  - Mobile support
  - Offline capabilities
  - Accessibility (a11y)

STORE: user_experience = {
  onboarding: "<excellent|good|average|poor>",
  ui_quality: "<modern|functional|dated>",
  learning_curve: "<low|moderate|steep>",
  mobile_app: <boolean>,
  offline_support: <boolean>,
  accessibility: "<description>",
  source: "<URL>"
}
```

---

## Step 6: Collect Reviews & Ratings

```
ACTION: WebSearch("{subject_name} G2 review rating")
ACTION: WebSearch("{subject_name} Capterra review rating")
ACTION: WebSearch("{subject_name} ProductHunt")
EXTRACT:
  - G2 rating and review count
  - Capterra rating and review count
  - ProductHunt upvotes (if applicable)
  - Common praise themes
  - Common complaint themes

STORE: reviews = {
  g2: {
    rating: <number or "N/A">,
    review_count: <number or "N/A">,
    top_praise: ["<theme>"],
    top_complaints: ["<theme>"]
  },
  capterra: {
    rating: <number or "N/A">,
    review_count: <number or "N/A">
  },
  producthunt: {
    upvotes: <number or "N/A">,
    launch_date: "<date or 'N/A'>"
  },
  source: ["<URL1>", "<URL2>"]
}
```

---

## Step 7: Collect Scalability & Enterprise Info

```
ACTION: WebSearch("{subject_name} enterprise scalability limits")
EXTRACT:
  - Usage limits (storage, users, API calls)
  - Enterprise features (SSO, SAML, SCIM, audit logs)
  - Multi-tenant support
  - Data residency options
  - SLA guarantees
  - Compliance certifications (SOC2, GDPR, HIPAA)

STORE: scalability = {
  limits: "<description>",
  enterprise_features: ["SSO", "SAML", "audit logs"],
  multi_tenant: <boolean>,
  data_residency: <boolean>,
  sla: "<percentage or 'N/A'>",
  compliance: ["SOC2", "GDPR"],
  source: "<URL>"
}
```

---

## Step 8: Collect Support & Community

```
ACTION: WebSearch("{subject_name} support community docs")
EXTRACT:
  - Documentation quality
  - Support channels (email, chat, phone)
  - Community (forum, Discord, Slack)
  - Knowledge base / help center
  - Status page

STORE: support = {
  docs_quality: "<excellent|good|average|poor>",
  channels: ["email", "chat", "phone"],
  community: {
    type: "<forum|Discord|Slack|none>",
    size: "<estimate or 'unknown'>"
  },
  knowledge_base: <boolean>,
  status_page: <boolean>,
  source: "<URL>"
}
```

---

## Step 9: Compile Inventory

```json
{
  "subject": "{subject_name}",
  "type": "product",
  "generatedAt": "<ISO-8601>",
  "method": "web-research-docs-and-reviews",
  "identity": {},
  "features": {},
  "pricing": {},
  "integrations": {},
  "user_experience": {},
  "reviews": {},
  "scalability": {},
  "support": {},
  "sources_consulted": [],
  "data_quality": {
    "features": "<verified|partial|estimated>",
    "pricing": "<current|possibly-outdated>",
    "reviews": "<recent|dated>",
    "confidence": "<high|medium|low>"
  }
}
```

---

## Step 10: Write Outputs

```
ACTION: Write("{output_dir}/inventory-{subject_name}.json", JSON.stringify(inventory, null, 2))
ACTION: Write("{output_dir}/inventory-{subject_name}.md", markdown_summary)
```

---

## Outputs

| File | Location | Format |
|------|----------|--------|
| Product inventory | `{output_dir}/inventory-{subject_name}.json` | JSON |
| Product summary | `{output_dir}/inventory-{subject_name}.md` | MD |

## Veto Conditions

1. **Product not identifiable** — Cannot find official website → HALT
2. **No pricing information** — Mark as "contact sales" and continue
3. **No reviews available** — Mark reviews as "N/A" and continue

## Verification

- [ ] JSON inventory file is valid (parseable)
- [ ] Pricing data has as_of_date
- [ ] Features verified against official source
- [ ] No assumed features without verification
- [ ] Sources consulted list is complete
- [ ] Data quality assessment is honest
