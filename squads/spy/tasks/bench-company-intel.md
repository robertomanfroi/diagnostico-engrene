# Task: Company Intelligence

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
id: bench-company-intel
name: "Company Intelligence"
category: benchmark-company
agent: bench-analyst
elicit: true
autonomous: false
estimated_duration: "15-20min"
description: "Collect company data: funding, team, market position, innovation for comparison"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Gather competitive intelligence on a company using publicly available data.
Collects market position, financials, team, innovation signals, growth trajectory,
and ecosystem data. Produces a structured inventory JSON used as input for the
universal comparison pipeline.

This task is the **company-specific** implementation of the inventory phase.
Data is collected from company websites, Crunchbase, LinkedIn, news, and press releases.

## Prerequisites

- [ ] Company identified (name)
- [ ] Comparison type confirmed as `company`
- [ ] Internet access available for web research

## Inputs

```yaml
inputs:
  subject_name:
    type: string
    required: true
    description: "Company identifier (e.g., 'anthropic', 'openai', 'google-deepmind')"

  company_url:
    type: string
    required: false
    description: "Official company website URL"

  output_dir:
    type: string
    required: false
    description: "Override output directory"
```

## Data Collection Protocol

```
PROTOCOL: PUBLIC_DATA_FIRST
METHODS: WebSearch, WebFetch
NEVER: Use unverified financial data, speculate on private metrics
ALWAYS: Cite source, note "estimated" vs "reported" vs "public record"
ONLY use PUBLIC data — no speculation on private financials
```

---

## Step 1: Identify Company

```
ACTION: WebSearch("{subject_name} company about founded headquarters")
ACTION: WebFetch(company_url) if provided
EXTRACT:
  - Full legal name
  - Founded date
  - Headquarters location
  - Industry / sector
  - Company type (private, public, subsidiary)
  - Mission statement / tagline

STORE: identity = {
  name: "<full name>",
  founded: "<year>",
  headquarters: "<city, country>",
  industry: "<sector>",
  type: "<private|public|subsidiary>",
  mission: "<statement>",
  url: "<official URL>"
}
```

---

## Step 2: Collect Market Position

```
ACTION: WebSearch("{subject_name} market share market position competitive landscape")
EXTRACT:
  - Estimated market share (if available)
  - Brand recognition level
  - Customer base size / segments
  - Key markets (geographic, vertical)
  - Main competitors

STORE: market_position = {
  market_share: "<percentage or 'N/A'>",
  brand_recognition: "<high|medium|low>",
  customer_base: "<description>",
  key_markets: ["<market1>", "<market2>"],
  main_competitors: ["<comp1>", "<comp2>"],
  source: "<URL>"
}
```

---

## Step 3: Collect Financial Data

```
ACTION: WebSearch("{subject_name} funding valuation revenue Crunchbase")
EXTRACT (PUBLIC DATA ONLY):
  - Total funding raised
  - Latest funding round (series, amount, date)
  - Valuation (if disclosed)
  - Revenue (if public company or disclosed)
  - Profitability status
  - Key investors

STORE: financials = {
  total_funding: "<amount or 'undisclosed'>",
  latest_round: {
    series: "<Series X>",
    amount: "<amount>",
    date: "<date>",
    lead_investors: ["<investor>"]
  },
  valuation: "<amount or 'undisclosed'>",
  revenue: "<amount or 'private'>",
  profitable: "<yes|no|unknown>",
  key_investors: ["<investor1>", "<investor2>"],
  data_type: "<public_record|reported|estimated>",
  source: "<URL>"
}
```

---

## Step 4: Collect Team & Talent

```
ACTION: WebSearch("{subject_name} team size employees leadership")
ACTION: WebSearch("{subject_name} engineering culture glassdoor")
EXTRACT:
  - Approximate headcount
  - Key executives (CEO, CTO, CPO)
  - Notable recent hires
  - Engineering team size (estimate)
  - Engineering culture reputation
  - Glassdoor rating (if available)
  - Office locations

STORE: team = {
  headcount: "<number or range>",
  executives: [
    {name: "<name>", role: "<title>", notable: "<background>"}
  ],
  engineering_team: "<estimate or 'unknown'>",
  culture: "<description>",
  glassdoor_rating: <number or "N/A">,
  offices: ["<location1>", "<location2>"],
  recent_notable_hires: ["<hire>"],
  source: ["<URL1>", "<URL2>"]
}
```

---

## Step 5: Collect Innovation Signals

```
ACTION: WebSearch("{subject_name} patents R&D innovation product launches 2024 2025")
ACTION: WebSearch("{subject_name} tech blog engineering blog")
EXTRACT:
  - Patent count / filings (if applicable)
  - R&D investment (if disclosed)
  - Recent product launches / major features
  - Technical blog quality and frequency
  - Open source contributions
  - Research publications
  - Technology leadership signals

STORE: innovation = {
  patents: "<count or 'N/A'>",
  rd_investment: "<amount or 'undisclosed'>",
  recent_launches: [
    {name: "<product>", date: "<date>", significance: "<description>"}
  ],
  tech_blog: {
    url: "<URL or 'none'>",
    frequency: "<weekly|monthly|sporadic|none>"
  },
  open_source: ["<project1>", "<project2>"],
  research_papers: <count or "N/A">,
  source: "<URL>"
}
```

---

## Step 6: Collect Growth Trajectory

```
ACTION: WebSearch("{subject_name} growth users revenue trajectory expansion")
EXTRACT:
  - User/customer growth (if disclosed)
  - Revenue growth rate (if public)
  - Geographic expansion
  - Product line expansion
  - Hiring velocity
  - Market expansion signals

STORE: growth = {
  user_growth: "<description or 'undisclosed'>",
  revenue_growth: "<percentage or 'undisclosed'>",
  geographic_expansion: ["<new market>"],
  product_expansion: ["<new product line>"],
  hiring_velocity: "<growing|stable|contracting>",
  trajectory_assessment: "<accelerating|steady|decelerating>",
  source: "<URL>"
}
```

---

## Step 7: Collect Ecosystem & Partnerships

```
ACTION: WebSearch("{subject_name} partnerships developer ecosystem community")
EXTRACT:
  - Key partnerships (strategic, technology, distribution)
  - Developer ecosystem (APIs, SDKs, developer program)
  - Community size and engagement
  - Conference presence
  - Certification programs

STORE: ecosystem = {
  partnerships: [
    {partner: "<name>", type: "<strategic|technology|distribution>"}
  ],
  developer_program: {
    available: <boolean>,
    api_access: <boolean>,
    sdk_languages: ["<lang>"],
    documentation: "<quality>"
  },
  community: {
    size: "<estimate>",
    channels: ["<Discord>", "<forum>"]
  },
  conferences: ["<event>"],
  certifications: <boolean>,
  source: "<URL>"
}
```

---

## Step 8: Collect News & Sentiment

```
ACTION: WebSearch("{subject_name} news latest 2025 2026")
EXTRACT:
  - Recent notable news (last 6 months)
  - Press sentiment (positive/neutral/negative)
  - Controversies or risks
  - Awards or recognitions

STORE: news = {
  recent: [
    {headline: "<title>", date: "<date>", sentiment: "<positive|neutral|negative>", source: "<URL>"}
  ],
  overall_sentiment: "<positive|mixed|negative>",
  controversies: ["<issue>"],
  awards: ["<recognition>"]
}
```

---

## Step 9: Compile Inventory

```json
{
  "subject": "{subject_name}",
  "type": "company",
  "generatedAt": "<ISO-8601>",
  "method": "web-research-public-data",
  "identity": {},
  "market_position": {},
  "financials": {},
  "team": {},
  "innovation": {},
  "growth": {},
  "ecosystem": {},
  "news": {},
  "sources_consulted": [],
  "data_quality": {
    "financials": "<public_record|reported|estimated>",
    "team_data": "<official|estimated>",
    "market_data": "<verified|estimated>",
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
| Company inventory | `{output_dir}/inventory-{subject_name}.json` | JSON |
| Company summary | `{output_dir}/inventory-{subject_name}.md` | MD |

## Veto Conditions

1. **Company not identifiable** — Cannot find basic information → HALT
2. **Zero public data** — No financial, team, or market data available → HALT
3. **Confusion with another entity** — Name ambiguous → ask user to clarify

## Verification

- [ ] JSON inventory file is valid (parseable)
- [ ] Financial data clearly labeled as public/reported/estimated
- [ ] No speculation on private metrics
- [ ] Sources consulted list is complete
- [ ] News data is recent (within 6 months)
- [ ] Data quality assessment is honest
