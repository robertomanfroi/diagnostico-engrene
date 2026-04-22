# Task: LLM Evaluation

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
id: bench-llm-eval
name: "LLM Evaluation"
category: benchmark-llm
agent: bench-analyst
elicit: true
autonomous: false
estimated_duration: "10-15min"
description: "Collect LLM specs, benchmark scores, pricing, and capabilities for comparison"
```

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish

## Purpose

Evaluate a Large Language Model by collecting its specifications, official benchmark scores,
pricing, capabilities, and performance metrics. Produces a structured inventory JSON used
as input for the universal comparison pipeline.

This task is the **LLM-specific** implementation of the inventory phase.
Data is collected from official documentation, papers, leaderboards, and pricing pages.

## Prerequisites

- [ ] Model identified (name, provider, version)
- [ ] Comparison type confirmed as `llm`
- [ ] Internet access available for web research

## Inputs

```yaml
inputs:
  subject_name:
    type: string
    required: true
    description: "Model identifier (e.g., 'claude-opus-4', 'gpt-4o', 'llama-3.1-405b')"

  provider:
    type: string
    required: false
    description: "Provider name (e.g., 'Anthropic', 'OpenAI', 'Meta')"

  official_url:
    type: string
    required: false
    description: "Official model documentation URL"

  output_dir:
    type: string
    required: false
    description: "Override output directory"
```

## Data Collection Protocol

```
PROTOCOL: BENCHMARK_DATA_FIRST
METHODS: WebSearch, WebFetch
NEVER: Fabricate benchmark scores, estimate without source
ALWAYS: Cite source URL for every data point
IF data unavailable: Report "N/A (not publicly available)" — never estimate
```

---

## Step 1: Identify Model

```
ACTION: WebSearch("{subject_name} official documentation specs")
EXTRACT:
  - Full model name and version
  - Provider / organization
  - Release date
  - Model family
  - Architecture type (transformer, MoE, etc.)

STORE: identity = {
  name: "<full name>",
  provider: "<organization>",
  version: "<version>",
  release_date: "<date>",
  family: "<model family>",
  architecture: "<type>"
}
```

---

## Step 2: Collect Technical Specs

```
ACTION: WebSearch("{subject_name} parameter count context window")
ACTION: WebFetch(official_url) if provided
EXTRACT:
  - Parameter count (if public)
  - Context window (tokens)
  - Training data cutoff date
  - Max output tokens
  - Supported modalities (text, image, audio, video)
  - Fine-tuning availability

STORE: specs = {
  parameters: "<count or 'undisclosed'>",
  context_window: <tokens>,
  max_output_tokens: <tokens>,
  training_cutoff: "<date>",
  modalities: ["text", "image"],
  fine_tuning: <boolean>,
  source: "<URL>"
}
```

---

## Step 3: Collect Benchmark Scores

```
ACTION: WebSearch("{subject_name} benchmark MMLU HumanEval scores")
ACTION: WebSearch("{subject_name} LMSYS chatbot arena ELO")

EXTRACT official/public scores for:

Reasoning:
  - MMLU (5-shot or 0-shot)
  - MMLU-Pro
  - ARC-Challenge
  - HellaSwag
  - WinoGrande
  - GSM8K / MATH
  - GPQA

Coding:
  - HumanEval / HumanEval+
  - MBPP / MBPP+
  - SWE-bench (verified)
  - LiveCodeBench

Knowledge:
  - TriviaQA
  - NaturalQuestions
  - DROP

Multimodal (if applicable):
  - MMMU
  - MathVista
  - DocVQA

Chat/Instruction:
  - MT-Bench
  - Chatbot Arena ELO
  - AlpacaEval 2.0

STORE: benchmarks = {
  reasoning: { mmlu: {score: X, source: "URL"}, ... },
  coding: { humaneval: {score: X, source: "URL"}, ... },
  knowledge: { ... },
  multimodal: { ... },
  chat: { arena_elo: {score: X, source: "URL"}, ... }
}

NOTE: For EACH score, record the source URL.
If a benchmark is not available, store: {score: "N/A", source: "not publicly available"}
```

---

## Step 4: Collect Pricing

```
ACTION: WebSearch("{subject_name} pricing API cost per token")
ACTION: WebFetch(pricing_page_url)

EXTRACT:
  - Input price ($/MTok)
  - Output price ($/MTok)
  - Batch pricing (if available)
  - Free tier details
  - Rate limits
  - Enterprise pricing notes

STORE: pricing = {
  input_per_mtok: <number>,
  output_per_mtok: <number>,
  batch_input: <number or null>,
  batch_output: <number or null>,
  free_tier: "<description or 'none'>",
  rate_limits: "<description>",
  currency: "USD",
  source: "<URL>",
  as_of_date: "<date>"
}
```

---

## Step 5: Collect Capabilities

```
ACTION: WebSearch("{subject_name} capabilities features API")
EXTRACT:
  - Vision / image understanding
  - Function calling / tool use
  - Structured output (JSON mode)
  - Streaming support
  - System prompts
  - Multi-turn conversation
  - Code execution
  - Web browsing
  - File upload/analysis
  - Fine-tuning
  - Embedding generation
  - Batch API

STORE: capabilities = {
  vision: <boolean>,
  function_calling: <boolean>,
  structured_output: <boolean>,
  streaming: <boolean>,
  system_prompts: <boolean>,
  code_execution: <boolean>,
  web_browsing: <boolean>,
  file_analysis: <boolean>,
  fine_tuning: <boolean>,
  embeddings: <boolean>,
  batch_api: <boolean>,
  source: "<URL>"
}
```

---

## Step 6: Collect Performance Metrics

```
ACTION: WebSearch("{subject_name} speed latency tokens per second TTFT")
EXTRACT (if publicly available):
  - Time to First Token (TTFT)
  - Tokens per second (output)
  - Throughput (requests/min)
  - Availability/uptime SLA

STORE: performance = {
  ttft_ms: <number or "N/A">,
  tokens_per_sec: <number or "N/A">,
  throughput: "<description or 'N/A'>",
  uptime_sla: "<percentage or 'N/A'>",
  source: "<URL>"
}
```

---

## Step 7: Collect Safety & Alignment Data

```
ACTION: WebSearch("{subject_name} safety policy alignment content policy")
EXTRACT:
  - Content policy description
  - Known refusal patterns
  - Safety training approach (RLHF, Constitutional AI, etc.)
  - Red-teaming results (if public)

STORE: safety = {
  safety_approach: "<description>",
  content_policy: "<summary>",
  refusal_behavior: "<description>",
  red_teaming: "<public results or 'undisclosed'>",
  source: "<URL>"
}
```

---

## Step 8: Compile Inventory

```json
{
  "subject": "{subject_name}",
  "type": "llm",
  "generatedAt": "<ISO-8601>",
  "method": "web-research-official-sources",
  "identity": {},
  "specs": {},
  "benchmarks": {},
  "pricing": {},
  "capabilities": {},
  "performance": {},
  "safety": {},
  "sources_consulted": [
    {"name": "<source name>", "url": "<URL>", "accessed": "<date>"}
  ],
  "data_quality": {
    "benchmark_scores": "<official|third-party|estimated>",
    "pricing": "<current|possibly-outdated>",
    "confidence": "<high|medium|low>"
  }
}
```

---

## Step 9: Write Outputs

```
ACTION: Write("{output_dir}/inventory-{subject_name}.json", JSON.stringify(inventory, null, 2))
ACTION: Write("{output_dir}/inventory-{subject_name}.md", markdown_summary)
```

The markdown summary should include:
- Model identity card (name, provider, release date)
- Key specs table (params, context, pricing)
- Benchmark scores summary table
- Capabilities checklist
- Performance metrics (if available)
- Sources consulted

---

## Outputs

| File | Location | Format |
|------|----------|--------|
| LLM inventory | `{output_dir}/inventory-{subject_name}.json` | JSON |
| LLM summary | `{output_dir}/inventory-{subject_name}.md` | MD |

## Veto Conditions

1. **Model not identifiable** — Cannot find official information → HALT
2. **No benchmark data available** — Zero scores from any source → WARN and continue with capabilities-only
3. **Pricing page unavailable** — Mark pricing as "N/A" and continue

## Verification

- [ ] JSON inventory file is valid (parseable)
- [ ] Every benchmark score has a source URL
- [ ] Pricing data has as_of_date
- [ ] No fabricated or estimated scores
- [ ] Capabilities accurately reflect official documentation
- [ ] Sources consulted list is complete
- [ ] Data quality assessment is honest
