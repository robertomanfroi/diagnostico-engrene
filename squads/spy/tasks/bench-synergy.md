# Task: bench-synergy

**Agent:** bench-analyst
**Command:** `*bench-synergy {subject_a} vs {subject_b}`
**Template:** `squads/spy/templates/bench-synergy-tmpl.md`
**Prerequisite:** Benchmark must exist at `docs/bench/{slug}/` with scorecard.json + gap-analysis.json

---

## Purpose

Analyze the SYNERGY potential between two subjects that were previously benchmarked.
Goes beyond comparison (who wins) to integration (how they combine).

Produces a structured synergy report covering: classification, capability coverage,
hybrid architecture, integration patterns, friction analysis, value proposition,
and implementation roadmap.

---

## Inputs

| Input | Source | Required |
|-------|--------|:--------:|
| `subject_a` | User parameter | YES |
| `subject_b` | User parameter | YES |
| `scorecard.json` | `docs/bench/{slug}/` | YES |
| `gap-analysis.json` | `docs/bench/{slug}/` | YES |
| `comparison-matrix.json` | `docs/bench/{slug}/` | YES |
| `executive-report.md` | `docs/bench/{slug}/` | YES |
| Internal analyses | `outputs/decoded/`, `outputs/sinkra-squad/` | OPTIONAL |

---

## Phases

### Phase 0: Load Benchmark Data
```
1. Verify benchmark exists at docs/bench/{slug}/
2. Load scorecard.json → extract dimension scores
3. Load gap-analysis.json → extract gaps bidirectional
4. Load comparison-matrix.json → extract parity scores
5. If internal analyses exist → load cross-reference data
```

### Phase 1: Synergy Classification
```
Determine the relationship type between A and B:

COMPLEMENTARY: Most dimensions have one subject strong, the other weak
  → Combined coverage >> individual coverage
  → Low overlap, high net new

OVERLAPPING: Both strong in same dimensions
  → Combined coverage ≈ individual coverage
  → High overlap, low net new

COMPETING: Same target, same strengths, same weaknesses
  → Combined adds little value
  → Consider "pick one" recommendation

INDEPENDENT: Unrelated capability spaces
  → No meaningful integration path

Classification algorithm:
  complementary_dims = count(dims where |score_a - score_b| > 30)
  overlap_dims = count(dims where |score_a - score_b| < 15 AND both > 60)
  
  if complementary_dims > 60% → COMPLEMENTARY
  if overlap_dims > 60% → OVERLAPPING
  if same_target AND overlap_dims > 40% → COMPETING
  else → INDEPENDENT
```

### Phase 2: Build Complementarity Index
```
For each dimension in the scorecard:
  1. Take score_a and score_b
  2. best_of = max(score_a, score_b)
  3. overlap = min(score_a, score_b) if both > 50, else 0
  4. complementary = YES if one > 70 and other < 40
  
Calculate:
  - Combined Coverage = avg(best_of across all dims)
  - Overlap Rate = count(overlap_dims) / total_dims
  - Complementarity Rate = count(complementary_dims) / total_dims
```

### Phase 3: Map 9 Synergy Categories
```
For each of 9 categories, assess potential:

1. CAPABILITY SYNERGY: Combined tools/features exceed either alone
2. WORKFLOW SYNERGY: One's output feeds the other's input naturally
3. PLATFORM SYNERGY: One provides access, the other provides depth
4. KNOWLEDGE SYNERGY: One's learning benefits the other's decisions
5. COST SYNERGY: Combined cheaper than running both independently
6. DATA SYNERGY: Shared data/memory multiplies insights
7. SECURITY SYNERGY: Combined security posture stronger
8. BRAND SYNERGY: Combined positioning more compelling
9. ECOSYSTEM SYNERGY: Combined community/marketplace larger

For each: evidence, effort, potential (HIGH/MED/LOW/NONE)
Prioritize into 3 tiers: Immediate / Short-term / Strategic
```

### Phase 4: Design Hybrid Architecture
```
Based on synergy classification and gaps:

1. Determine integration topology:
   - GATEWAY: A as front-end, B as back-end
   - PIPELINE: A processes first, passes to B
   - ORCHESTRATION: Third layer coordinates A and B
   - SIDECAR: B augments A transparently
   - DELEGATION: A delegates specific tasks to B
   - FALLBACK: B handles what A cannot

2. Define interface contracts:
   - Protocol (MCP / API / CLI / Webhook / File)
   - Data format (JSON / YAML / Markdown)
   - Authentication
   - Error handling

3. Build RACI matrix for each capability

4. Draw data flow diagram
```

### Phase 5: Analyze Integration Friction
```
For each integration point:
  1. Technical friction (language mismatch, protocol gaps)
  2. Operational friction (different deployment models)
  3. Commercial friction (licensing, cost implications)
  4. Architectural friction (state management, auth)

Score friction 0-100 per point
Calculate overall friction score
Identify mitigations for HIGH friction items
```

### Phase 6: Calculate Value Proposition
```
V(Combined) = V(A) + V(B) + Synergy_Value - Integration_Cost - Friction_Cost

Where:
  V(A) = weighted_score_a from scorecard
  V(B) = weighted_score_b from scorecard
  Synergy_Value = sum of tier1 + tier2 synergy values
  Integration_Cost = effort estimate from architecture design
  Friction_Cost = friction score normalized

Net Synergy = V(Combined) - max(V(A), V(B))

If Net_Synergy > 0 → integration recommended
If Net_Synergy < 0 → standalone recommended
```

### Phase 7: Build Use Case Matrix
```
For 5-10 representative use cases:
  Rate each subject alone (1-5)
  Rate combined (1-5)
  Recommend: A alone / B alone / Combined

Use cases should cover:
  - Core strength of A
  - Core strength of B
  - Overlap area
  - Neither's strength
  - Real-world workflow
```

### Phase 8: Implementation Roadmap
```
Phase 0: PoC (1-2 weeks)
  - Minimal integration proving value
  - 1-2 use cases end-to-end
  
Phase 1: Core (2-4 weeks)
  - Primary integration pattern implemented
  - Tier 1 synergies active

Phase 2: Advanced (4-8 weeks)
  - Tier 2 synergies
  - Data/knowledge sharing
  
Phase 3: Full Hybrid (8+ weeks)
  - All patterns active
  - Tier 3 strategic synergies
  - Optimization
```

### Phase 9: Generate Artifacts
```
Output to docs/bench/{slug}/:
  1. synergy-analysis.json     — machine-readable full analysis
  2. synergy-analysis.md       — human-readable (from template)
  3. hybrid-architecture.md    — architecture design detail
  4. integration-roadmap.md    — implementation plan

Update:
  5. executive-report.md       — add synergy section
  6. battle-card.md            — add hybrid recommendation
```

---

## Output

| # | Artifact | Format | Path |
|---|----------|--------|------|
| 1 | synergy-analysis.json | JSON | docs/bench/{slug}/ |
| 2 | synergy-analysis.md | MD | docs/bench/{slug}/ |
| 3 | hybrid-architecture.md | MD | docs/bench/{slug}/deep/ |
| 4 | integration-roadmap.md | MD | docs/bench/{slug}/deep/ |

---

## Quality Gates

- [ ] Benchmark prerequisite exists and is loaded
- [ ] Synergy classification backed by quantitative thresholds
- [ ] All 9 synergy categories assessed with evidence
- [ ] Architecture diagram includes interface contracts
- [ ] Value equation produces numeric result
- [ ] At least 5 use cases in matrix
- [ ] Roadmap has 4 phases with deliverables
- [ ] Dual format output (JSON + MD)
- [ ] All claims cite source artifact or analysis

---

## Frameworks Applied

| Framework | What we use | Original source |
|-----------|-------------|-----------------|
| **Gartner Magic Quadrant** | 2-axis positioning quadrant (Vision/Autonomy vs Execution/Coding) | [Gartner MQ Methodology](https://www.gartner.com/en/research/methodologies/magic-quadrants-research) |
| **Forrester Wave** | Weighted scoring across 3 dimensions (Current, Strategy, Feedback) | [Forrester Wave Methodology](https://www.forrester.com/policies/forrester-wave-methodology/) |
| **BrightWolves 9-3-1** | 9 synergy categories, 3 priority tiers, 1 integration roadmap | [9-3-1 Synergy Framework](https://www.brightwolves.com/post/the-9-3-1-synergy-framework) |
| **Klue FIA** | Fact-Impact-Act structure for actionable intelligence | [Klue Battlecards 101](https://klue.com/blog/competitive-battlecards-101) |
| **Stratechi Synergy** | Value equation: Revenue + Cost + Capital + Financial synergies | [Stratechi Synergies](https://www.stratechi.com/synergies/) |
| **RACI** | Responsibility matrix for hybrid capability ownership | Standard |

---

_bench-synergy task v1.0.0 | spy squad_
