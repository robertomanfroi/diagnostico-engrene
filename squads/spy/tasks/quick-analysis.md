# Task: Quick Player Analysis

## Contrato SINKRA

Domain: `Operational`

responsavel: spy
atomic_layer: Atom
Entrada:
- `handle`
- `platform`
Saida:
- artefatos em `outputs/spy/`
Checklist:
- `checklists/content-creation-checklist.md`
pre_condition: evidências mínimas carregadas e subject validado
post_condition: artefato persistido com achados e próximos passos rastreáveis
performance: falhar alto, registrar fontes e manter consistência entre evidências e relatório

**Task ID:** quick-analysis
**Version:** 2.0.0
**Status:** active
**Responsible Executor:** Agent (@spy)
**Execution Type:** Agent
**Model:** Haiku (fast analysis, structured output)
**Haiku Eligible:** YES - straightforward data extraction and formatting

## Input
| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `handle` | string | Yes | YouTube channel or Instagram handle |
| `platform` | enum | Yes | `youtube` or `instagram` |

## Output
| Artifact | Location | Description |
|----------|----------|-------------|
| Quick Report | `outputs/spy/{platform}/{handle}-{date}.md` | Analysis summary |

## Veto Conditions
- STOP if no API access (check credentials first)
- STOP if channel/profile not found
- STOP if no public content available

## Acceptance Criteria
- [ ] Top 5 content pieces identified
- [ ] Engagement rates calculated
- [ ] 3+ patterns identified
- [ ] 3+ actionable insights provided
- [ ] Report saved to outputs/spy/

---

## Objective
Quickly analyze a channel/profile and extract actionable insights.

## Workflow

### 1. Data Collection (2 min)
```bash
# YouTube
curl "https://www.googleapis.com/youtube/v3/search?part=snippet&channelId={ID}&type=video&maxResults=10&order=viewCount&key=$YOUTUBE_API_KEY"

# Instagram (via Graph API)
curl "https://graph.facebook.com/v18.0/{user_id}/media?fields=id,caption,like_count,comments_count,media_type&access_token=$META_ACCESS_TOKEN"
```

### 2. Analysis (3 min)
- [ ] Identify top 5 by views/engagement
- [ ] Extract title patterns
- [ ] Calculate average engagement rate
- [ ] Map recurring themes

### 3. Synthesis (2 min)
- [ ] 3 main insights
- [ ] 3 patterns to replicate
- [ ] 1 gap/opportunity

### 4. Output (1 min)
Save to: `outputs/spy/{platform}/{handle}-{date}.md`

## Total Time: ~8 minutes

---

## Quick Output Template

```markdown
# Quick Analysis: @{handle}

**Platform:** YouTube/Instagram
**Date:** {date}
**Followers:** {number}

## Top 3 Content
1. {title} - {views} views ({engagement}%)
2. {title} - {views} views ({engagement}%)
3. {title} - {views} views ({engagement}%)

## Title Patterns
- {pattern 1}
- {pattern 2}
- {pattern 3}

## Quick Insights
1. {insight}
2. {insight}
3. {insight}

## What to Replicate
- {action}
- {action}
- {action}

---
*Quick Analysis - Spy Mode*
```

---

## Post-Analysis Checklist

- [ ] Report saved to outputs/spy/
- [ ] Insights shared
- [ ] Player added to monitoring list

---

*Quick Analysis Task v2.0*

Completion Criteria: artefato concluído, validado contra checklist e pronto para handoff ou publish
