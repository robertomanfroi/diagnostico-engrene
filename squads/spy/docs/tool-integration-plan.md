# Tool Integration Plan - Spy Squad

## Objective
Increase analysis depth, reduce manual research time, and improve benchmark reproducibility for `spy`.
Execution policy: internal-first (use `etl-ops`/ETL infra first, external tools only as fallback).

## Implementation Waves

### Wave 1 (Immediate: 1-2 days)
1. Route `quick-analysis` and `deep-research` through `squads/etl-ops` profiles (`youtube_video`, `youtube_channel`, `web_page`).
2. Use ETL CLIs as default source layer (`youtube-transcript.js`, `youtube-metadata.js`, `fetch-page.js`).
3. Keep `yt-dlp` only as fallback path in extraction profiles.
4. Add `hyperfine` to benchmark-related tasks (`bench-*`) for deterministic timing evidence.

### Wave 2 (Short-term: 3-7 days)
1. Integrate YouTube Data API v3 enrichment (channel, video, engagement metadata).
2. Add Playwright MCP path for dynamic pages/screenshots only when ETL page fetch is insufficient.
3. Add Apify fallback for difficult social extraction paths.

### Wave 3 (Optional: 1-2 weeks)
1. Integrate Meta Graph API flows where account/app permissions allow.
2. Add `youtube-transcript-api` and `instaloader` as explicit fallback adapters.

## Proposed Task Wiring
- `quick-analysis`: `etl-ops` (`youtube_video`/`youtube_metadata`) + optional YouTube Data API
- `deep-research`: `etl-ops` (`web_page`/`youtube_channel`) + optional Apify fallback
- `bench-framework`: `hyperfine` + ETL evidence capture (+ Playwright only when needed)
- `bench-quick-compare`: ETL metadata pulls + transcript summary

## Environment Variables
- `YOUTUBE_API_KEY`
- `META_ACCESS_TOKEN`
- `FIRECRAWL_API_KEY`
- `APIFY_TOKEN`

## Success Metrics
1. >=30% reduction in manual research steps for deep research.
2. >=25% faster benchmark execution setup.
3. >=90% of analyses include source-backed metadata or transcript evidence.

## Validation Checklist
- [ ] `etl-ops` routing profile selected for each spy use case
- [ ] Internal ETL path executed before any external fallback
- [ ] Fallback path defined for each external dependency
- [ ] Rate-limit and cost guardrails documented
- [ ] At least one benchmark run with timing artifacts
- [ ] Output templates updated to include tool provenance
