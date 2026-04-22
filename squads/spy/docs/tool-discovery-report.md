# Tool Discovery Report - Spy Squad

## Metadata
- Date: 2026-02-17
- Squad: `spy`
- Domain: Competitive intelligence (YouTube + Instagram) and framework benchmarking
- Budget tier considered: `low_cost`
- Policy: internal-first (`squads/etl-ops` + ETL infra before external tools)

## Phase 0 - Capability Gap Analysis

### Use Cases Analyzed
1. Quick channel/profile analysis
2. Deep competitive research
3. Framework benchmarking (AIOX vs competitors)
4. Trend monitoring

### Capability Coverage
- Fully covered (native/current): YouTube transcript/channel/metadata pipelines, web extraction, chunking/cleanup, report generation
- Partially covered: Instagram official enrichment, browser-grade capture evidence, benchmark timing standardization
- Gaps:
  - Instagram official API enrichment
  - dynamic browser capture for anti-bot pages
  - benchmark timing standard for comparisons

## Phase 1-5 - Discovered Tools

### Internal Stack Already Available (Primary)
1. `squads/etl-ops` task routing (`data/routing-profiles.yaml`)
2. `youtube-transcript.js` / `youtube-pipeline.js` / `youtube-metadata.js`
3. `fetch-page.js` for deterministic web extraction
4. ETL transformers/validators in squad contracts (`checkpoints.yaml`, `output-contract.yaml`)

### MCP Servers (Fallback/Enhancement)
1. `@modelcontextprotocol/server-playwright` - browser automation and dynamic extraction
2. `firecrawl-mcp` - robust crawling for difficult pages
3. `@apify/actors-mcp-server` - actor-based fallback for hard social targets

### APIs
1. YouTube Data API v3 - channel/video/search metadata
2. Apify API - social/web actor-based extraction
3. Meta Graph API (Instagram Platform) - profile/media insights (with app review constraints)

### CLI Tools
1. Internal ETL CLIs (`youtube-*`, `fetch-page`, `transcribe`, `ebook-to-markdown`) as default
2. `yt-dlp` - metadata fallback if needed by ETL profile
3. `hyperfine` - benchmark execution timing
4. `instaloader` - optional Instagram fallback

### Libraries
1. `youtube-transcript-api` (Python) - programmatic transcript fallback
2. `apify-client` (Python/JS) - controlled data extraction workflows
3. `playwright` (Node/Python) - scripted browser extraction and validation

### GitHub Projects
1. `modelcontextprotocol/servers`
2. `mendableai/firecrawl-mcp-server`
3. `jkawamoto/mcp-youtube-transcript`
4. `yt-dlp/yt-dlp`
5. `instaloader/instaloader`

## Phase 6 - Prioritization (Impact vs Effort)

### Quick Wins (implement now)
1. Wire `spy` tasks to `etl-ops` process profiles as first path
2. Standardize benchmark timing with `hyperfine`
3. Keep `yt-dlp` as explicit fallback only (already compatible with ETL)

### Strategic (plan next)
1. YouTube Data API v3 enrichment in `spy` outputs
2. Playwright MCP for dynamic pages and screenshot evidence
3. Apify API/MCP for difficult Instagram and anti-bot scenarios

### Fill-ins
1. `youtube-transcript-api` fallback path
2. `instaloader` local fallback when Graph API is not available

### Avoid for now
1. Full enterprise social suites with high recurring cost and overlap with existing scope

## Recommended Capability Mapping

| Capability | Primary | Fallback |
|---|---|---|
| youtube_transcripts | `etl-ops` + `youtube-transcript.js` | `yt-dlp`, `youtube-transcript-api` |
| youtube_metadata | `etl-ops` + `youtube-metadata.js` | YouTube Data API v3, `yt-dlp` |
| instagram_profile_capture | Meta Graph API | `instaloader`, Apify |
| dynamic_page_extraction | `etl-ops` + `fetch-page.js` | Playwright MCP, `firecrawl-mcp` |
| benchmark_timing | `hyperfine` | shell `time` |
| deep_web_research | `exa` + `etl-ops` `fetch-page.js` | `web_fetch`, `firecrawl-mcp` |

## Risks and Constraints
- Meta Graph API coverage depends on app permissions and review path.
- Instagram extraction without official API can break with platform changes.
- API costs/rate limits should be budget-guarded in automation loops.

## Sources
- https://github.com/modelcontextprotocol/servers
- https://github.com/mendableai/firecrawl-mcp-server
- https://github.com/jkawamoto/mcp-youtube-transcript
- https://developers.google.com/youtube/v3
- https://www.youtube.com/@GoogleDevelopers/videos
- https://apify.com/apify/instagram-scraper
- https://docs.apify.com/platform/actors
- https://github.com/yt-dlp/yt-dlp
- https://github.com/instaloader/instaloader
- https://github.com/sharkdp/hyperfine
- https://github.com/jdepoix/youtube-transcript-api
- https://playwright.dev
- https://developers.facebook.com/docs/instagram-platform
