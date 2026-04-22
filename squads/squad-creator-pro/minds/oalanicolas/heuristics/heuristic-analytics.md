# Heuristic Occurrence Analytics

Este arquivo contabiliza a quantidade de vezes que cada heurística foi invocada, re-exigida ou implícita nas sessões avaliadas em `history.jsonl`.

| ID | Heurística Extrativa | Ocorrências Identificadas (Regex) |
|---|---|---|
| AN_KE_025 | Determinism Over LLM | **8** |
| AN_KE_026 | Squad Agnosticism | **17** |
| AN_KE_027 | Zero Emojis / Design | **24** |
| AN_KE_028 | Self-Contained | **9** |
| AN_KE_029 | Survival by Doc | **8** |
| AN_KE_030 | Anti-Fingerprint AI | **6** |
| AN_KE_031 | Localhost QA Gate | **10** |
| AN_KE_032 | Schema Immutability | **36** |
| AN_KE_033 | Chronological Reports | **3** |
| AN_KE_034 | Total Ghostwriting | **3** |

> **Nota:** As ocorrências são mapeadas por padrões analíticos de regex baseados na voz de extração do seu histórico de prompts.

## Configuration

| Campo | Valor |
|-------|-------|
| tension_with | AN_KE_017 (Research No Meio, Não No Início) |
