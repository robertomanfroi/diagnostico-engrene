# AN_KE_096 - Raw Import No Transform
**Zone:** 🔥 20% Impacto | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão mmos f10d21b4 — importação de dados sem transformar]

## Purpose

Ao importar dados externos (transcrições, documentos, datasets), importar RAW sem modificar. A IA tem tendência de "limpar" ou "melhorar" dados durante importação, perdendo informação original. Import raw, transform later.

## Configuration

```yaml
AN_KE_096:
  name: "Raw Import No Transform"
  zone: "impacto"
  trigger: "Importando dados de fontes externas: transcrições, docs, CSVs, APIs."

  rule: |
    SE importando dados externos
    ENTÃO importar RAW (sem alterar, sem limpar, sem transformar).
    Transformação é FASE SEPARADA após importação.
    Dado original perdido = irrecuperável.

  veto_condition:
    trigger: "IA 'melhorando' dados durante importação (corrigindo gramática, reformatando, summarizando)."
    action: "VETO — Import raw. Transform after. Preservar original."

  sys_tension:
    tension_with: "AN_KE_022 (Format Follows Generator) vs No Transform on Import"
    resolution: "Preserve raw data FIRST (AN_KE_096), then create transform pipeline with standards. Format divergence resolved in separate transformation phase. Original immutable, processed derivable."

  evidence:
    - "[SOURCE: sessão f10d21b4] 'nao deve ler com IA, deve pegar todo arquivo (raw) e importar sem alterar'"
    - "[RELATED] AN_KE_071 (Capture Raw Then Analyze) — 071 foca em API/auth data → JSONB. 096 foca em file imports → preservar arquivo original."
```

## Decision Tree

```javascript
IF (importing_external_content: transcription, document, CSV, dataset)
  STEP_1: SAVE original file AS-IS
    PRESERVE: encoding, formatting, typos, structure
    LOCATION: raw/{source}/{date}-{filename}
  STEP_2: ACKNOWLEDGE import complete
  STEP_3: TRANSFORM in separate step (never inline)
    Parse, clean, structure → output to processed/
    KEEP: original in raw/ untouched
  NEVER: "improve" text during import (fix grammar, reformat, summarize)
  DISTINCTION from AN_KE_071: this is FILE content, not API/JSONB data
```

## Failure Modes

### A Transcrição "Melhorada"
- **Trigger:** IA importa transcrição de podcast e "limpa" linguagem coloquial automaticamente.
- **Manifestation:** Nuances, expressões regionais, e tom original perdidos.
- **Detection:** Imported text sounds formal when source was casual.
- **Prevention:** "nao deve ler com IA, deve pegar todo arquivo raw e importar sem alterar."

## Validation

**Paradoxo Identificado:** Tensão entre a preservação irrevogável de dados brutos (AN_KE_096) e a necessidade de padronização e limpeza de dados para análise (AN_KE_093, AN_KE_085).

**Resolução:** A heurística estabelece a sequência temporal correta: IMPORT RAW FIRST (immutable), THEN STANDARDIZE in separate pipeline. O original nunca é perdido; transformações são reversíveis via derivação. Isto resolve o paradoxo ao diferenciar átomos (raw data imutable) de moléculas (transformed data ephemeral).

**Critério de Sucesso:** Importação ocorre sem transformação inline. Arquivo original recuperável 100%. Transformações ocorrem em fase separada e rastreável.
