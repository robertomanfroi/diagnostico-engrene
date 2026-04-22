# AN_KE_119 - Auto-Derive Over Mandatory Parameters

**Type:** Decision Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Zero-Config UX
**Source:** [SOURCE: sessão sinkra-hub 8b2b58da + 8dfc9a1b — domain-decoder runner]
**Tags:** [Agnostic, Automation, CLI]

## Purpose

CLIs que pedem parâmetros deriváveis criam fricção desnecessária. Se o source path contém um config.yaml com version, ou um package.json, o CLI pode auto-detectar version e slug sem pedir ao user. Cada parâmetro que pode ser derivado da fonte e é pedido ao user é uma barreira de adoção. A regra: auto-derive tudo que for derivável, aceitar override explícito, nunca pedir o que pode calcular.

## Configuration (True L3-State)

```yaml
AN_KE_119:
  name: "Auto-Derive Over Mandatory Parameters"
  zone: "impacto"
  trigger: "Desenhando CLI interface para pipeline que opera sobre source com metadata."

  rule: |
    SE parâmetro pode ser derivado do source (version, slug, name, etc.)
    ENTÃO auto-derivar com fallback chain (config.yaml → package.json → pyproject.toml → timestamp)
    E permitir override explícito (--version, --slug) para casos edge
    NUNCA pedir como parâmetro obrigatório o que pode ser calculado

  failure_modes:
    omission: "User precisa lembrar versão exata, slug format, etc. Erro de digitação = run perdido."
    misapplication: "Auto-derive de campo ambíguo (ex: 'name' que existe em 3 configs diferentes) sem prioridade clara = bug silencioso."

  evidence_threshold: "[EMPIRICAL]"
  evidence:
    - "[SOURCE: sessão sinkra-hub 8b2b58da] 'Version is auto-detected from source codebase: 1. package.json 2. config.yaml pack.version 3. pyproject.toml 4. VERSION file 5. Fallback: timestamp'"
    - "[SOURCE: sessão sinkra-hub 8dfc9a1b] 'basename of --source is slugified: squads/squad-creator → squad_creator'"
```

## Decision Tree (Strict Format)

```text
STEP_1: IF (parameter can be derived from source metadata)
          THEN implement derivation chain with ordered fallbacks
          AND accept explicit override via CLI flag
STEP_2: IF (derivation is ambiguous — multiple sources conflict)
          THEN log warning with both values, use first in priority chain
NEVER:
  - Make a derivable value a required CLI parameter
  - Fail silently on derivation — always log what was derived and from where
```

## Validation & Cross-Mind Divergence

### Self-Validation Ask
1. "Quantos parâmetros obrigatórios meu CLI tem? Cada um pode ser derivado? Se sim, por que é obrigatório?"

### Divergence Analysis (Baseline IA vs Mente Zero)
- **Base LLM Tendency:** Criar CLI com todos os parâmetros explícitos para "clareza".
- **Mind Zero Override:** "Menos parâmetros = mais adoção. Auto-derive > pedir."
