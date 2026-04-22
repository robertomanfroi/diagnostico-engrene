# AN_KE_024 - Resume = Same Run

**Type:** State Management Heuristic
**Zone:** 💎 4% Excelencia
**Agent:** @oalanicolas
**Pattern:** Pipeline Continuity
**Source:** [SOURCE: Sessao 2026-03-29 — --phase 8 criou run nova, QA deu 4/100 em pasta vazia]

## Purpose

Retomar pipeline = continuar NA MESMA pasta. Criar nova run pra resume quebra dependencias entre fases.

## Configuration

```yaml
AN_KE_024:
  name: "Resume = Same Run"
  zone: "excelencia"
  trigger: "Implementando resume/retry em pipeline multi-fase"

  rule: |
    SE --phase N (resume) → resolver ultima run → continuar nela
    NUNCA criar novo RUN_ID pra resume
    Artefatos anteriores DEVEM estar acessiveis

  evidence:
    - "--phase 8 criou run nova sem artefatos 1-7 → score 4/100 (invalido)"
    - "Score real na run correta: 83.05/100 (MAP-READY)"
    - "Fix: resolver symlink 'latest' em vez de criar novo RUN_ID"

  sys_tension:
    tension_with: "AN_KE_025 (Determinism Over LLM) — Resume must be deterministic (same run always) vs Default pipeline behavior (create new RUN_ID on new phase invocation)"
    resolution: "Resolver symlink 'latest' → last RUN_ID antes de criar run. Verificar artefatos anteriores existem em mesmo diretório antes de iniciar fase N. Se ausentes, erro + não prosseguir em estado vazio."
```

## Decision Tree

```javascript
IF (implementing_resume_in_pipeline)
  REQUIRE: --phase N resolves to LATEST run, not new run
  REQUIRE: artifacts from phases 1..N-1 accessible in same directory
  IMPLEMENTATION:
    RESOLVE: symlink 'latest' → last RUN_ID
    RESUME: continue in 'latest/' directory
    VERIFY: previous phase artifacts exist before starting phase N
  IF (previous artifacts missing) → ERROR with message, don't proceed with empty state
  NEVER: create new RUN_ID for resume — breaks inter-phase dependencies
```

## Failure Modes

### O Score 4/100 na Pasta Vazia
- **Trigger:** `--phase 8` creates new run directory. QA runs on empty directory without phases 1-7.
- **Manifestation:** Score 4/100 (invalid) vs correct run's 83.05/100 (MAP-READY).
- **Detection:** Score anomalously low + phase artifacts missing from run directory.
- **Prevention:** Resume resolves 'latest' symlink. All artifacts in same directory.

## Validation

✓ **Paradoxo identificado:** Resume automático cria novo RUN_ID (quebra dependências) vs Resume deve manter MESMA run (preserva estado)

✓ **Resolução implementada:** Symlink 'latest' resolve para último RUN_ID válido. Verificação obrigatória de artefatos anteriores antes de iniciar fase N.

✓ **Critério de sucesso:** Score QA na run resumida ≥ 80/100. Score em pasta vazia < 10/100 (rejeição automática).

✓ **Aplicação:** Pipeline multi-fase + resume/retry scenarios.
