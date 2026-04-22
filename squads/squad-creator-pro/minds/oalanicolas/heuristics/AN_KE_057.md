# AN_KE_057 - Multi-Window Isolation

**Type:** Workflow Architecture Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Trabalho Paralelo em Múltiplas Janelas
**Source:** [SOURCE: Sessões sinkra-hub 0f1fe148, f5cce682 — falsos positivos em hooks por /commit em outra janela + regras de slug único por janela]

**sys_tension:** (allow_parallel_windows, enforce_slug_isolation)
**resolution:** Use sessionId + timestamp + branch as composite key to partition state per window while allowing concurrent execution

## Purpose

Alan trabalha com múltiplas janelas Claude Code simultaneamente. Hooks, scripts e pipelines DEVEM tolerar esse padrão. Um slug = uma janela. Detecção de sessão não pode confundir commit de outra janela com atividade da sessão atual.

## Configuration

```yaml
AN_KE_057:
  name: "Multi-Window Isolation"
  zone: "excelencia"
  trigger: "Criando hooks, scripts de sessão, ou pipelines que detectam atividade do usuário."

  rule: |
    SE criando automação que detecta atividade (hooks, session detection, commit hooks)
    ENTÃO ASSUMA que Alan trabalha em múltiplas janelas simultaneamente.
    /commit em outra janela ≠ atividade da sessão atual.
    Um processo = um output slug único.
    Não reutilizar slug em duas janelas ao mesmo tempo.

  veto_condition:
    trigger: "Hook que assume que todo commit pertence à sessão ativa, ou pipeline que reusa slug entre janelas."
    action: "VETO — Adicione filtro de sessionId ou slug único por janela."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Complexidade de Parsing Local"
    resolution: "Paralelismo (AN_KE_073) requer isolamento (AN_KE_057) para evitar colisão de estado. Cada janela = executor independente com seu próprio sessionId:timestamp:branch. Outputs podem ser mergidos APÓS validação de que contextos não vazaram."

  evidence:
    - "[SOURCE: sessão 0f1fe148] 'nem sempre, mts vezes uso /commit em outra janela, entao deve ter mt falso positivo ai'"
    - "[SOURCE: sessão 0f1fe148] 'mas nem sempre faco handoff tb as vezes edito tudo faco tudo e dou commit em outra janela'"
    - "[SOURCE: sessão f5cce682] 'um processo = um output slug único / não reutilizar o mesmo slug em duas janelas ao mesmo tempo'"
```

## Decision Tree

```javascript
IF (building_hook OR session_detection OR activity_tracking)
  IF (using_git_commits_as_signal)
    THEN FILTER by sessionId or branch — not all commits belong to this session
  IF (using_duration_as_signal)
    THEN OK — duration is per-session
  IF (pipeline_with_output_slug)
    THEN ENFORCE one slug = one window
    THEN BLOCK reuse of same slug in concurrent windows
```

## Failure Modes

### O Hook Falso Positivo
- **Trigger:** Hook de sessão detecta 5 commits em 20 minutos e dispara extração de heurísticas.
- **Manifestation:** 4 dos 5 commits foram /commit de outra janela fazendo trabalho diferente.
- **Detection:** Heurísticas extraídas não fazem sentido — misturam contextos de 2 projetos.
- **Recovery:** Filtrar commits por branch ou sessionId antes de analisar.
- **Prevention:** Usar duration como sinal primário, commits como sinal secundário COM filtro.

## Integration with Workflow

```yaml
checkpoint:
  id: "multi-window-isolation-gate"
  heuristic: AN_KE_057
  phase: "Hook_Design / Session_Detection"
```

## Validation

✅ **Paradox identified:** Parallelism (multiple windows) requires isolation (unique slug), but commits flow across all windows without inherent filtering. Solution enforces composite key (`sessionId:timestamp:branch`) to partition state while allowing concurrent work without collision.

✅ **Prevention mechanism:** Hooks MUST filter activity by sessionId before processing, treating each window as independent execution context. Shared outputs (heuristics, artifacts) only merge AFTER validation that contexts don't bleed.

✅ **Test case:** Two windows, same branch, /commit in W2 should NOT trigger heuristic extraction in W1 unless explicitly aggregating across windows with explicit merge logic.
