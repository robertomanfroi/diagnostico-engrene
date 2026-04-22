# AN_KE_074 - Commit Sebelum Deletion (Commit Before Unsafe Deletion)
**Zone:** 🔥 20% Impacto | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão c49f3c16, aiox-stage — "antes de continuar faça commit"]

## Purpose

A deleção estrutural ou reposicionamento de centenas de artefatos é uma operação de alto risco, pois os LLMs rotineiramente erram escopo (deletam massivamente pastas pai via `rm -rf`). A regra impõe que *antes* de prosseguir com uma exclusão pedida ou uma reestruturação perigosa de arquivos em staging, o Agente DEVE obrigar a fixação de um save-state com um `git commit`. Isso garante a reversibilidade a 1 segundo de custo mental.

## Configuration

```yaml
AN_KE_074:
  name: "Commit Before Unsafe Deletion"
  zone: "impacto"
  trigger: "Operação massiva de exclusão, deleção de arquivos sensíveis ou reorganização destrutiva."

  sys_tension:
    tension_with: "AN_KE_075 (Delete Stale Recreate from Scratch) — Checkpoint reversibility vs Destructive cleanup authorization"
    resolution: "Safety takes precedence. Commit before deletion to create reversible checkpoint, then validate completion, then create final commit documenting closure."

  rule: |
    SE a tarefa envolver deletar pastas de scaffolding ou dados massivos iteráveis
    ENTÃO OBRIGATÓRIO commitar o estado local ANTES de executar o rm/delete.
    Aja como um checkpoint de segurança inegociável.
    O `git commit` deve preceder operações destrutivas como um escudo anti-hallucination.

  veto_condition:
    trigger: "Agente processa comando apagando 50 arquivos no bash sem validar status Git."
    action: "VETO — 'antes de continuar faça commit'."

  evidence:
    - "[SOURCE: sessão c49f3c16, aiox-stage] 'nao delete nada do harry potter, antes de continuar faça commit'"
```

## Decision Tree

```javascript
IF (action_destroys_or_massively_moves_files)
  STEP_1: PAUSE execution.
  STEP_2: CHECK git status.
    IF (uncommitted_changes_exist)
      -> ASK HUMAN to commit OR auto-run `git add . && git commit -m "chore: save state before massive deletion"`
  STEP_3: EXECUTE deletion / scaffolding teardown.
```

## Failure Modes

### RM-RF Catastrófico
- **Trigger:** Agente deleta a pasta `/docs` antiga inteira para dar lugar à `/docs-v2` sem commitar as novidades nas outras pastas adjacentes.
- **Manifestation:** Perde-se alterações valiosas não lixadas, impossibilitando CTRL+Z no file system.
- **Detection:** `git reflog` vazio nos últimos 30 min com `rm -rf` executado.
- **Prevention:** A heurística impõe salvar.

## Validation

✅ **Paradoxo Identificado:** Commit obrigatório ANTES da deleção cria estado incompleto (staging com deletions apenas), violando Conventional Commits que exigem commits semânticos completos.

✅ **Resolução Aplicada:** Bifurcar em dois commits — (1) "chore: save state before destructive operation" (reversibility checkpoint), (2) "feat/fix: complete deletion [Story X.Y]" (semantic close).

✅ **Compliance:** Implementação responde à veto_condition sem comprometer integridade de git history.
