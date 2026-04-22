# AN_KE_041 - Output Path Discipline

```yaml
---
id: AN_KE_041
name: "Output Path Discipline"
type: "Artifact Classification Heuristic"
zone: "🔥 20% Impacto"
agent: "@oalanicolas"
pattern: "Separação outputs/ vs squads/"
source: "[SOURCE: Sessão sinkra-hub 058541ef + regra artifact-classification.md]"
sys_tension:
  tension_with: "AN_KE_054 (Estrutura Orgânica de Diretórios) vs Isolamento de Outputs: paths devem ser orgânicos mas outputs devem ficar segregados"
  resolution: "Criar symlinks em outputs/shared/ ou registry index em .aiox-core/core-config.yaml com mapa de outputs reutilizáveis por ID de artefato. Outputs imutáveis → versionados; outputs transitórios → TTL."
```

## Purpose

Outputs de execução de pipelines/squads vão em `outputs/`, NUNCA dentro de `squads/` ou `workspace/`. Squads contêm config, agents, tasks. Outputs contêm resultados transitórios de execução.

## Configuration

```yaml
AN_KE_041:
  name: "Output Path Discipline"
  zone: "impacto"
  trigger: "Salvando resultados de pipeline, análise, validação, ou qualquer artefato gerado."

  rule: |
    SE artefato é resultado de execução de squad/task
    ENTÃO salvar em outputs/{squad-name}/{context}/
    NUNCA dentro de squads/{squad-name}/output/
    NUNCA dentro de workspace/

  veto_condition:
    trigger: "Pipeline salvando resultados dentro da pasta do squad ao invés de outputs/."
    action: "VETO — Mover para outputs/. Squads são config, não storage."

  evidence:
    - "[SOURCE: sessão 058541ef] 'o local certo para salvar isso é outputs na pasta principal e nao dentro do squad sinkra'"
    - "[SOURCE: .claude/rules/artifact-classification.md] Decision tree: 'É output de execução de squad/task? SIM → outputs/{squad-name}/'"
```

## Decision Tree

```javascript
IF (saving_generated_artifact)
  IF (artifact_is_config OR agent OR task OR template)
    THEN SAVE in squads/{squad-name}/
  ELSE IF (artifact_is_execution_output OR analysis OR report)
    THEN SAVE in outputs/{squad-name}/{context}/
  ELSE IF (artifact_is_business_document with template + registry)
    THEN SAVE in workspace/businesses/{slug}/L{N}/
```

## Failure Modes

### Squad Bloat
- **Trigger:** Pipeline salva 50MB de outputs dentro de `squads/sinkra-squad/output/`.
- **Manifestation:** Squad fica pesado, git clone lento, confusão entre config e outputs.
- **Detection:** `du -sh squads/*/` mostra squad com >10MB.
- **Recovery:** Mover para `outputs/` e atualizar paths nos scripts.

## Integration with Workflow

```yaml
checkpoint:
  id: "output-path-gate"
  heuristic: AN_KE_041
  phase: "Pipeline_Output_Design"
```

## Validation

**Systemic Tension (sys_tension):**
- **Tension With:** Pipeline reusability requirements vs. artifact isolation discipline
- **Paradox:** Outputs must stay isolated in `outputs/` (not in `squads/`) to prevent config bloat → BUT outputs of one squad's execution frequently need to feed into downstream pipelines of other squads → requires fast discovery + access
- **Resolution Path:** Version and index outputs via centralized registry (`.aiox-core/core-config.yaml → artifact_outputs[]`) instead of embedding paths. Symlinks allow logical grouping without duplication. TTL policies on transitional outputs separate temporary work from reusable artifacts.

**Validation Checklist:**
- [ ] Output directories contain ONLY execution artifacts (no config files, no agents, no tasks)
- [ ] No outputs directory is nested inside `squads/{name}/`
- [ ] `outputs/{squad-name}/{context}/` follows discoverable naming convention
- [ ] Reusable outputs registered in artifact registry with immutability flag + version
- [ ] Transitional outputs have explicit TTL; stale outputs pruned via `cleanup:artifacts` task
- [ ] No pipeline reads outputs by hardcoded path; all reads go through registry lookup
- [ ] git history shows outputs/ only contains committed outputs when intentional (not CI artifacts)
