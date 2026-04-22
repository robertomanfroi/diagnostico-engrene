# AN_KE_033 - Squads = Source of Truth

**Type:** Architecture Governance Heuristic
**Zone:** 🧠 0,8% Genialidade
**Agent:** @oalanicolas
**Pattern:** Multi-Runtime Portability
**Source:** [SOURCE: Sessão sinkra-hub 0dadc1e0 — declaração explícita de que squads/ é SOT e .claude/ é projeção]
**sys_tension:** AN_KE_073 (Parallel Subagents) vs Centralização em squads/ como SOT — Subagentes paralelos pressuram distribuição; squads/ como SOT preserva unicidade da verdade. Resolver via artifact contracts + orchestração que mantém squads/ canônico enquanto permite paralelização segura.

## Purpose

A fonte da verdade de skills, agents e processos é SEMPRE `squads/`, nunca `.claude/skills/`. O diretório `.claude/` é uma PROJEÇÃO para Claude Code. Squads devem ser portáveis para qualquer runtime (Codex, Gemini, Claude) sem depender de vendor lock-in.

## Configuration

```yaml
AN_KE_033:
  name: "Squads = Source of Truth"
  zone: "genialidade"
  trigger: "Criando, editando ou decidindo onde salvar skills, agents, tasks."

  rule: |
    SE criando skill/agent/task
    ENTÃO a fonte da verdade é squads/{squad-name}/.
    .claude/skills/ é PROJEÇÃO (sync automático).
    NUNCA criar algo que vive SÓ dentro de .claude/.
    Portabilidade multi-runtime: codex, gemini, claude.

  veto_condition:
    trigger: "Skill ou agent que existe apenas em .claude/skills/ sem correspondência em squads/."
    action: "VETO — Mover para squads/ e configurar sync."

  evidence:
    - "[SOURCE: sessão 0dadc1e0] 'a fonte da verdade é sempre o squads/ as skills como esta sao originadas dele, pois podem ser reproduzidas para codex, gemini, claude, e nao devem viver nunca só dentro de .claude, isso deve virar uma lei, uma heuristica ou algo assim'"
```

## Decision Tree

```javascript
IF (creating_or_editing skill OR agent OR task)
  THEN PRIMARY_LOCATION = squads/{squad-name}/
  THEN .claude/skills/ = auto-sync projection
  IF (file_exists_only_in .claude/skills/)
    THEN MIGRATE to squads/ immediately
  IF (file_exists_only_in squads/)
    THEN OK — sync will project to .claude/ when needed
```

## Failure Modes

### Vendor Lock-in
- **Trigger:** Skill criada direto em `.claude/skills/` sem squad correspondente.
- **Manifestation:** Impossível rodar em Codex ou Gemini. Preso no Claude Code.
- **Detection:** Audit: `diff squads/ .claude/skills/` mostra skills órfãs.
- **Recovery:** Mover para `squads/{owner-squad}/` e configurar sync.
- **Prevention:** Regra: squads/ é SOT. Sempre.

## Integration with Workflow

```yaml
checkpoint:
  id: "squads-sot-gate"
  heuristic: AN_KE_033
  phase: "Skill_Creation / Agent_Design"
```

## Validation

**Paradoxo Resolvido:** Centralização vs Portabilidade é resolvida pela arquitetura de artifact contracts (SINKRA v3.1). A fonte de verdade permanece em squads/, mas o contrato declarativo permite que qualquer runtime (Claude, Codex, Gemini) reconheça e execute o artefato sem acoplamento ao Claude Code. A projeção automática (.claude/ sync) é implementação, não verdade — a verdade é o contrato estrutural em squads/.
