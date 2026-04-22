# AN_KE_031 - Localhost QA Gate

**Type:** Release Gate Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Frontend Deployment & Safety
**Source:** [SOURCE: Derivado de conversas sobre a apariência de erros técnicos em produção que não deviam vazar ao usuário comum, indicando pulo de instâncias.]
**sys_tension:** (belief_in_minor_refactors_as_safe, necessity_of_rigorous_local_validation); resolution: All changes, regardless of perceived scope, demand pre-commit localhost execution

## Purpose

Garantir que não existe confiança cega de que um código refatorado ("só alterei uma linha de const") irá compilar tranquilamente na Vercel/Produção, causando white screens mortai em clientes finais. O Local QA é absoluto.

## Configuration

```yaml
AN_KE_031:
  name: "Localhost QA Gate"
  zone: "impacto"
  trigger: "Refatorações visuais ou integrações na base de código web/UI."

  rule: |
    SE foi realizado um refactor no React, Next.js ou HTML Vanilla
    ENTÃO NUNCA dê COMMIT antes do dev responsável certificar a visualização localhost para crashes imediatos.

  veto_condition:
    trigger: "Tentativa do AI Agent de commitar algo web sem a afirmação explícita de teste rodado/rodando ou print log do terminal provando sucesso do build."
    action: "VETO — Start `npm run dev` or build before pushing."

  evidence:
    - "[EXACT WORDS]: Erros como esse só podem aparecer assim em localhost, nunca online... Não commite sem validar a visão web."

  tension_with: "AN_KE_049 (Ship First, Doc Later) — Pressão para deployment rápido vs necessidade de validação local rigorosa antecedente"
```

## Decision Tree

```javascript
IF (UI_component_altered OR routing_changed OR hooks_refactored)
  IF (dev_checked_localhost == TRUE)
    THEN ALLOW_COMMIT_PUSH
  ELSE
    THEN BLOCK_COMMIT
    THEN PROMPT_AGENT ("Execute o npm run dev/build. Avaliou visualmente? O site quebrou?")
      IF (compilation_error)
        THEN FIX_IN_LOCAL
      ELSE
        THEN proceed cleanly
```

## Failure Modes

### Fatal Vercel Deployment Break
- **Trigger:** Refatorar estado do Tailwind ou trocar uma dependência menor num commit "rápido".
- **Manifestation:** O build passa o CI marginalmente ou o Dev mode omite erro de TypeScript restrito, quebrando clientes em produção (White Screen).
- **Detection:** Rollbacks emergenciais ou painéis de sentry alarmando.
- **Recovery:** Buscar o último hash estável e forçar reverter via git branch e testar local.
- **Prevention:** Uso rígido do checkpoint de teste QA na máquina desenvolvedora como premissa para a automação CI.

## Integration with Workflow

```yaml
checkpoint:
  id: "qa-visual-lock"
  heuristic: AN_KE_031
  phase: "Git_Commit"

  validation_questions:
    - "A branch foi verificada fisicamente no browser antes do git push ser autorizado?"
```

## Validation

✓ **Paradoxo Identificado:** Cognitive bias que assume refatorações com escopo "pequeno" como intrinsecamente seguras, quando o risco real é ortoganal à magnitude da mudança.

✓ **Resolução:** Obrigação incondicional de teste localhost **antes** de qualquer commit, eliminando a falsa dicotomia entre mudanças "seguras" e "perigosas".

✓ **Garantia:** White screens em produção causados por erosão de CI/CD safety são preveníveis através de validação sensorial do desenvolvedor na máquina local.
