# Greeting Script Checklist

> **Owner:** @squad-chief
> **Squad:** Squad Creator
> **Padrão:** GREETING-CONTINUITY-001
> **Versão:** 1.0.0

---

## 1. Estrutura do Script

- [ ] Arquivo em `squads/{squad}/scripts/generate-{squad}-greeting.cjs`
- [ ] Shebang `#!/usr/bin/env node` presente
- [ ] Usa `require('js-yaml')` com try/catch fallback
- [ ] ROOT resolvido via `process.cwd()`
- [ ] SQUAD_NAME e ENTRY_AGENT definidos como constantes

## 2. Funções Core (4 obrigatórias)

- [ ] `collectContext()` — Coleta dados do filesystem (ZERO LLM)
- [ ] `inferNextAction(context)` — Heurística determinística com prioridades
- [ ] `buildGreeting(context, nextAction)` — Monta output markdown
- [ ] `buildDirectives(context, nextAction)` — Gera bloco de runtime directives

## 3. Data Collection (collectContext)

- [ ] Lê config.yaml do squad
- [ ] Lê fontes de contexto relevantes (runtime, workspace, backlog, diagnósticos)
- [ ] Não depende de estado da LLM
- [ ] Falha silenciosamente se arquivo não existe (retorna null, não crash)
- [ ] Usa loadYaml com try/catch

## 4. Next Action Inference (inferNextAction)

- [ ] Implementa pelo menos 3 níveis de prioridade
- [ ] P1: Gap bloqueante → ação de remediação
- [ ] P2: Gap não-bloqueante → ação de completude
- [ ] P3: Intake/ready → comando operacional principal
- [ ] NUNCA sugere CTA genérico quando blocker existe
- [ ] Retorna objeto `{ action, reason, severity }`
- [ ] Severity é um de: `blocking`, `non_blocking`, `intake`, `ready`

## 5. Greeting Builder (buildGreeting)

- [ ] Output é markdown válido
- [ ] Inclui seção de contexto (se contexto disponível)
- [ ] Inclui tabela de comandos (top 8-10)
- [ ] Termina com **Next Action:** + severity icon + comando
- [ ] Next Action usa formato: `**Next Action:** {icon} \`{command}\``
- [ ] Linha seguinte: `> {reason}`
- [ ] Icons: 🔴 blocking, 🟡 non_blocking, 🔵 intake, 🟢 ready

## 6. Runtime Directives (buildDirectives)

- [ ] Bloco HTML comment: `<!-- {PREFIX}_RUNTIME_DIRECTIVES ... -->`
- [ ] Contém: squad, entry_agent, next_action, next_action_severity, next_action_reason
- [ ] Aparece ANTES do greeting no output
- [ ] Agent pode parsear para binding de sessão

## 7. Integração com Agent

- [ ] Entry agent tem STEP 3.5 no activation-instructions
- [ ] STEP 3.5 executa o script via `node squads/{squad}/scripts/generate-{squad}-greeting.cjs`
- [ ] STEP 3.5 diz "Display EXACTLY as returned"
- [ ] STEP 4 é fallback (só se script falha)

## 8. Integração com Config

- [ ] Script registrado em `config.yaml` seção `scripts:` (se existir)
- [ ] Trigger: `on_activation`

## 9. Testes (3 cenários obrigatórios)

- [ ] Cenário 1: **No context** (fresh start) — Next Action = blocking ou intake
- [ ] Cenário 2: **Blocking gap** — Next Action = remediação específica, NOT genérico
- [ ] Cenário 3: **Ready state** — Next Action = comando operacional principal
- [ ] Script executa sem erro (exit code 0) em todos os cenários

## 10. Qualidade

- [ ] Script < 400 linhas (sem contar comentários)
- [ ] Nenhuma dependência externa além de `js-yaml` e `fs/path`
- [ ] Sem `eval()`, sem execução dinâmica
- [ ] Sem hardcoded business data (squad agnosticism)
- [ ] Funções exportadas via `module.exports` para testabilidade

---

## Scoring

| Seção | Peso | Score |
|-------|------|-------|
| Estrutura | 10% | __/100 |
| Funções Core | 20% | __/100 |
| Data Collection | 15% | __/100 |
| Next Action | 25% | __/100 |
| Greeting Builder | 10% | __/100 |
| Directives | 5% | __/100 |
| Integração Agent | 5% | __/100 |
| Testes | 10% | __/100 |

**Gate Decision:**
- 90-100: PASS
- 70-89: CONCERNS (fix antes de ship)
- <70: FAIL (recriar)

---

*Checklist do Squad Creator — GREETING-CONTINUITY-001*
*Versão: 1.0.0*
