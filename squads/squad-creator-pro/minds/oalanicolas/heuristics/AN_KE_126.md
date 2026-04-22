# AN_KE_126 - Handoff-as-Infrastructure (Session Continuity Protocol)

**Type:** Execution Process Heuristic
**Zone:** 🧠 0,8% Genialidade
**Agent:** @oalanicolas
**Source:** [SOURCE: timestamp 1767457744, mmos] [SOURCE: timestamp 1774289281, mmos] [SOURCE: timestamp 1767051088, mmos]
**Tags:** [Process, Context, Continuity, Multi-Session]

## Purpose

Alan trata handoffs nao como atos casuais de cortesia entre sessoes, mas como infraestrutura critica de producao. Em 207 ocorrencias ao longo de 8+ projetos (mmos, aiox-core, aiox-stage, aiox-stage, sinkra-hub, mente_lendaria, forefy-prep-ahead, mentor-hub), handoffs sao pedidos sistematicamente como ultimo ato de TODA sessao produtiva — inclusive sob pressao de tokens acabando. A intensidade escala: comeca com "faca handoff" simples, evolui para exigir templates padronizados, depois para a criacao de uma SKILL dedicada (/handoff), e finalmente para pesquisas de mercado sobre como outros sistemas resolvem handoffs. Nenhum outro operador de IA que se conhca trata continuidade inter-sessao com essa seriedade. Isso define como este mind opera: a producao nao para quando a janela fecha.

## Configuration

```yaml
AN_KE_126:
  name: "Handoff-as-Infrastructure (Session Continuity Protocol)"
  zone: "genialidade"
  trigger: "Qualquer sessao que produziu trabalho significativo, especialmente sob pressao de context window ou tokens acabando."

  sys_tension:
    tension_with: "AN_KE_048 (Handoff Psicologico Completo)"
    resolution: "AN_KE_048 trata do CLOSURE PSICOLOGICO — nao deixar trabalho pela metade. AN_KE_126 trata da INFRAESTRUTURA MECANICA — o handoff como artefato estruturado que permite continuidade perfeita. Um fala de escopo, outro de formato. Coexistem."

  rule: |
    SE sessao produziu trabalho significativo
    ENTAO antes de encerrar:
      (1) Criar handoff ESTRUTURADO (nao texto corrido)
      (2) Incluir: o que foi feito, o que falta, decisoes tomadas, arquivos alterados
      (3) Handoff deve ser compreensivel por IA SEM CONTEXTO da sessao
      (4) Salvar em docs/sessions/ ou docs/logs/ (nao efemero)
    SE tokens acabando → handoff tem PRIORIDADE sobre qualquer task pendente
    SE handoff ruim → RECUSAR ("ta mt fraco, precisa ficar um handoff completo")

  veto_condition:
    trigger: "Sessao encerrada sem handoff estruturado. Ou handoff superficial sem contexto suficiente."
    action: "VETO — 'esse handoff e para uma IA que nao sabe nada do que fizemos aqui'"

  evidence:
    - "[SOURCE: timestamp 1767457744, mmos] 'faca agora um handoff desta sessao, principalmente adiiconando as descobertas que vao economizar muitos tokens na proxima sessao'"
    - "[SOURCE: timestamp 1767051088, mmos] 'voce deixou bem informado que e uma aplicacao externa, e todos os detalhes difernetrs que essa acao que estamos fazendo tem? esse handoff e para uma ia que naos abe nada do que fizemos aqui'"
    - "[SOURCE: timestamp 1774289281, mmos] 'Seri amais economico ao inves de ter uma sessao inteira explicando handoff eu ter uma skill com tudo isso e mais certo?'"
    - "[SOURCE: timestamp 1768604959, mmos] 'ta mt fraco, precisa ficar um handoff completo'"
    - "[SOURCE: timestamp 1767454908, mmos] 'seus tokens estao acabando faca handoff agora'"
    - "[SOURCE: timestamp 1771610262, global] 'coloque o maximo de dados neste handoff a IA via comecar do zero, sem saber nada, coloque principalmetne as ADR, as heuristicas, os motivos'"
```

## Decision Tree

```javascript
IF (session_ending || tokens_low || context_window_shrinking)
  STEP_1: STOP current task immediately
  STEP_2: CREATE structured handoff with:
    - WHAT was done (files, decisions, changes)
    - WHAT remains (with priority order)
    - WHY decisions were made (ADRs, heuristics)
    - WHERE files live (absolute repo paths)
    - BLOCKERS or risks for next session
  STEP_3: VALIDATE handoff quality
    IF (handoff is shallow or vague)
      REJECT → "ta mt fraco, precisa ficar um handoff completo"
    IF (handoff assumes context from this session)
      REJECT → "essa IA nao sabe nada do que fizemos aqui"
  STEP_4: SAVE to persistent location (docs/sessions/ or docs/logs/)
  NEVER: Close session with "faltou tempo" without handoff
  NEVER: Trust that next session will "figure it out"
```

## Failure Modes

### O Handoff Fantasma
- **Trigger:** Sessao termina com "vou continuar depois" sem documento estruturado.
- **Manifestation:** Proxima sessao gasta 30+ minutos tentando reconstruir contexto. Decisoes sao refeitas. Trabalho duplicado.
- **Detection:** Proxima sessao comeca com "o que estavamos fazendo?" sem referencia a handoff.
- **Prevention:** Handoff como ULTIMO ato obrigatorio, mesmo sob pressao de tokens. Skill /handoff com template padronizado.

### O Handoff Raso
- **Trigger:** Handoff criado mas com informacao insuficiente ("fizemos X, falta Y").
- **Manifestation:** IA na proxima sessao le o handoff mas nao consegue continuar com qualidade. Pede esclarecimentos que o humano nao lembra mais.
- **Detection:** Alan rejeita: "ta mt fraco" ou "precisa ficar um handoff completo".
- **Prevention:** Template com campos obrigatorios: decisoes, arquivos, contexto, blockers, proximos passos.
