# AN_KE_107 - Queue Concurrency Chaos
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão e6fec185, integrações n8n/whats — "escala... nao ficavam na ordem certa"]

## Purpose

Sistemas desenhados em laboratório muitas vezes rodam 1 iteração isolada via Postman com sucesso e são despachados como funcionais. Quando recebem volume real corporativo (ex. ingestão do WhatsApp ou Slack via webhooks N8N em massa), os microsserviços atropelam uns aos outros (Race Conditions), quebrando a linearidade do histórico das mensagens. Mapeado o erro custoso, a lei entra em vigor: todo sistema assíncrono que processa histórico ou linhas conectadas via eventos (Filas/Queues) DEVE possuir garantias estritas de Order Preservation (e evitação de concorrência ingênua).

## Configuration

```yaml
AN_KE_107:
  name: "Queue Concurrency Chaos"
  zone: "genialidade"
  trigger: "Desenhando lambdas, sub-funções cloud ou fluxos assíncronos (cron/webhook) de alto tráfego temporal."

  rule: |
    SE você implementar fluxos assíncronos que escutam eventos de disparo massivos ou chat logs
    ENTÃO PREVEJA E DESENHE uma barreira restritiva para a ORDEM CRONOLÓGICA (Order Preserving Queue).
    Testar o loop com apenas N=1 em dev é negligência. Concorrência escalável deve ser o Day 0.

  veto_condition:
    trigger: "Agente encerra a API Gateway alegando sucesso no script porque a requisição local salvou. Mas o banco está liberado pra 5 writes paralelos nas mesmas timestamps."
    action: "VETO — 'Depois não conseguia escalar essa estrutura porque o trabalho em fila não funcionava bem. As mensagens não ficavam na ordem certa...'"

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Garantia de Ordem em Queues"
    resolution: "Usar filas com particionamento por chave (message_key/partition_key) ou locks pessimistas no BD. N escritas paralelas em chaves diferentes = OK; N escritas na mesma chave = serializar via FIFO queue ou row-level lock."

  evidence:
    - "[SOURCE: sessão e6fec185] 'Depois não conseguia escalar essa estrutura porque o trabalho em fila não funcionava bem. As mensagens não ficavam na ordem certa quando tinham muita grupos'"
```

## Decision Tree

```javascript
IF (designing_messaging_queues_or_async_batch_importers)
  STEP_1: IDENTIFY ordering urgency (Do events A and B strictly rely on chronological insertion?)
  STEP_2: CHECK concurrency limits settings.
    IF missing -> LIMIT batch concurrency to 1 (Sequential) OR insert strict strict timestamp locks.
  STEP_3: IMPLEMENT dead-letter queues.
  STEP_4: IF using Supabase -> Lock row for update (RLS/Functions) preventing parallel transaction overrides.
```

## Failure Modes

### Race Conditions Temporais (Cronological Smash)
- **Trigger:** Webhook de recebimento do WhatsApp de cliente atinge a URL da Vercel. 5 mensagens enviadas no mesmo segundo batem nos workers que inserem via ORM cego ao banco.
- **Manifestation:** O "Olá" fica abaixo do "Tudo bem com você?", destruindo a experiência para leitura da conversa retroativa inteira da dashboard AIOX.
- **Prevention:** Enfileiradores estritos que enforcam `order key FIFO`.

## Validation

**Paradoxo:** Precisamos escalar concorrentemente (velocidade, throughput) ao mesmo tempo que garantimos ordem linear (integridade, UX). A tentação é testar com N=1 localmente e assumir que funciona em produção.

**Validação:**
- ✓ Filas configuradas com particionamento por entidade (conversation_id, user_id)?
- ✓ Testes de carga com N>=10 escritas simultâneas na mesma partição rodados antes do deploy?
- ✓ Dead-letter queues habilitadas para falhas e retries?
- ✓ Row-level locks (SELECT ... FOR UPDATE) implementados se banco relacional?
- ✓ Timestamp ordering verificado em logs retroativos (audit trail intacta)?

Sem cumprimento destas garantias, o sistema vai "funcionar" localmente e falhar em produção quando escala.
