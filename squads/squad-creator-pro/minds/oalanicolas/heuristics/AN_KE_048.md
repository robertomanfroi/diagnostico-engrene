# AN_KE_048 - Handoff Psicológico Completo

**Type:** Execution Ritual Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Mind-Mapping & Closure
**Source:** [SOURCE: Discussões de produtividade sobre o Zeigarnik effect (ansiedade do laço não fechado), forçando a sessão a focar em "Entregas Redondas" antes de encerrar o prompt do dia.]

## Purpose

Assegurar a limpeza da RAM mental do usuário/dev. Dividir uma função épica global pela metade porque a sessão de código se alongou causa ruído residual e esquecimento (Amnésia Crítica na reinicialização de janelas de Claude/Agentes). Todo sub-ticket deve acabar cravado. Se não couber numa sessão, não force o desmembramento; corte o escopo ou conclua a micro-ferramenta por completo na base de 100%.

## Configuration

```yaml
AN_KE_048:
  name: "Handoff Psicológico Completo"
  zone: "impacto"
  trigger: "Agente delineando roteiros ou executando a última fase de uma task épica, ou planejando o cronograma de ação de uma sessão diária."

  rule: |
    SE você for delinear as ações do dia
    ENTÃO delimite-as numa "Trilha de Completude Absoluta 100%". Pedaços abertos e features semi-refatoradas não geram closure psicológico e trazem fadiga para as próximas interações.

  veto_condition:
    trigger: "Criar roteiro enorme que deixará a Database migration feita no arquivo .sql pendente de implementação de ORM só amanhã."
    action: "VETO — Recorte o escopo. Construa apensas o Model da Autenticação Hoje de ponta a ponta (100% de handoff)."

  evidence:
    - "[EXACT WORDS]: Porque: Closure psicológico (100% do plano)... migration-generator.sh é o mais valioso... Realista para uma sessão."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Completude Psicológica de Closure"
    conflict: "Metodologias ágeis exigem entrega contínua de incrementos (parciais aceitáveis) e paralelização para throughput máximo, mas a psicologia humana necessita closure completo para evitar fadiga residual. Forçar handoff parcial viola closure; forçar completude absoluta viola iteração e throughput paralelo."
    resolution: "Estabelecer 'Unidades de Closure Mínima' — o menor escopo que gera psicologicamente satisfação COMPLETA (ex: feature testável end-to-end, não apenas backend). Priorizar essas unidades mínimas sobre feature backlog massivo, mesmo que isso reduza paralelização."
```

## Decision Tree

```javascript
IF (defining_session_scope OR executing_long_thread_tasks)
  IF (session_predicts_unfinished_branches_by_handoff_time == TRUE)
    THEN BLOCK_EXPANSION
    THEN SHRINK_SCOPE
      IF (Micro-Epic reaches 'Closure Psicológico' cleanly)
        // Everything tests, documents, and runs logically enclosed 
        THEN SAVE_FINAL_ARTIFACTS (Memory Handoff generation allowed)
  ELSE
    // Focus has been appropriately sized for atomic completeness.
    THEN ALLOW_EXECUTION
```

## Failure Modes

### Zumbi do Estado Parcial
- **Trigger:** Dev decide construir 3 scripts gigantes na mesma thread de madrugada (O Hub, Validador, Dashboard). O Dashboard fica com TypeErrors até 3h da manhã. O Dev desiste ali. No dia seguinte ele não quer mexer naquilo.
- **Manifestation:** O projeto se afunda de dívida técnica inabordável por dor psicológica, pois o usuário perdeu as "Linhas Mágicas" da compreensão do estado que existia na tela naquele momento. A LLM em thread nova "não entende a base crua" se não ler muito.
- **Detection:** Rejeição do usuário em progredir num projeto cheio de "Comentários TODO no meio do core".
- **Recovery:** Adoção de reverter as branches até um *Stable Closure* e repensar.
- **Prevention:** Somente pular do Módulo A para o Mês B após a verificação `Atomic_Integrity_Check` estar verdinha.

## Integration with Workflow

```yaml
checkpoint:
  id: "psychological-closure-validation"
  heuristic: AN_KE_048
  phase: "Thread_Ending / Epic Generation"

  validation_questions:
    - "A etapa atual foi encapsulada, selada com Handoff, testável independentemente e isenta de pendências vazadas? O humano pode dormir em paz?"
```

## Validation

**Paradoxo Confirmado:** Completude 100% vs Realismo de Sessão — A heurística exige atomicidade total (100% closure), mas real-world constraints (tempo, contexto, escopo) frequentemente impossibilitam conclusão completa.

**Resolução Aplicada:**
- Introduzido conceito de "Unidade de Closure Mínima" — o menor incremento que ainda satisfaz psicologicamente.
- Reframes sucesso: não é "fazer tudo", é "fazer-bem-uma-coisa-completa" em vez de "fazer-tudo-parcialmente".
- Alinha com iteração ágil (incremental) sem sacrificar closure psicológico.

**Aplicabilidade:** Crítica para sessions longas, multi-epic threads, e burnout prevention em dev teams.
