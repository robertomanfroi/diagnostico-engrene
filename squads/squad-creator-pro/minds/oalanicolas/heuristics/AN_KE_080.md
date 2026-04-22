# AN_KE_080 - Next Command Flow
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão d89753b9, aiox-stage — "me de o comando pra o proximo"]

## Purpose

A fluidez do loop Homem-Máquina exige atrito zero na passagem do bastão no terminal. Quando o Alan roda uma pipeline que processa dados e finaliza a sua fase atual, o agente ou script conclusivo JAMAIS deve terminar em silêncio de "concluído". Ele deve explicitamente antecipar e formatar em console o exato *próximo script ou comando* (`bash/CLI`) que precisará ser colado/executado na sequência. Transição sem cognição forçada.

## Configuration

```yaml
AN_KE_080:
  name: "Next Command Flow"
  zone: "excelencia"
  trigger: "Término de um epic execution run, validador ou script CLI multi-step interativo."
  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) — Serial Sequencing vs Parallel Execution"
    resolution: "Fornecer contexto de próximo passo em formato consultivo, não prescritivo — humano retém decisão final de sequenciação"

  rule: |
    SE você concluir um script, task complexa ou repassar o fluxo
    ENTÃO forneça o formato em bloco de código do COMANDO EXATO subsequente.
    A fricção entre o output de uma IA e o próximo passo natural deve ser zero.
    Sempre termine a saída dizendo "Próximo Comando:" e entregue o iterador necessário.

  veto_condition:
    trigger: "Script execute-epic termina dizendo 'Pronto, concluído!' e não mostra qual o próximo ID do story a ser rodado."
    action: "VETO — 'qual comando pra o proximo, quero sempre qu eno final me de o coamndo pra o proixmo'."

  evidence:
    - "[SOURCE: sessão d89753b9, aiox-stage] 'qual comando pra o proximo, quero sempre qu eno final me de o coamndo pra o proixmo / isso precisa ser alterado no execute-epic para ele sempre dar o comando do proximo execute'"
```

## Decision Tree

```javascript
IF (ending_script_execution_or_closing_task)
  STEP_1: IDENTIFY what is logically next to do (Is it the next story? Deploy? Test?)
  STEP_2: FORMAT output. Do not end conversation with a generic summary.
  STEP_3: EMBED CLI command
    `echo "Próximo Passo:"`
    `echo "npm run execute-epic --story 12.4"`
  STEP_4: EXIT gracefully leaving an actionable hook on screen.
```

## Failure Modes

### Dead-End Conversacional
- **Trigger:** Ao processar batch 1, agente finaliza respondendo apenas "Entendido e processado".
- **Manifestation:** O Alan perde tempo abrindo arquivos README ou `.MD` do backlog para lembrar qual era a story seguinte que ele anotou, quebrando o flow-state.
- **Prevention:** Pipeline chaining via sugestões hardcoded de script flow.

## Validation

**Paradoxo Identificado:** A heurística persegue "atrito zero" na transição (automação de sugestão de próximo passo), mas cria uma fricção cognitiva oposta — exigir que o agente antecipe o "próximo comando correto" sem contexto de prioridade/sequenciação do usuário viola a agência humana.

**Resolução:** Fornecer sugestões de próximo passo em modo **consultivo** (ex: "Próximos Candidatos:") em vez de **prescritivo** ("Execute isto"). O humano decide se quer executar ou desviar. Assim preserva-se fluidez sem sacrificar autonomia.

**Validação:** Teste em execute-epic: após conclusão de story, gerar lista de 3 próximas stories viáveis com seus IDs, precedidas por "→ Sugestões de Sequência:" e deixar Alan escolher qual executar.
