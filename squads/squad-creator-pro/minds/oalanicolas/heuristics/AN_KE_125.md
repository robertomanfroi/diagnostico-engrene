# AN_KE_125 - Headless LLM = Text Generator, Não Agente

**Type:** Architecture Heuristic
**Zone:** 🧠 0,8% Genialidade
**Agent:** @oalanicolas
**Pattern:** Persistence Inversion
**Source:** [SOURCE: sessão sinkra-hub 213d7429 — decoder.sh, 3 runs falhados consecutivos com haiku]
**Tags:** [Agnostic, Automation, Pipeline]

## Purpose

`claude -p` não é um agente — é um gerador de texto com tools opcionais. Tratar como agente ("salve os arquivos, sinalize quando terminar") falha com modelos menores: haiku gera análise, diz PHASE_COMPLETE, e nunca chama Write. O output morre no pipe. O script DEVE capturar o stdout como deliverable. O LLM pensa, o script registra.

## Configuration (True L3-State)

```yaml
AN_KE_125:
  name: "Headless LLM = Text Generator, Não Agente"
  zone: "genialidade"
  trigger: "Pipeline headless com qualquer LLM que deve produzir deliverables em disco."

  sys_tension:
    tension_with: "AN_KE_117 (Explicit Write Instruction)"
    resolution: "AN_KE_117 pede que o prompt instrua Write — é otimização. AN_KE_125 garante que o SCRIPT salva stdout — é safety net. Modelos grandes (opus/gemini) usam Write E tem stdout salvo. Modelos pequenos (haiku) só têm stdout. Belt and suspenders."

  rule: |
    SE pipeline usa claude -p / codex / gemini headless
    ENTÃO echo "$OUTPUT" > phase{N}-output.md SEMPRE (INCONDICIONAL)
    E prompt diz "sua resposta É o deliverable — estruture bem"
    NUNCA depender de tool execution como única forma de persistência

  veto_condition:
    trigger: "Pipeline onde output depende exclusivamente do LLM chamar Write."
    action: "VETO — 'haiku rodou 3x, 333 tokens de análise, zero arquivos. O script salva, o LLM pensa.'"

  failure_modes:
    omission: "Output morre no pipe. Gate falha. 10 retries. Zero progresso."
    misapplication: "Script salva lixo (150 chars de 'vou analisar...'). Threshold mínimo: 200 chars."

  evidence_threshold: "[EMPIRICAL] — 3 incidentes + 3 modelos confirmam"
  evidence:
    - "[SOURCE: sessão 4775d0c3] 'Haiku: 333 tokens, PHASE_COMPLETE, zero Write calls, zero arquivos.'"
    - "[SOURCE: sessão 213d7429] 'Fix: script salva stdout. Prompt: sua resposta É o deliverable. Confirmado haiku + opus + gemini.'"
```

## Decision Tree (Strict Format)

```text
STEP_1: LLM executes via pipe (claude -p / codex / gemini CLI)
STEP_2: Script captures $OUTPUT (ALWAYS)
STEP_3: IF (${#OUTPUT} > 200) → save as phase{N}-output.md
        AND VETO (pipeline without this step)
STEP_4: IF (LLM also wrote files via Write tool) → bonus, not requirement
NEVER:
  - Pipeline without stdout capture
  - Prompt that says "you MUST use Write tool" as sole persistence
```

## Validation & Cross-Mind Divergence

### Self-Validation Ask
1. "Se eu tirar Write dos --allowedTools, o pipeline ainda produz outputs em disco?"

### Divergence Analysis (Baseline IA vs Mente Zero)
- **Base LLM Tendency:** "Sou um agente, vou usar tools para salvar."
- **Mind Zero Override:** "Em headless, você é um text generator com tools opcionais. O pipe é o contrato."

## Behavioral Evidence (Real-World Application)

**Example:** "3 runs de haiku, zero arquivos, zero progresso"
- **Context:** decoder.sh Phase 0, haiku, prompt dizia "use Write tool".
- **Heuristic Application:** Script passou a salvar stdout. Prompt passou a dizer "sua resposta É o deliverable".
- **Outcome:** 3 modelos confirmam. Pipeline avança com qualquer modelo. Write tool = bônus.
