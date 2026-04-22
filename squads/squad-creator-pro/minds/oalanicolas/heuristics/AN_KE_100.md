# AN_KE_100 - Reverse Engineer Your Reasoning
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões sinkra-hub 5eb9bf45 (audit heurísticas), 0f1fe148 (validate-skill/squad)]

## Purpose

Meta-heurística suprema: quando completa processo complexo com resultado bom, FAZER ENGENHARIA REVERSA do próprio raciocínio e documentar como processo reprodutível. Mas a evidence do history revela que Alan não espera apenas um post-mortem no final — ele pede meta-extração DURANTE o processo ("Quais heuristicas podemos tirar de todo processo que estamos fazendo?") e COMPARTILHAMENTO entre ferramentas ("o que pode ser aproveitado entre eles que nao estamos aproveitando?"). A recursividade é tripla: (1) o processo de criar heurísticas É uma heurística, (2) o processo de compartilhar lógica entre scripts É um padrão ("log que é criado poderia ser compartilhado entre todos"), (3) o process-heuristic-mining-from-history.md que documenta ESTE processo é produto DESTA heurística.

## Configuration

```yaml
AN_KE_100:
  name: "Reverse Engineer Your Reasoning"
  zone: "genialidade"
  trigger: "Completou processo complexo com resultado de alta qualidade, OU identificou lógica reutilizável durante execução."
  sys_tension:
    tension_with: "AN_KE_025 (Determinism Over LLM) — parar para reverse-engineer quebra fluxo determinístico"
    resolution: "Extrair heurísticas DURANTE execução (não bloqueia), validar e compartilhar POST-MORTEM paralelo"

  rule: |
    SE completou processo complexo com resultado bom
    ENTÃO fazer engenharia reversa do próprio raciocínio em 3 tempos:
      (1) DURANTE: "quais heurísticas podemos tirar de todo processo que estamos fazendo?"
      (2) AO TÉRMINO: documentar como processo reprodutível por outras LLMs
      (3) CROSS-TOOL: "o que pode ser aproveitado entre eles que não estamos aproveitando?"
    O processo de criar heurísticas É uma heurística.
    O processo de compartilhar lógica É um padrão.

  veto_condition:
    trigger: "Resultado excelente obtido sem: (a) extrair heurísticas durante o processo, (b) documentar reasoning post-mortem, (c) identificar lógica compartilhável."
    action: "VETO — 'quando conclui faça engenharia reversa do seu reasoning para transformarmos em processo documentado. Isso por si só é material para heurística.'"

  evidence:
    - "[SOURCE: sessão 5eb9bf45, sinkra-hub] 'quando conclui faca uma engenharia reversa do seu reasoning para transforamrmos isso em um processo documentado que outras LLMs ou voce poderá executar isso no futuro, isso por si só já é material para uma heuristica'"
    - "[SOURCE: sessão 0f1fe148, sinkra-hub] 'Quais heuristicas podemos tirar de todo processo que estamos fazendo?'"
    - "[SOURCE: sessão 0f1fe148, sinkra-hub] 'o que pode ser aproveitado entre eles que nao estamos aproveitando?' + 'o log que é criado, nao poderia ser compartilhado entre todos tb?'"
    - "[META] Esta heurística é auto-referencial: foi criada pelo processo que ela descreve. A sessão 5eb9bf45 auditou os cards 060-100. O process-heuristic-mining-from-history.md é output direto desta heurística."
```

## Decision Tree

```javascript
IF (executing_complex_process)
  DURING_EXECUTION:
    QUESTION: "quais heurísticas podemos tirar deste processo?"
    IF (pattern_spotted) → NOTE for later formalization
    IF (reusable_logic_spotted) → FLAG: "isso pode ser compartilhado com X?"

  ON_COMPLETION:
    STEP_1: PAUSE — do not move to next task yet
    STEP_2: REVERSE-ENGINEER reasoning
      WHAT: exact sequence of decisions made
      WHY: rationale for each branching point
      WHICH: alternatives rejected and why
      WHERE: logic that could be shared between tools
    STEP_3: DOCUMENT as reproducible process
      FORMAT: step-by-step with decision gates (not prose)
      AUDIENCE: future self or another LLM executing same task
      DELIVERABLE: process .md file (like process-heuristic-mining-from-history.md)
    STEP_4: EXTRACT meta-patterns
      IF (process reveals new heuristic) → CREATE new AN_KE card
      IF (process confirms existing heuristic) → ADD evidence to existing card
      IF (logic is shared between tools) → EXTRACT to shared module (DRY)

  CROSS-TOOL CHECK (periodic):
    COMPARE: validate-skill vs validate-squad vs sinkra-map
    QUESTION: "o que pode ser aproveitado entre eles?"
    IF (shared logic found) → EXTRACT to shared lib (AN_KE_007 REUSE > CREATE)

  NEVER: finish excellent work without capturing the process that produced it
  NEVER: build similar tool without checking what can be shared from existing
```

## Failure Modes

### A Sessão Brilhante que Ninguém Reproduz
- **Trigger:** LLM executa pipeline perfeitamente mas não documenta o raciocínio.
- **Manifestation:** Próxima sessão tenta reproduzir → resultado medíocre porque reasoning steps são diferentes.
- **Detection:** Qualidade inconsistente entre sessões para mesma tarefa.
- **Prevention:** Post-mortem obrigatório: "como cheguei neste resultado? documentar."

### Os Três Scripts que Fazem a Mesma Coisa
- **Trigger:** validate-skill.sh, validate-squad.sh, sinkra-map.sh criados independentemente.
- **Manifestation:** "o que pode ser aproveitado entre eles que nao estamos aproveitando?" + "o log poderia ser compartilhado entre todos?"
- **Detection:** Diff de scripts mostra 60%+ de lógica duplicada (logging, model routing, phase patterns).
- **Prevention:** CROSS-TOOL CHECK antes de criar nova ferramenta. Extrair shared lib primeiro.

---

## Validation

**Paradoxo Identificado:** Meta-análise (observar o próprio reasoning) vs. Ação (executar tarefa). A heurística que extrai heurísticas cria auto-referência.

**Tensão Sistêmica:**
- Interromper execução para extrair padrões = custo de contexto + latência
- Não extrair = perder insights + duplicação de esforço em futuros projetos

**Resolução:** Análise paralela pós-execução (não-bloqueante). Task post-mortem iniciada APÓS conclusão da tarefa principal, preservando fluxo e capturando insights de forma assíncrona.

**Status:** ✓ Validado | Raciocínio reproduzível; evidência documental presente (sessões 5eb9bf45, 0f1fe148); auto-aplicabilidade confirmada.
