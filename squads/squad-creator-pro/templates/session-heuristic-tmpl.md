# AN_KE_{NNN} - {Nome da Heurística}

**Type:** {Decision Heuristic | Veto Heuristic | Architecture Heuristic | Observability Heuristic | State Management Heuristic}
**Zone:** {🔥 0,8% Genialidade | 💎 4% Excelência | 🚀 20% Impacto}
**Agent:** @oalanicolas
**Pattern:** {Nome do Pattern}
**Source:** [SOURCE: {descrição rastreável — epic/story ID, data, incidente específico}]
**Tags:** [{Agnostic}, {Scale}, {Automation}, {SINKRA}, {Framework}]

## Purpose

{Uma sentença brutal explicando o ganho existencial desta heurística. Clareza radical: o que ela previne que destruiria o sistema sistemicamente?}

## Configuration (True L3-State)

```yaml
AN_KE_{NNN}:
  name: "{Nome}"
  zone: "{genialidade|excelencia|impacto}"
  trigger: "{Quando esta heurística se aplica de forma inegociável}"
  
  sys_tension:
    tension_with: "{ID de outra heurística ou Productive Paradox que colide naturalmente. Ex: Liberdade vs Estrutura Rígida}"
    resolution: "{Como a Mente Zero de Alan arbitra esse conflito e decide qual pesa mais nesse contexto}"

  rule: |
    SE {condição/contexto ativador observável}
    ENTÃO {ação imperativa}
    NUNCA {a complacência padrão que a máquina ou o dev average costuma adotar}

  failure_modes:
    # Omissão é Inércia. Misapplication é Fanatismo.
    omission: "{O que acontece quando atalhos/preguiça impedem de rodar isso? Qual é a pressão ambiental? (E.g. prazo curto)}"
    misapplication: "{O que acontece quando você é bitolado em seguir a heurística às cegas sem context-awareness?}"

  evidence_threshold: "{[SYNTHESIZED] (Pattern recorrente extraído) ou [EMPIRICAL] (Causa raiz no incidente X/Y)}"
  evidence:
    - "{Evidência 1 com dados absolutos [SOURCE:]}"
```

## Decision Tree (Strict Format)

Árvore lógica estrita. A inteligência artificial precisa entender limites matemáticos e lógicos sem nuances escorregadias.

```text
STEP_1: IF ({condição raiz})
          THEN {ação core}
          AND VETO ({sinal/flag/ausência crítica que trava tudo})
STEP_2: IF ({edge case principal})
          THEN {sub-ação mitigante}
NEVER:
  - {anti-pattern corporativo 1 mascarado de 'boas práticas'}
  - {submissão à preguiça algorítmica 2 (Goodwill LLM)}
```

## Confidence Requirements & Reversibility

- **High-Commitment (One-Way Door):** {O que exige >90% de certeza antes de rodar esta heurística? Ex: Decisão irreversível de arquitetura}
- **Tactical (Two-Way Door):** {Onde podemos aplicar isso com 60% de confiança para ganhar velocidade?}

## Validation & Cross-Mind Divergence

### Self-Validation Ask
1. "{A pergunta polarizadora/Socrática que o agente deve se fazer antes de entregar a tarefa. Se a resposta for vaga, a refatoração volta pro início.}"

### Divergence Analysis (Baseline IA vs Mente Zero)
*Onde essa heurística subverte o compliance diplomático ou a alucinação otimista padrão de GPT/Claude originais?*
- **Base LLM Tendency:** {O LLM tende a adivinhar e preencher logs sem autorização, fingindo proatividade.}
- **Mind Zero Override:** {Alan exige Veto e travamento total [BLOCK] até o input real.}

## Behavioral Evidence (Real-World Application)

*Fundamentação empírica detalhada do expert (Inspirado no padrão PV_).*

**Example:** "{Título do Case/Situação Real}"
- **Context:** "{Qual era o cenário/problema de mercado?}"
- **Information Available:** "{Quais eram os sinais fracos na época?}"
- **Heuristic Application:** "{Como o expert aplicou essa regra exata na contramão do senso comum?}"
- **Outcome:** "{Resultado mensurável e inegável}"

---

## 3-Layer Format

Este `.md` é a **L3 (Full Documentation)** — a estrutura de auditabilidade pesada que retém a profundidade existencial da regra.

Após criar este arquivo, insira a tradução L2/Runtime em `squads/squad-creator-pro/minds/oalanicolas/heuristics/decision-cards.yaml`:

```yaml
  - id: AN_KE_{NNN}
    name: "{Nome}"
    rule: "SE {condição} → ENTÃO {ação}"
    zone: "{genialidade | excelencia | impacto}"
    trigger: "{quando se aplica}"
    evidence_threshold: "[SYNTHESIZED] ou [EMPIRICAL]"
    # Sub-ramificações para as instâncias do L3 acima
    pipeline_instances:
      - rule: "{Sub-regra vital do STEP_1}"
      - rule: "NEVER: {Sub-regra de VETO}"
```
