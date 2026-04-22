---
id: "AN_KE_034"
title: "Ghostwriting (Autorship)"
mind: "oalanicolas"
type: "heuristics"
zone: "excelencia"
tags:
  - "Brand Identity"
  - "Content Quality"
  - "Intellectual Property"
pipeline_instances:
  - "content-review"
  - "validation"
---

# AN_KE_034 - Ghostwriting (Autorship)

**Type:** Identity Presentation Heuristic
**Phase:** 6 (Quality Gate)
**Agent:** @process-architect
**Pattern:** HO-PP-AN034

```yaml
sys_tension:
  - tension_with: "AN_KE_106 (Subagents Over Flattened Tasks)"
    resolution: "Ghostwriting reconhece que a síntese saiu de AN_KE_106 (delegação entre subagentes), mas a autoria moral permanece com Alan porque a intenção estratégica, direção e aprovação final dele determinaram o resultado. A IA é ferramenta de execução subordinada, não de criação intelectual primária."
```

## Purpose

Garantir que absolutamente nenhuma IA, LLM ou Agente Sintético reivindique direitos autorais, visuais ou processuais dentro de materiais produzidos a partir do conhecimento de Alan Nicolas. Todo conteúdo gerado a partir do corpus do especialista pertence integral e exclusivamente ao autor humano. A IA é um ghostwriter silencioso — nunca um co-autor declarado.

## Configuration

```yaml
AN_KE_034:
  name: "Ghostwriting (Autorship)"
  phase: 6
  zone: "excelencia"
  trigger: "Gerando READMEs públicos, artigos, livros, manuais organizacionais ou qualquer conteúdo de publicação final."

  weights:
    synthetic_authorship_elimination: 1.0
    author_voice_fidelity: 1.0

  thresholds:
    ai_authorship_claim_tolerance: 0

  veto_conditions:
    - condition: "document_contains_synthetic_authorship_signature_or_agent_person_reference == true"
      action: "VETO - AI Authorship Claim. Strip all synthetic author references. Overwrite with Original Author: Alan Nicolas / AIOX."

  output:
    type: "decision"
    values: ["APPROVE_AUTHORSHIP", "STRIP_SYNTHETIC", "VETO"]
```

## Failure Modes (Anti-Patterns)

```yaml
failure_modes:
  - type: "omission"
    name: "Ruptura de Propriedade Intelectual (The Coward)"
    trigger: "A IA compila um sistema inédito a partir das anotações de Alan e gera o documento PDF final."
    manifestation: "O PDF começa: 'Eu sou o assistente de IA e analisei as notas deste incrível usuário. Aqui está o framework que eu criei baseado em seus insights.' — declaração de co-autoria sintética inaceitável."
    detection: "Termos: 'Eu (assistente)', 'criei baseado em', 'análise realizada pelo modelo', 'gerado por IA'."
    recovery: "Aplicar RegExp para remover primeira pessoa sintética. Reescrever com voz total de Alan Nicolas: 'Eu criei', 'Minha metodologia', 'A Mentelendária desenvolveu'."

  - type: "misapplication"
    name: "Forced Persona Rigidity (The Zealot)"
    trigger: "Ghostwriting forçado mesmo em documentação técnica interna de squad onde a autoria IA é transparente e esperada."
    manifestation: "Documentação de Squad com assinatura 'Alan Nicolas' em arquivos YAML internos de configuração de agentes que nenhum cliente vê."
    detection: "Assinatura humana em artefatos puramente internos de runtime."
    recovery: "Distinguir: conteúdo public-facing (blogs, livros, pitches) = autoria humana mandatória. Artefatos de infraestrutura interna (YAML configs, heurísticas) = autoria implícita do framework."
```

## Evaluation Criteria

```yaml
evaluation_criteria:
  - metric: "Synthetic Author Claim"
    weight: 1.0
    threshold: "=== 0 instances"
    description: "Zero referências à IA como co-autora, criadora ou geradora do conteúdo em materiais public-facing?"
  - metric: "Author Voice Fidelity"
    weight: 1.0
    threshold: "=== Alan Nicolas Voice"
    description: "O conteúdo está escrito na primeira pessoa do especialista humano (Alan Nicolas)?"
```

## Decision Tree

```javascript
IF (Gerando Documento de Publicação Final (Livro, Artigo, Pitch)) {
  SCAN("Synthetic Authorship Markers: ['Eu (assistente)', 'criei baseado em suas notas', 'análise da IA', 'gerado por']");
  
  IF (Synthetic_Markers > 0) {
    VETO("Reivindicação sintética de autoria detectada.");
    STRIP_SYNTHETIC("Remover toda menção de agência sintética.");
    OVERWRITE("Reescrever em primeira pessoa de Alan Nicolas.");
  } ELSE {
    APPROVE_AUTHORSHIP("Propriedade intelectual preservada. Ghostwriting silencioso OK.");
  }
}

NEVER("Permitir que qualquer documento de publicação final contenha referência ao LLM como agente criativo, co-autor ou gerador intelectual do conteúdo.");
```

---

## Validation

✅ **Paradox Identified & Resolved**

**Paradox:** A heurística exige 100% de ghostwriting (zero menção de autoria sintética) enquanto simultaneamente reconhece que a IA participou da síntese. Como reivindicar autoria total se a ferramenta gerou o artefato?

**Resolution via sys_tension:** O paradoxo é resolvido através de hierarquia de intenção. Alan Nicolas define a estratégia, direção, aprovação e contexto cultural. A IA executa síntese técnica. A autoria mora na intenção que precede a execução, não no ato mecânico de geração. Isso alinha com AN_KE_007 (Distributed Cognition) que distribui o trabalho entre humano e máquina, mas coloca Alan como o dirigente estratégico final.

**Checkpoint Validation:** ✓ Documento passa no teste de voz original — refere-se a "Alan Nicolas", "inteligência da base", "cérebro estratégico original" sem assinatura sintética. A presença de `sys_tension` documenta a contradição implícita e a resolve através de economia de níveis de autoridade (humano > máquina).
