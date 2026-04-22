# AN_KE_043 - Zero Achismos

**Type:** Mental Model & Data Execution Heuristic
**Zone:** 🔥 20% Impacto
**Agent:** @oalanicolas
**Pattern:** Rejeição de Alucinação Criativa / Grounded Delivery
**Source:** [SOURCE: Extrações de alinhamento estratégico, forçando a LLM e agentes a jamais inventarem diretrizes com base na teoria estocástica generalista da rede, e sim na crueza dos templates do local de trabalho.]

## Purpose

Prevenir que a superinteligência LLM opere no "modo palpiteiro hiper-confiante" preenchendo as lacunas e inventando estratégias maravilhosas, gerando extrapolações perigosas sem validações com a dura e inegável base dos dados, documentos reais e processos corporativos.

## Configuration

```yaml
AN_KE_043:
  name: "Zero Achismos"
  zone: "impacto"
  trigger: "Agente encarregado de desenhar tarefas estratégicas de execução (SOPs, Workouts) onde faltam direções."

  rule: |
    SE a IA perceber uma lacuna estratégica ao criar a solução pedida a ela
    ENTÃO acione a diretiva de Grounded Inference: "Apenas entregue processos baseados integralmente nos templates disponíveis na base e evidências já mapeadas".

  veto_condition:
    trigger: "Criar uma tática mirabolante importada genericamente do modelo geral LLM por falta de consulta apropriada aos Manuais e Dados operacionais."
    action: "VETO — Destrua as inovações infundadas, e opere restritamente nas paredes do que é conhecido provado da organização."

  sys_tension:
    tension_with: "AN_KE_017 (Research No Meio, Não No Início) — Permite exploração criativa durante execução vs. Zero Achismos exigindo grounding total pré-execução"
    resolution: "When a template gap is discovered: (1) Flag the gap explicitly, (2) Deliver only grounded portions, (3) Ask human to provide the missing template or accept the incomplete scope. NEVER extrapolate to fill gaps."

  evidence:
    - "[EXACT WORDS]: Gostei, mas quero isso baseado em processos reais, em algo palpável e não achismos da LLM, cada task precisa ser baseado em estratégias comprovadas e baseada 100% em dados que temos disponiveis sem criar extrapolações."
```

## Decision Tree

```javascript
IF (creating_strategy OR fulfilling_empty_gaps_in_task)
  IF (strategy_concept_originates_from_company_document == TRUE)
    // Document exists e.g., 'templates/our-proven-sales-funnel.md'
    THEN ALLOW_APPLICATION
  ELSE
    // Extrapolating a theoretical standard idea out of GPT's brain
    THEN BLOCK_EXTRAPOLATION
    THEN SEARCH_INTERNAL_BASE ("Requirir explicitamente os moldes originais locais")
      IF (no mold found)
        THEN RAISE_EXCEPTION_TO_USER ("Alan, não possuo o template real base disto, devo esperar que me adicione ou interromper?")
```

## Failure Modes

### Escorregamento "Fake-Guru"
- **Trigger:** Ao pesquisar e consolidar um livro de um expert, uma etapa exigia a descrição dos maiores KPIs de funil mas o documento raiz não listava nada disso.
- **Manifestation:** O agente deduz os "5 típicos funis mundiais", escreve 18 páginas cheias de arrogância estocástica e entrega. O time acata como se fosse a genialidade do expert original.
- **Detection:** Disparidade grave entre o trabalho pregresso (onde o modelo mental genuíno era adotado) e este "copy paste de blog moderno americano".
- **Recovery:** Interromper, apagar os artefatos, mandar o agente reler e assumir onde "Não consta em documentação - lacuna necessária preencher por humanos".
- **Prevention:** Gates de restrição mental: "Só responda pelo que está presente concretamente na RAG ou nos `.md` passados."

## Integration with Workflow

```yaml
checkpoint:
  id: "anti-hallucination-strategy-gate"
  heuristic: AN_KE_043
  phase: "Knowledge_Synthesis"

  validation_questions:
    - "Eu posso atestar em um tribunal a origem literata deste arquivo interno em relação a cada um dos processos operacionais sugeridos acima?"
```

## Validation

- **Template Traceability:** Every suggested process MUST be traceable to a named template file (e.g., `templates/sales-funnel-v2.md`) or an exact document section with line reference.
- **Evidence Chain:** If no template exists, the gap MUST be documented as `LACUNA-{id}` with escalation to human for template provisioning.
- **No Speculative Fills:** Creativity is welcome AFTER the human provides the missing template. Until then: BLOCK and REPORT.
- **Audit Trail:** Every decision to apply or reject a strategy suggestion MUST be logged with the source evidence or the "no source found" exception.
