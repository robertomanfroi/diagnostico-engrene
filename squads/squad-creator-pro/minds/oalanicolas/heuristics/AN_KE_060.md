# AN_KE_060 - IP Protection by Design
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão sinkra-hub ee0a7008 — squad-creator-pro delivery audit]

## Purpose

Artefatos entregues como produto NÃO devem permitir engenharia reversa da metodologia proprietária. A distinção não é code security — é IP architecture. O squad-creator-pro entrega squads como produto final, mas o *processo* de criação (SINKRA pipeline, DNA Mental™, composição de heurísticas, zone-classification) é IP que gera valor recorrente. Se o cliente reconstrói o método a partir do output, o produto vira commodity. Alan perguntou explicitamente: "isso está garantido?" — exige CERTEZA, não best-effort.

## Configuration

```yaml
AN_KE_060:
  name: "IP Protection by Design"
  zone: "genialidade"
  trigger: "Entregando artefato que foi gerado por, ou contém referências a, metodologia proprietária (SINKRA, DNA Mental, heuristic mining pipeline)."

  rule: |
    SE entregando artefato gerado por metodologia proprietária
    ENTÃO garantir separação arquitetural entre PRODUTO e PROCESSO:
      - Output = produto (squad, skill, clone) → entregável
      - Pipeline = processo (SINKRA phases, heuristic mining, zone classification) → IP protegida
    Engenharia reversa do output NÃO deve revelar o método.
    A proteção é DESIGN, não ofuscação — o artefato é limpo, mas não ensina a metodologia.

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) vs Complexidade de Parsing Local"
    resolution: "Transparência INTERNA (squad-creator work) vs EXTERNA (client delivery). Squad-creator-pro documenta o método internamente (AN_KE_073 governa paralelização interna); delivery packages sanitizam referências SINKRA para clientes (AN_KE_060 governa outputs/). Mesma arquitetura, diferentes públicos."

  veto_condition:
    trigger: "Artefato entregável contém: nomes de phases SINKRA internas, referências a zone-classification-criteria.yaml, heuristic-mining process, session IDs, ou termos 'DNA Mental' / 'Pareto ao Cubo'."
    action: "VETO — 'isso está garantido?' Sanitize antes de entregar. O cliente recebe o squad, não o pipeline."

  evidence:
    - "[SOURCE: sessão ee0a7008, sinkra-hub] 'OK, eu nao quero que ele tenha nada escrito sobre a metodologia sinkra ou que ela possa ser revertida ou compreeinda fazendo engenharia reveresa do squad-creator, isso está garantido?'"
    - "[CONTEXT] Sessão ee0a7008 é de migração aiox-stage → sinkra-hub. Alan auditou cada arquivo migrado verificando que a compatibilidade com SINKRA não expunha o framework."
```

## Decision Tree

```javascript
IF (delivering_artifact_externally)
  STEP_1: CLASSIFY artifact layers
    PRODUCT: squad files, agents, tasks, skills → DELIVERABLE
    PROCESS: composition-rules.yaml, zone-classification, mining scripts → INTERNAL ONLY
    EVIDENCE: session IDs, history extracts, decision-cards.yaml → NEVER DELIVER
  STEP_2: SCAN product layer for process leaks
    GREP: "SINKRA", "DNA Mental", "heuristic", "zone_0.8", "AN_KE_", "Pareto ao Cubo"
    GREP: session IDs (8-char hex patterns referencing internal sessions)
    GREP: internal pipeline names (Phase 1-7, sinkra-map, evidence-grading)
    IF (any_hit) → SANITIZE: abstract or remove
  STEP_3: REVERSE-ENGINEER test
    READ output as if you're a competitor. Can you reconstruct:
      - How zones are classified? → MUST be NO
      - How heuristics are mined? → MUST be NO
      - What SINKRA is? → MUST be NO
  STEP_4: VALIDATE delivery package
    Product value → INTACT (squad works as expected)
    Process knowledge → INVISIBLE (method is opaque)
```

## Failure Modes

### O Squad que Ensina o Método
- **Trigger:** Entregar squad com composition-rules.yaml, zone-classification-criteria.yaml, ou heuristic-mining references nos artefatos.
- **Manifestation:** Competidor lê o squad, identifica os 7 phases do SINKRA, reconstrói o pipeline, cria squads próprios sem pagar.
- **Detection:** `grep -ri "sinkra\|DNA Mental\|zone_0.8\|heuristic-mining" squads/*/` no delivery package.
- **Prevention:** Build pipeline separa delivery/ de process/. Entrega vem de delivery/ que já é sanitized. Sessão ee0a7008 validou isso na migração.

## Validation

**Paradoxo Identificado:** O squad-creator-pro deve ser transparente internamente (documentar seu próprio método via heurísticas) mas opaco externamente (não expor SINKRA aos clientes). Este é o núcleo do conflito entre AN_KE_060 (IP Protection) e AN_KE_058 (Transparency).

**Resolução Implementada:** Separação de públicos + sanitização de entrega.
- **Workspace (squad-creator-pro work):** Documentação completa do método, incluindo phase names, zone-classification, heuristic mining.
- **Outputs (client delivery):** Artefatos com referências SINKRA removidas. Squad funciona identicamente, mas método é opaco.
- **Teste de Validação:** `grep -ri "sinkra\|DNA Mental\|zone_0.8\|heuristic-mining\|phase_\[1-7\]" outputs/` deve retornar 0 hits.

**Status:** ✓ Coerência sistêmica restaurada. AN_KE_060 governa camada de delivery, AN_KE_058 governa camada de trabalho interno.
