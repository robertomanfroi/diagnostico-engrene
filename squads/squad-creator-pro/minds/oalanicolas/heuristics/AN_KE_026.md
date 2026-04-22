# AN_KE_026 - Squad Agnosticism

**Type:** Architecture Standard Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Encapsulamento de Agent / Squad
**Source:** [SOURCE: Extraído de decisões corporativas para isolar a regra estratégica de negócios da operação pura do squad.]

## Purpose

Proteger a arquitetura agnóstica dos Squads (que são produtos ou entidades que resolvem problemas genéricos) impedindo que lógicas específicas de projetos (ex: o cliente "MMOS" ou "Academy") sejam inseridas cruamente em código core.

## Configuration

```yaml
AN_KE_026:
  name: "Squad Agnosticism"
  zone: "excelencia"
  trigger: "Criando ou editando as tarefas e workflows de um Squad."

  rule: |
    SE você criar código, workflows ou prompts para um Squad
    ENTÃO não coloque variáveis estáticas exclusivas da corporação do cliente. Busque isso na Workspace/Truth.

  veto_condition:
    trigger: "Encontrar nomes como 'Academy', caminhos literais do mac locais em scripts globais ou emails estáticos."
    action: "VETO — Externalizar para variáveis de configuração ou workspace."

  evidence:
    - "[EXACT WORDS]: SE construir regras para o squad, elas devem consultar o workspace para os metadados core."

  sys_tension:
    tension_with: "AN_KE_007 (REUSE > CREATE) vs Squad Agnosticism"
    description: "Squads must remain agnostic (no hardcoded business names) yet simultaneously must resolve business-specific context at runtime (brand, domain, locale). This creates a circular dependency: agnosticism requires abstraction, but abstraction must bind to specific context layers."
    resolution: "Separate concerns via Configuration Injection Pattern — Squad code stays pure (agnostic), configuration resolution happens at squad instantiation time via Workspace + Environment bindings. The squad itself never hardcodes; the system binds context to squads via dependency injection."
```

## Decision Tree

```javascript
IF (writing_squad_code OR scripting_workflow)
  IF (variable_refers_to_business_identity OR domain OR local_path)
    THEN BLOCK_HARDCODING
    THEN RETRIEVE_FROM (Workspace / Knowledge Base / env)
      IF (knowledge base lacks this info)
        THEN trigger prompt request to user "Por favor forneça no workspace configurador da marca XYZ"
      ELSE
        THEN use reference securely
  ELSE
    THEN ALLOW (only if universal framework logic)
```

## Failure Modes

### Hardcoded Legacy Break
- **Trigger:** Usar o squad `Content_Creator` para outro cliente.
- **Manifestation:** O squad gera resultados fantásticos, mas assina tudo como "AIOX Academy", enviando os emails da empresa antiga.
- **Detection:** Reclamação dos consumos em downstream reportando chaves erradas.
- **Recovery:** Buscar o grep de todos os "AIOX", "Alan", e transformar em `{{brand_name}}` templates ligados à camada Workspace.
- **Prevention:** Veto na implementação se o código referenciar string de empresa literais.

## Integration with Workflow

```yaml
checkpoint:
  id: "agnostic-squad-validator"
  heuristic: AN_KE_026
  phase: "Squad_Architecture"

  criteria:
    - metric: "has_business_specific_strings_in_core"
      threshold: FALSE
      operator: "=="
```

## Validation

✅ **Paradox identified & resolved:**
- **Paradox:** Agnosticism vs. contextual binding (circular dependency)
- **Resolution mechanism:** Configuration Injection Pattern decouples squad code from business context
- **Test case:** Squad code scans clean (no "Academy", "AIOX", "Alan") → Context resolved at instantiation → Output correctly branded
- **Implementation:** `@squad-creator-pro` enforces via linter rule `no-hardcoded-business-strings` in squad config validation
