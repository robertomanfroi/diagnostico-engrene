# AN_KE_054 - Estrutura Orgânica de Diretórios

**Type:** Core Architecture Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** PKM / Folder Hierarchy
**Source:** [SOURCE: Line 1478 - Refinando Obsidian para a Mentelendaria]

## Purpose

Prevenir o engessamento de sistemas de gestão de conhecimento (PKMs, Obsidian, MOCs) e workspaces de equipe. Garantir que a estrutura de diretórios cresça organicamente via taxonomia de categorias, em vez de ser forçada por prefixos numéricos estáticos que quebram com expansões futuras.

## Configuration

```yaml
AN_KE_054:
  name: "Estrutura Orgânica de Diretórios"
  zone: "excelencia"
  trigger: "Criando pastas, agrupando arquivos ou desenhando PKMs."

  rule: |
    SE você precisar organizar arquivos em diretórios
    ENTÃO NUNCA use "01_Marketing", "02_Vendas"
    SOMENTE use numeração se a natureza do dado exigir estrita linearidade invariável (ex: Módulos de um Curso).

  veto_condition:
    trigger: "Tentativa de reordenar pastas usando números por conveniência visual."
    action: "VETO — Numeração gera dívida técnica de rearquivamento."

  sys_tension:
    tension_with: "AN_KE_012 (Batch Mecânico Primeiro, Hardening Depois) vs Crescimento Orgânico"
    resolution: "Usar numeração APENAS para sequências que 1) jamais mudarão de ordem (Course Modules, Wave Phases) e 2) nunca precisarão de inserção no meio. Para tudo mais (Departments, Categories, Topics), usar MOCs e taxonomias semânticas, permitindo crescimento orgânico sem rearquivamento."

  evidence:
    - "[EXACT WORDS]: não devemos ter pastas numeradas, ou evitar elas ao máximo a nao ser que seja algo como módulo de um curso ou algo que precise muito de numeração"
```

## Decision Tree

```javascript
IF (creating_new_folder OR restructuring_system)
  IF (entity_requires_strict_chronological_sequence == TRUE)
    // Example: Course Modules (01_Introducao, 02_Mecanica)
    // Example: Wave Phases (Phase_0, Phase_1)
    THEN ALLOW_NUMERICAL_PREFIX
  ELSE
    // Example: Departments, Wiki Categories, Brain Dump
    THEN BLOCK_NUMERICAL_PREFIX
    THEN USE_ORGANIC_NOMENCLATURE (e.g. "Marketing", "Engenharia")
      IF (sorting_needed)
        THEN rely on internal Obsidian MOCs (Map of Content) or yaml indexes
      ELSE
        THEN rely on alphabetical sorting
```

## Failure Modes

### Pseudo-Organization Break
- **Trigger:** Adicionar uma nova categoria primária que deve vir antes da "01".
- **Manifestation:** O usuário cria "00_Admin" ou renomeia de 01 a 15, quebrando links quebrados (Broken Links) em todo o Obsidian/Wiki.
- **Detection:** Presença de pastas como `02_A_Subcategoria` ou constantes renames em massa.
- **Recovery:** Rodar script de sanitização para remover todos os regex `^\d+[-_]`, substituindo a ordem via arquivo de `index.md` (MOC).
- **Prevention:** Veto na criação inicial orientando o uso de MOCs para navegação.

## Integration with Workflow

```yaml
checkpoint:
  id: "directory-creation-gate"
  heuristic: AN_KE_054
  phase: "PKM_Architecture"

  criteria:
    - metric: "has_numeric_prefix"
      threshold: FALSE
      operator: "=="

  veto_conditions:
    - condition: "Regex match: ^[0-9]{2,3}[-_ ]"
      action: "HALT - Exibir erro: Utilize links e taxonomias, não prefixos de OS."

  validation_questions:
    - "Esta pasta perderia o sentido se fosse listada em ordem alfabética?"
    - "A ordem destas pastas é imutável pelas próximas 5 décadas?"

  pass_action: "Diretório criado e adicionado ao MOC raiz."
  fail_action: "Loop back sugerindo nome limpo sem numerais."
```

## Validation

**✓ Paradoxo identificado:** A heurística permite numeração em casos específicos (sequências invariáveis) enquanto a regra geral veta numeração. Essa tensão é intencional e necessária.

**✓ Resolução implementada:** O campo `sys_tension` documenta explicitamente quando usar cada padrão, eliminando ambiguidade.

**✓ Aplicabilidade:** AN_KE_054 é válida para PKMs (Obsidian), wikis de equipe, e workspaces colaborativos onde crescimento orgânico é expectativa.
