# AN_KE_081 - Agnostic Taxonomy & English Combinatorics
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 5eac34ac, aiox-stage — "ingles e combinatorias"]

## Purpose

Sistemas caem sob seu próprio peso quando as taxonomias mudam a cada semana ou ficam engessadas em jargões fechados. As estruturas categóricas (como chaves de tags no db, identificadores de file paths, tipos num enum Prisma) precisam adotar padronização. Tudo o que é chave de máquina precisa ser gerado num modelo agnóstico combinatório (ex: inglês, descritivas e passíveis de se cruzarem — `topic:marketing`, `format:video`) em detrimento de uma tag monolítica estática `marketing-em-video-portugues`, garantindo extensibilidade a médio prazo.

## Configuration

```yaml
AN_KE_081:
  name: "Agnostic Taxonomy & Combinatorics"
  zone: "excelencia"
  trigger: "Modelagem lógica de tags em banco de dados, slugs combinatoriais ou chaves de metadados."

  rule: |
    SE definindo tags, nomes de esquemas ou categorias para coleções
    ENTÃO USE idioma de backend universal (Inglês) para as chaves nativas.
    GARANTA que o modelo seja combinatório e granular, não uma abstração hardcoded gigante.
    Categorias devem ser combinadas (`format` + `niche` + `geo`) e NUNCA string longas isoladas.

  veto_condition:
    trigger: "Criar uma chave numérico-localizada tipo `Tag: VideoYouTubeComAlan`"
    action: "VETO — 'taxonomias precisam ser em ingles e combinatórias, nunca isoladas'."

  evidence:
    - "[SOURCE: sessão 5eac34ac, aiox-stage] 'taxonomias precisam ser em ingles e combinatórias, nunca isoladas'"
    - "[PATTERN] Sistema base do MMOS adotou `skill_level`, `format_type` no lugar de categorias engessadas exclusivas."

  sys_tension:
    tension_with: "AN_KE_027 (Zero Emojis & Design Consistente) — exigência de design visual/semântico consistente vs. imposição de idioma inglês exclusivo para chaves de máquina"
    resolution: "Usar inglês APENAS para chaves de máquina (enums, DB slugs). Conteúdo e rótulos de UX podem ser em PT-BR ou localizados. Separação clara: machine layer (English) + presentation layer (multilíngue)."
```

## Decision Tree

```javascript
IF (defining_taxonomy_enums_tags_or_keys)
  STEP_1: FORCE english keywords exclusively (for DB enums and core machine slugs).
  STEP_2: CHECK taxonomy scope:
    IF (it conveys multiple dimensions like "Marketing Video") -> SPLIT THEM.
  STEP_3: COMBINATORICS
    Create `{ domain: 'marketing', format: 'video' }` instead of `{ category: 'marketing-video' }`.
```

## Failure Modes

### Monólito de Categorias Infinitas
- **Trigger:** "Novos cursos entraram e as categorias são muito específicas".
- **Manifestation:** Em 6 meses, a tabela de categorias passa a ter 1500 linhas que não possuem sentido agrupado para os filtros de dashboard.
- **Prevention:** Estrutura taxonômica compositável (Combinatorial Data).

---

## Validation

✅ **Paradoxo Identificado:** Inglês universal para máquina vs. conteúdo multilíngue de UX.

✅ **Resolução:** Camada de máquina (enums, slugs, DB keys) em inglês; camada de apresentação (labels, strings de UX) em PT-BR ou localizadas conforme necessário.

✅ **Evidência:** Pattern validado no MMOS (skill_level, format_type) mantém granularidade e extensibilidade sem engessamento.

✅ **Aplicabilidade:** Aplicar quando modelando taxonomias, definindo esquemas, ou criando enums de categorizações.
