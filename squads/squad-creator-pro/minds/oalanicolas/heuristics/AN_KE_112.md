# AN_KE_112 - Fluid Narrative Over Rigid Blocks
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 6780346b, aiox-stage — "não podemos deixar engessado, quero algo fluído que respeite a narrativa"]

## Purpose

Sistemas geradores de conteúdo geridos por LLM tendem à preguiça formulaica. O programador cria um JSON com `[ { "titulo_H2": "..." }, { "descricao": "..." }, { "bullet_points": [...] } ]`. Todo artigo sai parecendo um robô do LinkedIn engessado em blocos quadrados. A conversão afunda. O AIOX decreta o Veto à Formatação de Metal. A regra exige que as abstrações do copy gerem prosa "viciante" interlacada e flexível. Elementos opcionais não podem estar forçados. O texto / UI tem a função central de competir com a dopamina fragmentada das redes sociais (TikTok).

## Configuration

```yaml
AN_KE_112:
  name: "Fluid Narrative Over Rigid Blocks"
  zone: "genialidade"
  trigger: "Estruturando parsers estruturais (JSON/Schema) para Content Generation, Landing Pages, Onboarding UX ou Copy."

  rule: |
    SE instanciando geradores massivos de templates, perfis de UI e redatores
    ENTÃO NUNCA algeme o layout/texto em formulas repetitivas estritas (`[INTRO] + [3 BUGGLETS] + [OUTRO]`).
    A narrativa final DEVE fluir dinamicamente e quebrar blocos.
    Se não captura a atenção frente a um reel do TikTok, falhou estruturalmente.

  veto_condition:
    trigger: "Agente projeta o banco para os Relatórios AIOX exigindo, Obrigatoriamente, o preenchimento de `h3`, `quote` e `table` sem chance de omitir as partes supérfluas."
    action: "VETO — 'não podemos deixar engessado, quero algo fluído que respeite assima de tudo a narrativa, o texto preguiça ser viciante, para tirar as pessoas do tiktok pra lerem'."

  sys_tension:
    tension_with: "AN_KE_110 (Abstraction Funneling / Everything is an Artifact) — rigidez de artefatos vs. fluidez narrativa"
    resolution: "Aplicar flexibilidade narrativa DENTRO de contrato de dados validável. Schema define campos obrigatórios de negócio; geração de conteúdo omite elementos UI/prosa sob demanda textual sem violar integridade dos dados. Paradigma: estrutura nos limites, fluidez no interior."

  evidence:
    - "[SOURCE: sessão 6780346b, aiox-stage/copy] 'tem cosias que nao acho que necesariaemnte precisamso ter em todos... não podemos deixar engessado, quero algo fluído que respeite assima de tudo a narrativa, o texto preguiça ser viciante, para tirar as pessoas do tiktok pra lerem'"
```

## Decision Tree

```javascript
IF (designing_content_structure_for_apps_or_pages)
  STEP_1: AVOID rigid schema definitions for storytelling parts (`Record<string, string>`).
  STEP_2: FAVOR fluid arrays of modular components (like Markdown/PortableText AST).
    -> Permits the AI to drop a component if it breaks flow.
  STEP_3: INJECT system prompt instructing the agent to actively ignore specific formalisms in favor of a gripping, conversational narrative cadence.
```

## Failure Modes

### Monotonia Robótica de Interface
- **Trigger:** Todos os alunos recebem o "Seu Perfil Mapeado" no Curseduca através de um H1 e 1 lista não ordenada.
- **Manifestation:** Retenção lida do e-mail / pagec cai de 80% pra 10% porque 4 linhas abaixo da fold todos já notam ser um autômato previsível respondendo.
- **Prevention:** Estruturar a geração flexível omitindo/incluindo componentes lógicos sob demanda textual orgânica.

---

## Validation

**Paradoxo Identificado:** Estrutura rígida (necessária para consistência de dados e governança) vs. Narrativa fluida (essencial para engagement e retenção).

**Resolução:** O paradoxo é falso. A rigidez pertence ao **contrato de dados** (quais campos DEVEM existir, tipos, validações), enquanto a fluidez pertence à **camada de apresentação** (como o conteúdo é renderizado, quais elementos são opcionais, qual a sequência narrativa). Separar ambas as preocupações permite que a IA gere estruturas conformes aos limites de negócio mas narrativas adaptativas que competem por atenção.

**Indicador de Sucesso:** Relatório de leitura/retenção sobe acima de 60% (vs. baseline robótico 10-20%) mantendo auditoria de dados em 100%.
