# AN_KE_085 - Greenfield Over Spaghetti Refactor
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão mmos (clonagem de perfil), aiox-stage]

## Purpose

Quando nos deparamos com dados espaguetizados (múltiplas anotações velhas de prompts mescladas, templates falhos iterados no limite da sanidade ou scraps sobrecarregados), a mente impulsiva do desenvolvedor quer consertar o emaranhado tentando refatorar linha por linha. Alan entende a matemática do caos: "comece um greenfield do zero" jogando as bagunças para a pasta `sources/`. O tempo economizado descartando falsas fundações compensa o "orgulho do conserto". Se a entropia acumulou num volume doente, faça "tabula rasa" puxando raw assets isolados.

## Configuration

```yaml
AN_KE_085:
  name: "Greenfield Over Spaghetti Refactor"
  zone: "genialidade"
  trigger: "Processamento de fontes desorganizadas, documentação lixo no workspace herdado, refatoração impossível contínua."

  sys_tension:
    tension_with: "AN_KE_045 (Subtraction First Strategy) vs. Greenfield Reconstruction"
    resolution: "Subtraction-first privilegia eliminar complexity iterativamente. Greenfield privilegia reconstruir desde L0 quando entropia crítica supera 70%. Critério: Se refatoração contínua gera 2+ iterações de correção no mesmo artifact, greenfield é mais eficiente que subtrair incrementalmente."

  rule: |
    SE o domínio atual do projeto estiver poluído (falsas docs, código Frankenstein, assets contraditórios)
    ENTÃO NUNCA tente consertar a teia de aranha (refatorar em cima do escombro).
    Mova todo o lixo valioso para `sources/` estritas (como read-only raw material).
    Crie o trabalho de from scratch (Greenfield).
    A sanidade sistêmica cresce partindo do L0 em base limpa.

  veto_condition:
    trigger: "O documento do clone do Thiago Finch está terrível. O agente foca em rodar 8 passes de edição no mesmo arquivo quebrado para 'ajeitar' parágrafos."
    action: "VETO — 'começar um greenfield do zero: organize em sources'."

  evidence:
    - "[SOURCE: sessão clone_profile] 'O processo está com vários erros: Thiago Finch é uma figura pública e eu tenho documentos já do clone dele na pasta, entao deveria organizar os documentos em sources e começar um greenfield do zero'"
```

## Decision Tree

```javascript
IF (evaluating_messy_legacy_artifacts_or_docs)
  STEP_1: ESTIMATE entropy (Is this file completely distorted by prior bad iterations?)
  STEP_2: MOVE artifacts
    IF (entropy is critical) 
      -> `mkdir -p _sources_raw/`
      -> Mover lixo utilizável pra pasta sources original.
  STEP_3: START clear, standardized output schema in target folder.
  STEP_4: PULL logic cleanly from raw sources to greenfield skeleton.
```

## Failure Modes

### Sunk Cost Arquitetônico
- **Trigger:** Insistência em manter um script gigantesco legado para não perder o que parece prático.
- **Manifestation:** Em 1 mês o modelo conserta o Legacy que continua estourando em exceções bizarras (Doc Rot sistêmico).
- **Prevention:** Botão vermelho imediato de Wipe + Source-Isolate.

## Validation

**Paradoxo Identificado:** Greenfield (create from zero) tensiona contra Incremental Optimization (refactor continuously). A heurística resolve o paradoxo pela entropia: quando a estrutura herdada contém >70% de artefatos incoerentes/contraditórios, o custo marginal da refatoração supera o custo de começar do zero.

**Aplicabilidade:** Critério objetivamente verificável — contar iterações de correção no mesmo artefato. Se >2 iterações corretor-conserto em 1 período, greenfield é optimal.

**Contra-indicadores:** Quando a base contém núcleos estruturados e o lixo é periférico (<30%), incremental é mais eficiente (AN_KE_001 prevalece).
