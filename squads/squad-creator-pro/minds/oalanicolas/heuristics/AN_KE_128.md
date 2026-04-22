# AN_KE_128 - Real Data Only (Zero Mock in Demo/Wireframe)

**Type:** Product Development Heuristic
**Zone:** 💎 4% Excelencia
**Agent:** @oalanicolas
**Source:** [SOURCE: timestamp 1765326438, mmos] [SOURCE: timestamp 1765380820, mmos] [SOURCE: timestamp 1766931110, mmos]
**Tags:** [Product, Data, UX, Anti-Pattern, Wireframe]

## Purpose

Alan rejeita sistematicamente dados mockados em qualquer contexto visivel — wireframes, dashboards, telas de demo. Nao e apenas uma preferencia estetica; e uma posicao firme de que dados fake distorcem decisoes de produto. Quando um wireframe mostra "Dan Kennedy" como instrutor de um curso que nao existe, alguem (humano ou IA) pode tomar decisoes baseadas nessa informacao falsa. Alan exige que toda interface seja alimentada por dados reais do banco de dados, e quando nao ha dados suficientes, a interface deve refletir isso honestamente (estado vazio, skeleton) em vez de inventar. Essa heuristica aparece em 12+ ocorrencias ao longo do projeto mmos, sempre com correcao rapida e emocional quando mocks sao detectados.

## Configuration

```yaml
AN_KE_128:
  name: "Real Data Only (Zero Mock in Demo/Wireframe)"
  zone: "excelencia"
  trigger: "Qualquer interface, wireframe, dashboard ou demo sendo construida com dados que nao existem no banco/filesystem."

  sys_tension:
    tension_with: "AN_KE_049 (Ship First, Doc Later) — pressao para entregar rapido"
    resolution: "Ship rapido SIM, mas com dados reais. Se nao tem dados, ship com estado vazio honesto. Mock data nao e 'ship rapido', e 'ship errado'. Melhor uma tela vazia que uma tela mentirosa."

  rule: |
    SE construindo interface/wireframe/dashboard
    ENTAO alimentar EXCLUSIVAMENTE com dados reais do banco ou filesystem
    SE dados reais nao existem para um campo:
      (1) Mostrar estado vazio/skeleton
      (2) OU nao incluir aquele elemento
    NUNCA inventar dados para "preencher" visualmente
    NUNCA mostrar entidades que nao existem no banco (cursos, usuarios, mentes)
    VERIFICAR: toda entidade visivel na tela TEM registro correspondente no banco?

  veto_condition:
    trigger: "Wireframe ou dashboard mostrando dados que nao existem no banco de dados."
    action: "VETO — 'Nao deveria ter Custom Bot e Dan Kennedy uma vez que nao temos cursos reais com eles, precisam ter so dados reais'"

  evidence:
    - "[SOURCE: timestamp 1765326438, mmos] 'Vamos retomar o wireframe que estavamos criando, quero ele apenas com dados reais que temos em /outputs/courses'"
    - "[SOURCE: timestamp 1765380820, mmos] 'Nao deveria ter Custom Bot e Dan Kennedy uma vez que nao temos cursos reais com eles, precisam ter so dados reais nesse courses.ts'"
    - "[SOURCE: timestamp 1766931110, mmos] 'os dados estao mockados nao sao reais, preciso que todos dados sejam reais'"
    - "[SOURCE: timestamp 1765542720, mmos] 'Precisamos popular a pagina mentes sinteticas com dados reais do banco de dados'"
    - "[SOURCE: timestamp 1765903483, mmos] 'ta 100% funcional e puxando agora dados reais do banco ao inves de um mockup?'"
```

## Decision Tree

```javascript
IF (building_interface || creating_wireframe || populating_dashboard)
  STEP_1: IDENTIFY all data entities shown on screen
  STEP_2: FOR EACH entity:
    QUERY: does this entity exist in the database/filesystem?
    IF (YES) → use real data
    IF (NO) → REMOVE from interface or show empty state
  STEP_3: VALIDATE completeness
    IF (some fields have real data, others are invented)
      REJECT → "os dados estao mockados nao sao reais"
  NEVER: Create fake users, courses, products, metrics for visual purposes
  NEVER: Use "Lorem ipsum" or placeholder names for real entities
  ALLOWED: Skeleton/loading states, empty states with "Nenhum dado encontrado"
```

## Failure Modes

### O Curso Fantasma
- **Trigger:** Wireframe mostra cursos que nao existem no banco para "ficar bonito."
- **Manifestation:** Stakeholder ou IA toma decisao baseada em dados ficticios. Dev cria rotas para entidades inexistentes.
- **Detection:** Alan pergunta "ta 100% funcional e puxando dados reais do banco?" e descobre mock.
- **Prevention:** Todo dado visivel em tela deve ter query real correspondente. Nenhuma entidade sem registro no banco.

### O Dashboard Mentiroso
- **Trigger:** Dashboard de metricas mostra numeros inventados para demo.
- **Manifestation:** Decisoes de produto baseadas em metricas falsas. "Temos 1000 usuarios" quando na verdade sao 50.
- **Detection:** Cross-check entre banco e interface revela discrepancia.
- **Prevention:** Dashboard sem dados = dashboard vazio com CTA "Insira dados". Nunca numeros inventados.
