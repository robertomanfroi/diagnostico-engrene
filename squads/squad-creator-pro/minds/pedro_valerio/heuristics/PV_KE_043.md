---
id: "PV_KE_043"
title: "A Primazia do Atributo (Task-First Architecture)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Task-First Architecture"
  - "Resilience"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "AN_KE_106 (Subagents Over Flattened Tasks) vs Task-First Monolith"
  resolution: "Tier de Impacto — SINKRA governa esteiras Core-Value repetíveis; tasks ad hoc sandbox escapam do mapeamento formal"
---

# PV_KE_043 - A Primazia do Atributo (Task-First Architecture)

**Type:** Decision Heuristic
**Zone:** 🧠 0.8% Genialidade | **Agent:** @hybridOps:process-architect
**Source:** [SOURCE: SINKRA-v4.md | Capítulos 1 e 3 - O executor é um atributo transversal]

## Purpose
A fundação filosófica inteira contra "O Erro Invisível de 115 anos". Em diagramas clássicos (BPMN), desenhávamos o processo ao redor da pressuposição silenciosa de que humanos executavam as caixas de fluxo. Na Era Sincronizada Human-AI, os donos do Processo não são mais "Quem fará essa automação de RPA/Make". A primazia absoluta volta para a *Task*. Se O QUE entra e O QUE sai da molécula está selado a vácuo, QUEM aperta o botão vira uma chave mecânica.

## Configuration
```yaml
PV_KE_043:
  name: "Task-First / Primazia do Atributo Executor"
  zone: "zone_0.8"
  trigger: "Design de processos novos, documentação de pipelines ou mapeamento para instanciar novos times / esquadrões."
  evidence_threshold: "first_principles_inference"
  rule: |
    SE você está desenhando a interface de um fluxo operacional de valor
    ENTÃO proíba os termos "Robô", "Zappier", "Make", "Fulano" na arquitetura nuclear inicial.
    Obrigatório: Modele O-QUE-É-A-TAREFA (Input, Output, Limitante de Custo, Limitante de Tempo).
    SOMENTE AO FINAL, como um seletor visual na tabela, o Time deve setar o "executor_type" em um enum = (AGENT | WORKER | HUMAN | CLONE).
  veto_condition:
    trigger: "O diagrama de processos tem a 'Raia Inteligência Artificial' misturando script Python de regex, um LLM e uma automação."
    action: "VETO DA DOCUMENTAÇÃO. É mandatório aplicar divisões nítidas dos 4 Executores transversais para evitar pontos cegos."
```

## Decision Tree
```javascript
IF (mapping_new_molecule_for_pipeline)
  STEP_1: DEFINE atom_task prerequisites (Input, Output, SLAs, Pre-conditions)
  STEP_2: MEASURE task functional profile (Deterministic? Needs scale? Creative? Liability?)
  STEP_3: ASSIGN transversally the Executor Class
    IF (strict determinism & volume) -> WORKER
    IF (stochastic analytics) -> AGENT
    IF (strict corporate ethos needed) -> CLONE
    IF (unforgiving legal/moral liability) -> HUMAN
    
NEVER:
  Montar um "departamento de AI" sem modelar quais Atos eles substituem no chassi primordial do Organism. Processo sem executor classificado não é framework, é intenção folclórica.
```

## Failure Modes

### Misapplication / Excess: "O Excesso de Abstração Engessante"
- **Trigger:** A empresa força a teoria até a ponta hiper-micro. Tudo na operação precisa ser estritamente planejado com 9 graus de abstração estrutural para a "matemática não quebrar".
- **Manifestation:** Um *designer* não consegue subir um simples banner com um prompt básico de IA nas mídias sociais porque a PM do time embarga exigindo "mapeamento dos Atoms com executor attribute definido".
- **Detection:** Entregas param; o backlog infla brutalmente pois toda experimentação leve esbarra no *wall* arquitetural do "Sinkra Framework". A infra virou trava de inovação frontal.
- **Recovery:** Determinar a barreira estrita de impacto. A SINKRA e os executores transversais **governam os `Organisms` de Core-Value** da Empresa. Tasks corriqueiras individuais (Ad hoc de sandbox) pulam totalmente o mapeamento, sobrevivendo como ferramentas soltas da pessoa que quiser usá-las.
- **Prevention:** Adotar níveis de engajamento do Design. A arquitetura só se aplica para esteiras repetíveis que custam recursos vitais da esteira produtiva da companhia.

### Omission / Failure to Activate: "O Herói-Dependente ou A Ferramenta-Mestra"
- **Trigger:** A equipe delega totalmente o processo a uma API do momento, ao invés de codificar a essência da tarefa.
- **Manifestation:** "Automatizamos no Make ligando um Webhook no ChatGPT" vira o idioma principal do time. 6 meses depois o "João", dono disso, vaza ou o software da plataforma quebra. Todo o pipeline desaba e a Diretoria é incapaz de ler o código fonte.  A operação era do "João da Automação", não da Empresa.
- **Detection:** Quando indagados: "O que entra ali perfeitamente?", os gerentes dizem: "Só sei que cai na planilha do João".
- **Recovery:** Uma implacável reestruturação reversa. Isolar o nó com o João. Obrigar que a documentação declare os Inputs e Outputs e trocá-la mentalmente testando se um terceirizado ou human fallback do Cazaquistão poderia assumir o buraco que deixou sem colapsar a molécula.
- **Prevention:** Durante as `Weekly Reviews`, o Board não revê os botões apertados; reverifica se a camada sintética das "Tasks" no nível 2 e 3 ainda bate com a matemática do negócio.

---

## Validation

✓ **Paradoxo identificado:** Rigor estrutural (SINKRA governance em Core-Value) vs. velocidade experimental (ad hoc sandbox)
✓ **Resolução documentada:** Tier de impacto — diferenciação explícita de when-to-apply
✓ **sys_tension:** Codificado no YAML frontmatter
✓ **Implicação tática:** Designers e PMs ganham clareza sobre quando pedir mapeamento formal e quando liberar solução ágil
✓ **Failure modes aligned:** Omission e Excess refletem os dois polos da tensão
