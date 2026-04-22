# create-business-story

```yaml
task:
  name: Create Business Story
  id: create-business-story
  description: Guia completo para criar historias de negocios usando a metodologia de Kindra Hall - Stories That Stick
  icon: "\U0001F4D6"
  category: storytelling
  complexity: medium
  estimated_time: "1-3 hours"

metadata:
  version: "1.0.0"
  created: "2026-01-30"
  agent: kindra-hall
  methodology: "Stories That Stick - Four Essential Business Stories"
  changelog:
    - "1.0: Initial release - complete business story creation workflow based on Kindra Hall research"

inputs:
  required:
    - story_purpose: "Objetivo da historia (vender, alinhar, inspirar, provar)"
    - target_audience: "Quem vai ouvir/ler esta historia"
    - business_context: "Contexto do negocio (produto, servico, empresa)"
  optional:
    - story_type: "Tipo especifico (Value, Founder, Purpose, Customer)"
    - existing_content: "Material existente para transformar em historia"
    - channel: "Canal de entrega (apresentacao, video, email, conversa)"
    - time_constraint: "Duracao maxima da historia"

outputs:
  - story_diagnosis: "Analise da lacuna e tipo de historia recomendado"
  - story_components: "Os 4 componentes estruturados"
  - story_draft: "Historia completa em formato Normal-Explosion-New Normal"
  - delivery_guide: "Guia de como contar a historia"
  - validation_checklist: "Checklist de qualidade da historia"
```

---

## Workflow Overview

```
FASE 1: DIAGNOSTICO DE NECESSIDADE
    |
    v
FASE 2: IDENTIFICACAO DA LACUNA
    |
    v
FASE 3: SELECAO DO TIPO DE HISTORIA
    |
    v
FASE 4: COLETA DE MATERIAL (FIND)
    |
    v
FASE 5: ESTRUTURACAO DA HISTORIA (CRAFT)
    |
    v
FASE 6: APLICACAO DOS 4 COMPONENTES
    |
    v
FASE 7: REFINAMENTO E VALIDACAO
    |
    v
FASE 8: PREPARACAO PARA ENTREGA (TELL)
```

---

## FASE 1: DIAGNOSTICO DE NECESSIDADE

### 1.1 Questionario Inicial

**Perguntas para o Usuario:**

```markdown
## Diagnostico de Storytelling para Negocios

### 1. Objetivo da Comunicacao
O que voce precisa que aconteca DEPOIS que a pessoa ouvir sua historia?

- [ ] Comprar meu produto/servico
- [ ] Investir no meu negocio
- [ ] Confiar na minha empresa
- [ ] Se alinhar com nossa missao (funcionario/parceiro)
- [ ] Indicar para outros
- [ ] Mudar uma percepcao
- [ ] Outro: _______

### 2. Publico-Alvo
Quem e a pessoa especifica que vai ouvir esta historia?

- **Cargo/Papel:** _______
- **Industria:** _______
- **Desafio principal que enfrenta:** _______
- **O que ja tentou antes:** _______
- **Por que deveria se importar com voce:** _______

### 3. Contexto Atual
Onde voce esta na jornada com esse publico?

- [ ] Primeiro contato (nao me conhecem)
- [ ] Conhecem mas nao confiam ainda
- [ ] Confiam mas nao veem valor
- [ ] Veem valor mas nao priorizam
- [ ] Sao clientes mas nao advogados da marca
- [ ] Sao funcionarios que precisam de alinhamento

### 4. Canal de Entrega
Como a historia vai ser contada?

- [ ] Apresentacao ao vivo
- [ ] Video
- [ ] Email/Texto
- [ ] Conversa 1:1
- [ ] Website/Landing page
- [ ] Redes sociais
- [ ] Material impresso
- [ ] Outro: _______

### 5. Restricao de Tempo
Quanto tempo voce tem para contar a historia?

- [ ] 30 segundos (elevator pitch)
- [ ] 1-2 minutos (conversa rapida)
- [ ] 3-5 minutos (apresentacao curta)
- [ ] 10+ minutos (keynote/palestra)
- [ ] Sem limite (conteudo longo)

### 6. Material Existente
Voce ja tem algum desses materiais?

- [ ] Depoimentos de clientes
- [ ] Historia de como comecou o negocio
- [ ] Cases de sucesso documentados
- [ ] Dados de resultados/impacto
- [ ] Historias de funcionarios
- [ ] Nenhum material ainda
```

### 1.2 Output do Diagnostico

```markdown
## Resultado do Diagnostico

### Situacao Identificada
**Objetivo:** [resumo do que precisa acontecer]
**Publico:** [descricao especifica]
**Lacuna Principal:** [o que separa voce do publico]
**Canal:** [como vai entregar]
**Duracao:** [tempo disponivel]

### Recomendacao de Tipo de Historia
**Tipo Recomendado:** [Value/Founder/Purpose/Customer]
**Justificativa:** [por que este tipo]
**Alternativa:** [segundo tipo se aplicavel]
```

---

## FASE 2: IDENTIFICACAO DA LACUNA

### 2.1 Os Tres Tipos de Lacuna

> "A primeira lacuna nos negocios e a lacuna de valor. A segunda e a lacuna de credibilidade. A terceira e a lacuna de proposito."

```markdown
## Mapeamento de Lacunas

### LACUNA DE VALOR
"O publico nao entende POR QUE precisa do que voce oferece"

**Sintomas:**
- [ ] "Interessante, mas nao e prioridade agora"
- [ ] "Quanto custa?" (sem entender o valor)
- [ ] Conversas longas sobre features, nao sobre resultados
- [ ] Comparacoes de preco com concorrentes
- [ ] "O que exatamente voce faz?"

**Historia Recomendada:** Value Story ou Customer Story

---

### LACUNA DE CREDIBILIDADE
"O publico nao confia em VOCE ou sua empresa"

**Sintomas:**
- [ ] "Por que devo confiar em voce?"
- [ ] "Quem mais usa isso?"
- [ ] "Qual e sua experiencia?"
- [ ] Ceticismo sobre promessas
- [ ] Preferencia por marcas conhecidas

**Historia Recomendada:** Founder Story ou Customer Story

---

### LACUNA DE PROPOSITO
"O publico (interno) nao esta alinhado com a missao"

**Sintomas:**
- [ ] Funcionarios fazem o minimo
- [ ] Falta de engajamento em iniciativas
- [ ] "E so um trabalho"
- [ ] Alta rotatividade
- [ ] Resistencia a mudancas

**Historia Recomendada:** Purpose Story

---

### Sua Lacuna Principal
**Lacuna Identificada:** _______
**Evidencias:** _______
**Impacto de Nao Resolver:** _______
```

### 2.2 Matriz de Decisao

```
┌─────────────────────────────────────────────────────────────────┐
│                    MATRIZ DE SELECAO DE HISTORIA                │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  LACUNA DE VALOR        LACUNA DE CREDIBILIDADE                │
│        │                         │                              │
│        v                         v                              │
│  ┌──────────────┐         ┌──────────────┐                     │
│  │ VALUE STORY  │         │ FOUNDER STORY │                     │
│  │    ou        │         │      ou       │                     │
│  │ CUSTOMER     │         │  CUSTOMER     │                     │
│  │ STORY        │         │  STORY        │                     │
│  └──────────────┘         └──────────────┘                     │
│                                                                 │
│  LACUNA DE PROPOSITO      TODAS AS LACUNAS                     │
│        │                         │                              │
│        v                         v                              │
│  ┌──────────────┐         ┌──────────────┐                     │
│  │ PURPOSE      │         │ Combinacao   │                     │
│  │ STORY        │         │ de historias │                     │
│  └──────────────┘         └──────────────┘                     │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## FASE 3: SELECAO DO TIPO DE HISTORIA

### 3.1 Guia de Selecao Detalhado

#### VALUE STORY - Quando Usar

```markdown
## Checklist: E uma Value Story?

**Use Value Story SE:**
- [ ] O publico NAO entende o valor do que voce oferece
- [ ] Voce esta vendendo um produto/servico
- [ ] O publico conhece o PROBLEMA mas nao sua SOLUCAO
- [ ] Precisa converter interesse em acao
- [ ] O foco e no RESULTADO para o cliente

**Contextos Ideais:**
- Pagina de vendas
- Pitch para cliente
- Proposta comercial
- Email de follow-up
- Apresentacao de produto
- Landing page

**Estrutura Especifica:**
```
NORMAL: O cliente tem uma dor/problema
EXPLOSION: Seu produto/servico aparece
NEW NORMAL: A vida do cliente e melhor
```

**Exemplo de Value Story:**
> NORMAL: "Maria, gerente de projetos, passava 4 horas por semana criando relatorios manualmente. Era frustrante, demorado, e ainda assim os dados ficavam desatualizados."

> EXPLOSION: "Quando descobriu nossa ferramenta de automacao, instalou em 15 minutos. Na primeira semana, percebeu que os relatorios se geravam sozinhos."

> NEW NORMAL: "Agora Maria recuperou 200 horas por ano. Usa esse tempo para projetos estrategicos. Na ultima avaliacao, foi promovida."
```

---

#### FOUNDER STORY - Quando Usar

```markdown
## Checklist: E uma Founder Story?

**Use Founder Story SE:**
- [ ] O publico NAO sabe quem voce e
- [ ] Precisa construir confianca rapidamente
- [ ] Esta pitchando para investidores
- [ ] O "por que voce" e a questao central
- [ ] Sua historia pessoal se conecta com o problema que resolve

**Contextos Ideais:**
- Pitch para investidores
- Pagina "Sobre" do site
- Entrevistas e podcasts
- Networking eventos
- Recrutamento
- Palestras

**Estrutura Especifica:**
```
NORMAL: Quem voce era antes
EXPLOSION: O momento que mudou tudo
NEW NORMAL: Por que voce HAD TO fazer isso
```

**Exemplo de Founder Story:**
> NORMAL: "Trabalhei 10 anos em consultoria financeira. Via as mesmas planilhas, os mesmos problemas, as mesmas solucoes caras que so grandes empresas podiam pagar."

> EXPLOSION: "Um dia, um cliente pequeno me perguntou: 'Por que isso precisa ser tao complicado?' Nao tinha resposta. A pergunta ficou na minha cabeca por meses."

> NEW NORMAL: "Sai do emprego e criei uma solucao que qualquer empresa pode usar. Hoje, 500 pequenos negocios usam o que aquele cliente me fez criar."
```

---

#### PURPOSE STORY - Quando Usar

```markdown
## Checklist: E uma Purpose Story?

**Use Purpose Story SE:**
- [ ] O publico sao funcionarios/equipe interna
- [ ] Precisa alinhar pessoas com a missao
- [ ] Quer dar vida aos valores da empresa
- [ ] Esta passando por mudanca organizacional
- [ ] Quer motivar alem do salario

**Contextos Ideais:**
- Onboarding de funcionarios
- Reunioes de equipe
- Momentos de crise
- Lancamento de iniciativas
- Celebracao de conquistas
- Comunicados internos

**Estrutura Especifica:**
```
NORMAL: O trabalho cotidiano
EXPLOSION: O momento que voce VIU o impacto
NEW NORMAL: POR ISSO fazemos o que fazemos
```

**Exemplo de Purpose Story:**
> NORMAL: "Todo dia processamos centenas de pedidos. Embalamos, enviamos, repetimos. Parece rotina."

> EXPLOSION: "Semana passada, uma cliente ligou chorando. O pacote chegou no aniversario do filho. Ela estava no hospital com ele, tratando cancer. O presente que enviamos foi a unica coisa normal naquele dia caótico."

> NEW NORMAL: "Cada caixa que fechamos pode ser essa caixa. Nao vendemos produtos - entregamos momentos. POR ISSO caprichamos em cada envio."
```

---

#### CUSTOMER STORY - Quando Usar

```markdown
## Checklist: E uma Customer Story?

**Use Customer Story SE:**
- [ ] Precisa de PROVA SOCIAL
- [ ] O publico e cetico sobre suas promessas
- [ ] Tem clientes com resultados reais
- [ ] Quer que o cliente seja o heroi
- [ ] Precisa de credibilidade maxima

**Contextos Ideais:**
- Cases no site
- Propostas comerciais
- Apresentacoes de vendas
- Materiais de marketing
- Emails de nurturing
- Social proof em landing pages

**Estrutura Especifica:**
```
NORMAL: A vida do cliente ANTES
EXPLOSION: Quando encontrou sua solucao
NEW NORMAL: Como a vida e diferente AGORA
(Contada na voz do CLIENTE)
```

**Exemplo de Customer Story:**
> NORMAL: "Eu estava exausto. Tentei tres agencias diferentes para nosso marketing digital. Gastamos muito, resultados zero. Ja ia desistir."

> EXPLOSION: "Um colega me indicou [empresa]. Fui cetico - 'mais uma'. Mas na primeira reuniao, mostraram exatamente o que estava errado. Em 30 dias, implementaram o que outros prometeram em 6 meses."

> NEW NORMAL: "Hoje nosso custo de aquisicao caiu 40%. Dobramos os leads. Mas o melhor: finalmente durmo tranquilo sabendo que marketing esta funcionando."
```

---

## FASE 4: COLETA DE MATERIAL (FIND)

### 4.1 Perguntas para Encontrar Historias

#### Para VALUE STORY

```markdown
## Perguntas de Descoberta - Value Story

### Sobre o Problema
1. "Quem e uma pessoa especifica que tinha esse problema?"
2. "Como era a vida dessa pessoa ANTES de encontrar voce?"
3. "O que ela ja tinha tentado que NAO funcionou?"
4. "Qual era o impacto emocional/financeiro do problema?"
5. "O que aconteceria se ela nunca resolvesse?"

### Sobre a Transformacao
6. "Como essa pessoa descobriu voce/sua solucao?"
7. "Qual foi o momento 'aha' - quando ela percebeu que funcionava?"
8. "Quanto tempo levou para ver resultados?"
9. "O que mudou PRIMEIRO?"

### Sobre o Resultado
10. "Como e a vida dela AGORA?"
11. "Que numero/metrica representa a mudanca?"
12. "Como ela SE SENTE diferente?"
13. "O que ela pode fazer agora que nao podia antes?"
```

#### Para FOUNDER STORY

```markdown
## Perguntas de Descoberta - Founder Story

### Sobre o Antes
1. "O que voce fazia antes de comecar isso?"
2. "O que parecia 'normal' na sua area que te incomodava?"
3. "Quais foram os primeiros sinais de que algo precisava mudar?"
4. "O que te mantinha na situacao anterior?"

### Sobre o Momento de Virada
5. "Tem um dia/momento especifico que mudou tudo?"
6. "Onde voce estava? O que aconteceu?"
7. "O que voce percebeu que outros nao percebiam?"
8. "Por que NAO podia ignorar?"

### Sobre a Missao
9. "O que voce decidiu fazer diferente?"
10. "Que conexao existe entre sua historia e o que faz hoje?"
11. "Por que SÓ VOCE poderia fazer isso?"
12. "O que voce quer que seu legado seja?"
```

#### Para PURPOSE STORY

```markdown
## Perguntas de Descoberta - Purpose Story

### Sobre o Cotidiano
1. "Descreva um dia tipico no trabalho."
2. "Quais tarefas parecem 'rotineiras' ou 'mundanas'?"
3. "O que faz todo dia que parece 'so trabalho'?"

### Sobre o Impacto
4. "Conte sobre uma vez que voce VIU o impacto real do trabalho."
5. "Quem foi a pessoa que foi impactada?"
6. "O que aconteceu especificamente?"
7. "Como voce se sentiu naquele momento?"

### Sobre o Significado
8. "Por que ISSO e o que fazemos?"
9. "Como essa historia representa nossos valores?"
10. "O que essa historia te ensinou sobre nosso trabalho?"
```

#### Para CUSTOMER STORY

```markdown
## Perguntas de Descoberta - Customer Story

### As Tres Perguntas Essenciais (Metodo Native Deodorant)
1. "O que fez voce experimentar?"
2. "O que voce usava/fazia antes?"
3. "O que mudou?"

### Perguntas Expandidas
4. "Como voce descreveria sua vida ANTES de usar [produto/servico]?"
5. "Qual era sua maior frustracao?"
6. "O que voce ja tinha tentado?"
7. "Como foi sua primeira experiencia?"
8. "Qual foi o momento em que voce percebeu que funcionava?"
9. "O que e diferente agora?"
10. "O que voce diria a alguem considerando isso?"
```

### 4.2 Story Banking Template

```markdown
## Banco de Historias

### Categoria: VALUE STORIES
| ID | Titulo Resumido | Protagonista | Problema | Resultado | Fonte | Data |
|----|-----------------|--------------|----------|-----------|-------|------|
| V1 | _______ | _______ | _______ | _______ | _______ | _______ |
| V2 | _______ | _______ | _______ | _______ | _______ | _______ |

### Categoria: FOUNDER STORIES
| ID | Momento-Chave | Licao | Conexao com Missao | Data |
|----|---------------|-------|-------------------|------|
| F1 | _______ | _______ | _______ | _______ |

### Categoria: PURPOSE STORIES
| ID | Valor Ilustrado | Personagem | Impacto | Uso Recomendado | Data |
|----|-----------------|------------|---------|-----------------|------|
| P1 | _______ | _______ | _______ | _______ | _______ |

### Categoria: CUSTOMER STORIES
| ID | Cliente | Antes | Depois | Canal de Coleta | Data |
|----|---------|-------|--------|-----------------|------|
| C1 | _______ | _______ | _______ | _______ | _______ |
```

---

## FASE 5: ESTRUTURACAO DA HISTORIA (CRAFT)

### 5.1 Template Universal: Normal-Explosion-New Normal

```markdown
## Estrutura da Historia: [Titulo]

### Tipo: [Value/Founder/Purpose/Customer]
### Objetivo: [O que deve acontecer depois]
### Publico: [Quem vai ouvir]
### Duracao Alvo: [X minutos/segundos]

---

## NORMAL (O Antes)
> "Coisas sao como sao"

### Contexto
[Descreva a situacao inicial. Estabeleca o "normal" que vai ser interrompido.]

### O Protagonista
- **Quem:** [Nome/Papel/Caracteristicas identificaveis]
- **Situacao:** [O que estava acontecendo]
- **Desafio:** [O problema/dor/frustracao]

### Detalhes Especificos
[Inclua 2-3 detalhes que o publico vai reconhecer]
- Detalhe 1: _______
- Detalhe 2: _______
- Detalhe 3: _______

### Emocao Presente
[Que emocao o protagonista sentia?]
- [ ] Frustracao
- [ ] Medo
- [ ] Confusao
- [ ] Desespero
- [ ] Estagnacao
- [ ] Outro: _______

### RASCUNHO DO NORMAL:
```
[Escreva 2-4 frases que estabelecem o "antes"]
_________________________________________________
_________________________________________________
_________________________________________________
_________________________________________________
```

---

## EXPLOSION (A Mudanca)
> "Algo acontece"

### O Momento de Virada
- **Quando:** [Seja especifico - data, hora, lugar]
- **O que aconteceu:** [O evento/descoberta/decisao]
- **Por que foi significativo:** [O que tornou este momento diferente]

### O Catalisador
[O que causou a mudanca?]
- [ ] Descoberta do produto/servico
- [ ] Uma pessoa/conversa
- [ ] Um evento externo
- [ ] Uma realizacao interna
- [ ] Uma crise que forcou acao

### Detalhe do Momento
[Um detalhe sensorial que ancora o momento]
- O que viu: _______
- O que ouviu: _______
- O que sentiu: _______

### RASCUNHO DO EXPLOSION:
```
[Escreva 2-4 frases que descrevem o momento de mudanca]
_________________________________________________
_________________________________________________
_________________________________________________
_________________________________________________
```

---

## NEW NORMAL (O Depois)
> "Coisas sao diferentes"

### A Transformacao
- **Resultado Tangivel:** [Numero, fato, evidencia]
- **Resultado Emocional:** [Como a pessoa se sente agora]
- **O que Pode Fazer Agora:** [Capacidades novas]

### Comparacao Antes vs Depois
| Aspecto | ANTES | DEPOIS |
|---------|-------|--------|
| _______ | _______ | _______ |
| _______ | _______ | _______ |
| _______ | _______ | _______ |

### Implicacao para o Ouvinte
[O que isso significa para quem esta ouvindo?]
_______________________________________

### RASCUNHO DO NEW NORMAL:
```
[Escreva 2-4 frases que mostram a transformacao]
_________________________________________________
_________________________________________________
_________________________________________________
_________________________________________________
```

---

## HISTORIA COMPLETA (Primeiro Rascunho)

```
[Junte os tres blocos em uma narrativa fluida]

[NORMAL]
_________________________________________________
_________________________________________________

[EXPLOSION]
_________________________________________________
_________________________________________________

[NEW NORMAL]
_________________________________________________
_________________________________________________
```
```

### 5.2 Templates por Tipo de Historia

#### Template Value Story

```markdown
## VALUE STORY: [Nome do Produto/Servico]

### Objetivo
Convencer [PUBLICO] que [PRODUTO/SERVICO] resolve [PROBLEMA]

### NORMAL
**Setup:** "[PROTAGONISTA] enfrentava [PROBLEMA ESPECIFICO]."

**Detalhamento:**
- O que estava acontecendo: _______
- O que ja tinha tentado: _______
- O impacto na vida/trabalho: _______

**Exemplo de Escrita:**
> "[Nome], [cargo] em [empresa/contexto], passava [tempo] lidando com [problema]. Ja tinha tentado [solucao anterior], mas [por que nao funcionou]. Estava chegando ao ponto de [consequencia]."

### EXPLOSION
**Momento:** "[PROTAGONISTA] descobriu/encontrou [SUA SOLUCAO]."

**Detalhamento:**
- Como descobriu: _______
- Primeira acao: _______
- Primeiro resultado: _______

**Exemplo de Escrita:**
> "Foi quando [como descobriu]. [Primeira acao tomada]. Em [tempo], [primeiro resultado visivel]."

### NEW NORMAL
**Transformacao:** "Agora, [PROTAGONISTA] [NOVO ESTADO]."

**Detalhamento:**
- Resultado quantificavel: _______
- Mudanca emocional: _______
- O que pode fazer agora: _______

**Exemplo de Escrita:**
> "Hoje, [resultado numerico]. Mas mais que isso - [mudanca emocional]. [O que pode fazer agora que nao podia antes]."

### CTA IMPLICITO
[O que voce quer que o ouvinte faca depois desta historia?]
```

#### Template Founder Story

```markdown
## FOUNDER STORY: [Nome do Fundador]

### Objetivo
Construir confianca mostrando por que [FUNDADOR] criou [EMPRESA]

### NORMAL
**Setup:** "Antes de [EMPRESA], eu era [QUEM/O QUE FAZIA]."

**Detalhamento:**
- Vida/carreira anterior: _______
- O que parecia normal: _______
- Sinais de inquietacao: _______

**Exemplo de Escrita:**
> "Por [X anos], trabalhei em [area]. Via [situacao comum]. Todo mundo aceitava que [crenca limitante]. Mas algo me incomodava."

### EXPLOSION
**Momento:** "O dia/momento em que tudo mudou."

**Detalhamento:**
- Quando/Onde aconteceu: _______
- O que aconteceu especificamente: _______
- O que percebeu: _______

**Exemplo de Escrita:**
> "Foi em [quando/onde]. [Evento especifico]. Naquele momento, percebi que [insight]. E soube que nao podia ignorar."

### NEW NORMAL
**Missao:** "Por isso criei [EMPRESA]."

**Detalhamento:**
- A decisao tomada: _______
- A conexao com o problema: _______
- O que representa hoje: _______

**Exemplo de Escrita:**
> "Deixei [o que deixou para tras]. Criei [empresa/solucao] porque [conexao com momento de virada]. Hoje, [impacto/missao atual]."

### CONEXAO COM O PUBLICO
[Como sua historia se conecta com a necessidade do cliente?]
```

#### Template Purpose Story

```markdown
## PURPOSE STORY: [Valor/Missao Ilustrado]

### Objetivo
Mostrar [VALOR] em acao para alinhar/inspirar [PUBLICO INTERNO]

### NORMAL
**Setup:** "Todo dia fazemos [TRABALHO COTIDIANO]."

**Detalhamento:**
- Rotina diaria: _______
- O que parece mundano: _______
- O que fazemos "mecanicamente": _______

**Exemplo de Escrita:**
> "Na maioria dos dias, [descricao da rotina]. [Tarefa especifica] atras de [tarefa especifica]. Parece so trabalho."

### EXPLOSION
**Momento:** "Mas entao [MOMENTO DE IMPACTO]."

**Detalhamento:**
- Quem foi impactado: _______
- O que aconteceu: _______
- O que voce viu/sentiu: _______

**Exemplo de Escrita:**
> "[Quando/Contexto], [pessoa especifica] [o que aconteceu]. [Detalhe emocional]. Foi ali que [o que percebeu]."

### NEW NORMAL
**Significado:** "POR ISSO fazemos o que fazemos."

**Detalhamento:**
- Conexao com o trabalho diario: _______
- O que isso significa para a equipe: _______
- O proposito revelado: _______

**Exemplo de Escrita:**
> "Cada [acao cotidiana] pode ser [impacto potencial]. Nao [descricao generica] - [significado real]. Por isso [comportamento desejado]."

### USO RECOMENDADO
[Em quais momentos contar esta historia: onboarding, crises, reunioes]
```

#### Template Customer Story

```markdown
## CUSTOMER STORY: [Nome/Perfil do Cliente]

### Objetivo
Prover prova social de que [SOLUCAO] funciona

### PERFIL DO CLIENTE
- **Nome (ou tipo):** _______
- **Contexto:** _______
- **Permissao para uso:** [ ] Sim [ ] Anonimizado

### NORMAL (Na Voz do Cliente)
**Setup:** "Antes de [SOLUCAO], eu..."

**Elementos a Capturar:**
- Situacao inicial: _______
- O problema especifico: _______
- O que ja tinha tentado: _______
- O impacto: _______

**Exemplo de Escrita (1a pessoa):**
> "Eu estava [situacao]. [Problema especifico]. Ja tinha tentado [solucoes anteriores], mas [por que nao funcionaram]. Estava [emocao/consequencia]."

### EXPLOSION (Na Voz do Cliente)
**Momento:** "Entao eu descobri/experimentei [SOLUCAO]."

**Elementos a Capturar:**
- Como descobriu: _______
- Decisao de tentar: _______
- Primeira experiencia: _______
- Momento "aha": _______

**Exemplo de Escrita (1a pessoa):**
> "[Como descobriu]. [Por que decidiu tentar]. [Primeira experiencia]. O momento que soube que era diferente foi quando [momento aha]."

### NEW NORMAL (Na Voz do Cliente)
**Transformacao:** "Agora eu..."

**Elementos a Capturar:**
- Resultado tangivel: _______
- Mudanca emocional: _______
- Recomendacao: _______

**Exemplo de Escrita (1a pessoa):**
> "Hoje [resultado numerico]. Mas o que mais importa e [mudanca emocional]. Para quem esta pensando - [recomendacao]."

### NOTAS DE AUTENTICIDADE
- [ ] Voz natural do cliente mantida
- [ ] Imperfeicoes incluidas
- [ ] Detalhes especificos autenticos
- [ ] Nao "polida demais"
```

---

## FASE 6: APLICACAO DOS 4 COMPONENTES

### 6.1 Checklist dos 4 Componentes

```markdown
## Validacao dos 4 Componentes de Kindra Hall

### 1. PERSONAGENS IDENTIFICAVEIS

**Checklist:**
- [ ] O protagonista tem nome ou descricao especifica?
- [ ] O publico-alvo consegue se ver no protagonista?
- [ ] Ha detalhes que humanizam o personagem?
- [ ] O personagem tem vulnerabilidade/falha?
- [ ] Esta limitado a 1-3 personagens principais?

**Se Faltando:**
- Adicione nome, cargo, contexto especifico
- Inclua um detalhe pessoal reconhecivel
- Mostre uma limitacao ou desafio humano

**Exemplo de Melhoria:**
- Antes: "Um cliente nosso..."
- Depois: "Maria, gerente de uma loja de roupas em Campinas, mae de dois..."

---

### 2. EMOCAO AUTENTICA

**Checklist:**
- [ ] Ha emocao no Normal? (frustracao, medo, confusao)
- [ ] Ha tensao no Explosion? (esperanca, duvida, surpresa)
- [ ] Ha satisfacao no New Normal? (alivio, orgulho, gratidao)
- [ ] A emocao e MOSTRADA, nao apenas descrita?
- [ ] E uma emocao que o publico pode sentir tambem?

**Se Faltando:**
- Pergunte: "Como o protagonista se SENTIU naquele momento?"
- Use verbos de acao emocional: "suspirou aliviado", "sentiu o estomago apertar"
- Conecte a emocao universal (medo de fracasso, desejo de reconhecimento)

**Exemplo de Melhoria:**
- Antes: "Ele estava preocupado com os resultados."
- Depois: "Cada fim de mes, ele sentia o estomago apertar ao abrir o relatorio de vendas."

---

### 3. MOMENTO SIGNIFICATIVO

**Checklist:**
- [ ] Ha um momento ESPECIFICO e identificavel?
- [ ] Voce pode visualizar a cena? (quando, onde)
- [ ] E o ponto de virada claro da historia?
- [ ] O momento tem detalhes sensoriais?
- [ ] E memoravel?

**Se Faltando:**
- Pergunte: "Quando EXATAMENTE isso aconteceu?"
- Adicione: data, local, circunstancia
- Use: "Foi numa terça-feira, no escritorio, quando..."

**Exemplo de Melhoria:**
- Antes: "Em algum momento, ele descobriu nossa solucao."
- Depois: "Era uma quarta-feira de chuva. Ele estava no cafe perto do escritorio quando viu um post no LinkedIn..."

---

### 4. DETALHES ESPECIFICOS

**Checklist:**
- [ ] Ha pelo menos 2-3 detalhes especificos?
- [ ] Os detalhes sao relevantes para o publico?
- [ ] Os detalhes criam imagem mental?
- [ ] Os detalhes sao autenticos (nao inventados)?
- [ ] Os detalhes mostram que voce conhece o publico?

**Se Faltando:**
- Pergunte: "O que uma camera filmaria naquele momento?"
- Use detalhes que seu publico especifico reconheceria
- Inclua objetos, lugares, acoes concretas

**Exemplo de Melhoria:**
- Antes: "Ela trabalhava muito."
- Depois: "Seu notebook tinha tres abas do Excel abertas, uma planilha em cada monitor, e ainda assim ela anotava em post-its amarelos colados na parede."
```

### 6.2 Matriz de Enriquecimento

```markdown
## Matriz de Enriquecimento da Historia

### Historia Atual
[Cole sua historia aqui]

### Analise por Componente

| Componente | Presente? | Forca (1-5) | Melhoria Sugerida |
|------------|-----------|-------------|-------------------|
| Personagem Identificavel | [ ] | __ | _________________ |
| Emocao Autentica | [ ] | __ | _________________ |
| Momento Significativo | [ ] | __ | _________________ |
| Detalhes Especificos | [ ] | __ | _________________ |

### Acoes de Enriquecimento

**Personagem:**
- [ ] Adicionar nome/descricao
- [ ] Incluir contexto pessoal
- [ ] Mostrar vulnerabilidade

**Emocao:**
- [ ] Descrever sentimento no Normal
- [ ] Aumentar tensao no Explosion
- [ ] Amplificar satisfacao no New Normal

**Momento:**
- [ ] Especificar quando/onde
- [ ] Adicionar detalhes sensoriais
- [ ] Tornar memoravel

**Detalhes:**
- [ ] Incluir objeto/lugar especifico
- [ ] Usar referencia que publico reconhece
- [ ] Adicionar acao concreta

### Historia Enriquecida
[Reescreva a historia com melhorias]
```

---

## FASE 7: REFINAMENTO E VALIDACAO

### 7.1 Checklist de Qualidade Final

```markdown
## Validacao Final da Historia

### ESTRUTURA
- [ ] Tem Normal-Explosion-New Normal claros?
- [ ] A proporcao esta equilibrada (nem muito Normal, nem muito curto)?
- [ ] Ha transicao fluida entre as partes?
- [ ] O arco esta completo (nao para no meio)?

### COMPONENTES
- [ ] Personagem identificavel? (1-5): __
- [ ] Emocao autentica? (1-5): __
- [ ] Momento significativo? (1-5): __
- [ ] Detalhes especificos? (1-5): __
- [ ] MEDIA: __ (Minimo recomendado: 4.0)

### OBJETIVO
- [ ] A historia preenche a lacuna identificada?
- [ ] Gera a emocao desejada no publico?
- [ ] Tem CTA claro (mesmo que implicito)?
- [ ] O ouvinte sabera o que fazer depois?

### AUTENTICIDADE
- [ ] E baseada em fatos reais?
- [ ] Os detalhes sao verificaveis?
- [ ] A voz e autentica (nao corporativese)?
- [ ] Ha imperfeicoes que humanizam?

### DURACAO
- [ ] Cabe no tempo disponivel?
- [ ] Nao e longa demais para o canal?
- [ ] Cada parte contribui (nao ha filler)?

### PUBLICO
- [ ] O protagonista ressoa com o publico?
- [ ] Os detalhes sao reconheciveis pelo publico?
- [ ] O problema e relevante para o publico?
- [ ] A solucao e acessivel para o publico?

### SCORE FINAL
| Criterio | Score (1-5) |
|----------|-------------|
| Estrutura | __ |
| Componentes | __ |
| Objetivo | __ |
| Autenticidade | __ |
| Duracao | __ |
| Publico | __ |
| **MEDIA** | __ |

**Recomendacao:**
- 4.5+: Pronta para uso
- 4.0-4.4: Pequenos ajustes
- 3.5-3.9: Revisao necessaria
- <3.5: Reconstruir
```

### 7.2 Teste de Leitura em Voz Alta

```markdown
## Teste de Leitura em Voz Alta

### Instrucoes
1. Leia a historia em voz alta
2. Cronometre o tempo
3. Note onde tropeça ou parece artificial
4. Observe onde a energia cai

### Metricas

**Tempo Total:** ___ minutos ___ segundos

**Alvo por Canal:**
- Elevator pitch: 30-60 segundos
- Conversa rapida: 1-2 minutos
- Apresentacao: 3-5 minutos

**Pontos de Tropeço:**
- Linha/Trecho: _______
- Problema: [ ] Longo demais [ ] Complexo [ ] Artificial [ ] Sem ritmo

**Energia:**
- [ ] Normal engaja desde o inicio?
- [ ] Explosion cria tensao?
- [ ] New Normal fecha com forca?

### Ajustes Necessarios
1. _______
2. _______
3. _______
```

### 7.3 Teste de Relevancia para o Publico

```markdown
## Teste de Relevancia

### Perguntas de Validacao

**Sobre o Problema (Normal):**
- "Meu publico reconhece esse problema?"
  - [ ] Sim, com certeza
  - [ ] Provavelmente
  - [ ] Talvez nao
  - [ ] Nao

**Sobre o Protagonista:**
- "Meu publico consegue se ver no protagonista?"
  - [ ] Sim, com certeza
  - [ ] Provavelmente
  - [ ] Talvez nao
  - [ ] Nao

**Sobre a Solucao:**
- "A solucao apresentada e acessivel/relevante para meu publico?"
  - [ ] Sim, com certeza
  - [ ] Provavelmente
  - [ ] Talvez nao
  - [ ] Nao

**Sobre a Acao:**
- "Depois de ouvir, meu publico sabera o que fazer?"
  - [ ] Sim, com certeza
  - [ ] Provavelmente
  - [ ] Talvez nao
  - [ ] Nao

### Se Houver "Talvez nao" ou "Nao"
Ajustar o elemento correspondente para aumentar relevancia.
```

---

## FASE 8: PREPARACAO PARA ENTREGA (TELL)

### 8.1 Adaptacao por Canal

```markdown
## Guia de Adaptacao por Canal

### APRESENTACAO AO VIVO

**Ajustes:**
- Pausas para efeito dramatico
- Contato visual nos momentos-chave
- Gestos para enfatizar
- Variacao de tom de voz

**Estrutura de Slides (se usar):**
- Slide 1: Visual do Normal (problema)
- Slide 2: Visual do Explosion (momento)
- Slide 3: Visual do New Normal (resultado)
- NAO colocar texto da historia nos slides

**Dicas:**
- Pratique 5x antes
- Grave e assista
- Ajuste timing baseado em feedback

---

### VIDEO

**Ajustes:**
- Mais visual, menos texto
- Cortes no Explosion para criar tensao
- B-roll para detalhes especificos
- Musica para emocao

**Estrutura:**
- 0-15s: Hook (parte do problema)
- 15-45s: Normal completo
- 45-75s: Explosion
- 75-90s: New Normal + CTA

**Dicas:**
- Primeiro 3 segundos decidem se continua
- Legendas para quem assiste sem som
- Call-to-action visual no final

---

### EMAIL/TEXTO

**Ajustes:**
- Paragrafos curtos
- Linha de abertura compelling
- Espacamento para respiro
- CTA claro no final

**Estrutura:**
```
Linha 1: Hook que gera curiosidade
[espaco]
Normal (2-3 frases)
[espaco]
Explosion (2-3 frases)
[espaco]
New Normal (2-3 frases)
[espaco]
CTA
```

**Dicas:**
- Subject line que gera abertura
- Pre-header alinhado
- Mobile-first formatting

---

### CONVERSA 1:1

**Ajustes:**
- Tom conversacional
- Pausas para reacao
- Adaptar baseado em feedback ao vivo
- Perguntas de transicao

**Estrutura:**
- "Deixa eu te contar sobre um cliente..."
- Normal (observe reacao)
- "E ai que aconteceu algo interessante..."
- Explosion (pause para efeito)
- "Hoje..."
- New Normal

**Dicas:**
- Leia a linguagem corporal
- Ajuste nivel de detalhe conforme interesse
- Termine com pergunta para engajamento

---

### WEBSITE/LANDING PAGE

**Ajustes:**
- Visual primeiro, texto segundo
- Escaneabilidade
- Multiplas historias em formato case
- Provas sociais visuais

**Estrutura:**
- Headline com promessa (New Normal)
- Visual do protagonista
- Normal em bullets ou citacao
- Explosion como destaque
- Resultado com numeros
- CTA

**Dicas:**
- Above the fold: promessa clara
- Testimonials em video preferivel
- Numeros em destaque
- CTA repetido

---

### REDES SOCIAIS

**Ajustes:**
- Mais curto (adequar ao canal)
- Hook nos primeiros caracteres
- Hashtags estrategicas
- Visual atrativo

**Estrutura LinkedIn:**
```
[Hook - 1 linha que para o scroll]

[Normal - 2-3 linhas]

[Explosion - 2-3 linhas]

[New Normal - 2-3 linhas]

[Licao/CTA]
```

**Estrutura Instagram:**
- Visual: Antes/Depois ou Momento-chave
- Caption: Historia condensada
- CTA: "Link na bio" ou DM

**Dicas:**
- Primeira linha e tudo
- Emojis com moderacao
- Engaje nos comentarios
```

### 8.2 Cartao de Referencia Rapida

```markdown
## Cartao de Referencia: [Titulo da Historia]

### Tipo: [Value/Founder/Purpose/Customer]

### Em Uma Frase
_________________________________________________

### Estrutura Resumida

**NORMAL (__ segundos):**
_________________________________________________

**EXPLOSION (__ segundos):**
_________________________________________________

**NEW NORMAL (__ segundos):**
_________________________________________________

### Pontos-Chave para Nao Esquecer
1. Detalhe crucial: _______
2. Emocao a transmitir: _______
3. Numero/Fato importante: _______

### Quando Usar
- [ ] Situacao 1: _______
- [ ] Situacao 2: _______
- [ ] Situacao 3: _______

### O que NÃO Fazer
- Nao pular o Normal (sem contexto, sem impacto)
- Nao apressar o Explosion (e o momento-chave)
- Nao terminar sem New Normal (historia incompleta)
```

---

## TEMPLATES DE OUTPUT FINAL

### Template de Historia Completa

```markdown
# [TITULO DA HISTORIA]

## Metadados
- **Tipo:** [Value/Founder/Purpose/Customer]
- **Objetivo:** [O que deve acontecer depois]
- **Publico:** [Quem vai ouvir]
- **Canal:** [Onde sera contada]
- **Duracao:** [X minutos]
- **Criada em:** [Data]

---

## A Historia

### NORMAL

[2-4 paragrafos estabelecendo o antes]

---

### EXPLOSION

[2-3 paragrafos sobre o momento de mudanca]

---

### NEW NORMAL

[2-3 paragrafos mostrando a transformacao]

---

## Guia de Entrega

### Pontos de Enfase
1. [Momento para pausar]
2. [Frase para enfatizar]
3. [Emocao a transmitir]

### Adaptacoes por Canal

**Se Apresentacao:**
[Ajustes especificos]

**Se Email:**
[Ajustes especificos]

**Se Conversa:**
[Ajustes especificos]

---

## Validacao

| Componente | Score (1-5) |
|------------|-------------|
| Personagem Identificavel | __ |
| Emocao Autentica | __ |
| Momento Significativo | __ |
| Detalhes Especificos | __ |
| **MEDIA** | __ |

**Status:** [ ] Pronta [ ] Ajustes Necessarios

---

## Versoes Alternativas

### Versao Curta (30 segundos)
[Historia condensada]

### Versao Longa (5+ minutos)
[Historia expandida com mais detalhes]

---

## Notas
[Observacoes adicionais, fonte dos dados, permissoes]
```

---

## REFERENCIAS E FONTES

### Obras de Kindra Hall
- "Stories That Stick" (2019) - WSJ #2 Bestseller
- "Choose Your Story, Change Your Life" (2022)
- "The Story Edge" (2024)

### Frameworks Utilizados
- Four Essential Business Stories (Value, Founder, Purpose, Customer)
- Normal-Explosion-New Normal Structure
- Four Components (Character, Emotion, Moment, Details)
- Find-Craft-Tell Process

### Research Aplicada
- Stanford Research: Stories 22x more memorable than facts
- Native Deodorant case study: 3-question story collection
- Sodexo case study: Purpose Story implementation

### Clientes de Referencia
- Facebook, Hilton Hotels, Target
- Berkshire Hathaway, Harvard Medical School
- Tyson Foods, SUCCESS Magazine

---

## TROUBLESHOOTING

### Problema: Historia Parece Generica
**Causa:** Faltam detalhes especificos
**Solucao:**
1. Adicione nome/cargo/contexto ao protagonista
2. Inclua pelo menos 3 detalhes concretos
3. Especifique quando/onde no Explosion

### Problema: Historia Nao Conecta
**Causa:** Falta emocao autentica
**Solucao:**
1. Pergunte "como o protagonista se SENTIU?"
2. Mostre a emocao, nao apenas descreva
3. Conecte a emocao universal

### Problema: Historia E Longa Demais
**Causa:** Excesso de detalhes ou Normal extenso
**Solucao:**
1. Corte detalhes que nao servem a historia
2. Va direto ao problema no Normal
3. Mantenha foco no momento-chave do Explosion

### Problema: Historia Nao Gera Acao
**Causa:** Falta de conexao com o publico ou CTA
**Solucao:**
1. Verifique se o protagonista ressoa com publico
2. Certifique-se que o problema e relevante
3. Adicione CTA claro (mesmo que implicito)

### Problema: Historia Parece Inventada
**Causa:** Falta de autenticidade
**Solucao:**
1. Use fatos e pessoas reais
2. Mantenha imperfeicoes
3. Inclua detalhes que nao poderiam ser inventados
4. Use voz natural, nao "corporativese"

---

*Task Version: 1.0*
*Agent: kindra-hall*
*Lines: 900+*
*Methodology: Stories That Stick - Kindra Hall*
*Last Updated: 2026-01-30*
