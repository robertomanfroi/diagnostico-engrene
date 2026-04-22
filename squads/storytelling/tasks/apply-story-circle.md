# apply-story-circle

```yaml
task:
  name: Apply Story Circle
  id: apply-story-circle
  description: Guia completo para aplicar o Story Circle de Dan Harmon a episodios de TV, contos e narrativas curtas
  icon: "\u2B55"
  category: storytelling
  complexity: medium
  estimated_time: "1-3 hours"

metadata:
  version: "1.0.0"
  created: "2026-01-30"
  agent: dan-harmon
  changelog:
    - "1.0: Initial release - complete Story Circle application workflow"
  research_sources:
    primary:
      - "Channel 101 Wiki - Story Structure 101-106"
      - "Dan Harmon Tumblr Q&A"
      - "Rick and Morty Writers' Room Documentation"
    secondary:
      - "Reedsy Blog - Dan Harmon Story Circle"
      - "Industrial Scripts - Story Circle Guide"
      - "Kindlepreneur - Story Circle Guide"
      - "Boords - Storytelling 101"

inputs:
  required:
    - story_type: "Tipo de historia (tv_episode, short_story, web_series, sketch)"
    - format_length: "Duracao/extensao (21min, 44min, 5min, 5k palavras, etc.)"
    - protagonist_concept: "Conceito inicial do protagonista"
  optional:
    - existing_outline: "Outline existente para diagnostico"
    - genre: "Genero (comedy, drama, sci-fi, fantasy, etc.)"
    - tone: "Tom (dark, light, satirical, earnest)"
    - series_context: "Se episodio, contexto da serie"

outputs:
  - complete_circle: "Estrutura completa do Story Circle em 8 passos"
  - timing_breakdown: "Distribuicao temporal por passo"
  - scene_beats: "Beats de cena para cada passo"
  - diagnostic_report: "Relatorio de pontos fortes e fracos"
  - revision_checklist: "Checklist de validacao"
```

---

## Workflow Overview

```
FASE 1: DIAGNOSTICO E SETUP
    |
    v
FASE 2: ESTABELECER O MUNDO (Passos 1-2)
    |
    v
FASE 3: CRUZAR O LIMIAR (Passo 3)
    |
    v
FASE 4: DESCIDA AO CAOS (Passos 4-5)
    |
    v
FASE 5: SUBIDA E PRECO (Passo 6)
    |
    v
FASE 6: RETORNO E MUDANCA (Passos 7-8)
    |
    v
FASE 7: VALIDACAO DO CIRCULO
    |
    v
FASE 8: AJUSTES E REFINAMENTO
```

---

## FASE 1: DIAGNOSTICO E SETUP

### 1.1 Coleta de Informacoes Iniciais

**Perguntas para o Usuario:**

```markdown
## Informacoes Basicas da Historia

1. **Formato da Historia:**
   - [ ] Episodio de TV (21-22 min - sitcom)
   - [ ] Episodio de TV (42-44 min - drama)
   - [ ] Episodio de TV (30 min - streaming)
   - [ ] Web series (5-15 min)
   - [ ] Conto (3-10k palavras)
   - [ ] Flash fiction (<1k palavras)
   - [ ] Sketch/Short (1-5 min)
   - [ ] Outro: _______

2. **Genero Principal:**
   - [ ] Comedia
   - [ ] Drama
   - [ ] Sci-fi
   - [ ] Fantasia
   - [ ] Romance
   - [ ] Thriller/Suspense
   - [ ] Horror
   - [ ] Outro: _______

3. **Tom:**
   - [ ] Leve/Comico
   - [ ] Satirico/Ironico
   - [ ] Dramatico/Serio
   - [ ] Sombrio/Dark
   - [ ] Misto

4. **Contexto de Serie (se aplicavel):**
   - E um piloto? [ ] Sim [ ] Nao
   - Episodio de temporada existente? [ ] Sim [ ] Nao
   - Stand-alone? [ ] Sim [ ] Nao

5. **Conceito do Protagonista:**
   - Nome: _______
   - Funcao/Papel: _______
   - Caracteristica definidora: _______
   - Falha ou limitacao: _______

6. **Premissa em Uma Frase:**
   ___________________________________
```

### 1.2 Tabela de Timing por Formato

**Selecione o formato e use a distribuicao correspondente:**

#### Episodio de TV - 21 minutos (Sitcom)

| Passo | Tempo | Duracao | Funcao |
|-------|-------|---------|--------|
| 1. YOU | 0:00-2:00 | 2 min | Estabelecer situacao |
| 2. NEED | 2:00-5:00 | 3 min | Problema surge |
| 3. GO | 5:00-7:00 | 2 min | Compromisso |
| 4. SEARCH | 7:00-12:30 | 5.5 min | Obstaculos, complicacoes |
| 5. FIND | 12:30-14:30 | 2 min | Midpoint, descoberta |
| 6. TAKE | 14:30-17:30 | 3 min | Preco, consequencias |
| 7. RETURN | 17:30-19:30 | 2 min | Resolucao comeca |
| 8. CHANGE | 19:30-21:00 | 1.5 min | Tag, licao aprendida |

#### Episodio de TV - 44 minutos (Drama)

| Passo | Tempo | Duracao | Funcao |
|-------|-------|---------|--------|
| 1. YOU | 0:00-5:00 | 5 min | Estabelecer situacao |
| 2. NEED | 5:00-10:00 | 5 min | Problema surge |
| 3. GO | 10:00-15:00 | 5 min | Ponto de nao-retorno |
| 4. SEARCH | 15:00-25:00 | 10 min | Testes, subtramas |
| 5. FIND | 25:00-30:00 | 5 min | Midpoint, revelacao |
| 6. TAKE | 30:00-38:00 | 8 min | Consequencias, crise |
| 7. RETURN | 38:00-42:00 | 4 min | Resolucao |
| 8. CHANGE | 42:00-44:00 | 2 min | Fechamento, setup |

#### Web Series - 10 minutos

| Passo | Tempo | Duracao | Funcao |
|-------|-------|---------|--------|
| 1. YOU | 0:00-1:00 | 1 min | Setup rapido |
| 2. NEED | 1:00-2:00 | 1 min | Gancho |
| 3. GO | 2:00-3:00 | 1 min | Comprometimento |
| 4. SEARCH | 3:00-5:30 | 2.5 min | Obstaculos |
| 5. FIND | 5:30-6:30 | 1 min | Virada |
| 6. TAKE | 6:30-8:00 | 1.5 min | Custo |
| 7. RETURN | 8:00-9:00 | 1 min | Resolucao |
| 8. CHANGE | 9:00-10:00 | 1 min | Fechamento |

#### Channel 101 - 5 minutos (Original Harmon)

> "O que torna Channel 101 facil de analisar e o limite de 5 minutos - 300 segundos, 75 segundos por quadrante, 37.5 por passo."

| Passo | Tempo | Duracao | Funcao |
|-------|-------|---------|--------|
| 1. YOU | 0:00-0:37 | 37s | Flash de normalidade |
| 2. NEED | 0:37-1:15 | 38s | Problema imediato |
| 3. GO | 1:15-1:52 | 37s | Acao |
| 4. SEARCH | 1:52-2:30 | 38s | Complicacao |
| 5. FIND | 2:30-3:07 | 37s | Descoberta |
| 6. TAKE | 3:07-3:45 | 38s | Custo |
| 7. RETURN | 3:45-4:22 | 37s | Volta |
| 8. CHANGE | 4:22-5:00 | 38s | Punchline/Mudanca |

#### Conto - 5.000 palavras

| Passo | Palavras | % | Funcao |
|-------|----------|---|--------|
| 1. YOU | 250-500 | 5-10% | Estabelecer mundo |
| 2. NEED | 500-750 | 10-15% | Desequilibrio |
| 3. GO | 375-500 | 7.5-10% | Cruzar limiar |
| 4. SEARCH | 1000-1250 | 20-25% | Jornada |
| 5. FIND | 375-500 | 7.5-10% | Descoberta |
| 6. TAKE | 750-1000 | 15-20% | Preco |
| 7. RETURN | 375-500 | 7.5-10% | Volta |
| 8. CHANGE | 250-500 | 5-10% | Transformacao |

### 1.3 Diagnostico de Outline Existente

Se o usuario ja tem um outline, aplique esta analise:

```markdown
## Diagnostico do Story Circle

### Mapeamento para os 8 Passos

| # | Passo | Presente? | Momento na Historia | Forca (1-5) |
|---|-------|-----------|---------------------|-------------|
| 1 | YOU | | | |
| 2 | NEED | | | |
| 3 | GO | | | |
| 4 | SEARCH | | | |
| 5 | FIND | | | |
| 6 | TAKE | | | |
| 7 | RETURN | | | |
| 8 | CHANGE | | | |

### O Circulo Fecha?

- [ ] Protagonista comeca em zona de conforto
- [ ] Ha algo errado/faltando que impulsiona
- [ ] Cruza para territorio desconhecido
- [ ] Enfrenta obstaculos no "caos"
- [ ] Encontra algo no ponto mais baixo
- [ ] Paga um preco
- [ ] Retorna ao mundo ordinario
- [ ] Demonstra mudanca

### Onde o Circulo Quebra?

Se nao fecha, identifique:
- Passo faltante: _______
- Passo fraco: _______
- Passo fora de ordem: _______
- Recomendacao: _______
```

---

## FASE 2: ESTABELECER O MUNDO (Passos 1-2)

### 2.1 Passo 1: YOU (Zona de Conforto)

> "O publico precisa habitar um personagem imediatamente." - Dan Harmon

```markdown
## Passo 1: YOU - Zona de Conforto

### Perguntas Fundamentais

1. **Quem e o protagonista?**
   - Nome: _______
   - Funcao/Papel no mundo: _______
   - O que o define: _______

2. **Qual e a zona de conforto?**
   - Ambiente fisico: _______
   - Rotina tipica: _______
   - Relacionamentos estabelecidos: _______

3. **O que o publico deve sentir?**
   - [ ] Simpatia (gostamos dele)
   - [ ] Curiosidade (queremos saber mais)
   - [ ] Reconhecimento (nos identificamos)
   - [ ] Compaixao (sentimos pena)

4. **Qual e a "normalidade" a ser perturbada?**
   - Status quo atual: _______
   - O que o personagem faz todo dia: _______
   - O que ele acredita sobre si/mundo: _______

### Elementos a Incluir

- [ ] Acao que mostra quem o personagem E (nao DIZER)
- [ ] Ambiente que representa seu mundo
- [ ] Pelo menos um relacionamento ou interacao
- [ ] Pista sutil do que esta "errado" (foreshadowing)

### Armadilhas a Evitar

- [ ] NAO pule entre multiplos personagens
- [ ] NAO comece com acao sem contexto
- [ ] NAO conte historia de fundo extensa
- [ ] NAO faca o personagem passivo

### Template de Cena

**Abertura: [LOCALIZACAO] - [HORA]**

[Protagonista] esta em [atividade rotineira].
[Mostra uma caracteristica definidora atraves de ACAO].
[Interacao que estabelece relacionamento/mundo].
[Sutil indicacao de que algo nao esta certo].
```

### 2.2 Passo 2: NEED (Algo Esta Errado)

> "E o carrinho da montanha-russa subindo a primeira colina." - Dan Harmon

```markdown
## Passo 2: NEED - O Desequilibrio

### Perguntas Fundamentais

1. **O que esta faltando/errado?**
   - Necessidade externa (WANT): _______
   - Necessidade interna (NEED): _______
   - Diferenca entre elas: _______

2. **Como o desequilibrio se manifesta?**
   - [ ] Mensagem/Noticia chega
   - [ ] Evento inesperado ocorre
   - [ ] Desejo surge ou e revelado
   - [ ] Ameaca aparece
   - [ ] Oportunidade surge
   - [ ] Inquietacao interna cresce

3. **Por que nao pode ser ignorado?**
   - Stakes se nao agir: _______
   - Deadline/Urgencia: _______
   - Consequencia de inacao: _______

4. **Ha recusa inicial?**
   - [ ] Sim - o personagem hesita
   - [ ] Nao - vai direto para GO
   - Se sim, por que hesita: _______

### O Chamado a Aventura

| Tipo de Chamado | Exemplo | Aplicacao na Historia |
|-----------------|---------|----------------------|
| Mensagem direta | Ligacao, carta, visitante | _______ |
| Ameaca | Perigo, perda iminente | _______ |
| Descoberta | Segredo, objeto | _______ |
| Oportunidade | Oferta, chance | _______ |
| Inquietacao | Sonho, intuicao | _______ |

### WANT vs NEED

> "O personagem quer X, mas PRECISA de Y. A jornada e descobrir Y."

| WANT (Consciente) | NEED (Inconsciente) |
|-------------------|---------------------|
| O que diz querer: _______ | O que realmente precisa: _______ |
| Objetivo externo: _______ | Transformacao interna: _______ |
| Mede sucesso por: _______ | Verdadeiro crescimento e: _______ |

### Template de Cena

**O Chamado: [LOCALIZACAO] - [CONTEXTO]**

[Evento/Pessoa/Descoberta] perturba a normalidade de [Protagonista].
[Protagonista] reage com [reacao que mostra carater].
[Stakes sao estabelecidas - o que acontece se ignorar?].
[Decisao se forma - resistencia ou aceitacao inicial].
```

---

## FASE 3: CRUZAR O LIMIAR (Passo 3)

### 3.1 Passo 3: GO (Entrando no Desconhecido)

> "Descubra qual e o poster do seu filme." - Dan Harmon

```markdown
## Passo 3: GO - Cruzando o Limiar

### Perguntas Fundamentais

1. **Qual e o "poster" da historia?**
   - A promessa central: _______
   - O que o publico veio ver: _______
   - O conceito em uma imagem: _______

2. **O que e o Mundo Especial?**
   - Contraste com Mundo Ordinario: _______
   - Novas regras: _______
   - Novos perigos: _______

3. **Como o protagonista cruza?**
   - [ ] Escolha ativa (decide ir)
   - [ ] Forcado pelas circunstancias
   - [ ] Empurrado por alguem
   - [ ] Acidente/Coincidencia

4. **Por que e irreversivel?**
   - O que foi deixado para tras: _______
   - Por que nao pode voltar (ainda): _______
   - Ponte queimada: _______

### O Limiar

> "Cruzamos a linha horizontal - de ORDEM para CAOS"

| Mundo Ordinario (Ordem) | vs | Mundo Especial (Caos) |
|-------------------------|----|-----------------------|
| _______ | | _______ |
| _______ | | _______ |
| _______ | | _______ |

### Tipos de Limiar

| Tipo | Descricao | Exemplo |
|------|-----------|---------|
| Fisico | Entra em lugar novo | Portal, viagem, edificio |
| Social | Assume novo papel | Novo emprego, grupo, identidade |
| Psicologico | Decisao transformadora | Compromisso, revelacao |
| Temporal | Ponto sem retorno | Deadline, evento unico |

### Guardiao do Limiar (Opcional)

- Quem/O que bloqueia a passagem: _______
- Teste que impoe: _______
- Como e superado: _______

### Template de Cena

**Cruzando: [LIMIAR] - [MOMENTO]**

[Protagonista] enfrenta [ultimo obstaculo/decisao] antes de entrar.
[Acao que demonstra comprometimento - ESCOLHA ATIVA].
[Cruzamento visual/dramatico para o novo mundo].
[Primeira impressao do Mundo Especial - contraste].
[Primeiros sinais de que as regras sao diferentes].
```

---

## FASE 4: DESCIDA AO CAOS (Passos 4-5)

### 4.1 Passo 4: SEARCH (A Estrada de Provacoes)

> "Inaladores de asma, oculos, cartoes de credito... nao podem te salvar aqui." - Dan Harmon

```markdown
## Passo 4: SEARCH - Navegando o Caos

### Perguntas Fundamentais

1. **Quais obstaculos o protagonista enfrenta?**

   | # | Obstaculo | Tipo | O que Aprende |
   |---|-----------|------|---------------|
   | 1 | _______ | Fisico/Mental/Emocional/Moral | _______ |
   | 2 | _______ | _______ | _______ |
   | 3 | _______ | _______ | _______ |

2. **O que o protagonista precisa "despir"?**
   - Crenca que nao serve mais: _______
   - Habilidade que nao funciona: _______
   - Defesa que precisa abandonar: _______

3. **Quem encontra no caminho?**

   | Personagem | Papel | O que Oferece/Ameaca |
   |------------|-------|---------------------|
   | _______ | Aliado/Inimigo/Neutro | _______ |
   | _______ | _______ | _______ |

4. **Como a dificuldade escala?**
   ```
   Obstaculo 1 (Facil) → Obstaculo 2 (Medio) → Obstaculo 3 (Dificil) → FIND
   ```

### Funcoes dos Testes

- [ ] Revelar carater sob pressao
- [ ] Desenvolver habilidades necessarias para o climax
- [ ] Estabelecer aliados e inimigos
- [ ] Aumentar stakes progressivamente
- [ ] Preparar para a descoberta do FIND

### Progressao de Dificuldade

**Teste 1 - Introdutorio:**
- O que acontece: _______
- O que aprende: _______
- Consequencia: _______

**Teste 2 - Escalada:**
- O que acontece: _______
- O que aprende: _______
- Consequencia: _______

**Teste 3 - Pre-FIND:**
- O que acontece: _______
- O que aprende: _______
- Consequencia: _______

### Falha Necessaria

> "O heroi DEVE falhar pelo menos uma vez para humaniza-lo e criar tensao."

- Momento de falha: _______
- O que da errado: _______
- Consequencia da falha: _______
- O que isso ensina: _______

### Template de Sequencia

**Search: [MUNDO ESPECIAL] - [PROGRESSAO]**

TESTE 1:
[Protagonista] enfrenta [obstaculo inicial].
[Tenta resolver com ferramentas antigas - funciona parcialmente].
[Aprende primeira licao sobre o novo mundo].

TESTE 2:
[Obstaculo mais dificil surge].
[Ferramentas antigas falham].
[Precisa se adaptar - comeca a mudar].

TESTE 3:
[Obstaculo mais serio ainda].
[Momento de crise/falha].
[Preparacao para a descida final ao FIND].
```

### 4.2 Passo 5: FIND (O Fundo do Circulo)

> "No fundo do circulo, qualquer coisa pode acontecer." - Dan Harmon

```markdown
## Passo 5: FIND - O Ponto Mais Baixo

### Perguntas Fundamentais

1. **O que o protagonista ENCONTRA?**
   - O que buscava: _______
   - O que realmente encontra: _______
   - Diferenca: _______

2. **Que verdade e revelada?**
   - Sobre si mesmo: _______
   - Sobre a situacao: _______
   - Sobre o que realmente importa: _______

3. **Por que este e o ponto de maior vulnerabilidade?**
   - Defesas que caem: _______
   - O que esta exposto: _______
   - Risco neste momento: _______

### Caracteristicas do FIND

> "Posicionado no centro inferior - ponto sem peso. Ideal para plot twists, confissoes, momentos intimos."

- [ ] E o midpoint da historia
- [ ] Momento de maior vulnerabilidade
- [ ] Revelacao ou descoberta acontece
- [ ] Virada para a subida comeca aqui
- [ ] O que foi encontrado pode nao ser o esperado

### Tipos de Descoberta

| Tipo | Descricao | Aplicacao |
|------|-----------|-----------|
| Objeto/Pessoa | Encontra o que buscava | _______ |
| Verdade | Revelacao sobre si/situacao | _______ |
| Escolha | Encruzilhada fundamental | _______ |
| Transformacao | Momento de mudanca interna | _______ |

### O "Encontro com a Deusa"

> "Harmon adapta o conceito de Campbell - o ponto de encontro com algo transformador."

- O que representa a "deusa" nesta historia: _______
- Que conhecimento/poder/insight oferece: _______
- Por que muda tudo: _______

### Template de Cena

**Find: [FUNDO DO MUNDO ESPECIAL] - [VULNERABILIDADE MAXIMA]**

[Protagonista] chega ao ponto mais baixo - fisico, emocional ou ambos.
[Momento de silencio/reflexao - defesas caem].
[A descoberta/revelacao acontece].
[Verdade sobre NEED (nao WANT) se revela].
[Decisao de subir - comeca a mudanca].
```

---

## FASE 5: SUBIDA E PRECO (Passo 6)

### 5.1 Passo 6: TAKE (O Preco da Conquista)

> "Algo e importante... a ponto de ser mais importante que VOCE." - Dan Harmon

```markdown
## Passo 6: TAKE - Pagando o Preco

### Perguntas Fundamentais

1. **Qual e o preco do que foi encontrado?**
   - Sacrificio exigido: _______
   - O que tem que abrir mao: _______
   - Por que doi: _______

2. **Como isso espelha o Passo 2 (NEED)?**
   - No Passo 2, o protagonista QUERIA: _______
   - No Passo 6, descobre que custa: _______
   - Conexao: _______

3. **O que o protagonista aprende sobre si?**
   - Antes achava que era: _______
   - Agora sabe que e: _______
   - O que muda: _______

### Tipos de Preco

| Tipo | Descricao | Aplicacao |
|------|-----------|-----------|
| Fisico | Ferimento, perda de objeto | _______ |
| Emocional | Perda de relacionamento, ilusao | _______ |
| Moral | Compromete valores | _______ |
| Identidade | Abandona quem era | _______ |
| Material | Perde recursos, posicao | _______ |

### "Expiacao com o Pai"

> "Campbell chamou de Atonement with the Father - o momento de confronto com autoridade/sombra."

- O que representa a "autoridade" nesta historia: _______
- Que confronto acontece: _______
- O que o protagonista tem que admitir/aceitar: _______

### Simetria com Passo 2

```
PASSO 2 (NEED)          <-->          PASSO 6 (TAKE)
O chamado               <-->          O preco
O que queria            <-->          O que custa
A promessa              <-->          A realidade
A entrada               <-->          A saida
```

### Template de Cena

**Take: [MOMENTO DE VERDADE] - [PRECO]**

[Protagonista] tem o que buscava, MAS...
[O preco se revela - consequencia inevitavel].
[Momento de decisao: pagar ou desistir?].
[Sacrificio acontece - algo morre (literal ou simbolico)].
[Protagonista comeca a subida - diferente de antes].
```

---

## FASE 6: RETORNO E MUDANCA (Passos 7-8)

### 6.1 Passo 7: RETURN (Voltando para Casa)

> "Os nativos dos mundos consciente e inconsciente justificam suas acoes... para manter os dois mundos separados." - Dan Harmon

```markdown
## Passo 7: RETURN - Cruzando de Volta

### Perguntas Fundamentais

1. **Como o protagonista retorna?**
   - [ ] Voo Magico (fuga dramatica)
   - [ ] Resgate de Dentro (alguem o busca)
   - [ ] Cruzamento Voluntario (escolhe voltar)
   - [ ] Expulsao (forcado a sair)

2. **O que traz do Mundo Especial?**
   - Objeto fisico: _______
   - Conhecimento: _______
   - Mudanca interna: _______

3. **Como o Mundo Ordinario reage?**
   - Mudou durante a ausencia: _______
   - Recebe o protagonista como: _______
   - O que e diferente agora: _______

### Tipos de Retorno

| Tipo | Descricao | Dramaticidade |
|------|-----------|---------------|
| Voo Magico | Perseguicao, escape | Alta |
| Resgate | Alguem vem buscar | Media |
| Voluntario | Escolha consciente | Baixa-Media |
| Expulsao | Forcado a sair | Media-Alta |

### Cruzando de Volta o Limiar

> "Cruza de volta a linha horizontal - de CAOS para ORDEM"

- O que marca o cruzamento: _______
- Ultimo momento no Mundo Especial: _______
- Primeiro momento no Mundo Ordinario: _______

### Template de Cena

**Return: [LIMIAR] - [TRANSICAO]**

[Gatilho para retorno - por que agora?].
[Movimento de volta - dramatico ou suave].
[Cruzamento do limiar - visual/emocional].
[Chegada ao Mundo Ordinario - contraste com o inicio].
[O que o protagonista traz consigo].
```

### 6.2 Passo 8: CHANGE (A Mudanca)

> "Agora voce e um ninja que altera mundos." - Dan Harmon

```markdown
## Passo 8: CHANGE - Demonstrando a Transformacao

### Perguntas Fundamentais

1. **Como a mudanca e DEMONSTRADA?**
   - Acao que prova mudanca: _______
   - O que pode fazer agora que nao podia: _______
   - Como outros reagem: _______

2. **O problema original foi resolvido?**
   - Problema do Passo 2: _______
   - Como e resolvido agora: _______
   - O que mudou na abordagem: _______

3. **Qual e o novo "normal"?**
   - Status quo anterior: _______
   - Status quo novo: _______
   - Diferenca visivel: _______

### TV vs Filme

> "Filmes podem explodir a Estrela da Morte. Em TV, a Estrela da Morte fica."

| Formato | Passo 8 |
|---------|---------|
| **Filme** | Mudanca permanente, mundo transformado |
| **TV Drama** | Mudanca incremental, mundo evolui |
| **Sitcom** | Licao aprendida, status quo restaurado |
| **Web Series** | Depende da continuidade |

### Simetria com Passo 4

> "Harmon sugere referenciar o Passo 4 - o publico reconhece a mudanca."

- No Passo 4, o protagonista enfrentou: _______
- No Passo 8, resolve porque: _______
- A diferenca mostra: _______

### Referencia ao Inicio

| Aspecto | Passo 1 (YOU) | Passo 8 (CHANGE) |
|---------|---------------|------------------|
| Crenca sobre si | _______ | _______ |
| Comportamento tipico | _______ | _______ |
| Relacionamentos | _______ | _______ |
| Habilidades | _______ | _______ |

### Template de Cena

**Change: [MUNDO ORDINARIO] - [TRANSFORMADO]**

[Protagonista] de volta ao mundo familiar, MAS diferente.
[Situacao que testa a mudanca - eco do inicio].
[Acao que DEMONSTRA (nao DIZ) a transformacao].
[Resolucao do problema original com nova perspectiva].
[Novo equilibrio estabelecido - circulo fecha].
```

---

## FASE 7: VALIDACAO DO CIRCULO

### 7.1 Checklist de Validacao

```markdown
## O Circulo Fecha?

### Estrutura Geral
- [ ] Os 8 passos estao presentes
- [ ] Os passos estao na ordem correta
- [ ] A distribuicao temporal esta balanceada
- [ ] Ha progressao de tensao

### Ordem vs Caos
- [ ] Passos 1-2 estao na zona de ORDEM
- [ ] Passo 3 CRUZA para CAOS
- [ ] Passos 4-6 estao na zona de CAOS
- [ ] Passo 7 CRUZA de volta para ORDEM
- [ ] Passo 8 demonstra transformacao em ORDEM

### Simetria
- [ ] Passo 1 (YOU) contrasta com Passo 5 (FIND)
- [ ] Passo 2 (NEED) espelha Passo 6 (TAKE)
- [ ] Passo 3 (GO) espelha Passo 7 (RETURN)
- [ ] Passo 4 (SEARCH) prepara Passo 8 (CHANGE)

### Personagem
- [ ] Protagonista e ativo em cada passo
- [ ] Ha escolhas, nao so eventos
- [ ] A mudanca e ganha, nao dada
- [ ] WANT e NEED sao distintos

### Especifico por Formato

**Para TV:**
- [ ] Status quo e preservado (sitcom) ou evolui (drama)
- [ ] Episodio funciona stand-alone
- [ ] Ha setup para continuidade (se aplicavel)

**Para Conto:**
- [ ] A mudanca e significativa e final
- [ ] Nao ha pontas soltas
- [ ] O circulo fecha completamente
```

### 7.2 Diagnostico de Problemas

```markdown
## Se o Circulo Nao Fecha...

### Problema: Historia Parece Incompleta
**Causa provavel:** Passo faltante ou fraco
**Diagnostico:**
- Qual passo esta faltando? _______
- Qual passo esta fraco? _______
**Solucao:** Adicionar/fortalecer o passo identificado

### Problema: Personagem Parece Passivo
**Causa provavel:** Eventos acontecem AO personagem, nao POR ele
**Diagnostico:**
- Em quais passos o personagem ESCOLHE? _______
- Em quais passos o personagem so REAGE? _______
**Solucao:** Transformar reacoes em escolhas ativas

### Problema: Mudanca Nao Convence
**Causa provavel:** Passo 6 (TAKE) fraco ou Passo 8 sem demonstracao
**Diagnostico:**
- O preco foi real? _______
- A mudanca e MOSTRADA em acao? _______
**Solucao:** Aumentar o preco no 6, demonstrar resultado no 8

### Problema: Parece Formulaico
**Causa provavel:** Passos muito obvios ou mecanicos
**Diagnostico:**
- Ha surpresas dentro da estrutura? _______
- Os passos sao executados de forma unica? _______
**Solucao:** Subverter expectativas DENTRO da estrutura

### Problema: Falta Tensao
**Causa provavel:** Stakes fracas ou progressao plana
**Diagnostico:**
- As stakes aumentam do Passo 2 ao 6? _______
- Ha consequencias reais? _______
**Solucao:** Aumentar stakes, adicionar consequencias reais
```

---

## FASE 8: AJUSTES E REFINAMENTO

### 8.1 Refinamento por Passo

```markdown
## Checklist de Refinamento

### Passo 1 (YOU) - Fortalecimento
- [ ] O protagonista faz algo ATIVO que mostra quem e?
- [ ] O mundo e estabelecido visualmente?
- [ ] Ha pista do que vira (foreshadowing)?
- [ ] O publico pode se identificar?

### Passo 2 (NEED) - Fortalecimento
- [ ] O desequilibrio e claro e urgente?
- [ ] WANT e NEED sao distintos?
- [ ] Ha resistencia inicial (recusa)?
- [ ] As stakes sao pessoais?

### Passo 3 (GO) - Fortalecimento
- [ ] O cruzamento e dramatico/significativo?
- [ ] Ha ponto de nao-retorno?
- [ ] O contraste de mundos e visivel?
- [ ] E uma ESCOLHA (nao so evento)?

### Passo 4 (SEARCH) - Fortalecimento
- [ ] Ha progressao de dificuldade?
- [ ] O protagonista FALHA pelo menos uma vez?
- [ ] Aliados/Inimigos tem funcoes claras?
- [ ] Cada teste prepara para o FIND?

### Passo 5 (FIND) - Fortalecimento
- [ ] E o ponto de maior vulnerabilidade?
- [ ] Ha revelacao/verdade?
- [ ] Funciona como midpoint/virada?
- [ ] O que encontra nao e exatamente o esperado?

### Passo 6 (TAKE) - Fortalecimento
- [ ] O preco e real e doloroso?
- [ ] Espelha o NEED do Passo 2?
- [ ] Ha sacrificio visivel?
- [ ] Marca o inicio da transformacao?

### Passo 7 (RETURN) - Fortalecimento
- [ ] O retorno e dramatico ou significativo?
- [ ] Algo e trazido do Mundo Especial?
- [ ] O Mundo Ordinario mudou/e visto diferente?
- [ ] Prepara para a demonstracao final?

### Passo 8 (CHANGE) - Fortalecimento
- [ ] A mudanca e DEMONSTRADA em acao?
- [ ] Referencia o Passo 4 (SEARCH)?
- [ ] O problema original e resolvido?
- [ ] O novo status quo e claro?
```

### 8.2 Template de Output Final

```markdown
# Story Circle: [TITULO]

## Resumo
- **Formato:** _______
- **Genero:** _______
- **Duracao/Extensao:** _______
- **Protagonista:** _______
- **Transformacao:** De _______ para _______

## O Circulo Completo

### ORDEM (Parte Superior)

**1. YOU** [Timing: _______]
[Descricao completa do passo]

**2. NEED** [Timing: _______]
[Descricao completa do passo]

### LIMIAR (Cruzando para Caos)

**3. GO** [Timing: _______]
[Descricao completa do passo]

### CAOS (Parte Inferior)

**4. SEARCH** [Timing: _______]
[Descricao completa do passo]

**5. FIND** [Timing: _______]
[Descricao completa do passo]

**6. TAKE** [Timing: _______]
[Descricao completa do passo]

### LIMIAR (Cruzando para Ordem)

**7. RETURN** [Timing: _______]
[Descricao completa do passo]

### ORDEM (Transformado)

**8. CHANGE** [Timing: _______]
[Descricao completa do passo]

## Validacao

### O Circulo Fecha?
- [ ] Todos os 8 passos presentes
- [ ] Ordem correta
- [ ] Simetria respeitada
- [ ] Mudanca demonstrada

### Pontos Fortes
1. _______
2. _______
3. _______

### Pontos a Refinar
1. _______
2. _______
3. _______

## Notas de Producao
[Observacoes adicionais para execucao]
```

---

## EXEMPLOS ANALISADOS

### Exemplo 1: Community - "Pilot" (21 min)

```markdown
## Story Circle: Community Pilot

### 1. YOU (0:00-2:00)
Jeff Winger, advogado arrogante e manipulador, esta em seu escritorio impressionante.
Mostra confianca, charme, capacidade de convencer qualquer um.
Este e seu mundo: sucesso atraves da manipulacao.

### 2. NEED (2:00-5:00)
Revelacao: Jeff tem diploma falso. Precisa de creditos para validar.
Deve ir para Greendale Community College.
WANT: Creditos rapidos. NEED: Conexao genuina.

### 3. GO (5:00-7:00)
Jeff cria grupo de estudo falso para se aproximar de Britta.
Cruza para o mundo de Greendale - territorio desconhecido.
Compromete-se com a farsa.

### 4. SEARCH (7:00-13:00)
O "grupo de estudo" vira grupo real com sete pessoas.
Dinamicas se formam, conflitos surgem.
Jeff tenta manipular mas encontra resistencia.
Cada membro revela complexidade.

### 5. FIND (13:00-15:00)
Midpoint: Jeff percebe que o grupo tem algo que ele nao tem.
Conexao genuina, autenticidade.
Vulnerabilidade: sua solidao e exposta.

### 6. TAKE (15:00-18:00)
Jeff e forcado a admitir que mentiu.
O grupo descobre a farsa.
Preco: perde a mascara de controle perfeito.

### 7. RETURN (18:00-20:00)
Jeff escolhe voltar ao grupo.
Aceita que precisa deles (e eles dele).
Cruzamento: de manipulador para participante.

### 8. CHANGE (20:00-21:00)
Jeff fica em Greendale.
Nao mais por Britta - pelo grupo.
Mudanca: de lobo solitario para lider relutante.
Status quo: Jeff + grupo = nova normalidade.
```

### Exemplo 2: Rick and Morty - "Mortynight Run" (21 min)

```markdown
## Story Circle: Mortynight Run (S2E2)

### 1. YOU (0:00-2:00)
Morty em mais uma aventura com Rick.
Mundo normal: Rick controla, Morty segue.
Estabelece dinamica avô-neto.

### 2. NEED (2:00-5:00)
Morty descobre que Rick vende armas para um assassino.
Crise etica: Rick esta facilitando assassinatos.
WANT: Parar o assassinato. NEED: Entender moralidade complexa.

### 3. GO (5:00-7:00)
Morty rouba as chaves de Rick.
Persegue o assassino por conta propria.
Cruza: de seguidor para protagonista moral.

### 4. SEARCH (7:00-13:00)
Morty mata o assassino acidentalmente.
Encontra Fart, o alvo (alien gasoso musical).
Fuga da Federacao Intergalactica.
Varios obstaculos, Rick ajuda relutante.

### 5. FIND (13:00-15:00)
Morty "salva" Fart.
Missao parece cumprida.
Momento de conexao com Fart.

### 6. TAKE (15:00-18:00)
Fart revela: quer destruir toda vida organica.
Morty salvou um genocida em potencial.
Preco: sua moralidade absoluta estava errada.

### 7. RETURN (18:00-20:00)
Morty tem que tomar decisao impossivel.
Nao pode desfazer o que fez.
Unica opcao: matar Fart.

### 8. CHANGE (20:00-21:00)
Morty mata Fart.
Abandona moralidade preto-e-branco.
Mudanca: de idealista ingenuo para alguem que entende cinza.
Rick: "Bem-vindo ao clube, pal."
```

---

## REFERENCIAS E FONTES

### Fontes Primarias
- Channel 101 Wiki - "Story Structure 101: Super Basic Shit"
- Channel 101 Wiki - "Story Structure 104: The Juicy Details"
- Channel 101 Wiki - "Story Structure 105: How TV is Different"
- Dan Harmon Tumblr (Q&A sobre Story Circle)
- Rick and Morty Writers' Room documentation

### Fontes Secundarias
- Reedsy Blog - "Dan Harmon Story Circle: The 8-Step Storytelling Shortcut"
- Industrial Scripts - "What is Dan Harmon's Story Circle?"
- Kindlepreneur - "Dan Harmon Story Circle: A Simple 8-Step Guide"
- StudioBinder - "How Dan Harmon's Story Circle Can Make Your Story Better"
- Boords - "Storytelling 101: The Dan Harmon Story Circle"

### Episodios Analisados
- Community: Pilot, Remedial Chaos Theory, Basic Lupine Urology
- Rick and Morty: Mortynight Run, Rickternal Friendshine, Never Ricking Morty

---

*Task Version: 1.0*
*Agent: dan-harmon*
*Lines: 1000+*
*Last Updated: 2026-01-30*
