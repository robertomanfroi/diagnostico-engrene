# apply-save-the-cat

```yaml
task:
  name: Apply Save the Cat
  id: apply-save-the-cat
  purpose: "Aplicar a metodologia Save the Cat! de Blake Snyder para criar estrutura narrativa comercial com os 15 beats"
  triggers:
    - "estruturar historia"
    - "criar beat sheet"
    - "aplicar save the cat"
    - "15 beats"
    - "estrutura de roteiro"

metadata:
  version: "1.0.0"
  created: "2026-01-30"
  estimated_time: "45-90 min"
  complexity: "medium-high"

dependencies:
  required_inputs:
    - "Conceito/premissa da historia (pode ser bruto)"
    - "Genero pretendido ou incerteza"
    - "Formato (screenplay 110p, novel, TV)"
  optional_inputs:
    - "Personagem principal definido"
    - "Antagonista definido"
    - "Tema pretendido"

outputs:
  primary:
    - "Beat sheet completo com timing"
    - "Logline com ironia"
  secondary:
    - "Genre identification"
    - "Six Things That Need Fixing"
    - "Board structure (40 cards)"
```

---

## Task Overview

Este task guia o usuario atraves da metodologia Save the Cat! de Blake Snyder para criar uma estrutura narrativa comercialmente viavel. O processo transforma uma ideia bruta em um beat sheet completo com 15 beats, timing preciso, e todos os elementos necessarios para uma historia que funciona.

**Filosofia Central:** "Estrutura nao e formula. Estrutura e o esqueleto que permite a historia ficar de pe." - Blake Snyder

---

## Workflow Completo

### Fase 1: Discovery e Conceito

#### Step 1.1: Capturar a Ideia Bruta

**Input necessario do usuario:**
```
1. Qual e a ideia central da sua historia?
   (Pode ser uma frase, paragrafo, ou conceito vago)

2. Qual o formato pretendido?
   [ ] Screenplay (110 paginas)
   [ ] Novel/Romance (especifique word count)
   [ ] Serie de TV (episodio piloto vs arco de temporada)
   [ ] Outro (especifique)

3. Qual o tom/genero tradicional?
   (comedia, drama, acao, terror, romance, etc.)
```

**Output esperado:**
- Conceito capturado em forma bruta
- Formato definido para calcular timing
- Tom geral identificado

---

#### Step 1.2: Criar a Logline

**Os 4 Requisitos da Logline (Snyder):**

1. **IRONIA** - O hook que cria a pergunta "Como isso vai funcionar?"
2. **MENTAL PICTURE** - Deve implicar toda a historia visualmente
3. **AUDIENCIA E CUSTO** - Tom e viabilidade comercial clara
4. **KILLER TITLE** - Par perfeito com a logline

**Template de Logline:**
```
"Um(a) [ADJETIVO] [TIPO DE HEROI] deve [OBJETIVO]
quando [SITUACAO que muda tudo],
mas [COMPLICACAO/OBSTACULO principal]."
```

**Processo de Criacao:**

1. **Identifique o Heroi:**
   - Quem e? (profissao, idade, situacao)
   - Qual adjetivo o define? (solitario, ambicioso, timido, rebelde)

2. **Identifique o Objetivo:**
   - O que o heroi QUER? (objetivo tangivel)
   - O que o heroi PRECISA? (objetivo espiritual - para B Story)

3. **Identifique a Situacao/Catalyst:**
   - O que muda tudo?
   - O que joga o heroi no Mundo Especial?

4. **Identifique a Complicacao:**
   - Quem/o que impede?
   - Qual o obstaculo principal?

5. **Teste de Ironia:**
   - A logline provoca "Como isso vai funcionar?"
   - Ha tensao inerente na premissa?

**Exemplos de Loglines Efetivas:**

| Filme | Logline | Ironia |
|-------|---------|--------|
| Die Hard | "Um policial de NY tenta salvar a esposa e outros de terroristas durante a festa de Natal da empresa dela" | Policial comum vs. terroristas treinados |
| Pretty Woman | "Um empresario se apaixona pela prostituta que contratou para ser sua acompanhante no fim de semana" | Amor improvavel entre classes opostas |
| Legally Blonde | "Uma patricinha loira decide entrar em Harvard Law para reconquistar o ex-namorado" | Estereotipo vs. instituicao seria |
| The Matrix | "Um hacker descobre que sua realidade e uma simulacao de computador e que ele pode ser 'o escolhido' para salvar a humanidade" | Realidade como mentira |

**Checklist de Logline:**
- [ ] Tem adjetivo para o heroi
- [ ] Objetivo e claro e identificavel
- [ ] Situacao/catalyst muda tudo
- [ ] Complicacao cria tensao
- [ ] Ha ironia que fisga
- [ ] Cria mental picture da historia
- [ ] Tom e claro (comedia, drama, etc.)

---

#### Step 1.3: Identificar o Genero (Snyder)

**Os 10 Generos de Snyder:**

| Genero | Elementos Obrigatorios | Pergunta-Chave |
|--------|------------------------|----------------|
| **Monster in the House** | Monstro + Casa (espaco confinado) + Pecado | Ha uma ameaca presa com o heroi? |
| **Golden Fleece** | Estrada + Time + Premio | E uma jornada com objetivo? |
| **Out of the Bottle** | Desejo + Magia + Licao | Ha elemento sobrenatural/magico? |
| **Dude with a Problem** | Heroi Inocente + Evento Subito + Vida/Morte | Pessoa comum em perigo extremo? |
| **Rites of Passage** | Problema de Vida + Abordagem Errada + Aceitacao | E sobre transicao de vida? |
| **Buddy Love** | Heroi Incompleto + Contraparte + Complicacao | Dois personagens que se completam? |
| **Whydunit** | Detetive + Segredo + Virada Sombria | E investigacao sobre natureza humana? |
| **Fool Triumphant** | Tolo + Establishment + Transmutacao | Underdog vs. sistema? |
| **Institutionalized** | Grupo + Escolha + Sacrificio | Individuo vs. instituicao? |
| **Superhero** | Poder Especial + Nemesis + Maldicao | Heroi extraordinario? |

**Processo de Identificacao:**

1. Leia a logline criada
2. Responda cada pergunta-chave acima
3. Identifique qual genero tem mais "sim"
4. Verifique se os 3 elementos obrigatorios estao presentes
5. Se elementos faltam, considere adiciona-los

**Output:**
```
GENERO IDENTIFICADO: [Nome do Genero]

Elementos Presentes:
- [Elemento 1]: [Como aparece na historia]
- [Elemento 2]: [Como aparece na historia]
- [Elemento 3]: [Como aparece na historia]

Elementos a Desenvolver:
- [Se algum elemento esta fraco, como fortalecer]
```

---

### Fase 2: Construcao dos Personagens

#### Step 2.1: Definir o Protagonista

**Template de Protagonista:**

```
PROTAGONISTA
Nome: _______________
Idade/Fase: _______________
Ocupacao/Situacao: _______________

ARCO DE TRANSFORMACAO
Estado Inicial (Opening Image): _______________
Estado Final (Final Image): _______________
O que precisa aprender (Tema): _______________

MOTIVACOES
O que QUER (objetivo tangivel): _______________
O que PRECISA (objetivo espiritual): _______________
Por que NAO consegue sozinho: _______________

SAVE THE CAT MOMENT
(Cena que faz audiencia amar o heroi no Ato 1)
Ideia: _______________
```

**Regra Save the Cat:**
O heroi DEVE fazer algo no primeiro ato que faca a audiencia torcer por ele. Mesmo anti-herois precisam disso.

**Exemplos de Save the Cat Moments:**
- Aladdin: Divide comida roubada com criancas famintas
- Indiana Jones: Enfrenta perigo para salvar artefato
- Elle Woods: Demonstra bondade genuina apesar da aparencia superficial

---

#### Step 2.2: Definir o Antagonista/Forca Opositora

**Template de Antagonista:**

```
ANTAGONISTA/FORCA OPOSITORA
Quem/O que: _______________
Relacao com protagonista: _______________

POR QUE E AMEACA
Poder/Vantagem: _______________
Por que o heroi nao pode simplesmente vencer: _______________

CONEXAO COM TEMA
Como o antagonista representa o oposto do tema: _______________
```

---

#### Step 2.3: Definir o Personagem B Story

**Template B Story:**

```
PERSONAGEM B STORY
Nome: _______________
Tipo: [ ] Love Interest [ ] Mentor [ ] Amigo [ ] Rival [ ] Familiar

FUNCAO TEMATICA
Como ajuda heroi a aprender a licao: _______________
O que representa (novo mundo/nova forma de pensar): _______________

RELACAO COM A STORY
Como A e B Story se conectam no Break into Three: _______________
```

---

#### Step 2.4: Six Things That Need Fixing

**Template:**

```
SIX THINGS THAT NEED FIXING
(Estabelecer no Set-Up, pagar no Finale)

1. FALHA DE CARATER:
   Setup: _______________
   Payoff: _______________

2. NECESSIDADE NAO ATENDIDA:
   Setup: _______________
   Payoff: _______________

3. DESEJO NAO REALIZADO:
   Setup: _______________
   Payoff: _______________

4. INIMIGO/RIVAL:
   Setup: _______________
   Payoff: _______________

5. ALGO FALTANDO NA VIDA:
   Setup: _______________
   Payoff: _______________

6. PROBLEMA A SER RESOLVIDO:
   Setup: _______________
   Payoff: _______________
```

**Regra:** Cada item plantado no Set-Up deve ter payoff satisfatorio depois. Audiencia ama call-backs.

---

### Fase 3: Construcao do Beat Sheet

#### Step 3.1: Calcular Timing

**Para Screenplay (110 paginas):**
```
Beat 1  - Opening Image:      Pagina 1      (1%)
Beat 2  - Theme Stated:       Pagina 5      (5%)
Beat 3  - Set-Up:             Paginas 1-10  (1-10%)
Beat 4  - Catalyst:           Pagina 12     (10-12%)
Beat 5  - Debate:             Paginas 12-25 (12-25%)
Beat 6  - Break into Two:     Pagina 25     (25%)
Beat 7  - B Story:            Pagina 30     (30%)
Beat 8  - Fun and Games:      Paginas 30-55 (30-55%)
Beat 9  - Midpoint:           Pagina 55     (50%)
Beat 10 - Bad Guys Close In:  Paginas 55-75 (55-75%)
Beat 11 - All Is Lost:        Pagina 75     (75%)
Beat 12 - Dark Night:         Paginas 75-85 (75-85%)
Beat 13 - Break into Three:   Pagina 85     (85%)
Beat 14 - Finale:             Paginas 85-110 (85-99%)
Beat 15 - Final Image:        Pagina 110    (100%)
```

**Para Novel (adaptar por word count):**
```
Exemplo: 80.000 palavras

Beat 1  - Opening Image:      0-800 palavras         (1%)
Beat 2  - Theme Stated:       4.000 palavras         (5%)
Beat 3  - Set-Up:             0-8.000 palavras       (1-10%)
Beat 4  - Catalyst:           8.000-9.600 palavras   (10-12%)
Beat 5  - Debate:             9.600-20.000 palavras  (12-25%)
Beat 6  - Break into Two:     20.000 palavras        (25%)
Beat 7  - B Story:            24.000 palavras        (30%)
Beat 8  - Fun and Games:      24.000-44.000 palavras (30-55%)
Beat 9  - Midpoint:           40.000 palavras        (50%)
Beat 10 - Bad Guys Close In:  44.000-60.000 palavras (55-75%)
Beat 11 - All Is Lost:        60.000 palavras        (75%)
Beat 12 - Dark Night:         60.000-68.000 palavras (75-85%)
Beat 13 - Break into Three:   68.000 palavras        (85%)
Beat 14 - Finale:             68.000-79.200 palavras (85-99%)
Beat 15 - Final Image:        80.000 palavras        (100%)
```

**Formula Universal:**
```
Posicao do Beat = [Total] x [Porcentagem]
```

---

#### Step 3.2: Preencher os 15 Beats

**BEAT SHEET TEMPLATE COMPLETO:**

---

##### ATO 1 - TESE (25%)

**BEAT 1: Opening Image (1%)**
```
Timing: _______________
Descricao da Cena:
_______________________________________________

O que mostra:
- [ ] Estado "antes" do protagonista
- [ ] Tom da historia
- [ ] Mood e atmosfera
- [ ] Escopo visual

Como espelha o Final Image:
_______________________________________________
```

---

**BEAT 2: Theme Stated (5%)**
```
Timing: _______________
Descricao da Cena:
_______________________________________________

Quem fala o tema: _______________
Fala/Momento: "_______________________________________________"

Checklist:
- [ ] Personagem secundario fala
- [ ] Heroi NAO entende ainda
- [ ] E sutil, nao "na cara"
- [ ] Planta a semente da licao
```

---

**BEAT 3: Set-Up (1-10%)**
```
Timing: _______________

MUNDO ORDINARIO DO HEROI:
_______________________________________________

PERSONAGENS INTRODUZIDOS:
- A Story: _______________
- Antagonista (hint): _______________
- Suporte: _______________

SIX THINGS THAT NEED FIXING PLANTADAS:
1. _______________
2. _______________
3. _______________
4. _______________
5. _______________
6. _______________

SAVE THE CAT MOMENT:
Cena: _______________________________________________
Por que faz audiencia amar heroi: _______________

Checklist:
- [ ] Mundo ordinario claro
- [ ] Todos personagens principais introduzidos
- [ ] Six Things plantadas
- [ ] Save the Cat moment presente
- [ ] Stasis = Death implicitoTO (heroi precisa mudar)
```

---

**BEAT 4: Catalyst (10-12%)**
```
Timing: _______________
Descricao da Cena:
_______________________________________________

O QUE ACONTECE:
_______________________________________________

POR QUE MUDA TUDO:
_______________________________________________

Checklist:
- [ ] E um EVENTO, nao decisao do heroi
- [ ] Impossivel voltar a vida normal
- [ ] Mundo virou de cabeca pra baixo
- [ ] Claro e dramatico
```

---

**BEAT 5: Debate (12-25%)**
```
Timing: _______________

QUESTAO QUE O HEROI SE FAZ:
"_______________________________________________?"

COMO O HEROI RESISTE:
_______________________________________________

O QUE O HEROI FAZE DURANTE O DEBATE:
- _______________
- _______________
- _______________

ULTIMA CHANCE DE VER O MUNDO ANTIGO:
_______________________________________________

Checklist:
- [ ] Heroi mostra relutancia
- [ ] Questao e clara
- [ ] Busca conselho/informacao
- [ ] Mostra o que sera perdido
```

---

**BEAT 6: Break into Two (25%)**
```
Timing: _______________
Descricao da Cena:
_______________________________________________

A ESCOLHA QUE O HEROI FAZ:
_______________________________________________

COMO ENTRA NO MUNDO ESPECIAL:
_______________________________________________

Checklist:
- [ ] E uma ESCOLHA ativa do heroi
- [ ] Nao e empurrado, decide ir
- [ ] Marca fim do Ato 1
- [ ] Frequentemente mudanca de locacao
- [ ] Nao ha volta
```

---

##### ATO 2 - ANTITESE (50%)

**BEAT 7: B Story (30%)**
```
Timing: _______________

PERSONAGEM B STORY INTRODUZIDO:
Nome: _______________
Tipo: _______________

CENA DE INTRODUCAO:
_______________________________________________

COMO CARREGA O TEMA:
_______________________________________________

COMO VAI AJUDAR HEROI A APRENDER A LICAO:
_______________________________________________

Checklist:
- [ ] Personagem novo ou em novo papel
- [ ] Representa o tema
- [ ] Contraste com mundo antigo do heroi
- [ ] Conexao emocional estabelecida
```

---

**BEAT 8: Fun and Games (30-55%)**
```
Timing: _______________

A PROMESSA DA PREMISSA:
(O que o trailer mostraria)
_______________________________________________

HEROI ESTA:
[ ] Brilhando no novo mundo
[ ] Lutando no novo mundo

SEQUENCIAS PRINCIPAIS:

Sequencia 1:
_______________________________________________

Sequencia 2:
_______________________________________________

Sequencia 3:
_______________________________________________

CONFLITOS (mesmo em "fun"):
_______________________________________________

Checklist:
- [ ] Entrega a promessa da premissa
- [ ] Mais leve/diferente em tom (nao drama pesado ainda)
- [ ] Heroi testando o novo mundo
- [ ] Ainda tem conflito em cada cena
- [ ] Nao e "filler" - avanca historia
```

---

**BEAT 9: Midpoint (50%)**
```
Timing: _______________
Descricao da Cena:
_______________________________________________

TIPO:
[ ] Falsa Vitoria (parece que ganhou, mas...)
[ ] Falsa Derrota (parece que perdeu, mas...)

O QUE ACONTECE:
_______________________________________________

COMO AS STAKES SOBEM:
_______________________________________________

TICKING CLOCK INTRODUZIDO (se aplicavel):
_______________________________________________

CONEXAO COM ALL IS LOST:
(Midpoint e All Is Lost sao opostos emocionais)
Se Midpoint e alto, All Is Lost sera: _______________
Se Midpoint e baixo, All Is Lost sera: _______________

Checklist:
- [ ] Exatamente no meio da historia
- [ ] Falsa vitoria OU falsa derrota
- [ ] Stakes sobem significativamente
- [ ] Muda o jogo da segunda metade
- [ ] Ticking clock (se aplicavel)
```

---

**BEAT 10: Bad Guys Close In (55-75%)**
```
Timing: _______________

PRESSAO EXTERNA:
(Antagonista/forcas externas)
_______________________________________________

PRESSAO INTERNA:
(Duvidas, falhas do heroi, time se desintegrando)
_______________________________________________

SEQUENCIA DE DETERIORACAO:

Evento 1 (coisas pioram):
_______________________________________________

Evento 2 (pioram mais):
_______________________________________________

Evento 3 (quase insuportavel):
_______________________________________________

Checklist:
- [ ] Consequencias do Midpoint
- [ ] Antagonista reagrupa/ataca
- [ ] Falhas internas do heroi voltam
- [ ] Time/aliados sob pressao
- [ ] Progressao clara de mal a pior
```

---

**BEAT 11: All Is Lost (75%)**
```
Timing: _______________
Descricao da Cena:
_______________________________________________

O PONTO MAIS BAIXO:
_______________________________________________

WHIFF OF DEATH:
Tipo: [ ] Morte literal [ ] Morte metaforica

O que morre:
[ ] Personagem (mentor, amigo)
[ ] Sonho/esperanca
[ ] Relacionamento
[ ] Identidade ("Quem sou eu sem isso?")
[ ] Inocencia
[ ] Outro: _______________

Descricao:
_______________________________________________

OPOSTO DO MIDPOINT:
Se Midpoint foi vitoria falsa, agora e: _______________
Se Midpoint foi derrota falsa, agora e: _______________

Checklist:
- [ ] Ponto mais baixo absoluto
- [ ] Whiff of Death presente
- [ ] Parece que nao ha saida
- [ ] Mundo antigo/forma antiga de pensar MORRE
- [ ] Oposto emocional do Midpoint
```

---

**BEAT 12: Dark Night of the Soul (75-85%)**
```
Timing: _______________

O QUE O HEROI SENTE:
_______________________________________________

COMO PROCESSA O ALL IS LOST:
_______________________________________________

A PERGUNTA QUE SE FAZ:
(Diferente do Debate - agora e sobre SI MESMO)
"_______________________________________________?"

A REALIZACAO QUE COMECA A SURGIR:
_______________________________________________

Checklist:
- [ ] Heroi processa emocionalmente
- [ ] Diferente de Debate (era sobre situacao, agora sobre SI)
- [ ] Reflexao sobre como chegou aqui
- [ ] Semente da solucao comeca a germinar
- [ ] Escuridao antes do amanhecer
```

---

##### ATO 3 - SINTESE (25%)

**BEAT 13: Break into Three (85%)**
```
Timing: _______________
Descricao da Cena:
_______________________________________________

A EPIFANIA:
O que o heroi finalmente entende:
_______________________________________________

COMO A + B STORY SE UNEM:
_______________________________________________

A NOVA INFORMACAO/INSIGHT:
(Frequentemente vem do personagem B Story)
_______________________________________________

O NOVO PLANO:
_______________________________________________

Checklist:
- [ ] Momento "eureka" claro
- [ ] A Story e B Story se conectam
- [ ] Heroi entende o que precisa fazer
- [ ] Usa o que aprendeu
- [ ] Decide agir
```

---

**BEAT 14: Finale (85-99%)**
```
Timing: _______________

FIVE-POINT FINALE:

1. GATHERING THE TEAM:
(Heroi reune aliados, recursos)
_______________________________________________

2. EXECUTING THE PLAN:
(Tentativa inicial)
_______________________________________________

3. HIGH TOWER SURPRISE:
(Complicacao no pior momento possivel)
_______________________________________________

4. DIG DEEP DOWN:
(Heroi encontra forca interior, usa o que aprendeu)
_______________________________________________

5. EXECUTION OF NEW PLAN:
(Vitoria usando a licao aprendida)
_______________________________________________

CONFRONTO FINAL:
_______________________________________________

COMO O HEROI MUDA O MUNDO:
_______________________________________________

SIX THINGS PAYOFFS:
1. _______________ → Payoff: _______________
2. _______________ → Payoff: _______________
3. _______________ → Payoff: _______________
4. _______________ → Payoff: _______________
5. _______________ → Payoff: _______________
6. _______________ → Payoff: _______________

Checklist:
- [ ] Five-Point structure presente
- [ ] Heroi usa licao aprendida
- [ ] Vilao/obstaculo derrotado
- [ ] Mundo transformado
- [ ] Six Things pagas
```

---

**BEAT 15: Final Image (100%)**
```
Timing: _______________
Descricao da Cena:
_______________________________________________

COMO ESPELHA OPENING IMAGE:
Opening Image mostrava: _______________
Final Image mostra: _______________

A TRANSFORMACAO:
_______________________________________________

Checklist:
- [ ] Espelha Opening Image
- [ ] Mostra transformacao completa
- [ ] Estado "depois" claro
- [ ] Satisfacao emocional
- [ ] Prova que jornada valeu
```

---

### Fase 4: The Board (40 Cartoes)

#### Step 4.1: Estruturar o Board

**Layout Visual:**
```
FILEIRA 1 - ATO 1 (Paginas 1-25)
[1][2][3][4][5][6][7][8][9][10]

FILEIRA 2 - ATO 2A (Paginas 25-55)
[11][12][13][14][15][16][17][18][19][20]

FILEIRA 3 - ATO 2B (Paginas 55-85)
[21][22][23][24][25][26][27][28][29][30]

FILEIRA 4 - ATO 3 (Paginas 85-110)
[31][32][33][34][35][36][37][38][39][40]
```

#### Step 4.2: Template de Cartao

**Para cada cena:**
```
CARTAO #___

Titulo da Cena: _______________

Descricao (inicio-meio-fim):
_______________________________________________

CONFLITO (><):
_______________ vs _______________

MUDANCA EMOCIONAL (+/-):
Comeca: _______________
Termina: _______________

Cor/Categoria:
[ ] A Story  [ ] B Story  [ ] Ambas
```

---

### Fase 5: Validacao e Refinamento

#### Step 5.1: Checklist de Validacao

**Estrutura Geral:**
- [ ] Todos 15 beats presentes
- [ ] Timing correto para o formato
- [ ] Atos com proporcao 25/50/25

**Ato 1:**
- [ ] Opening Image forte
- [ ] Theme Stated sutil
- [ ] Six Things plantadas
- [ ] Catalyst claro e dramatico
- [ ] Break into Two e escolha do heroi

**Ato 2:**
- [ ] B Story carrega tema
- [ ] Fun and Games entrega premissa
- [ ] Midpoint exatamente em 50%
- [ ] All Is Lost com Whiff of Death
- [ ] Dark Night processa emocionalmente

**Ato 3:**
- [ ] Break into Three une A e B Story
- [ ] Finale com Five-Point structure
- [ ] Six Things pagas
- [ ] Final Image espelha Opening Image

**Personagens:**
- [ ] Heroi tem arco de transformacao
- [ ] Save the Cat moment presente
- [ ] Antagonista adequado ao genero
- [ ] B Story character desenvolve tema

---

#### Step 5.2: Diagnostico de Problemas

**Se a historia "nao funciona", verifique:**

| Sintoma | Problema Provavel | Solucao |
|---------|-------------------|---------|
| Inicio lento | Set-Up muito longo | Mover Catalyst para mais cedo |
| Meio arrastado | Fun and Games sem conflito | Adicionar obstaculos |
| Midpoint fraco | Nao e verdadeira virada | Aumentar stakes |
| Ato 2 sags | Bad Guys Close In fraco | Aumentar pressao externa E interna |
| Final apressado | Finale sem Five-Point | Expandir cada ponto |
| Nao satisfaz | Six Things sem payoff | Voltar ao Set-Up e plantar |
| Heroi chato | Sem Save the Cat | Adicionar momento de empatia |

---

## Output Final Template

```markdown
# BEAT SHEET: [TITULO]

## Metadata
- Genero Snyder: [Genero]
- Formato: [Screenplay/Novel/TV]
- Word Count/Paginas: [Total]

## Logline
[Logline com ironia]

## Personagens Principais
- Protagonista: [Nome] - [Descricao]
- Antagonista: [Nome] - [Descricao]
- B Story: [Nome] - [Descricao]

## Os 15 Beats

### ATO 1 - TESE (25%)

1. **Opening Image** ([timing])
   [Descricao]

2. **Theme Stated** ([timing])
   [Descricao]

3. **Set-Up** ([timing])
   [Descricao]

4. **Catalyst** ([timing])
   [Descricao]

5. **Debate** ([timing])
   [Descricao]

6. **Break into Two** ([timing])
   [Descricao]

### ATO 2 - ANTITESE (50%)

7. **B Story** ([timing])
   [Descricao]

8. **Fun and Games** ([timing])
   [Descricao]

9. **Midpoint** ([timing])
   [Descricao]

10. **Bad Guys Close In** ([timing])
    [Descricao]

11. **All Is Lost** ([timing])
    [Descricao]

12. **Dark Night of the Soul** ([timing])
    [Descricao]

### ATO 3 - SINTESE (25%)

13. **Break into Three** ([timing])
    [Descricao]

14. **Finale** ([timing])
    [Descricao]

15. **Final Image** ([timing])
    [Descricao]

## Six Things That Need Fixing
1. [Item] → [Payoff]
2. [Item] → [Payoff]
3. [Item] → [Payoff]
4. [Item] → [Payoff]
5. [Item] → [Payoff]
6. [Item] → [Payoff]

## Validacao
- [ ] Todos beats presentes
- [ ] Timing correto
- [ ] Genero respeitado
- [ ] Arco de transformacao completo
```

---

## Exemplos de Beat Sheets Completos

### Exemplo 1: Die Hard (Dude with a Problem)

**Logline:** Um policial de NY tenta salvar a esposa e outros reféns de terroristas durante a festa de Natal da empresa dela.

| Beat | Timing | Descricao |
|------|--------|-----------|
| Opening Image | 1% | John McClane no aviao, nervoso, dica de descalco |
| Theme Stated | 5% | "Ninguem pode resolver seus problemas" |
| Set-Up | 1-10% | John conhece Argyle, chega ao Nakatomi, ve Holly |
| Catalyst | 12% | Hans Gruber e terroristas tomam o predio |
| Debate | 12-25% | John se esconde, avalia situacao, descalco |
| Break into Two | 25% | Decide lutar - puxa alarme de incendio |
| B Story | 30% | Al Powell - conexao via radio |
| Fun and Games | 30-55% | John vs terroristas um a um (promessa: Die Hard!) |
| Midpoint | 50% | John faz contato com policia, parece vitoria |
| Bad Guys Close In | 55-75% | FBI corta energia, Hans descobre sobre Holly |
| All Is Lost | 75% | Hans tem Holly, pes sangrando, parece perdido |
| Dark Night | 75-85% | John fala com Al, confessa falhas do casamento |
| Break into Three | 85% | John percebe Hans quer abrir cofre |
| Finale | 85-99% | Confronto no telhado, salva Holly, mata Hans |
| Final Image | 100% | John e Holly juntos, reconciliados |

---

### Exemplo 2: The Matrix (Superhero)

**Logline:** Um hacker descobre que sua realidade é uma simulação e que ele pode ser o escolhido para salvar a humanidade.

| Beat | Timing | Descricao |
|------|--------|-----------|
| Opening Image | 1% | Cursor piscando - mundo digital |
| Theme Stated | 5% | "Voce precisa se desconectar" |
| Set-Up | 1-10% | Neo como Thomas Anderson, trabalho chato, busca Morpheus |
| Catalyst | 12% | Agentes capturam Neo, rastreador no corpo |
| Debate | 12-25% | Neo decide se confia em Morpheus |
| Break into Two | 25% | Pilula vermelha - descobre a Matrix |
| B Story | 30% | Trinity - amor e crenca no "escolhido" |
| Fun and Games | 30-55% | Treinamento! Kung Fu, saltos, simulacoes |
| Midpoint | 50% | Oraculo - "Voce nao e o escolhido... ainda" (falsa derrota) |
| Bad Guys Close In | 55-75% | Cypher trai, Agentes atacam |
| All Is Lost | 75% | Morpheus capturado, parece que tudo acabou |
| Dark Night | 75-85% | Neo processa - ir embora ou salvar Morpheus? |
| Break into Three | 85% | Decide voltar - "Ninguem fez isso" / "Por isso vai funcionar" |
| Finale | 85-99% | Resgata Morpheus, luta com Smith, morre e renasce |
| Final Image | 100% | Neo voa - totalmente transformado |

---

## Recursos Adicionais

### Calculadora de Beats

**Para qualquer formato:**
```
Total de paginas/palavras: _______________

Opening Image (1%):      _______________
Theme Stated (5%):       _______________
Catalyst (10-12%):       _______________
Break into Two (25%):    _______________
B Story (30%):           _______________
Midpoint (50%):          _______________
All Is Lost (75%):       _______________
Break into Three (85%):  _______________
Final Image (100%):      _______________
```

### Generos - Quick Reference

| Genero | Pergunta Chave | Exemplo |
|--------|----------------|---------|
| Monster in the House | Preso com ameaca? | Alien, Jaws |
| Golden Fleece | Jornada com premio? | Star Wars |
| Out of the Bottle | Desejo magico? | Bruce Almighty |
| Dude with a Problem | Inocente em perigo? | Die Hard |
| Rites of Passage | Transicao de vida? | The Graduate |
| Buddy Love | Dois que se completam? | Rain Man |
| Whydunit | Investigacao? | Chinatown |
| Fool Triumphant | Underdog vs sistema? | Legally Blonde |
| Institutionalized | vs Grupo? | One Flew Over |
| Superhero | Heroi extraordinario? | Spider-Man |

---

## Conclusao

Este task guiou voce atraves de todo o processo Save the Cat! de Blake Snyder. Ao final, voce deve ter:

1. **Logline** com ironia e mental picture
2. **Genero** identificado com todos elementos
3. **Personagens** desenvolvidos com arcos
4. **15 Beats** completos com timing preciso
5. **Six Things** plantadas e pagas
6. **Board** de 40 cartoes visualizado

Lembre-se das palavras de Snyder: "Estrutura nao e formula. E o esqueleto que permite a historia ficar de pe."

---

*Task Version: 1.0*
*Lines: 750+*
*Based on Blake Snyder's Save the Cat! Methodology*
