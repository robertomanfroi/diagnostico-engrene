# apply-heros-journey

```yaml
task:
  name: Apply Hero's Journey
  id: apply-heros-journey
  description: Guia completo para aplicar a Jornada do Heroi de Joseph Campbell a qualquer narrativa
  icon: "\U0001F3DB"
  category: storytelling
  complexity: medium
  estimated_time: "2-4 hours"

metadata:
  version: "1.0.0"
  created: "2026-01-30"
  agent: joseph-campbell
  changelog:
    - "1.0: Initial release - complete Hero's Journey application workflow"

inputs:
  required:
    - story_type: "Tipo de historia (novel, screenplay, short story, game)"
    - genre: "Genero (fantasy, sci-fi, drama, romance, thriller, etc.)"
    - hero_concept: "Conceito inicial do heroi"
  optional:
    - existing_outline: "Outline existente para diagnostico"
    - word_count_target: "Meta de palavras/paginas"
    - specific_stage: "Estagio especifico para desenvolver"

outputs:
  - complete_structure: "Estrutura completa da jornada em 12 estagios"
  - archetype_map: "Mapa de arquetipos da historia"
  - stage_breakdowns: "Desenvolvimento detalhado de cada estagio"
  - transformation_arc: "Arco de transformacao do heroi"
  - diagnostic_report: "Relatorio de pontos fortes e fracos"
```

---

## Workflow Overview

```
FASE 1: DIAGNOSTICO E PREPARACAO
    |
    v
FASE 2: CONSTRUCAO DO MUNDO ORDINARIO
    |
    v
FASE 3: ESTRUTURA DO ATO I (Separacao)
    |
    v
FASE 4: ESTRUTURA DO ATO II (Iniciacao)
    |
    v
FASE 5: ESTRUTURA DO ATO III (Retorno)
    |
    v
FASE 6: MAPEAMENTO DE ARQUETIPOS
    |
    v
FASE 7: ARCO DE TRANSFORMACAO
    |
    v
FASE 8: VALIDACAO E REFINAMENTO
```

---

## FASE 1: DIAGNOSTICO E PREPARACAO

### 1.1 Coleta de Informacoes Iniciais

**Perguntas para o Usuario:**

```markdown
## Informacoes Basicas da Historia

1. **Tipo de Narrativa:**
   - [ ] Romance/Novel
   - [ ] Roteiro de Filme
   - [ ] Roteiro de Serie
   - [ ] Conto
   - [ ] Historia de Game
   - [ ] Outro: _______

2. **Genero Principal:**
   - [ ] Fantasia
   - [ ] Ficcao Cientifica
   - [ ] Drama
   - [ ] Romance
   - [ ] Thriller/Suspense
   - [ ] Acao/Aventura
   - [ ] Horror
   - [ ] Outro: _______

3. **Tom da Historia:**
   - [ ] Epico/Grandioso
   - [ ] Intimo/Pessoal
   - [ ] Sombrio/Gritty
   - [ ] Luminoso/Esperancoso
   - [ ] Ambiguo/Complexo

4. **Meta de Extensao:**
   - Palavras: _______ (romances: 80-100k)
   - Paginas de roteiro: _______ (filmes: 90-120)

5. **Conceito do Heroi:**
   - Nome (se definido): _______
   - Ocupacao/Papel: _______
   - Idade aproximada: _______
   - Tracos distintivos: _______

6. **Premissa em Uma Frase:**
   _______________________________________
```

### 1.2 Diagnostico de Outline Existente

Se o usuario ja tem um outline, execute esta analise:

```markdown
## Diagnostico da Jornada

### Checklist de Estagios Presentes

| # | Estagio | Presente? | Forca (1-5) | Notas |
|---|---------|-----------|-------------|-------|
| 1 | Mundo Ordinario | | | |
| 2 | Chamado a Aventura | | | |
| 3 | Recusa do Chamado | | | |
| 4 | Encontro com Mentor | | | |
| 5 | Travessia do Limiar | | | |
| 6 | Testes, Aliados, Inimigos | | | |
| 7 | Aproximacao da Caverna | | | |
| 8 | Provacao Suprema | | | |
| 9 | Recompensa | | | |
| 10 | Caminho de Volta | | | |
| 11 | Ressurreicao | | | |
| 12 | Retorno com Elixir | | | |

### Arquetipos Identificados

| Arquetipo | Personagem | Forca (1-5) | Notas |
|-----------|------------|-------------|-------|
| Heroi | | | |
| Mentor | | | |
| Sombra | | | |
| Guardiao do Limiar | | | |
| Arauto | | | |
| Camaleao | | | |
| Aliado | | | |
| Malandro | | | |

### Pontos Fortes
1. _______
2. _______
3. _______

### Pontos a Fortalecer
1. _______
2. _______
3. _______

### Recomendacoes Prioritarias
1. _______
2. _______
3. _______
```

---

## FASE 2: CONSTRUCAO DO MUNDO ORDINARIO

### 2.1 Template do Mundo Ordinario

O Mundo Ordinario estabelece a linha de base para toda a transformacao. Sem ele, a jornada perde impacto.

```markdown
## Mundo Ordinario de [NOME DO HEROI]

### Ambiente Fisico
- **Localizacao:** _______
- **Epoca:** _______
- **Atmosfera:** _______
- **Limitacoes do ambiente:** _______

### Vida Cotidiana
- **Rotina diaria:** _______
- **Ocupacao/Papel:** _______
- **Relacionamentos principais:** _______
- **Atividades que definem o personagem:** _______

### O Que Falta (Necessidade Interna)
> A necessidade interna e o que o heroi PRECISA mas NAO SABE que precisa.

- **Falha central:** _______
- **O que esta reprimido:** _______
- **Potencial nao realizado:** _______
- **Ferida do passado:** _______

### O Que o Heroi Quer (Desejo Externo)
> O desejo externo e o que o heroi QUER CONSCIENTEMENTE.

- **Objetivo consciente:** _______
- **Por que quer isso:** _______
- **Obstaculos atuais:** _______

### Conflito WANT vs NEED
| WANT (Desejo) | NEED (Necessidade) |
|---------------|-------------------|
| Consciente | Inconsciente |
| Externo | Interno |
| O que busca | O que transforma |
| _______ | _______ |

### Prenuncios da Jornada
- **Inquietacao visivel:** _______
- **Sinais de que algo vai mudar:** _______
- **Simbolos plantados:** _______

### Stakes (O Que Esta em Risco)
- **Se nada mudar:** _______
- **O que o heroi pode perder:** _______
- **O que o mundo pode perder:** _______
```

### 2.2 Checklist do Mundo Ordinario

```markdown
## Validacao do Mundo Ordinario

- [ ] O leitor/espectador entende a vida do heroi antes da aventura
- [ ] A falha do heroi e mostrada (nao dita)
- [ ] O que falta na vida do heroi e claro
- [ ] Ha contraste suficiente com o Mundo Especial
- [ ] Os relacionamentos principais estao estabelecidos
- [ ] As stakes pessoais sao claras
- [ ] Ha prenuncios sutis da jornada por vir
- [ ] O WANT e NEED do heroi sao distintos
- [ ] A inquietacao do heroi e perceptivel
- [ ] O leitor se identifica/simpatiza com o heroi
```

---

## FASE 3: ESTRUTURA DO ATO I (SEPARACAO)

### 3.1 Estagio 2: O Chamado a Aventura

```markdown
## O Chamado a Aventura

### Tipo de Chamado
- [ ] Mensagem direta (carta, ligacao, visitante)
- [ ] Ameaca (perigo iminente, perda)
- [ ] Descoberta (segredo revelado, objeto encontrado)
- [ ] Acidente (evento inesperado)
- [ ] Tentacao (oportunidade atraente)
- [ ] Inquietacao interna (sonho, visao, intuicao)

### Descricao do Chamado
- **O que acontece:** _______
- **Quem/O que traz o chamado (Arauto):** _______
- **Quando na historia:** _______
- **Onde acontece:** _______

### Impacto no Heroi
- **Reacao emocional inicial:** _______
- **O que o chamado representa:** _______
- **Por que nao pode ser ignorado:** _______

### Stakes Levantadas
- **O que acontece se aceitar:** _______
- **O que acontece se recusar:** _______
- **Por que e urgente:** _______

### Conexao com WANT/NEED
- **Relacao com WANT (desejo consciente):** _______
- **Relacao com NEED (necessidade inconsciente):** _______
```

### 3.2 Estagio 3: Recusa do Chamado

```markdown
## Recusa do Chamado

### Razoes da Recusa
- [ ] Medo do desconhecido
- [ ] Obrigacoes no mundo ordinario
- [ ] Senso de inadequacao
- [ ] Duvida sobre a missao
- [ ] Conforto com status quo
- [ ] Outro: _______

### Manifestacao da Recusa
- **O que o heroi diz/faz:** _______
- **Comportamento de evitacao:** _______
- **Justificativas que usa:** _______

### O Que Muda a Decisao
- **Evento catalisador:** _______
- **Pessoa que influencia:** _______
- **Consequencia de nao agir:** _______

### Momento de Aceitacao
- **O que o heroi percebe:** _______
- **Decisao consciente:** _______
- **Sacrificio implicito:** _______

### Duracao da Recusa
- [ ] Breve (uma cena)
- [ ] Moderada (algumas cenas)
- [ ] Extensa (varios capitulos)
- [ ] Recorrente (volta em momentos de crise)
```

### 3.3 Estagio 4: Encontro com o Mentor

```markdown
## Encontro com o Mentor

### Perfil do Mentor
- **Nome:** _______
- **Relacao com o heroi:** _______
- **Background:** _______
- **Por que esta qualificado:** _______

### Tipo de Mentor
- [ ] Sabio (conhecimento, perspectiva)
- [ ] Treinador (habilidades, confianca)
- [ ] Consciencia (orientacao moral)
- [ ] Caido (sabedoria de falhas passadas)
- [ ] Supernatural (ajuda magica/divina)

### O Que o Mentor Oferece

| Tipo | O Que E | Funcao na Historia |
|------|---------|-------------------|
| Conhecimento | _______ | _______ |
| Ferramenta/Presente | _______ | _______ |
| Treinamento | _______ | _______ |
| Confianca | _______ | _______ |
| Empurrao | _______ | _______ |

### Limitacoes do Mentor
- **Por que nao resolve os problemas:** _______
- **Fraquezas/Falhas:** _______
- **Quando/Como sai da historia:** _______

### Relacao com a Sombra
- **Conexao com o antagonista:** _______
- **Conhecimento do perigo:** _______
- **Avisos que da:** _______

### Momento de Saida
- [ ] Morte
- [ ] Abandono
- [ ] Captura
- [ ] Missao separada
- [ ] Alcancou limite de ajuda
```

### 3.4 Estagio 5: Travessia do Primeiro Limiar

```markdown
## Travessia do Primeiro Limiar

### O Limiar
- **O que separa o Mundo Ordinario do Especial:** _______
- **Manifestacao fisica:** _______
- **Manifestacao simbolica:** _______

### Guardiao do Limiar
- **Quem/O que guarda a passagem:** _______
- **Teste que impoe:** _______
- **Como o heroi supera:** _______
- **Se torna aliado?: _______

### Momento da Travessia
- **Acao do heroi:** _______
- **O que deixa para tras:** _______
- **Ponto de nao retorno:** _______

### Entrada no Mundo Especial
- **Primeira impressao:** _______
- **Contraste com Mundo Ordinario:** _______
- **Novas regras:** _______
- **Perigos imediatos:** _______

### Impacto Emocional
- **O que o heroi sente:** _______
- **Duvidas remanescentes:** _______
- **Determinacao renovada:** _______
```

---

## FASE 4: ESTRUTURA DO ATO II (INICIACAO)

### 4.1 Estagio 6: Testes, Aliados, Inimigos

```markdown
## Testes, Aliados, Inimigos

### Serie de Testes

| # | Teste | Tipo | Habilidade Desenvolvida | Resultado |
|---|-------|------|------------------------|-----------|
| 1 | _______ | Fisico/Mental/Emocional/Moral | _______ | Sucesso/Falha |
| 2 | _______ | _______ | _______ | _______ |
| 3 | _______ | _______ | _______ | _______ |
| 4 | _______ | _______ | _______ | _______ |
| 5 | _______ | _______ | _______ | _______ |

### Aliados Encontrados

| Aliado | Arquetipo | Habilidades | Relacao com Heroi |
|--------|-----------|-------------|-------------------|
| _______ | Aliado/Malandro/Camaleao | _______ | _______ |
| _______ | _______ | _______ | _______ |
| _______ | _______ | _______ | _______ |

### Inimigos Revelados

| Inimigo | Tipo | Ameaca que Representa | Conexao com Sombra |
|---------|------|----------------------|-------------------|
| _______ | Capanga/Tenente/Rival | _______ | _______ |
| _______ | _______ | _______ | _______ |

### Regras do Mundo Especial
- **O que funciona diferente aqui:** _______
- **Poderes/Habilidades disponiveis:** _______
- **Perigos constantes:** _______
- **Hierarquia social:** _______

### Progressao de Dificuldade
```
Teste 1 (Facil) --> Teste 2 (Medio) --> Teste 3 (Dificil) --> Provacao (Extremo)
```

### Falhas Importantes
> O heroi DEVE falhar pelo menos uma vez para humaniza-lo e criar tensao.

- **Momento de falha:** _______
- **Consequencias:** _______
- **Aprendizado:** _______
```

### 4.2 Estagio 7: Aproximacao da Caverna Oculta

```markdown
## Aproximacao da Caverna Oculta

### A Caverna (Lugar do Perigo Maximo)
- **O que representa:** _______
- **Localizacao fisica:** _______
- **Significado simbolico:** _______

### Preparativos
- **O que o heroi faz antes de entrar:** _______
- **Aliados que o acompanham:** _______
- **Ferramentas/Armas preparadas:** _______

### Momento de Duvida
- **Medos que surgem:** _______
- **Tentacao de voltar:** _______
- **O que o empurra adiante:** _______

### Tensao Crescente
- **Sinais de perigo:** _______
- **Prenuncios da Provacao:** _______
- **Atmosfera:** _______

### Ponto de Comprometimento
- **Momento em que nao ha volta:** _______
- **Decisao final:** _______
- **O que esta em jogo:** _______
```

### 4.3 Estagio 8: A Provacao Suprema (The Ordeal)

> "A caverna que voce teme entrar contem o tesouro que voce busca." - Joseph Campbell

```markdown
## A Provacao Suprema

### O Confronto
- **O que o heroi enfrenta:** _______
- **Manifestacao do medo maximo:** _______
- **Por que e o momento mais perigoso:** _______

### Morte Simbolica
- **Tipo de morte:**
  - [ ] Literal (morre e renasce)
  - [ ] Fisica (quase morre)
  - [ ] Emocional (parte de si morre)
  - [ ] Social (reputacao/identidade destruida)
  - [ ] Espiritual (fe abalada)

- **Como a "morte" acontece:** _______
- **Duracao do estado de morte:** _______
- **O que morre no heroi:** _______

### Confronto com a Sombra
- **Aspecto sombrio enfrentado:** _______
- **Espelho do heroi revelado:** _______
- **Escolha crucial:** _______

### Renascimento
- **O que aciona o renascimento:** _______
- **Nova compreensao ganha:** _______
- **Poder/Habilidade adquirida:** _______
- **Mudanca visivel no heroi:** _______

### Estrutura da Provacao
```
CRISE MAXIMA --> MORTE SIMBOLICA --> MOMENTO DE ESCURIDAO -->
LUZ/INSIGHT --> RENASCIMENTO --> TRANSFORMACAO
```

### Impacto nos Aliados
- **Quem testemunha:** _______
- **Reacoes:** _______
- **Mudanca nas relacoes:** _______

### Conexao com NEED
- **Como a provacao endereça a necessidade interna:** _______
- **O que o heroi finalmente entende:** _______
```

### 4.4 Estagio 9: Recompensa (Apoderando-se da Espada)

```markdown
## Recompensa

### O Tesouro Conquistado
- **Tipo de recompensa:**
  - [ ] Objeto fisico
  - [ ] Conhecimento/Segredo
  - [ ] Pessoa resgatada
  - [ ] Poder/Habilidade
  - [ ] Reconciliacao
  - [ ] Nova identidade

- **Descricao especifica:** _______
- **Por que tem valor:** _______

### Momento de Celebracao
- **Como o heroi reage:** _______
- **Celebracao com aliados:** _______
- **Reflexao sobre o que foi superado:** _______

### Complicacoes
- **Consequencias imprevistas:** _______
- **Novos problemas criados:** _______
- **Setup para Ato III:** _______

### Mudanca no Heroi
- **Antes da Provacao vs. Depois:**

| Aspecto | Antes | Depois |
|---------|-------|--------|
| Crenca sobre si | _______ | _______ |
| Habilidade | _______ | _______ |
| Relacoes | _______ | _______ |
| Objetivo | _______ | _______ |
```

---

## FASE 5: ESTRUTURA DO ATO III (RETORNO)

### 5.1 Estagio 10: O Caminho de Volta

```markdown
## O Caminho de Volta

### Motivacao para Retornar
- **Por que o heroi deve voltar:** _______
- **O que o puxa de volta:** _______
- **Obrigacao ou escolha:** _______

### Perseguicao/Complicacoes
- **Quem/O que persegue:** _______
- **Novos obstaculos:** _______
- **Stakes elevadas:** _______

### Tentacao de Ficar
- **O que o mundo especial oferece:** _______
- **Por que seria mais facil nao voltar:** _______
- **O que faz o heroi resistir:** _______

### Viagem de Volta
- **Desafios no caminho:** _______
- **Uso das habilidades adquiridas:** _______
- **Aproximacao do climax:** _______
```

### 5.2 Estagio 11: Ressurreicao

```markdown
## Ressurreicao

### O Teste Final
- **Natureza do confronto final:** _______
- **Por que e diferente da Provacao:** _______
- **O que esta em jogo agora:** _______

### Aplicacao de Tudo que Aprendeu
| Licao Aprendida | Como E Aplicada |
|-----------------|-----------------|
| _______ | _______ |
| _______ | _______ |
| _______ | _______ |

### Morte Final do Eu Antigo
- **O que finalmente morre:** _______
- **Sacrificio necessario:** _______
- **Escolha definitiva:** _______

### Transformacao Completa
- **Quem o heroi se tornou:** _______
- **Diferenca do inicio:** _______
- **Prova da mudanca:** _______

### Resolucao do Conflito Externo
- **Como a ameaca e derrotada/resolvida:** _______
- **Destino da Sombra:** _______
- **Impacto no mundo:** _______

### Resolucao do Conflito Interno (NEED)
- **A necessidade interna foi satisfeita?:** _______
- **O heroi superou a falha?:** _______
- **Nova crenca estabelecida:** _______
```

### 5.3 Estagio 12: Retorno com o Elixir

```markdown
## Retorno com o Elixir

### O Elixir
- **Tipo de elixir:**
  - [ ] Tesouro fisico para a comunidade
  - [ ] Sabedoria para compartilhar
  - [ ] Cura ou restauracao
  - [ ] Amor conquistado
  - [ ] Paz/Ordem restaurada
  - [ ] Transformacao social

- **Descricao especifica:** _______
- **Como beneficia a comunidade:** _______

### Retorno ao Mundo Ordinario
- **Estado do mundo ao retornar:** _______
- **Recepcao do heroi:** _______
- **Mudancas visiveis:** _______

### Novo Equilibrio
- **Antes vs. Depois:**

| Aspecto | Mundo no Inicio | Mundo no Fim |
|---------|-----------------|--------------|
| Status do heroi | _______ | _______ |
| Comunidade | _______ | _______ |
| Ameaca | _______ | _______ |
| Relacoes | _______ | _______ |

### Fechamento Tematico
- **Tema da historia:** _______
- **Como o retorno ilustra o tema:** _______
- **Mensagem final:** _______

### Tipo de Encerramento
- [ ] Fechado (todos os fios amarrados)
- [ ] Aberto (possibilidade de continuacao)
- [ ] Agridoce (vitoria com custo)
- [ ] Ciclico (volta ao inicio transformado)
```

---

## FASE 6: MAPEAMENTO DE ARQUETIPOS

### 6.1 Template de Arquetipos

```markdown
## Mapa de Arquetipos

### O HEROI
- **Nome:** _______
- **WANT (Desejo):** _______
- **NEED (Necessidade):** _______
- **Falha Central:** _______
- **Arco de Transformacao:** De _______ para _______
- **Momento de Provacao:** _______
- **Sacrificio:** _______

### O MENTOR
- **Nome:** _______
- **Relacao com Heroi:** _______
- **O que Oferece:** _______
- **Limitacoes:** _______
- **Momento de Saida:** _______

### A SOMBRA
- **Nome:** _______
- **Espelho do Heroi:** _______
- **O que Representa:** _______
- **Conexao com NEED do Heroi:** _______
- **Destino:** _______

### O ARAUTO
- **Nome/Forma:** _______
- **Mensagem que Traz:** _______
- **Momento de Aparicao:** _______

### O GUARDIAO DO LIMIAR
- **Nome/Forma:** _______
- **Teste que Impoe:** _______
- **Se Torna Aliado?: _______

### O CAMALEAO
- **Nome:** _______
- **Aparencia Inicial:** _______
- **Revelacao:** _______
- **Impacto na Historia:** _______

### ALIADOS
| Nome | Habilidade | Funcao | Arco |
|------|------------|--------|------|
| _______ | _______ | _______ | _______ |
| _______ | _______ | _______ | _______ |
| _______ | _______ | _______ | _______ |

### O MALANDRO
- **Nome:** _______
- **Funcao Comica:** _______
- **Momento de Verdade:** _______
```

### 6.2 Checklist de Arquetipos

```markdown
## Validacao de Arquetipos

### Heroi
- [ ] WANT e NEED sao distintos e em tensao
- [ ] Falha central e visivel e superavel
- [ ] Faz escolhas ativas (nao e passivo)
- [ ] Transformacao e crivel e ganha

### Mentor
- [ ] Oferece ferramentas, nao solucoes
- [ ] Tem limitacoes claras
- [ ] Sai da historia no momento certo
- [ ] Relacao com heroi e significativa

### Sombra
- [ ] Reflete aspecto sombrio do heroi
- [ ] Ameaca e pessoal, nao so fisica
- [ ] Tem motivacoes compreensiveis
- [ ] Destino ressoa com tema

### Suporte
- [ ] Cada arquetipo tem funcao clara
- [ ] Nao ha redundancia entre personagens
- [ ] Personagens podem combinar arquetipos
- [ ] Todos servem ao arco do heroi
```

---

## FASE 7: ARCO DE TRANSFORMACAO

### 7.1 Template de Transformacao

```markdown
## Arco de Transformacao do Heroi

### Estado Inicial (Mundo Ordinario)
- **Crenca limitante:** _______
- **Medo central:** _______
- **Falha dominante:** _______
- **Comportamento padrao:** _______

### Catalisador (Chamado)
- **O que desafia a crenca:** _______
- **Primeiro vislumbre de mudanca:** _______

### Resistencia (Recusa)
- **Por que resiste a mudanca:** _______
- **O que teria que abrir mao:** _______

### Preparacao (Mentor)
- **Ferramentas para mudanca:** _______
- **Nova perspectiva oferecida:** _______

### Primeiros Passos (Limiar)
- **Primeira acao de mudanca:** _______
- **Desconforto inicial:** _______

### Aprendizado (Testes)
| Teste | Licao Aprendida |
|-------|-----------------|
| _______ | _______ |
| _______ | _______ |
| _______ | _______ |

### Crise (Provacao)
- **Confronto com medo central:** _______
- **Momento de escuridao:** _______
- **Insight transformador:** _______

### Nova Identidade (Recompensa)
- **Crenca nova:** _______
- **Comportamento novo:** _______

### Teste da Nova Identidade (Ressurreicao)
- **Prova definitiva da mudanca:** _______
- **Escolha que demonstra transformacao:** _______

### Estado Final (Retorno)
- **Quem o heroi se tornou:** _______
- **Como ve o mundo agora:** _______
- **O que pode oferecer aos outros:** _______

### Resumo da Transformacao
```
DE: [Crenca/Comportamento Antigo]
PARA: [Crenca/Comportamento Novo]
ATRAVES DE: [Experiencia Transformadora]
```
```

### 7.2 Arco de Mudanca de Crenca

```markdown
## Arco de Crenca (Lie to Truth)

### A MENTIRA (Crenca Falsa Inicial)
> A mentira e o que o heroi acredita no inicio que o impede de ser completo.

- **A mentira:** _______
- **Origem da mentira:** _______
- **Como a mentira limita o heroi:** _______
- **Evidencias que "comprovam" a mentira:** _______

### A VERDADE (O que o Heroi Precisa Aprender)
> A verdade e a crenca que substituira a mentira e permitira a transformacao.

- **A verdade:** _______
- **Por que e dificil aceitar:** _______
- **Como a verdade liberta:** _______

### MOMENTOS DE CONFRONTO

| Momento | Mentira Desafiada | Reacao do Heroi |
|---------|-------------------|-----------------|
| Chamado | _______ | Nega |
| Testes | _______ | Duvida |
| Provacao | _______ | Confronta |
| Ressurreicao | _______ | Aceita |

### CENA DE REVELACAO
- **Quando a verdade se torna inegavel:** _______
- **O que o heroi finalmente ve:** _______
- **Custo de aceitar a verdade:** _______
```

---

## FASE 8: VALIDACAO E REFINAMENTO

### 8.1 Checklist Final da Jornada

```markdown
## Validacao Completa da Jornada do Heroi

### ESTRUTURA GERAL
- [ ] Os tres atos estao balanceados (25/50/25)
- [ ] Cada estagio tem funcao clara
- [ ] Ha progressao de dificuldade
- [ ] Stakes aumentam ao longo da historia

### ATO I: SEPARACAO
- [ ] Mundo Ordinario estabelece baseline
- [ ] WANT e NEED do heroi sao claros
- [ ] Chamado e impossivel de ignorar
- [ ] Recusa humaniza o heroi
- [ ] Mentor prepara mas nao resolve
- [ ] Travessia marca ponto sem retorno

### ATO II: INICIACAO
- [ ] Testes desenvolvem habilidades necessarias
- [ ] Aliados e inimigos tem funcoes claras
- [ ] Provacao e o momento de maior perigo
- [ ] Ha morte simbolica
- [ ] Renascimento traz mudanca visivel
- [ ] Recompensa e significativa

### ATO III: RETORNO
- [ ] Ha motivacao para retornar
- [ ] Ressurreicao testa transformacao
- [ ] Heroi aplica tudo que aprendeu
- [ ] Elixir beneficia a comunidade
- [ ] Novo equilibrio e estabelecido
- [ ] Temas sao resolvidos

### ARQUETIPOS
- [ ] Heroi tem arco de transformacao completo
- [ ] Sombra espelha aspecto do heroi
- [ ] Mentor tem limitacoes
- [ ] Cada personagem serve a historia

### TRANSFORMACAO
- [ ] Crenca inicial (mentira) e clara
- [ ] Crenca final (verdade) e conquistada
- [ ] Mudanca e ganha, nao dada
- [ ] Prova da mudanca e visivel

### TEMA
- [ ] Tema e explorado atraves da jornada
- [ ] Provacao e Ressurreicao ilustram tema
- [ ] Resolucao encapsula mensagem
```

### 8.2 Diagnostico de Problemas Comuns

```markdown
## Diagnostico de Problemas

### Se a Historia Parece Formulaica:
- Subverta uma expectativa em cada ato
- Combine arquetipos de forma inesperada
- Faca o heroi falhar onde esperaria sucesso
- Questione o proprio framework dentro da historia

### Se o Heroi E Passivo:
- Garanta escolhas ativas em cada estagio
- Reduza ajuda externa
- Aumente consequencias de inacao
- Faca o heroi iniciar acoes, nao so reagir

### Se a Provacao Parece Fraca:
- Conecte ao medo mais profundo do heroi
- Garanta que algo realmente "morra"
- Aumente as stakes pessoais
- Faca a vitoria parecer impossivel

### Se o Retorno E Anticlimactico:
- Garanta que o elixir tem valor real
- Mostre impacto no mundo ordinario
- Demonstre a transformacao em acao
- Resolva os temas plantados

### Se os Personagens Sao Rasos:
- De a cada arquetipo motivacoes proprias
- Crie conexoes pessoais com o heroi
- Permita que personagens secundarios mudem
- Faca a Sombra ter um ponto valido
```

---

## TEMPLATES DE OUTPUT

### Template de Estrutura Completa

```markdown
# Estrutura da Jornada do Heroi: [TITULO]

## Resumo
- **Premissa:** _______
- **Heroi:** _______
- **Transformacao:** De _______ para _______
- **Tema:** _______

## ATO I: SEPARACAO (~25%)

### 1. Mundo Ordinario
[Descricao detalhada]

### 2. Chamado a Aventura
[Descricao detalhada]

### 3. Recusa do Chamado
[Descricao detalhada]

### 4. Encontro com o Mentor
[Descricao detalhada]

### 5. Travessia do Primeiro Limiar
[Descricao detalhada]

## ATO II: INICIACAO (~50%)

### 6. Testes, Aliados, Inimigos
[Descricao detalhada]

### 7. Aproximacao da Caverna Oculta
[Descricao detalhada]

### 8. Provacao Suprema
[Descricao detalhada]

### 9. Recompensa
[Descricao detalhada]

## ATO III: RETORNO (~25%)

### 10. Caminho de Volta
[Descricao detalhada]

### 11. Ressurreicao
[Descricao detalhada]

### 12. Retorno com o Elixir
[Descricao detalhada]

## Mapa de Arquetipos
[Tabela completa]

## Arco de Transformacao
[Descricao do arco Lie to Truth]

## Notas e Consideracoes
[Observacoes adicionais]
```

---

## GUIA DE ADAPTACAO POR FORMATO

### Para Romances (80-100k palavras)

| Estagio | % | Palavras | Capitulos |
|---------|---|----------|-----------|
| Mundo Ordinario | 5-10% | 5-10k | 1-3 |
| Chamado-Limiar | 15-20% | 15-20k | 3-6 |
| Testes | 25-30% | 25-30k | 6-10 |
| Provacao-Recompensa | 15-20% | 15-20k | 4-6 |
| Retorno | 20-25% | 20-25k | 5-8 |

### Para Roteiros (90-120 paginas)

| Estagio | Paginas |
|---------|---------|
| Mundo Ordinario | 1-10 |
| Chamado | 10-15 |
| Recusa/Mentor | 15-25 |
| Travessia (Fim Ato I) | 25-30 |
| Testes | 30-55 |
| Provacao (Midpoint) | 55-65 |
| Recompensa-Volta | 65-90 |
| Ressurreicao (Climax) | 90-110 |
| Elixir | 110-120 |

### Para Contos (5-15k palavras)

- Condense Mundo Ordinario para 1-2 paragrafos
- Combine Chamado/Recusa/Mentor
- Foque em 2-3 testes
- Provacao e o climax
- Retorno pode ser implicito

### Para Series/Sagas

- Cada livro/temporada pode ser uma jornada completa
- Jornada maior atravessa toda a serie
- Personagens secundarios podem ter mini-jornadas
- Provacao pode ser distribuida em momentos de virada

---

## REFERENCIAS E FONTES

### Obras de Joseph Campbell
- "The Hero with a Thousand Faces" (1949)
- "The Power of Myth" (1988)
- "Pathways to Bliss" (2004)

### Adaptacoes Recomendadas
- Christopher Vogler - "The Writer's Journey" (1992)
- Dan Harmon - "Story Circle" (simplificacao para TV)
- Blake Snyder - "Save the Cat" (beat sheet para filmes)

### Exemplos Analisados
- Star Wars: A New Hope
- The Lord of the Rings
- The Matrix
- Harry Potter
- The Lion King

---

*Task Version: 1.0*
*Agent: joseph-campbell*
*Lines: 900+*
*Last Updated: 2026-01-30*
