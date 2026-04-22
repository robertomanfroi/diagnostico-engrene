# AN_KE_114 - Dynamic Variances in UX
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão c6cc1808, aiox-ui — "nao tao engessados ... variar de titulos"]

## Purpose

O efeito "Deja Vu" digital é mortal (A fadiga da uniformidade). Quando o React Component tem Títulos ou Textos fixos como `"Seu Portal AIOX"` engessados em todo maldito reload, a interface para de surpreender o cérebro humano. A heurística dita que um software premium que lida com inteligência artifical é *Vivo e Dinâmico*. Insira vetores randomizados com classe (Greetings temporais baseados no relógio, variações em títulos secundários de sub-header no Load). O frontend deve oscilar organicamente para evitar parecer um bloco rígido semalma programada via template obsoleto.

## Configuration

```yaml
AN_KE_114:
  name: "Dynamic Variances in UX"
  zone: "genialidade"
  trigger: "Programando componentes vitais estáticos de Welcome, Headers, Onboarding text ou Landing Pages."
  sys_tension:
    tension_with: "AN_KE_027 (Zero Emojis & Design Consistente)"
    resolution: "Variações dinâmicas respeitam DNA visual (paleta, tipografia, tone-of-voice). Caos criativo dentro de um framework estruturado."

  rule: |
    SE implementando um template massificado de visualização do domínio UX
    ENTÃO ELIMINE engessamentos robóticos. A interface DEVE ter variações no copy textual embarcado.
    Mude o tom. Varie os greetings. Não repita mecanicamente a mesma descrição "Abaixo todos os seus itens" se puder randomizar gentilmente 4 strings no frontend para fluidez psicológica.

  veto_condition:
    trigger: "Agente encerra a Dashboard de cursos contendo estaticamente um `h1>Bem Vindo ao Dashboard</h1` que nunca oscila com o retorno ou uso do aluno."
    action: "VETO — 'nao faz sentido ser o mesmo título sempre, quero variaaccao de titulos... aproveitar melhor o design da página para sermos mais fluidos, e nao tao engessados'."

  evidence:
    - "[SOURCE: sessão c6cc1808, aiox-ui] 'nao faz sentido ser o mesmo título sempre, quero variaaccao de titulos, e nao quero falar de figma tanto quanto estamos falando, precisamos aproveitar melhor o design da página para sermos mais fluidos, e nao tao engessados'"
```

## Decision Tree

```javascript
IF (hardcoding_generic_greeting_titles_or_copy_in_TSX_UI)
  STEP_1: PAUSE construction of static texts.
  STEP_2: REPLACE static `<h1>Dashboard AIOX Front</h1>` with dynamic arrays or contextual hooks.
    `const titles = ["Pronto para avançar?", "Seus assets arquiteturais:", "Mapeado e ativo."]`
    `const title = sample(titles)`
  STEP_3: IMPLEMENT intelligent UI logic taking advantage of the space fluidity (dynamic heights, changing sub-components) rather than blocky borders.
```

## Failure Modes

### Sintomatologia Clássica de Software Legado
- **Trigger:** Portal administrativo sempre dá o exato mesmo texto robótico padrão do TailwindUI ou Next.js starter pack em suas páginas centrais.
- **Manifestation:** Destrói o gatilho da sofisticação de um software que deveria ser customizado ao portador; fica idêntico ao dashboard da loja da esquina de bairro.
- **Prevention:** Aleatoriedade injetada no frontend com contexto temporal ou comportamental (Fluid UX).

## Validation

**Paradoxo Identificado:** Ordem (templates estáticos) vs Caos (variações dinâmicas sem critério) = interface confusa ou inconsistente.

**Resolução:** Estruturar a aleatoriedade. Bancos de copy pré-aprovados + contexto temporal/comportamental (não puro random). Exemplo: greetings variam por período do dia (bom dia, boa tarde, boa noite) ou por estado do usuário (first-login, returning-user, power-user). Assim há **previsibilidade estruturada** (a interface não é idêntica ao refresh, mas é confiável). Esta é a síntese: caos criativo dentro de guardrails de marca.
