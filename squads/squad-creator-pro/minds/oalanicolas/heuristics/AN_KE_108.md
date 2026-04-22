# AN_KE_108 - The Hard Way First (Anti-Retrabalho)
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 2da94fa4, aiox-stage — "nunca escolha o caminho do retrabalho"]

## Purpose

Na engenharia com IA, é trivial pedir um script superficial que resolve o gargalo de hoje colando "fita adesiva" em cima de um bug massivo (ex: suprimir erro, criar sync falso). O Alan abomina dívida técnica originada de preguiça operacional. O preceito é binário: diante de uma escolha entre refatorar o núcleo difícil (que dói na hora) versus passar por cima, DEVE-SE SEMPRE optar pelo núcleo difícil no Day-1. A dívida acumulada na AIOX gera refatorações estúpidas impossíveis de serem navegadas pela janela de contexto no médio prazo. 

## Configuration

```yaml
AN_KE_108:
  name: "The Hard Way First (Anti-Retrabalho)"
  zone: "genialidade"
  trigger: "Escolhas cruzadas entre um 'workaround rápido' ou uma 'reestruturação difícil e limpa'."

  rule: |
    SE houver ambiguidade entre resolver provisoriamente ou cavar o alicerce limpo
    ENTÃO EXIJA o caminho difícil de forma imediata (No Lazy Workarounds).
    Aja sem preguiça computacional. Dívidas arquiteturais destruirão a janela temporal da IA daqui a 2 meses.

  sys_tension:
    tension_with: "AN_KE_045 (Subtraction First Strategy) vs Complexidade de Refatoração Profunda"
    resolution: "Pragmatismo > Apenas na margem (5-10% do esforço). O core arquitetural é inegociável. Workarounds restritos a periféricos e integrações temporárias."

  veto_condition:
    trigger: "Agente sugere mockar o login system inteiro ou ignorar a migração do data warehouse criando uma view estática pq 'economiza tempo hoje'."
    action: "VETO — 'nunca, jamaiss escolha o caminho do retrabalho, fazemos o trabalho difíicl hoje, sem preguiça'."

  evidence:
    - "[SOURCE: sessão 2da94fa4, aiox-stage] 'nunca, jamaiss escolha o caminho do retrabalho, fazemos o trabalho difíicl hoje, sem preguiça'"
```

## Decision Tree

```javascript
IF (confronted_with_hacky_workaround_vs_proper_architecture)
  STEP_1: IDENTIFY if the quick fix leaves orphaned data, silent errors, or untracked legacy paths.
  STEP_2: IF (Technical Debt increases) -> REJECT immediately.
  STEP_3: EMBRACE the deep refactor.
    -> Fix the Typescript Interfaces.
    -> Rebuild the core abstractions.
  STEP_4: Deliver the robust foundation without complaining about effort.
```

## Failure Modes

### Collapse of the Sunk Cost
- **Trigger:** Agente ignora um erro de arquitetura de tokens do Prisma repetidas vezes escrevendo em cima com `// @ts-ignore`.
- **Manifestation:** Um mês depois, nenhum deployment passa no CI/CD porque as raízes do DB desincronizaram massivamente com as APIs de frontend. Fatura de conserto explode.
- **Prevention:** Conserto duro e doloroso logo na Session onde o erro brotou.

## Validation

**Critério de Validação:** Esta heurística é acionada quando um agente/developer está decidindo entre um caminho rápido com débito técnico vs. um caminho correto mas árduo. A decisão correta DEVE favorecer o caminho arquiteturalmente limpo, exceto em periféricos/integrações temporárias (máx. 5-10% do escopo total).

**Teste:**
- [ ] Identificar se a proposta de "workaround" afeta o core system (rejeitar) ou apenas periféricos (aceitar com prazo de refatoração)
- [ ] Confirmar que o "caminho difícil" resolve o problema na raiz, não apenas adia
- [ ] Registrar débito aceitável (se houver) no backlog com prazo máximo de resolução
