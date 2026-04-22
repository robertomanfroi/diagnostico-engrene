# AN_KE_104 - Modular Generic Scripts
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 58ebd69e, aiox-stage — "sem precisar criar um novo script toda vez"]

## Purpose

Scripts "escreveu, rodou, lixou" (One-offs desvairados) espalhados na base causam inflamação sistêmica gigantesca. Processos rotineiros como consolidar artefatos de IA, extrações DDL de banco, ou parse de JSONLs tendem a ser recriados do nada pra cada pasta nova do projeto. Alan blinda o repor contra scripts inúteis cobrando a Parametrização Universal. Operações bash/node repetitivas DEVEM ser moduladas (recebendo flags CLI) para atuarem como ferramentas de orquestração atemporais em `/scripts`.

## Configuration

```yaml
AN_KE_104:
  name: "Modular Generic Scripts"
  zone: "genialidade"
  trigger: "Criando ou editando shell/node scripts operacionais do repositório (`./scripts/`)."

  sys_tension:
    tension_with: "AN_KE_050 (Inimigo Zero: Complexidade Inútil) — overhead de modularização vs. manutenção exponencial"
    resolution: "Scripts únicos (<1 dia) permitem clonagem. Scripts recorrentes (>2 usos) exigem parametrização genérica. Gate de decisão: Vai usar este script para >2 contextos? SIM → Modularize. NÃO → Clone aceito."

  rule: |
    SE o script atende um fluxo temporal de arquivos que se repetirá para outras personas ou áreas
    ENTÃO DEVE processar caminhos como Argumentos Modulares (`--input`, `--target`).
    NUNCA desenhe diretórios engessados soltos onde "apenas criar um clone do script resolve a cópia nova".
    O script deve encapsular a lógica, o utilizador define a variável.

  veto_condition:
    trigger: "Criar o `clone_pedro.sh` fixo, rodar, e depois ser instruído a clocar o Elon Musk criando o `clone_elon.sh` ao lado no mesmo formato."
    action: "VETO — 'como podemos fazer siso de forma moduarlizada paar que possamos usa rno futuro sem precisar criar um novo script toda vez?'."

  evidence:
    - "[SOURCE: sessão 58ebd69e, aiox-stage] 'quero um script paralelo como ./scripts/consolidation-phase1.sh como podemos fazer siso de forma moduarlizada paar que possamos usa rno futuro sem precisar criar um novo script toda vez?'"
```

## Decision Tree

```javascript
IF (creating_maintenance_or_pipeline_script)
  STEP_1: IDENTIFY TARGET: Is this manipulating `/squads/copy` or `/minds/pedro`?
  STEP_2: EXTRACT TARGET TO FLAGS:
    `const target = process.argv[2] || 'default-fallback';`
  STEP_3: REPLACE hardcoded paths with string interpolation.
  STEP_4: BAKE "How to Run" comments on file header demonstrating its agnostic usage.
```

## Failure Modes

### Cemitério de Scripts Abandonados
- **Trigger:** A pasta `./scripts` aloja 35 scripts soltos no repositório. Ninguém lembra que `parse-transcriptions-2024.js` faz exatamente a mesma coisa que a nova feature demanda.
- **Manifestation:** Duplicação de features fundamentais da infraestrutura resultando em manutenções em silos duplos (se conserta os logs na cópia nova, a cópia do mês passado continua quebrando em casos limite).
- **Prevention:** Um script governante universal para lógicas pareadas.

---

## Validation

✓ **Paradoxo identificado:** Modularidade demanda overhead (flags, docs, error handling) vs. imediatismo de duplicação.
✓ **Resolução:** Threshold de 2+ usos como critério binário.
✓ **Aplicabilidade:** Scripts de infra-ops, transformação de dados, orchestração de artefatos.
✓ **Trade-off:** SIM modular = manutenção centralizada + reutilização futura. NÃO modular = tech debt exponencial.
