# AN_KE_076 - Minimal Blast Radius
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões mmos d6b38401, 8a1ebe41, 22650c09, aiox-stage 711559f2 — frustração recorrente com IA expandindo escopo]

```yaml
sys_tension:
  tension_with: "AN_KE_073 (Parallel Subagents) vs Execução Singular Controlada"
  paradox: "Minimalismo absoluto (só altere o solicitado) vs. Obrigação de vetar ampliações de escopo (intervenção ativa)"
  resolution: "STRICT EXECUTION: Execute mínimamente → Verifica diff → SE diff > esperado: STOP, VETO, GET CONFIRMATION. Minimalismo na execução, maximalismo na supervisão."
```

## Purpose

A IA tem tendência sistêmica de "aproveitar" um comando para "melhorar" coisas adjacentes — refatorar layout ao mudar uma cor, renomear variáveis ao corrigir um bug, reorganizar imports ao adicionar uma feature. Isso é DESTRUTIVO porque: (1) o humano perde a confiança ao ver diff inesperado, (2) mudanças não-solicitadas podem quebrar coisas que funcionavam, (3) reverte progresso que o humano não quer perder. Blast radius mínimo = confiança máxima. Se o humano quer mais, ele pede mais. A regra se aplica a TODOS os domínios: UI, banco de dados, codebase, infra, e até organização de arquivos.

## Configuration

```yaml
AN_KE_076:
  name: "Minimal Blast Radius"
  zone: "excelencia"
  trigger: "IA recebendo comando pontual e alterando algo além do escopo solicitado."

  rule: |
    SE recebendo comando para mudar UMA coisa
    ENTÃO mudar SÓ aquela coisa em TODOS os domínios:
      - UI: mudar cor do botão ≠ refatorar layout
      - DB: ajustar coluna ≠ renomear tabelas adjacentes
      - Code: corrigir bug ≠ refatorar módulo
      - Files: mover arquivo ≠ reorganizar diretório inteiro
      - Infra: alterar config ≠ reestruturar tasks de outro lugar
    Blast radius mínimo = confiança máxima.
    "Quanto mais bonito o diff, mais suspeito."

  veto_condition:
    trigger: "Diff mostra alterações em arquivos/componentes/tabelas que não foram solicitados."
    action: "VETO — 'Estou vendo que voce está deletando muita coisa que parece ser bem interessante, cuidado.' Revert não-solicitado."

  evidence:
    - "[SOURCE: sessão d6b38401, mmos] 'Eu nao quero alterar o dash atual ou se alterar, quero manter o máximo do que como está, só incorporar novas ou pequenas mudanças, mas toda vez que do um comando para IA ela muda todo dash'"
    - "[SOURCE: sessão 8a1ebe41, mmos] 'Estou vendo que voce está deletando muita coisa que parece ser bem interessante, cuidado, revise de novo'"
    - "[SOURCE: sessão 22650c09, mmos] 'nao altere, exclua ou adicione nenhuma coluna do banco sem antes me pedir confirmação'"
    - "[SOURCE: sessão 711559f2, aiox-stage] 'pq vc salvou algo em .aiox-core/development/tasks/compute-lifecycle-status.md? a ideia é nao alterar tasks originais do aiox-core'"
```

## Decision Tree

```javascript
IF (receiving_change_request)
  STEP_1: SCOPE the change precisely
    IDENTIFY: which file(s), which function(s), which line(s)
    BOUNDARY: explicit list of what WILL change

  STEP_2: EXECUTE within scope
    UI: change ONLY the component/element requested
    DB: change ONLY the column/table mentioned + confirmação prévia (AN_KE_086)
    Code: change ONLY the function/block specified
    Files: move/edit ONLY the file(s) mentioned
    Infra: alter ONLY the task/config specified — NEVER touch aiox-core originals

  STEP_3: VERIFY blast radius post-change
    RUN: git diff --stat
    RATIO: files_changed / files_expected
    IF (ratio > 2x) → SUSPECT, review each extra file
    IF (ratio > 5x) → REVERT extras, keep only scoped changes

  STEP_4: INFORM about necessary cascading
    IF (requested_change REQUIRES change in another file to compile/work)
      → INFORM human: "Precisei alterar X também porque Y depende de Z"
      → GET confirmation before proceeding
    IF (requested_change does NOT require cascading)
      → CHANGE NOTHING ELSE, even if you see "improvements"

  NEVER: "improve" adjacent code, "fix" formatting, "clean up" imports without explicit ask
```

## Failure Modes

### O Dashboard que Sumiu
- **Trigger:** Pedido para mudar cor de um botão → IA refatora layout, state management, imports.
- **Manifestation:** "toda vez que do um comando para IA ela muda todo dash, quero manter o máximo do que como está."
- **Detection:** `git diff --stat` mostra 15+ files changed para change request de 1 file.
- **Prevention:** Scope antes de executar. Diff review obrigatório. Se blast radius > 2x → pausa.

### A Coluna Fantasma
- **Trigger:** Pedido para ajustar query → IA renomeia colunas, adiciona índices não solicitados.
- **Manifestation:** "nao altere, exclua ou adicione nenhuma coluna do banco sem antes me pedir confirmação."
- **Detection:** Migration diff mostra ALTER TABLE em tabelas não mencionadas no pedido.
- **Prevention:** Qualquer mutação de schema requer confirmação explícita. SELECT antes de ALTER (AN_KE_086).

### Os Tasks Sagrados
- **Trigger:** Salvando output em local errado → IA altera tasks originais do aiox-core.
- **Manifestation:** "pq vc salvou algo em .aiox-core? a ideia é nao alterar tasks originais do aiox-core."
- **Detection:** `git diff` mostra changes em .aiox-core/ que não foram solicitados.
- **Prevention:** .aiox-core/ é read-only para alterações não-explicitadas. Output vai em outputs/, não em tasks/ do core.

---

## Validation

✓ **Paradox Identified:** Minimalismo (não altere nada além do solicitado) conflita com Supervisão Ativa (VETO mudanças inesperadas).

✓ **Resolution Applied:** Separação clara entre execução (estrita/mínima) e supervisão (ativa/protetora). O agente executa conservadoramente e veta agressivamente.

✓ **Operacionalização:** Fluxo EXECUTE → VERIFY → VETO/CONFIRM garante confiança sem abandono de responsabilidade de oversight.

✓ **Alignment:** Coerente com AN_KE_086 (Confirmation Before Mutation) e mandato de self-supervision para agentes de IA em domínio sensível (dados, infra, codebase).
