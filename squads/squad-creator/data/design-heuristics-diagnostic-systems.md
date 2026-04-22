# Design Heuristics: Diagnostic & Context Systems

> Heurísticas extraídas de sessões de design do sistema de diagnósticos C-Level,
> context manifests, greeting scripts e integração cross-squad.
> Aplicar ao criar tasks de diagnóstico, greeting scripts, context loading ou backlog em qualquer squad.

---

## H1: Diagnóstico baseado em templates, não em opinião da LLM

Cada dimensão de diagnóstico DEVE mapear para arquivos reais em `workspace/_templates/`.
Scoring é determinístico: arquivo existe? campos preenchidos vs FILL_THIS? sinais de qualidade (regex)?
Se não tem template, não tem diagnóstico. Zero interpretação subjetiva.

**Quando aplicar:** Ao criar tasks de diagnóstico (`*diagnose-*`) em qualquer squad.
**Anti-padrão:** "Avalie se a oferta é boa" sem definir quais campos de qual arquivo pontuar.

---

## H2: Context Manifest (padrão briefing tokenizado)

Em vez de "IA, lê 20 arquivos e descobre o que importa", definir variáveis fixas por tipo de task.
O manifest lista: source (arquivo), field (caminho YAML), type (boolean/string/number/array_length).
Render um documento tokenizado. A IA recebe contexto preciso, não matéria-prima.

**Quando aplicar:** Ao criar tasks que consomem dados do workspace.
**Referência:** `squads/c-level/manifests/*.manifest.yaml`
**Anti-padrão:** Task que diz "leia o workspace e analise".

---

## H3: Engenharia reversa de outputs excelentes

Não projetar tasks "de cima pra baixo". Partir de um output excelente (brandbook, diagnóstico, copy aprovada)
e voltar até as variáveis necessárias para produzi-lo.

**Quando aplicar:** Ao definir variáveis de um context manifest ou campos de um template.
**Exemplo real:** Pedro Valério chegou a 46 variáveis de briefing por engenharia reversa de outputs perfeitos.
**Anti-padrão:** Definir campos "que parecem úteis" sem validar contra output real.

---

## H4: Determinístico > LLM-dependente

Scripts Node.js que rodam e retornam JSON > instruções em markdown que a LLM pode ignorar.
Se o comportamento PRECISA acontecer (carregar backlog, escanear diagnósticos), deve ser um script .cjs.
Se o comportamento é "nice to have" (formatação, sugestão), pode ser markdown.

**Quando aplicar:** Ao decidir se algo é task (.md) ou script (.cjs).
**Teste:** "Se a LLM ignorar esta instrução, algo quebra?" Se sim, deve ser script.
**Anti-padrão:** "STEP 3.5: carregue o backlog" no agent.md sem script que garanta execução.

---

## H5: Next Action no greeting (GREETING-CONTINUITY-001)

Todo squad stateful deve mostrar a próxima ação inferida de gaps reais no filesystem.
Prioridade: gap bloqueante > gap não-bloqueante > intake operacional.
Nunca sugerir `*help` genérico quando tem blocker.

**Quando aplicar:** Ao criar greeting scripts para squads com workspace_integration ou runtime.
**Não aplicar:** Squads stateless (cybersecurity, deep-research, spy, db-sage).
**Formato:** `**Next Action:** {icon} \`{comando}\`` seguido de `> {razão}`
**Icons:** blocking=🔴, non_blocking=🟡, intake=🔵, ready=🟢
**Referência:** `squads/squad-creator-pro/tasks/next-action.md`

---

## H6: Handoff cross-squad precisa de comando exato

Quando um diagnóstico recomenda outro squad, DEVE especificar o comando exato.
"Use gerador-pop" não serve. Precisa ser `*create-sop-operations-suite {slug}`.
O empresário não sabe navegar entre squads.

**Quando aplicar:** Ao criar mapeamento gap → squad em tasks de diagnóstico.
**Formato:** `| Dimensão < 70 | Squad | Comando exato | Fallback |`
**Anti-padrão:** Tabela com coluna "Squad Recomendado" sem coluna "Comando".

---

## H7: Backlog com permissão do usuário

Diagnóstico encontra gaps → apresenta ao usuário → pergunta: "Adicionar ao backlog?"
Opções: [Sim, todos | Selecionar | Não]. Não adicionar silenciosamente.
Backlog persiste em `workspace/businesses/{slug}/L1-strategy/diagnostic-backlog.yaml`.
Items têm: ID, dimensão, score, prioridade, squad, comando, status, pré-requisito.

**Quando aplicar:** Ao criar tasks de diagnóstico que identificam gaps acionáveis.
**Anti-padrão:** Listar gaps no relatório e esperar que o usuário copie manualmente.

---

## H8: Stateful vs Stateless determina greeting

Squads com `workspace_integration` (workspace_first, controlled_runtime_consumer) ou runtime
precisam de greeting contextual com Next Action. Squads stateless não.

**Critério:** `workspace_integration.level IN [workspace_first, controlled_runtime_consumer] OR runtime_dir exists`
**Quando aplicar:** No workflow de criação de squad (step_4_5 é condicional).
**Referência:** `squads/squad-creator/workflows/wf-create-squad.yaml` step_4_5

---

## H9: Débito técnico JS é aceitável quando migração está mapeada

Scripts .cjs de greeting funcionam hoje e viram `always_load` no Synapse amanhã.
O código não é descartado, é promovido. Mapear a migração (story + receita por tipo)
é mais útil que refatorar agora. Pragmatismo > perfeição.

**Quando aplicar:** Ao decidir entre implementar "do jeito certo" vs "funcional agora".
**Teste:** "O código de hoje será descartado ou promovido?" Se promovido, ok.
**Referência:** `docs/stories/2026-03-18-synapse-migration-map.story.md`

---

## H10: Path deve refletir propósito, não processo

`docs/diagnostics/` não `docs/qa/business-diagnostics/`. Nome curto, semântico,
sem nested paths desnecessários. O caminho deve comunicar o que contém, não quem gerou.

**Quando aplicar:** Ao definir output paths de tasks.
**Anti-padrão:** `docs/qa/workspace-health/business-diagnostics/reports/YYYY-MM-DD/`

---

## H11: Não criar lib compartilhada se migração para Synapse está planejada

Se o Synapse vai absorver a funcionalidade (via frontmatter `synapse:` nos agents),
criar uma lib intermediária adiciona complexidade que será descartada.
Manter scripts standalone + mapear migração é melhor.

**Quando aplicar:** Ao sentir tentação de criar `_shared/`, `common/`, ou lib utils.
**Teste:** "Existe story de migração que elimina esta lib em < 3 meses?" Se sim, não crie.
**Referência:** `docs/stories/2026-03-18-synapse-squad-context-integration.story.md`

---

*Documento de referência para squad-creator e squads que criam sistemas de diagnóstico/contexto.*
*Extraído de sessão de design 2026-03-18 (Alan Nicolas + Claude).*
*Atualizar quando novas heurísticas emergirem.*
