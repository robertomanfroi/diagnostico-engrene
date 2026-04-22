# AN_KE_131 - Anti-Document-Pollution (Kill Junk Reports)

**Type:** Information Hygiene Heuristic
**Zone:** 💎 4% Excelencia
**Agent:** @oalanicolas
**Source:** [SOURCE: timestamp 1766024285, mmos] [SOURCE: timestamp 1766930774, mmos] [SOURCE: timestamp 1761853141, mente_lendaria]
**Tags:** [Documentation, Hygiene, Anti-Pattern, Cleanup]

## Purpose

Alan identifica um anti-pattern critico onde agentes de IA geram documentos explicativos, relatorios de mudancas, e backups que ninguem vai ler e que poluem a base de codigo. Isso cria entropia documental — a quantidade de documentos cresce mas a utilidade por documento cai. Os sintomas: relatorios pos-acao que repetem o que o commit ja diz, backups manuais quando git ja versiona, documentos "README_CHANGES.md" que ficam desatualizados em 24h. Alan reage com frustacao emocional intensa ("pare de criar documentos explicando as mudancas, ninguem vai ler isso so cria lixo", "esses reltorios so ficam enchendo de arquivos idiotas nossa base de documentos exclua esses"). A regra e: todo documento deve ter CONSUMIDOR claro. Se ninguem vai ler, nao crie.

## Configuration

```yaml
AN_KE_131:
  name: "Anti-Document-Pollution"
  zone: "excelencia"
  trigger: "Agente criando documento explicativo, relatorio de mudancas, backup manual, ou README que ninguem vai consumir."

  sys_tension:
    tension_with: "AN_KE_029 (Survival by Documentation) — documentar para sobreviver a resets"
    resolution: "AN_KE_029 pede documentacao para SOBREVIVENCIA (handoffs, context recovery). AN_KE_131 combate documentacao INUTIL (relatorios pos-acao que repetem commits, backups manuais, READMEs de changelog). A diferenca: handoff tem CONSUMIDOR (proxima sessao). Relatorio de mudancas NAO tem consumidor."

  rule: |
    ANTES de criar qualquer documento, responder:
      (1) QUEM vai ler isso? (humano? IA na proxima sessao? CI?)
      (2) JA EXISTE no git? (commit message, diff, log)
      (3) VAI FICAR ATUALIZADO? (se nao, nao crie)
    SE nenhum consumidor claro → NAO CRIAR
    SE informacao ja esta no git → NAO DUPLICAR em documento
    SE documento vai desatualizar em < 7 dias → NAO CRIAR (ou criar como efemero)
    BACKUPS manuais sao PROIBIDOS — git e o unico controle de versao (AN_KE_066)
    RELATORIOS de mudancas sao PROIBIDOS — commit messages existem

  veto_condition:
    trigger: "Agente criando documento que descreve mudancas que acabou de fazer, ou backup manual de arquivo."
    action: "VETO — 'pare de criar documentos explicando as mudancas, ninguem vai ler isso so cria lixo'"

  evidence:
    - "[SOURCE: timestamp 1766024285, mmos] 'pare de criar documentos explicando as mudancas, ninguem vai ler isso so cria lixo'"
    - "[SOURCE: timestamp 1766930774, mmos] 'esses reltorios so ficam enchendo de arquivos idiotas nossa base de documentos exclua esses'"
    - "[SOURCE: timestamp 1766031287, mmos] 'eu nao quero saber desses documentos eles devem ser temporarios, quero que tu melhore eles e depois exclua essa porcaria'"
    - "[SOURCE: timestamp 1761853141, mente_lendaria] 'uma boa pratica que precisamos ter, e de nao ficar criando trocentos documentos e backups deles que vao acumulando, nos ja temos o git, e deve ser uma boa pratica versionar com git e nao fic'"
    - "[SOURCE: timestamp 1761550661, mente_lendaria] 'Ainda tem MUITO documento em docs, precisamos organizar e mandar para log geral do sistema o que ja nao precisa mais estar la'"
```

## Decision Tree

```javascript
IF (about_to_create_document)
  STEP_1: IDENTIFY consumer
    WHO will read this? (human, AI next session, CI pipeline, nobody?)
    IF (consumer == "nobody" || consumer == "maybe someday")
      BLOCK → "ninguem vai ler isso so cria lixo"
  STEP_2: CHECK redundancy
    IF (information already in git commit message) → BLOCK
    IF (information already in existing doc) → UPDATE existing, don't create new
    IF (information is backup of existing file) → BLOCK (git is versioning)
  STEP_3: CHECK lifespan
    IF (document will be outdated in < 7 days) → CREATE as ephemeral or DON'T CREATE
    IF (document is changelog/post-action report) → BLOCK
  ALLOWED documents:
    - Handoffs (consumer: next session AI)
    - Architecture docs (consumer: future developers)
    - Session logs (consumer: human review)
  BLOCKED documents:
    - "What I changed" reports
    - Manual backups of files
    - READMEs that duplicate git log
```

## Failure Modes

### A Entropia Documental
- **Trigger:** Agente cria 5+ documentos por sessao descrevendo mudancas feitas.
- **Manifestation:** Pasta /docs cresce descontroladamente. Documentos ficam desatualizados em dias. Busca por informacao relevante fica impossivel.
- **Detection:** Alan explode: "esses reltorios so ficam enchendo de arquivos idiotas."
- **Prevention:** Todo documento precisa de consumidor declarado. Zero documentos "just in case."

### O Backup Manual no Supabase
- **Trigger:** Agente "faz backup" duplicando tabela no banco antes de migration.
- **Manifestation:** Banco poluido com tabelas _backup, _old, _bkp que ninguem limpa.
- **Detection:** Alan encontra tabelas duplicadas e reage com furia.
- **Prevention:** Git e o unico controle de versao. Backup = branch ou tag, nunca duplicacao.
