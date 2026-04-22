# AN_KE_066 - Git is the Only Version Control
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessões mmos c8e8c269, b6e16d1d — "nunca use v2"]

## Purpose

Abolir completamente a prática amadora de gerenciar versões de arquivos usando sufixos nos nomes de arquivos (ex: `index_v2.tsx`, `schema_new.sql`, `backup_old.md`). Alan tem zero tolerância para essa proliferação de lixo digital. O versionamento de código, documentos e decisões pertence exclusivamente ao Git. Trabalhar no `sinkra-hub` ou `mmos` exige limpeza absoluta de workspace. Sempre sobrescreva o conteúdo iterando-o em cima da fonte original; a rastreabilidade vem do histórico de commits, não dos nomes de arquivo.

## Configuration

```yaml
AN_KE_066:
  name: "Git is the Only Version Control"
  zone: "excelencia"
  trigger: "Criando iterações, recriando arquivos, ou realizando backup local de scripts e documentos."
  sys_tension:
    tension_with: "AN_KE_074 (Commit Before Deletion) — Git é único vs. Proteção contra sobrescrita destrutiva"
    resolution: "Commit antes de sobrescrever. Use `git stash`, `git branch`, ou `git checkout` para reverter—não nomes de arquivo. Qualquer hesitação é um sinal de planejar melhor, não criar cópias."

  rule: |
    SE você precisar atualizar, testar ou iterar um arquivo
    ENTÃO DEVE sempre sobrescrever o arquivo original.
    NUNCA use "v2", "v3", "_new", "_old", "_backup" no nome do arquivo.
    O histórico de edições é gerenciado estritamente pelo Git.
    Qualquer sufixo de versionamento é um design smell inaceitável.

  veto_condition:
    trigger: "Criar um arquivo chamado 'script_v2.py' para manter o antigo 'script.py' seguro."
    action: "VETO — 'nunca use v2, v3 no nome de um arquivo o versionameneto acontece via git apenas'. Substitua o original."

  evidence:
    - "[SOURCE: sessão c8e8c269, mmos] 'nunca use v2, v3 no nome de um arquivo o versionameneto acontece via git apenas'"
    - "[SOURCE: sessão b6e16d1d, mmos] 'nunca use v2, v3 no nome de um arquivo o versionameneto acontece via git apenas revise todo projeto e corrija o que precisar'"
    - "[SOURCE: sessão 017a1f24, mmos] 'vamos evitar usar em arquivos, v2, v3, isso está inclusive como regra em claude.md' (mesclada via AN_KE_099)"
```

## Decision Tree

```javascript
IF (updating_file_or_making_new_version)
  STEP_1: IDENTIFY target file
  STEP_2: CHECK for temptation to create backup copy manually
    IF (creating file with suffixes like _v2, -new, -backup) → CANCEL action
  STEP_3: DESTRUCTIVE UPDATE of the original file
    ACTION: Overwrite existing file entirely
  STEP_4: RELY on Git
    If rollback is needed, use `git checkout`, `git revert`, or `git restore`
```

## Failure Modes

### O Buraco Negro do "Final_v2"
- **Trigger:** Agente que não tem confiança no refator atual decide criar `/utils/validation-v2.ts`.
- **Manifestation:** O projeto acaba com dependências aleatórias importando o V1, enquanto novas importam o V2, quebrando build com inconsistências do sistema.
- **Detection:** `ls` directory e buscar patterns `*_v[0-9]*.*`.
- **Prevention:** Deletar imediatamente e renomear com overriding da V1, refatorando todos os imports referenciados.

---

## Validation

✅ **Paradoxo identificado:** Simplicidade (Git é único) vs. Segurança (proteção contra perda).
✅ **Resolução:** Usar Git tooling (`stash`, `branch`, `checkout`) em vez de sufixos de arquivo.
✅ **sys_tension adicionado:** Tensão registrada com resolução clara.
✅ **Aplicabilidade:** AN_KE_066 reflete mandato Alan de zero tolerância a sufixos de versionamento em workspaces.
✅ **Status:** Validado e pronto.
