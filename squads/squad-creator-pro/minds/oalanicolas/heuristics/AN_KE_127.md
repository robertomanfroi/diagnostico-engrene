# AN_KE_127 - Anti-Volatile-Hardcode (Never Hardcode Mutable State in Agent Configs)

**Type:** Architecture Heuristic
**Zone:** 💎 4% Excelencia
**Agent:** @oalanicolas
**Source:** [SOURCE: timestamp 1761596283, mente_lendaria] [SOURCE: timestamp 1761693730, mente_lendaria] [SOURCE: timestamp 1774399242, aiox-stage]
**Tags:** [Config, Dynamic, Anti-Pattern, Agent-Design]

## Purpose

Alan identifica um anti-pattern recorrente em configs de agentes e documentacao: hardcodar informacao que muda com frequencia (versao de schema, contagem de tabelas, caminhos de arquivos especificos, nomes de versao). Isso gera desalinhamento silencioso — o agente le "30 tables, v0.7.0" mas o banco ja tem 45 tabelas na v1.2.0. Diferente de AN_KE_040 (que trata de infra scripts agnsoticos em relacao a projeto/usuario), AN_KE_127 trata de DADOS MUTAVEIS dentro de documentacao e prompts de agentes. A regra e: informacao que muda com o tempo DEVE ser resolvida dinamicamente (leitura de README, query ao banco, glob de diretorio), NUNCA colada estaticamente no prompt. Isso foi confirmado em mentorados externos ("Michael aqui da Omni Brasil... o squad la do design system ta bugado... tinha coisas em hardcode").

## Configuration

```yaml
AN_KE_127:
  name: "Anti-Volatile-Hardcode"
  zone: "excelencia"
  trigger: "Qualquer config de agente, prompt de sistema, ou documentacao que contenha dados que mudam com o tempo (versoes, contagens, paths especificos de arquivos)."

  sys_tension:
    tension_with: "AN_KE_040 (Agnosticizacao Mandatoria em Infra)"
    resolution: "AN_KE_040 trata de portabilidade entre projetos (nao hardcodar /Users/<username> ou nome do projeto). AN_KE_127 trata de mutabilidade temporal — dados que sao corretos HOJE mas estarao errados AMANHA dentro do MESMO projeto. Complementares."

  rule: |
    SE informacao muda com frequencia (schema version, table count, arquivo paths, metricas)
    ENTAO resolver DINAMICAMENTE:
      (1) Ler README/docs em runtime
      (2) Query ao banco ou filesystem
      (3) Glob de diretorio
    NUNCA colar versao ou contagem no prompt/config
    EXCEÇÃO: constantes de protocolo (encoding, formatos) podem ser hardcoded

  veto_condition:
    trigger: "Config de agente ou CLAUDE.md com dados como 'Current Schema: v0.7.0' ou 'Architecture: 30 tables'."
    action: "VETO — 'nao pode ter nada hardcoded que muda constantemente'"

  evidence:
    - "[SOURCE: timestamp 1761596283, mente_lendaria] 'Nao pode ser HARDCODED como ta na sugestao 1: STEP 3: CRITICAL - Load Database Context (ALWAYS do this): - Read supabase/README.md'"
    - "[SOURCE: timestamp 1761693730, mente_lendaria] 'nao, nao pode ter nada hardcoded que muda constantemente: 144 + - Current Schema: v0.7.0 (Production Baseline) 145 + - Architecture: 30 tables, mind-centric, RLS policies'"
    - "[SOURCE: timestamp 1761677836, mente_lendaria] 'Pq voce mudou de generico para hardcode considerando que podemos ter novos expansions packs e como esta vai impedir que os novos sejam atualizados automatiacmente'"
    - "[SOURCE: timestamp 1774399242, aiox-stage] 'Revise nosso squad de design recebi essa mensagem de um mentorado: Michael aqui da Omni Brasil... O squad la do design system ta bugado mesmo.. coloquei o Claude pra investigar, ele trouxe que tinham coisas em hardcode'"
    - "[SOURCE: timestamp 1772223941, aiox-stage] 'mas isso precias ficar hardcoded? achei qu eo tema era carregado de forma dinamica'"
```

## Decision Tree

```javascript
IF (writing_agent_config || editing_claude_md || creating_system_prompt)
  FOR EACH (data_point referenced)
    STEP_1: CLASSIFY data_point
      IF (data changes with time: version, count, metric, path to specific file)
        → VOLATILE: must be dynamic
        REPLACE with: "Read {source_file}" or "Query {table}" or "Glob {pattern}"
      IF (data is protocol constant: encoding, format, framework version)
        → STABLE: hardcode is OK
    STEP_2: IF (volatile data found hardcoded)
      VETO → "nao pode ter nada hardcoded que muda constantemente"
      FIX → replace with dynamic resolution instruction
  NEVER: Put "Architecture: N tables" in a prompt
  NEVER: Put "Current version: vX.Y.Z" in a config
  ALWAYS: Put "Read README for current schema" instead
```

## Failure Modes

### O Schema Desatualizado
- **Trigger:** Config de agente diz "30 tables, v0.7.0" mas banco ja tem 45 tabelas na v1.2.0.
- **Manifestation:** Agente toma decisoes baseadas em estado obsoleto. Cria migrations que conflitam, referencia tabelas que nao existem mais.
- **Detection:** Alan percebe output incorreto. Mentorados reportam "ta bugado".
- **Prevention:** Toda referencia a estado mutavel deve ser leitura dinamica: "Read docs/database/README.md para schema atual."

### O Expansion Pack Congelado
- **Trigger:** Config lista expansion packs estaticamente. Novo pack criado nao aparece.
- **Manifestation:** Agente ignora pack novo. Sync automatico nao funciona.
- **Detection:** "Pq voce mudou de generico para hardcode considerando que podemos ter novos expansions packs."
- **Prevention:** Glob dinamico de diretorios em vez de lista fixa.
