# AN_KE_102 - LLM Downgrade Defense
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 74ce8793, aiox-stage — "sem precisarmos de LLM no futuro"]

## Purpose

Inteligência Artificial de ponta (Claude 3.7 Sonnet) é uma ferramenta para orquestração, decisão arquitetural pesada e raciocínios caóticos, e não um estivador para arrumar arquivos estáticos se a regex faz isso. O Alan detesta processos escaláveis onde a automação diária torra dezenas de tokens cegamente. Ao construir um worker ou pipeline persistente, o desenvolvedor DEVE rastrear o padrão determinístico da tarefa. Se inevitável, adote downgrade de inferência: delegar processos repetitivos estritos para os Tiers inferiores de LLMs (Haiku / 8B local).

## Configuration

```yaml
AN_KE_102:
  name: "LLM Downgrade Defense (Deterministic First)"
  zone: "genialidade"
  trigger: "Desenhando extrações massivas, processadores cron-like ou conversores ETL de dados rotineiros."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) — escalabilidade via múltiplos subagents vs. simplificar para Haiku determinístico"
    resolution: "Piramide de seleção: Regex/Script (zero cost) → Haiku para classificação simples → Sonnet para decisão arquitetural pesada. A falha é usar Sonnet onde Regex serve."

  rule: |
    SE a tarefa trata manipulação em scale (parse de imagens, split de blocos textuais)
    ENTÃO PRIORIDADE ABSOLUTA: Construir via JavaScript/Bash (puro determinismo, custo zero).
    SE impossível ser determinista → Delegue prompt em `system` rígido para LLMs nível Haiku/Flash.
    Somente instâncias cerebrais críticas necessitam instanciar Tiers Master.

  veto_condition:
    trigger: "Codar um script Python que invoca o `claude-3-7-sonnet` para parsear IDs e Datas explícitos de dentro de uma lista markdown de 8.000 linhas."
    action: "VETO — 'tente entender o padrao que permitiria um script conseguir replicar isso, sem precisarmos de LLM... ou criar um prompt para uma LLM mais barata Haiku...'"

  evidence:
    - "[SOURCE: sessão 74ce8793, aiox-stage] 'tente entender o padrao que permitiria um script conseguir replicar isso, sem precisarmos de LLM no futuro, ou entao criar um prompt para que uma LLM mais barata com Haiku faca esse trabalho'"
```

## Decision Tree

```javascript
IF (creating_automation_for_repetitive_processing)
  STEP_1: CHALLENGE the LLM usage. (Does it require reasoning OR just pattern matching?)
  STEP_2: IF (Pattern Matching possible via Regex/DOM Parse/JSON path)
    -> Build a standard Script. Drop AI dependency.
  STEP_3: IF (Simple Reasoning required like minor classification)
    -> Adopt Claude-3-Haiku endpoint config.
  STEP_4: IF (Deep Context understanding required)
    -> Adopt Sonnet tier.
```

## Failure Modes

### Burn Rate Arquitetônico
- **Trigger:** Pipeline de ingestão roda chamadas API de reasoning pesado para cada log capturado da Vercel para identificar se foi "Erro TS" ou "Aviso CSS".
- **Manifestation:** Fatura Cloud Anthropic atinge $1k em 3 dias testando lixo trivial.
- **Prevention:** Pipeline Defense. Programação clássica em primeiro lugar para jobs operacionais.

---

## Validation

✓ **Paradoxo identificado:** A heurística prescreve usar LLMs avançados para decisões críticas ao mesmo tempo que veda seu uso em tarefas determinísticas, criando tensão entre custo/capacidade.

✓ **Resolução declarada:** Pirâmide de delegação (Regex → Haiku → Sonnet) garante que cada nível de complexidade use o modelo apropriado.

✓ **Applicability:** Crítica para pipelines de produção, ETL em escala e automações de longo prazo onde burn rate é mensurável.

Status: **VALID** — Paradoxo capturado, tensão resolvida via `sys_tension` field.
