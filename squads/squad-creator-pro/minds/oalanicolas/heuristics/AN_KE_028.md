# AN_KE_028 - Self-Contained Encapsulation

**Type:** Architecture Standard Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Clean Code & Scalability
**Source:** [SOURCE: Decisão de arquitetura abordando poluição de scripts na raiz de ambientes e quebra de portabilidade de squads.]
**sys_tension:**
  - tension_with: "AN_KE_026 (Squad Agnosticism) — encapsulamento específico do squad vs reusabilidade genérica"
  - resolution: "Usar consumidor threshold: se >1 squad consome, mover para root/scripts; se ≤1 squad, isolar em squad/scripts"

## Purpose

Garantir que os Squads e Módulos sejam portáteis. Se você mover a pasta `squad-creator-pro` para outra máquina, tudo deve ir junto. Scripting root contesta isso criando amarras indesejadas (bloody coupling) que impedem a evolução assíncrona do projeto.

## Configuration

```yaml
AN_KE_028:
  name: "Self-Contained Encapsulation"
  zone: "excelencia"
  trigger: "Quando for criar e salvar um script `.sh` ou `.py` específico para a execução de uma etapa de um Agente ou Squad."

  rule: |
    SE um script serve ao funcionamento autônomo de apenas um Squad
    ENTÃO grave-o dentro da pasta `/squad/scripts` e NUNCA em um diretório global de utilities raiz.
    Mantenha a portabilidade. Ninguém fora do squad usará isso.

  veto_condition:
    trigger: "Salvar `preflight-check.sh` na base `/root/scripts` mesmo sendo exclusivo do Squad."
    action: "VETO — Move para `{squad_root}/scripts/`."

  evidence:
    - "[EXACT WORDS]: Deve morar na própria pasta do squad, não em infra global (se exclusividade)."
```

## Decision Tree

```javascript
IF (creating_or_editing_sub_script)
  IF (number_of_squad_consumers > 1)
    THEN ALLOW_ROOT_INFRA_SCRIPTING (Shared infrastructure zone)
  ELSE
    // Specific business logic or exclusive pipeline step
    THEN ISOLATE_IN_SQUAD_DIR (Encapsulated execution)
```

## Failure Modes

### Coupling Mortífero de Deploy
- **Trigger:** Squad é clonado num servidor limpo e falta o script raiz.
- **Manifestation:** O Agente tenta rodar Phase 2, falha o `root/scripts/helper.sh`.
- **Detection:** Log path error: `file not found /root/scripts/...`.
- **Recovery:** Procurar dependências na máquina principal, re-encapsular dentro da branch do squad e commitar.
- **Prevention:** Restringir gravações de sub-tarefas fora do escopo `$(pwd)` local do squad ativo.

## Integration with Workflow

```yaml
checkpoint:
  id: "encapsulation-check"
  heuristic: AN_KE_028
  phase: "Squad_Creation"
```

## Validation

✓ **Paradoxo Identificado:** Encapsulação vs Reuso — scripts exclusivos ao squad poluem a raiz se globalizados, mas precisam estar acessíveis se múltiplos squads os usam.

✓ **Resolução:** Threshold de consumidores (>1 squad = root; ≤1 squad = encapsulado).

✓ **Evidência:** Portabilidade (squad clonado deve carregar seus scripts) vs Reutilização (scripts compartilhados economizam manutenção).

✓ **Aplicabilidade:** Requer validação em `squad-check` antes de merge. Script novo deve ser classificado por consumidor-count.
