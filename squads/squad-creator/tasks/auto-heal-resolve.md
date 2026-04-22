# Task: Auto-Heal — Resolve

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `auto-heal-resolve` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Hybrid` |

## Metadata

```yaml
id: auto-heal-resolve
name: "Auto-Heal — Resolve"
category: runtime
agent: squad-chief
elicit: false
autonomous: true
description: "Diagnostica o erro, classifica severidade, e aplica fix seguro ou escala para ação humana. Uma única unidade de decisão: diagnóstico determina o caminho (fix ou escalada)."
accountability:
  human: squad-operator
  scope: full
domain: Operational
```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::auto_heal_resolve
Output: artifact::auto_heal_resolve
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Determinar categoria, severidade e estratégia de remediação do erro, executando
a correção quando segura ou produzindo handoff claro para investigação humana.
Este é um único ciclo de decisão: o diagnóstico define se o caminho é fix ou escalada.

## Inputs

| Input | Tipo | Obrigatório | Descrição |
|-------|------|-------------|-----------|
| `error_message` | string | Sim | Mensagem de erro capturada |
| `error_source` | string | Não | Componente ou task de origem |
| `squad_name` | string | Não | Squad onde o erro ocorreu |
| `error_context` | object | Não | Contexto adicional (stack trace, logs) |

## Workflow

### Step 1: Diagnose

Classificar o erro e decidir a estratégia de remediação.

1. Extrair categoria do erro (schema_error, missing_file, validation_failure, permission_denied, unknown)
2. Determinar severidade (LOW, MEDIUM, HIGH, CRITICAL)
3. Identificar root cause resumida
4. Decidir `auto_fixable: true|false` com justificativa explícita
5. Se categoria = `UNKNOWN` ou severidade = `CRITICAL`, marcar `auto_fixable: false`

### Step 2: Fix or Escalate

**Caminho A -- Fix (quando `auto_fixable = true`):**

1. Criar backup do estado atual antes de qualquer modificação
2. Aplicar correção dentro do escopo permitido pelo auto-heal
3. Emitir resultado com status claro (`fix_applied`, `fix_partial`, `fix_failed`)
4. Se `fix_failed` ou `fix_partial` sem resolução, redirecionar para Caminho B

**Caminho B -- Escalate (quando `auto_fixable = false` ou fix falhou):**

1. Determinar nível de escalada (WARN, BLOCK, HALT)
2. Preparar handoff com: erro original, diagnóstico, tentativas de fix (se houve), próximo passo recomendado
3. Emitir escalada com próximo passo claro para o operador humano

## Output

```yaml
resolve_result:
  diagnosis:
    category: string       # schema_error | missing_file | validation_failure | permission_denied | unknown
    severity: string       # LOW | MEDIUM | HIGH | CRITICAL
    root_cause: string     # Resumo da causa raiz
    auto_fixable: boolean
  action_taken: string     # fix_applied | fix_partial | fix_failed | escalated
  escalation:              # Presente apenas se action_taken = escalated
    level: string          # WARN | BLOCK | HALT
    next_step: string      # Instrução para operador
    handoff: object        # Contexto completo para investigação
  backup_created: boolean
  files_modified: string[] # Lista de arquivos alterados (vazia se escalado)
```

## Acceptance Criteria

- [ ] Erro classificado em categoria conhecida ou `UNKNOWN`
- [ ] `auto_fixable` decidido explicitamente com justificativa
- [ ] Root cause resumida em texto legível
- [ ] Fix só ocorre quando `auto_fixable = true`
- [ ] Backup exigido antes de qualquer modificação
- [ ] Resultado do fix emitido com status claro
- [ ] Escalada emitida quando fix não resolve ou é vetado
- [ ] Nível de escalada explicitado (WARN, BLOCK, HALT)
- [ ] Próximo passo fica claro para o operador humano

## Veto Conditions

- NUNCA aplicar fix sem backup prévio
- NUNCA aplicar fix em erro `UNKNOWN` sem classificação prévia
- NUNCA aplicar fix em erro `CRITICAL` sem aprovação explícita
- NUNCA escalar sem incluir contexto de diagnóstico completo

## Related Documents

- `auto-heal.md`
- `auto-heal-close.md`
- `workflows/wf-auto-heal.yaml`
- `templates/auto-heal-task-tmpl.md`

---

_Task Version: 1.0.0_
