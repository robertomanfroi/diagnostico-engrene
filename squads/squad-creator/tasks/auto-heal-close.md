# Task: Auto-Heal — Close

## Task Anatomy

| Field | Value |
|-------|-------|
| **Task ID** | `auto-heal-close` |
| **Version** | `1.0.0` |
| **Status** | `active` |
| **Responsible Executor** | `squad-chief` |
| **Execution Type** | `Worker` |

## Metadata

```yaml
id: auto-heal-close
name: "Auto-Heal — Close"
category: runtime
agent: squad-chief
elicit: false
autonomous: true
description: "Verifica resultado pós-resolve, aplica rollback quando necessário, persiste trilha auditável e emite veredito final do auto-heal."
accountability:
  human: squad-operator
  scope: review_only
domain: Operational
```


<!-- SINKRA_CONTRACT -->
Domain: `Operational`
atomic_layer: Atom
Input: request::auto_heal_close
Output: artifact::auto_heal_close
pre_condition: contexto mínimo carregado e rota validada
post_condition: decisão registrada com artefato persistido ou handoff emitido
performance: registrar evidências, falhas e próximo passo sem erro silencioso
Completion Criteria: contrato mínimo SINKRA explícito e saída rastreável produzida

## Purpose

Garantir que o auto-heal não deixa correções parciais ou regressões em aberto,
registrar o resultado completo em log auditável, e emitir o veredito final
que encerra o ciclo de heal.

## Inputs

| Input | Tipo | Obrigatório | Descrição |
|-------|------|-------------|-----------|
| `resolve_result` | object | Sim | Output da task `auto-heal-resolve` |
| `original_error` | object | Sim | Erro original que disparou o auto-heal |
| `squad_name` | string | Não | Squad onde o erro ocorreu |

## Workflow

### Step 1: Verify

Reexecutar validações pós-resolve para confirmar que o estado é consistente.

1. Se `action_taken = fix_applied`, reexecutar a validação que falhou originalmente
2. Se validação passa, marcar `verification: passed`
3. Se validação falha, aplicar política de rollback:
   - Restaurar backup criado durante resolve
   - Marcar `verification: failed_with_rollback`
4. Se `action_taken = escalated`, marcar `verification: skipped_escalated`
5. Se `action_taken = fix_failed`, marcar `verification: skipped_failed`

### Step 2: Persist

Registrar o resultado completo do ciclo de auto-heal.

1. Preparar entrada de log com:
   - Timestamp ISO 8601
   - Erro original (message, source, category)
   - Diagnóstico (category, severity, root_cause)
   - Ação tomada (fix_applied, escalated, etc.)
   - Resultado da verificação
   - Arquivos alterados ou ausência de mudanças
2. Registrar resultado (`success | failed | escalated | rolled_back`)
3. Persistir no log local do squad

### Step 3: Emit Verdict

Emitir o veredito final que encerra o ciclo.

1. Compor `heal_verdict` baseado no resultado completo:
   - `HEALED` -- fix aplicado e verificado com sucesso
   - `ROLLED_BACK` -- fix falhou na verificação, estado restaurado
   - `ESCALATED` -- problema requer intervenção humana
   - `FAILED` -- fix e rollback falharam (estado potencialmente inconsistente)
2. Se `FAILED`, emitir alerta de estado inconsistente para operador

## Output

```yaml
close_result:
  verification:
    status: string         # passed | failed_with_rollback | skipped_escalated | skipped_failed
    revalidation_output: string  # Output da reexecução (quando aplicável)
  persistence:
    logged: boolean
    log_entry_id: string   # Identificador da entrada no log
    result: string         # success | failed | escalated | rolled_back
    files_changed: string[] # Lista de arquivos alterados no ciclo completo
  heal_verdict: string     # HEALED | ROLLED_BACK | ESCALATED | FAILED
```

## Acceptance Criteria

- [ ] Retry ou validação pós-fix executado quando aplicável
- [ ] Política de rollback aplicada quando verificação falha
- [ ] Entrada de log preparada com todos os campos obrigatórios
- [ ] Resultado (`success | failed | escalated | rolled_back`) explicitado
- [ ] Arquivos alterados ou ausência de mudanças registrados
- [ ] Veredito final emitido (HEALED, ROLLED_BACK, ESCALATED, FAILED)
- [ ] Estado inconsistente alertado quando veredito = FAILED

## Veto Conditions

- NUNCA emitir veredito `HEALED` sem verificação pós-fix bem-sucedida
- NUNCA omitir rollback quando verificação falha e backup existe
- NUNCA persistir log sem resultado explícito
- NUNCA fechar ciclo sem veredito final

## Related Documents

- `auto-heal.md`
- `auto-heal-resolve.md`
- `workflows/wf-auto-heal.yaml`
- `templates/auto-heal-task-tmpl.md`

---

_Task Version: 1.0.0_
