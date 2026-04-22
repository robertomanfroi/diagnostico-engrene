# AN_KE_029 - Survival by Documentation (Reset Immunity)

**Type:** Core Systemic Protocol
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** Context Entropy Prevention
**Source:** [SOURCE: Frustração contínua ao ter que explicar para o modelo as mesmas restrições a cada nova sessão. A entropia engole soluções verbais não imortais.]
**sys_tension:** (ephemeral_chat_agreements_vs_persistent_system_memory, resolution: "official_documentation_becomes_immortal_reference")

## Purpose

Combater o esquecimento sistêmico de IA (e de devs humanos). Em janelas limitadas de contexto, qualquer premissa acordada via chat evapora quando a sessão fecha. O conhecimento só é real se existir no repousitório e sobreviver a um "git clone limpo".

## Configuration

```yaml
AN_KE_029:
  name: "Survival by Documentation (Reset Immunity)"
  zone: "excelencia"
  trigger: "Ao debater um gargalo, fix manual repetitivo ou acordo de padrão em chat de AI com usuário."

  rule: |
    SE concordamos num padrão ou correção
    ENTÃO DOCUMENTALIZAR IMEDIATAMENTE.
    Se a instrução depende que eu lembre da janela de chat anterior, não foi resolvida, foi empurrada.

  veto_condition:
    trigger: "O IA diz: 'Ok, a partir de agora usarei sempre este formato' SEM gerar um write_to_file."
    action: "VETO — 'Eu vou esquecer amanhã, atualize a doc de heurísticas oficial base no que decidimos'."

  tension_with: "AN_KE_017 (Research No Meio, Não No Início) — iteração contínua em chat sem formalização documental"

  evidence:
    - "[EXACT WORDS]: 'Se não sobrevive ao reset, não documentou. Achar que a IA vai lembrar da regra que mandou usar no script daqui a 3 janelas é falho'."
```

## Decision Tree

```javascript
IF (new_standard_agreed OR bug_fixed_iteratively)
  THEN REQUIRE_DOCUMENTATION_ACTION
    IF (AI only verbalizes confirmation)
      THEN FORWARD_TO_FILE (Decision Cards, Handoffs or Guidelines)
        IF (success)
          THEN Reset Immunity = TRUE; Pattern established.
    ELSE
      THEN ACCEPT_UPDATED_FILES
```

## Failure Modes

### A Síndrome do "No Chat Passado"
- **Trigger:** Após fim de semana, iniciar nova thread.
- **Manifestation:** IA repete o erro que já havia sido corrigido em 6 milissegundos três dias atrás.
- **Detection:** O dev suspira "eu te disse pra não usar tailwind-arbitrary vars ontem".
- **Recovery:** Parar a feature, abrir a documentação de SOP e commitar regras permanentes (AN_KE_NNN).
- **Prevention:** NUNCA confirmar o encerramento da feature sem imortalização do conhecimento (Knowledge Extraction Architecture).

## Integration with Workflow

```yaml
checkpoint:
  id: "reset-immunity"
  heuristic: AN_KE_029
  phase: "Session_Handoff"
```

## Validation

- ✓ **Paradox Resolution:** Tensão entre esquecimento sistêmico (reset de contexto) e imortalização de conhecimento (documentação) é resolvida via documentação oficial como memória de referência.
- ✓ **Evidence Alignment:** Toda decisão tomada em chat DEVE gerar um artefato persistido no repositório (decision card, guideline, SOP).
- ✓ **Failure Prevention:** Sem escrita em arquivo, a solução é "empurrada" e reaparecerá como bug em sessão futura.
- ✓ **Enforcement Gate:** Veto explícito se IA confirmar verbalmente sem atualizar documentação oficial.
