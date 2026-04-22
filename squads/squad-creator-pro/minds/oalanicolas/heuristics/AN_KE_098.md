# AN_KE_098 - 100 Tests Before Deterministic (Complex Domains)
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão sinkra-hub 2026-03-30 — correção ao vivo de arquitetura zone-classifier]

## Purpose

Para domínios de EXATAS (contagem, formatação, schema validation), Worker determinístico é seguro desde o dia 1. Para domínios COMPORTAMENTAIS (classificar qualidade, julgar heurísticas, avaliar impacto humano), NÃO automatizar até ter 100+ exemplos validados por humano+LLM. O padrão só emerge com volume de dados de qualidade.

## Configuration

```yaml
AN_KE_098:
  name: "100 Tests Before Deterministic (Complex Domains)"
  zone: "genialidade"
  trigger: "Propondo automatizar com Worker/script algo que envolve julgamento humano ou análise comportamental."

  rule: |
    SE domínio é EXATAS (contagem, formato, regex, schema)
    ENTÃO Worker determinístico AGORA. Zero risco.
    SE domínio é COMPORTAMENTAL (classificar qualidade, julgar impacto, avaliar unicidade)
    ENTÃO humano + LLM PRIMEIRO → acumular 100+ testes validados → SÓ ENTÃO extrair padrões determinísticos.
    Antes de 100 testes, não há dados suficientes pra saber o que é padrão e o que é exceção.

  sys_tension:
    tension_with: "AN_KE_097 (Fail-Safe Small Batches) vs 100 Testes Antes de Determinismo"
    description: "Requer 100+ testes validados para automatizar análise comportamental, MAS a própria classificação do domínio (se é comportamental ou exatas) É UMA TAREFA COMPORTAMENTAL que pressupõe semântica. Bootstrap semântico: necessário humano+LLM para validar os primeiros exemplos, estabelecer âncoras semânticas, e SÓ DEPOIS acumular volume."
    resolution: "Resolver em 3 fases: (1) Humano establece semântica inicial para ~30 exemplos-âncora; (2) LLM infere padrões e gera hipóteses para próximos 70; (3) Padrões validados em 100+ → extrair determinismo. A semântica initial bootstrapeia o volume. Não é sequencial puro; é iterativo."

  veto_condition:
    trigger: "Criar Worker Python com IF/ELSE para classificar heurísticas em zones de Pareto."
    action: "VETO — Classificar se algo é 'paradigm-defining' (0.8%) requer entender SIGNIFICADO, não contar campos. Humano+LLM primeiro."

  evidence:
    - "[SOURCE: sessão 2026-03-30] 'até termos muitos dados de qualidade nao vale a pena criar um worker, primeiro precisamos garantir qualidade com humano e LLM e quando identificarmos padroes solidos, de preferencia acima de 100 testes e entao, temos algo para extrair algo mais deterministico quando diz respeito a analises complexas como comportamento humano, quando nao é algo de exatas'"
    - "[SOURCE: sessão 2026-03-30] Correção de zone-classifier de Worker→Agent: classificar zona requer entender significado, julgar impacto relativo, avaliar unicidade — tudo semântico"
```

## Decision Tree

```javascript
IF (proposing_deterministic_automation)
  CLASSIFY domain:
    EXACT_SCIENCE (counting, formatting, regex, schema, paths)
      → Worker/Script IMMEDIATELY. $0, 100% reliable.
    BEHAVIORAL (quality judgment, impact assessment, uniqueness, classification)
      → CHECK: how many validated examples exist?
        IF (examples < 100)
          → KEEP as Human + LLM. Accumulate validated data.
        IF (examples >= 100)
          → ANALYZE patterns in the 100+ examples
          → EXTRACT deterministic rules WHERE patterns are solid
          → KEEP LLM for edge cases where patterns are weak
```

## Failure Modes

### O Worker Prematuro
- **Trigger:** Criar IF/ELSE Python para classificar heurísticas como 0.8%/4%/20%/80%.
- **Manifestation:** Worker classifica "reality_arbitration" (paradigm-defining para Elon Musk) como 20% porque não tem campo "is_unique=true". O script não entende semântica.
- **Detection:** Classificações absurdas: heurísticas de genialidade classificadas como impacto genérico.
- **Recovery:** Reverter para Human+LLM até ter dados de treinamento suficientes.
- **Prevention:** Regra dos 100: SÓ automatizar domínio comportamental após 100+ exemplos validados.

## Integration with Workflow

```yaml
checkpoint:
  id: "deterministic-maturity-gate"
  heuristic: AN_KE_098
  phase: "Automation_Architecture"

  validation_questions:
    - "Esse domínio é exatas ou comportamental?"
    - "SE comportamental: temos 100+ exemplos validados por humano?"
    - "SE < 100: quem vai julgar até lá? (Human+LLM)"
```

## Validation

**Semântica Inicial (Fases 1-2):**
- [ ] Humano estabeleceu semântica em 20-30 exemplos-âncora?
- [ ] LLM consegue gerar hipóteses baseado nas âncoras?
- [ ] Hipóteses validadas em ≥50% dos casos novos?

**Volume & Padrão (Fase 3):**
- [ ] Acumulado ≥100 exemplos com semântica consistente?
- [ ] Padrões comportamentais emergem em ≥70% da massa?
- [ ] Existe margem semântica para exceções (≤30%)?

**Determinismo (Após Phase 3):**
- [ ] Worker proposto cobre padrão majoritário (≥70%)?
- [ ] LLM retém casos de borda (exceções semânticas)?
- [ ] Coexistência Worker+LLM testada em batch?

**Paradoxo Resolvido?**
- [ ] Tensão com AN_KE_097 documentada e aceita?
- [ ] Bootstrap semântico inicial internalizado pelo time?
- [ ] Diferenciação clara entre EXATAS (determinismo dia 1) e COMPORTAMENTAL (fase 3)?
