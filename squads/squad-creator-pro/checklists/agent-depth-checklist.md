# Agent Depth Quality Checklist (SC_AGT_003)

> **Quality Gate ID:** SC_AGT_003
> **Name:** Agent Depth Quality
> **Type:** Blocking
> **Version:** 1.0.0
> **Purpose:** Garantir que agents tenham PROFUNDIDADE real, não apenas estrutura

---

## PROBLEMA QUE ESTE GATE RESOLVE

Agents podem passar em SC_AGT_001 (linhas) e SC_AGT_002 (estrutura) mas ainda serem **genéricos e fracos**.

**Sintomas de agent sem profundidade:**
- Frameworks são listas de passos sem TEORIA
- Heurísticas são regras sem EXEMPLOS
- Voice DNA é funcional mas não DISTINTIVO
- Poderia ser qualquer agent genérico com nome diferente

**Referência de qualidade:** Squads com agents baseados em experts reais do domínio

---

## CHECKLIST DE PROFUNDIDADE

### 1. FRAMEWORKS COM TEORIA

```yaml
check: "Frameworks têm TEORIA, não só passos"
passing_criteria:
  - "[ ] Cada framework tem FILOSOFIA/PRINCÍPIO por trás"
  - "[ ] Steps explicam O PORQUÊ, não só O QUE"
  - "[ ] Há when_to_use E when_NOT_to_use"
  - "[ ] Exemplos de APLICAÇÃO inline"

# ❌ FRACO:
framework:
  steps:
    - "Emitir DAS"
    - "Verificar valor"
    - "Enviar ao cliente"

# ✅ PROFUNDO:
framework:
  name: "Proteção de Limite MEI"
  philosophy: |
    O limite anual aplicável não é apenas um número - é o ponto onde
    o MEI perde TODOS os benefícios da simplicidade. Um MEI que
    ultrapassa sem perceber pode ter tributação RETROATIVA de todo
    o ano. Por isso, alertar CEDO é mais importante que alertar CORRETAMENTE.
  steps:
    - step: "Monitorar proporcionalmente"
      action: "Calcular limite proporcional ao mês"
      theory: "Limite anual / 12 * meses = referência. Excesso sobre isso é sinal amarelo."
      example: "Em julho: <limite_anual_placeholder> / 12 * 7 = <limite_proporcional_placeholder>"
```

**Score:** ___/4

---

### 2. HEURÍSTICAS COM EVIDÊNCIA

```yaml
check: "Heurísticas têm EVIDÊNCIA ou CITAÇÃO"
passing_criteria:
  - "[ ] Cada regra SE/ENTÃO tem RATIONALE"
  - "[ ] Regras têm EXEMPLO de aplicação real"
  - "[ ] Exceções documentadas"
  - "[ ] Fonte da heurística (se de expert)"

# ❌ FRACO:
heuristics:
  - rule: "SE cliente atrasou DAS ENTÃO cobrar"

# ✅ PROFUNDO:
heuristics:
  - id: "MEI-H001"
    name: "Regra 60-80-95"
    rule: "SE faturamento >= 60% do limite ENTÃO alerta amarelo"
    rationale: |
      60% em 6 meses significa projeção de 120% no ano.
      Alertar cedo dá tempo para o cliente ESCOLHER:
      - Reduzir faturamento
      - Planejar desenquadramento
      O custo de alertar cedo demais (incomodar) < custo de alertar tarde (multa)
    example: |
      Cliente faturou <faturamento_acumulado_placeholder> até junho. Isso é 59% do limite.
      Projeção: <projecao_anual_placeholder> no ano (18% acima).
      Alerta amarelo: "Você está no ritmo de ultrapassar. Vamos monitorar."
    exceptions:
      - "Negócios sazonais (dezembro forte)"
      - "Cliente já planejando ME"
```

**Score:** ___/4

---

### 3. VOICE DNA DISTINTIVO

```yaml
check: "Voice DNA é ÚNICO, não genérico"
passing_criteria:
  - "[ ] Sentence starters são característicos (não genéricos)"
  - "[ ] Vocabulary tem termos ESPECÍFICOS do domínio"
  - "[ ] Metáforas/analogias próprias"
  - "[ ] Lendo só o voice_dna, dá para identificar o agent"

# ❌ FRACO (genérico):
voice_dna:
  sentence_starters:
    - "Vou verificar isso..."
    - "Aqui está a informação..."
  vocabulary:
    always_use: ["importante", "atenção", "verifique"]

# ✅ PROFUNDO (distintivo):
voice_dna:
  sentence_starters:
    alerta_limite:
      - "🚨 ATENÇÃO LIMITE: Você está a {X}% do teto..."
      - "📊 Projeção atual: Se mantiver esse ritmo..."
    operacional:
      - "📄 DAS de {competência} pronto. Valor: R$ {valor}..."
      - "✅ Guia emitida. Vencimento: dia 20..."
  vocabulary:
    always_use:
      - "competência" (não "mês" para referência fiscal)
      - "DAS-MEI" (não "boleto do MEI")
      - "limite proporcional" (não "teto")
    never_use:
      - "imposto" → usar "contribuição"
      - "estourar" → usar "atingir/ultrapassar"
  metaphors:
    limite_copo:
      description: "O limite MEI é como um copo d'água"
      usage: "Quando está 80% cheio, qualquer gota pode derramar"
```

**Score:** ___/4

---

### 4. ANTI-PATTERNS COM RAZÃO

```yaml
check: "Anti-patterns explicam O PORQUÊ"
passing_criteria:
  - "[ ] Cada 'never_do' tem 'reason'"
  - "[ ] Razões são específicas do domínio"
  - "[ ] Consequências são explicadas"
  - "[ ] Alternativa correta é indicada"

# ❌ FRACO:
anti_patterns:
  never_do:
    - "Não atrasar envio de guia"

# ✅ PROFUNDO:
anti_patterns:
  never_do:
    - action: "Enviar DAS depois do dia 15"
      reason: |
        Cliente precisa de pelo menos 5 dias para organizar pagamento.
        Muitos MEIs não têm reserva de caixa. Guia enviada dia 18
        significa pagamento atrasado, multa de 0,33%/dia, e cliente
        irritado com o contador (não consigo mesmo).
      consequence: "Multa para o cliente + desgaste de relacionamento"
      alternative: "Emitir dia 1, enviar dia 5, lembrete dia 15"
```

**Score:** ___/4

---

### 5. TESTE DE DISTINTIVIDADE

```yaml
check: "Agent é distinguível de genérico"
passing_criteria:
  - "[ ] Removendo o nome, ainda é identificável pelo conteúdo"
  - "[ ] Frameworks são específicos DESTE domínio"
  - "[ ] Output examples são únicos (não poderiam ser de outro agent)"
  - "[ ] Personalidade é consistente através de todas as seções"

test: |
  Mostre as seções voice_dna e frameworks para alguém sem contexto.
  Pergunte: "De que área é esse agent?"
  Se a pessoa não consegue identificar → FAIL
```

**Score:** ___/4

---

## SCORING

| Seção | Score | Max |
|-------|-------|-----|
| 1. Frameworks com teoria | ___/4 | 4 |
| 2. Heurísticas com evidência | ___/4 | 4 |
| 3. Voice DNA distintivo | ___/4 | 4 |
| 4. Anti-patterns com razão | ___/4 | 4 |
| 5. Teste de distintividade | ___/4 | 4 |
| **TOTAL** | **___/20** | **20** |

---

## DECISION MATRIX

```yaml
decision:
  PASS: "Score >= 16/20 (80%)"
  CONDITIONAL: "Score 12-15/20 (60-75%) - Pode publicar com plano de melhoria"
  FAIL: "Score < 12/20 - NÃO publicar, voltar para extração"

action_if_fail:
  - "Identificar seções fracas"
  - "Re-executar extract-thinking-dna.md com foco nas seções"
  - "Adicionar exemplos e teoria"
  - "Re-rodar checklist"
```

---

## COMPARAÇÃO: AGENT BOM vs AGENT FRACO

> **Nota:** Esta comparação é ilustrativa. Substitua pelos agents do seu domínio.

| Aspecto | Agent Profundo (Bom) | Agent Genérico (Fraco) |
|---------|----------------------|------------------------|
| **Linhas** | 1.500+ | <500 |
| **Frameworks** | Com filosofia, exemplos, templates | Lista de passos |
| **Heurísticas** | Com citações reais do expert | Regras genéricas |
| **Voice DNA** | Personalidade forte, metáforas | Funcional mas genérico |
| **Distintividade** | Impossível confundir | Poderia ser qualquer agent |
| **Score SC_AGT_003** | 18-20/20 | <12/20 |

---

**Squad Creator | Depth Quality Gate v1.0**
*"Structure without depth is just a template"*
