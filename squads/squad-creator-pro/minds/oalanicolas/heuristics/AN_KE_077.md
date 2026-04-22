# AN_KE_077 - Design Smell Detector
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: 14+ instâncias cross-project (Hackathon-Hub, mmos, aiox-stage, sinkra-hub) — "nao faz sentido"]

## Purpose

A frase "não faz sentido" é um DESIGN SMELL DETECTOR natural. Quando Alan diz isso, tem problema arquitetural — dado no lugar errado, abstração incorreta, componente desnecessário, ou lógica ilógica. Funciona em TODOS os domínios: schema de banco ("is_premium BOOLEAN nao faz sentido por si só"), UI ("widget Maior Nota nao faz sentido"), organização de arquivos ("nao faz sentido /ui /system /libraries"), pricing de modelos ("Gemini Pro ficou mais barato que haiku? nao faz sentido"), e até segurança ("tem dado sensivel que nao faz sentido estar aqui"). Inclui detecção de falsos determinísticos: se algo é rotulado como determinístico mas tem variabilidade → também é design smell ("isso deve ser deterministico").

## Configuration

```yaml
AN_KE_077:
  name: "Design Smell Detector"
  zone: "excelencia"
  trigger: "Frase 'não faz sentido' (ou equivalente) aparece durante review, build, ou discussão."

  sys_tension:
    tension_with: "AN_KE_050 (Inimigo Zero: Complexidade Inútil) vs Detecção Subjetiva de Smell — ambas buscam eliminar o desnecessário, mas AN_KE_050 via controle de WIP estruturado enquanto AN_KE_077 via sinalização perceptual"
    resolution: "Transmutar subjetividade em investigação estruturada: ao invés de validar/rejeitar baseado em opinião, sempre PARAR e executar decisão-tree objetiva (DATA_PLACEMENT, ABSTRACTION, EXISTENCE, LOGIC, SECURITY). Se após análise estruturada ainda houver desacordo → escalar para decisor designado, nunca ignorar a sinalização."

  rule: |
    SE "não faz sentido" aparece (de qualquer pessoa):
    ENTÃO PARAR e investigar o design smell:
      - Dado no lugar errado? → MOVER
      - Abstração incorreta? → REFATORAR
      - Componente desnecessário? → DELETAR
      - Lógica ilógica? → REDESENHAR
      - Coisa que deveria ser determinística mas não é? → TORNAR determinístico
    A frase é SEMPRE um sinal legítimo — nunca ignorar.

  veto_condition:
    trigger: "Alguém disse 'não faz sentido' e a conversa seguiu sem investigar."
    action: "VETO — Parar. Investigar. 'Não faz sentido' NUNCA é gratuito."

  evidence:
    - "[SOURCE: sessão d6b38401, mmos] 'Essa estatistica Live Supabase nao faz sentido nenhum estar ali'"
    - "[SOURCE: sessão 4fb48802, mmos] 'is_premium BOOLEAN DEFAULT false, nao faz sentido isso por si só já é um tipo de oferta'"
    - "[SOURCE: sessão 1723d762, mmos] 'nao faz sentido termos capa com imagem se podemos fazer tudo com HTML e ser mais leve e 100% responsivo'"
    - "[SOURCE: sessão d73d5bfc, aiox-stage] 'nao faz sentido /ui /system /libraries, isso tudo deveria estar...'"
    - "[SOURCE: sessão d73d5bfc, aiox-stage] 'tem mt dado dentro do legado de workspace que nao faz sentido nenhum estar aqui tem até dado sensivel'"
    - "[SOURCE: sessão 711559f2, aiox-stage] 'quem vai executar esta task? para o que ela serve? nao faz sentido criar uma nova task aleatoria jogada em qualquer pasta'"
    - "[SOURCE: sessão a13d8b00, sinkra-hub] 'Como que Gemini Pro ficou mais barato que haiku? isso nao faz sentido algum'"
    - "[SOURCE: sessão 95634505, aiox-stage] 'isso nao faz sentido, isso deve ser deterministico' (merged de AN_KE_094)"
```

## Decision Tree

```javascript
IF (phrase_detected: "não faz sentido" OR equivalent)
  STEP_1: STOP current work — this is a signal, not noise

  STEP_2: CLASSIFY the smell
    TYPE_A: DATA_PLACEMENT — "não faz sentido estar aqui/ali"
      → Dado está no componente/tabela/pasta errada
      → ACTION: mover para local correto
    TYPE_B: ABSTRACTION — "não faz sentido por si só" / "não faz sentido ter X se Y"
      → Abstração está no nível errado (granular demais ou genérica demais)
      → ACTION: refatorar abstraction level
    TYPE_C: EXISTENCE — "pra que serve isso?" / "nao faz sentido ter isso"
      → Componente/campo/widget não deveria existir
      → ACTION: deletar (AN_KE_075)
    TYPE_D: LOGIC — "como que X é mais barato que Y?" / "isso deveria ser determinístico"
      → Lógica contradiz expectativa razoável
      → ACTION: investigar root cause, provavelmente bug ou design flaw
    TYPE_E: SECURITY — "tem dado sensível que não faz sentido estar aqui"
      → Informação sensível in wrong scope
      → ACTION: mover imediatamente, audit trail

  STEP_3: FIX the smell (don't just note it)
  STEP_4: VERIFY fix resolved the "não faz sentido" feeling
```

## Failure Modes

### O Widget que Ninguém Sabe Pra Que Serve
- **Trigger:** Dashboard tem "Maior Nota" widget que mostra dado sem contexto claro.
- **Manifestation:** "nao faz sentido, pq vários recebem isso, vamos pensar em outro."
- **Detection:** Quando explicar o widget leva > 10 segundos → design smell.
- **Prevention:** Cada componente deve responder "pra que serve?" em 1 frase.

### O Dado Sensível no Lugar Errado
- **Trigger:** Workspace público contém dados operacionais de negócio com dados sensíveis.
- **Manifestation:** "tem mt dado sensivel da operacao que nao faz sentido estar aqui."
- **Detection:** Grep por dados pessoais, financeiros, ou credenciais em pastas compartilhadas.
- **Prevention:** SECURITY audit como parte de qualquer migração/reorganização.

## Validation

**Context:** AN_KE_077 resolve a tensão intrínseca entre subjetividade e objetividade na detecção de problemas de design. A heurística reconhece que "não faz sentido" é fundamentalmente uma percepção, mas transforma essa percepção em investigação estruturada através da decision-tree de tipos (DATA_PLACEMENT, ABSTRACTION, EXISTENCE, LOGIC, SECURITY).

**Validation Criteria:**
1. ✓ **Tensão identificada:** Subjetividade (interpretação) vs. Objetividade (investigação estruturada)
2. ✓ **Resolução inscrita:** Toda sinalização gatilha parada + análise estruturada, nunca descarte por subjetividade
3. ✓ **Decision-tree presente:** Permite classificação e ação determinística mesmo com origem subjetiva
4. ✓ **Escalonamento definido:** Se análise estruturada não resolver desacordo, escala para decisor designado
5. ✓ **Ligações cross-heurística:** Conecta com AN_KE_044 (pragmatismo vs purismo) e AN_KE_089 (consenso)

**Status:** ✅ Válida — paradoxo resolvido através de transmutação de subjetividade em protocolo estruturado.
