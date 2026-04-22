# AN_KE_101 - Framework Strict Isolation
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão aiox-core/arquitetura — "misturando framework com expansão"]

## Purpose

A fundação do AIOX e do framework SINKRA v3.1 reside na agnosticidade total do core operacional. Injetar configurações específicas de domínios corporativos (`scan-registry.yaml`, por exemplo), tokens de clientes, ou rotas personalizadas dentro do núcleo base (`.aiox-core`) destrói a portabilidade do repositório. O núcleo é a engrenagem pura; qualquer injeção de "negócio" DEVE acontecer via *Expansion Packs*, `squads/`, ou `.Codex/`, garantindo encapsulamento da máquina.

## Configuration

```yaml
AN_KE_101:
  name: "Framework Strict Isolation"
  zone: "genialidade"
  trigger: "Modificando scripts, ferramentas ou pastas vitais de `.aiox-core` com dados pontuais da sessão local."

  rule: |
    SE você encontrar um script que requer dados específicos do negócio ou de um client
    ENTÃO externalize o payload de dados do framework básico (`.aiox-core`).
    NUNCA coloque lógica hardcoded de projeto dentro do Core Agnóstico.
    O sistema DEVE sobreviver como open-source intacto. Toda camada de bussiness é um pacote isolado.

  veto_condition:
    trigger: "Agente cria estrutura `.aiox-core/lib/scan-registry.yaml` para rastrear processos do workspace do usuário."
    action: "VETO — 'Você tem razão absoluta! Estava misturando framework com expansão. ❌ Estrutura Errada... NÃO deveria ter dados do projeto'."

  evidence:
    - "[SOURCE: histórico manual] 'Estava misturando framework com expansão. Vamos corrigir: ❌ Estrutura Errada (que propus) .aiox-core/ # Framework - NÃO deveria ter dados do projeto'"

  sys_tension:
    - tension_with: "AN_KE_026 (Squad Agnosticism) vs Complexidade de Parsing Local"
      resolution: "AN_KE_101 impõe purismo agnóstico ao core framework, enquanto AN_KE_026 demanda agnosticismo de squads em relação a domínios; paradoxo resolvido via Expansion Packs como camada intermediária que encapsula injeção de negócio sem poluir base"
```

## Decision Tree

```javascript
IF (adding_new_feature_to_core_architecture)
  STEP_1: IDENTIFY domain (Is this generic orchestration code OR business-specific tracking?)
  STEP_2: IF (Business/Project specific)
    -> ROUTE to `squads/*` OR `workspace/*` OR `expansion-packs/*`.
    -> DISCARD changes mapped to `.aiox-core/`.
  STEP_3: IF (Generic Orchestration)
    -> APPEND to `.aiox-core/` while preserving parameter injection instead of hardcoded state.
```

## Failure Modes

### Monolithic Core Pollution
- **Trigger:** Configurações de "AllFluence" e integrações do ClickUp vazam para arquivos base em `.aiox-core`.
- **Manifestation:** Qualquer clone do repositório base que queira montar uma arquitetura para Hospital ou EdTech falhará tentando resolver keys do "AllFluence".
- **Prevention:** Isolação purista. O Framework não possui DNA proprietário, ele o invoca.

## Validation

✓ **Paradox Identified:** Purismo agnóstico (.aiox-core) vs. Necessidade operacional de rastreamento/contexto do projeto.

✓ **Tension Resolved:** sys_tension aponta para AN_KE_070 (Dynamic Expansion) como mecanismo de resolução — Expansion Packs permitem injeção sem poluição do core.

✓ **Evidence Chain:** Manual history confirms veto of `.aiox-core/lib/scan-registry.yaml` como erro arquitetural; caminho correto é `squads/*/config.yaml` + `workspace/` + `expansion-packs/`.

✓ **Heuristic Stability:** Rule is deterministic and falsifiable — qualquer adição de dados-specificos ao `.aiox-core` viola a heurística.
