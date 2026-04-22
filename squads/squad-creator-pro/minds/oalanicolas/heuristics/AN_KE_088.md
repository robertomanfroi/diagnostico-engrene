# AN_KE_088 - Runners as Product Process
**Zone:** 💎 4% Excelência | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão sinkra-hub b3c022b9 — sinkra-map CLI + modo YOLO]

## Purpose

Quando um pipeline CLI funciona bem (sinkra-map.sh, validate-squad.sh, mmos.sh), a próxima evolução natural é PRODUTIZAR como processo autônomo. Não é só "rodar script" — é criar modos que escalam execução sem intervenção humana: modo YOLO (100% autônomo para as N fases), ssh runners (execução remota), e batch runners (múltiplos squads em sequência). Alan vê CLI runners como PRODUTO, não ferramenta — algo que deveria ter seu próprio processo formalizado no squad-creator-pro.

## Configuration

```yaml
AN_KE_088:
  name: "Runners as Product Process"
  zone: "excelencia"
  trigger: "Pipeline CLI estável com 5+ runs manuais bem-sucedidos."

  rule: |
    SE pipeline CLI estável (5+ runs, edge cases conhecidos)
    ENTÃO produtizar como processo formal:
      (1) Modo interativo (default, humano no loop)
      (2) Modo YOLO (100% autônomo, todas fases sem parar)
      (3) Modo batch (múltiplos inputs em sequência)
      (4) Modo remoto (ssh runners para execução distribuída)
    Cada modo é um processo formal no squad-creator-pro.
    Runner = produto. Script = protótipo.

  veto_condition:
    trigger: "Pipeline CLI com 10+ runs manuais sem modo autônomo disponível."
    action: "VETO — 'isso precisa virar um processo de criar esses modos autônomos, esses runners.' Produtizar."

  sys_tension:
    tension_with: "AN_KE_073 (Parallel Subagents for Throughput) — Produtizar automatiza sequencialmente (modo YOLO percorre fases sem parar), mas AN_KE_073 propõe paralelização para throughput. Tensão: sequencialismo robusto vs paralelismo escalável. Resolvida por decisão de design: runners mantêm sequencialismo (cada fase depende da anterior), mas runners múltiplos executam em paralelo (batch mode com N squads simultâneos)."
    resolution: "Hierarquia de modos: (1) interativo é default seguro, (2) YOLO é sequencial (cada fase espera a anterior), (3) batch paralelo roda múltiplos YOLO em runners distintos. Mudança de paradigma: script → processo → produto."

  evidence:
    - "[SOURCE: sessão b3c022b9, sinkra-hub] 'assim como mmos.sh tb quero criar um modo 100% YOLO para as 7 fases do sinkra map-proceess'"
    - "[SOURCE: sessão b3c022b9, sinkra-hub] 'isso precisa virar um processo em squad creator-pro de criar esses modos autonomos sei la o nome esses runners ssh'"
    - "[SOURCE: sessão f268bcf6, sinkra-hub] 'Shell runner + prompt template são DELIVERABLES obrigatórios de create-pipeline. Outputs: 6 required (was 3). Shell Runner Requirements: 10 non-negotiable items. Veto: missing .sh, prompt, or flags'"
```

## Decision Tree

```javascript
IF (cli_pipeline_stable AND run_count >= 5)
  STEP_1: ASSESS automation readiness
    CHECKS:
      - Edge cases documented? (from manual runs)
      - Error handling covers known failures?
      - Output is deterministic and validatable?
    IF (all checks pass) → proceed to productize

  STEP_2: CREATE runner modes
    MODE_INTERACTIVE: default, human confirms each phase
    MODE_YOLO: all phases execute sequentially without stopping
      - Requires: fallback chain (AN_KE_064)
      - Requires: error recovery per phase
    MODE_BATCH: iterate over list of inputs
      - Input: file with list of squad names / paths
      - Output: per-input results directory
    MODE_REMOTE: ssh to runner machine, execute there
      - Requires: environment setup script
      - Requires: result sync back to local

  STEP_3: FORMALIZE as process in squad-creator-pro
    CREATE: task definition for "productize CLI pipeline"
    DOCUMENT: which modes are available, how to invoke

  NEVER: manually run pipeline 20+ times without creating YOLO mode
```

## Failure Modes

### O Script que Só o Criador Sabe Rodar
- **Trigger:** sinkra-map.sh funciona perfeitamente para Alan, 0 documentação de modos.
- **Manifestation:** Ninguém mais consegue executar. Cada run requer explicação verbal.
- **Detection:** Script sem --help que mostra modos disponíveis.
- **Prevention:** Modos formalizados com flags (--mode yolo, --mode batch). --help auto-gerado.

## Validation

**Paradoxo Identificado:** Automação vs Controle — Quanto mais autônomo o runner (modo YOLO), menor a capacidade humana de intervir em tempo real. Quanto mais humano no loop (interativo), mais lento e menos escalável.

**Validação da Resolução:**
1. ✅ Modo interativo = default seguro (preserva decisão humana)
2. ✅ Modo YOLO = camada adicional explícita (opt-in, não obrigatório)
3. ✅ Fallback chain (AN_KE_064) mitiga falhas autônomas
4. ✅ Mudança epistemológica: Script → Processo → Produto resolve a tensão por reposicionamento de abstração

**Status:** Heurística validada contra paradoxo de automação balanceada.
