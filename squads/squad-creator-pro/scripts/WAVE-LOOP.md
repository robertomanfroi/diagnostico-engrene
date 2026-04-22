# Wave Loop

`wave-loop` e o launcher externo estilo SSH do `squad-creator-pro` para executar waves em sessoes LLM frescas.

## Quando usar

Use quando quiser continuar `*create-squad <slug> --wave=N` sem depender da janela atual do agente:

- retomar um runtime existente
- rodar uma ou mais waves em sequencia
- inspecionar o proximo passo sem executar
- operar via `codex`, `claude` ou `auto`

## Pontos de entrada

Shell wrapper:

```bash
bash squads/squad-creator-pro/scripts/wave-loop.sh slides-creator --runtime codex
```

Node direto:

```bash
node squads/squad-creator-pro/scripts/wave-loop.cjs slides-creator --runtime codex
```

Runner oficial:

```bash
node squads/squad-creator-pro/scripts/squad-workflow-runner.cjs wave-loop slides-creator --runtime codex
```

Se o `slug` nao for passado, o comando tenta usar o active squad pointer atual.

## Modos principais

Inspecionar o runtime sem executar:

```bash
node squads/squad-creator-pro/scripts/wave-loop.cjs slides-creator --status --runtime codex --json
```

Planejar sem executar:

```bash
node squads/squad-creator-pro/scripts/wave-loop.cjs slides-creator --dry-run --runtime codex --max-waves 1
```

Executar uma wave:

```bash
node squads/squad-creator-pro/scripts/wave-loop.cjs slides-creator --runtime codex --max-waves 1
```

Executar ate uma wave final especifica:

```bash
node squads/squad-creator-pro/scripts/wave-loop.cjs slides-creator --runtime auto --to 8
```

## Runtime

`--runtime` aceita:

- `codex`
- `claude`
- `auto`

Regras:

- `codex` exige binario `codex` no `PATH`
- `claude` exige binario `claude` no `PATH`
- `auto` prefere `codex` e cai para `claude`
- se um runtime explicito nao existir, o comando falha cedo com erro de configuracao

## O que o loop faz

Para cada wave planejada:

1. le `.aiox/squad-runtime/create-squad/<slug>/state.json`
2. infere a proxima wave a partir do runtime atual
3. abre uma sessao fresca do runtime escolhido
4. ativa explicitamente `$squad-chief`
5. executa exatamente uma wave
6. grava log e atualiza `wave-loop-state.json`

## Arquivos gerados

Estado do loop:

```text
.aiox/squad-runtime/create-squad/<slug>/wave-loop-state.json
```

Logs:

```text
.aiox/squad-runtime/create-squad/<slug>/logs/wave-loop/
```

O `wave-loop-state.json` registra:

- runtime solicitado e selecionado
- plano de waves
- ultima wave iniciada/concluida
- ultimo log
- historico resumido de execucao

## Estado terminal

Se o runtime ja estiver concluido:

- `--status` retorna `status: completed`
- `nextWave` vira `null`
- `nextCommand` vira `null`
- nenhuma wave nova e planejada

## Flags uteis

- `--status`: inspeciona runtime e plano sem executar
- `--dry-run`: persiste o plano sem executar waves
- `--from N`: forca a primeira wave
- `--to N`: limita a ultima wave
- `--max-waves N`: limita quantas waves rodar nesta sessao
- `--json`: emite payload legivel por automacao

## Observabilidade

Status rapido:

```bash
node squads/squad-creator-pro/scripts/wave-loop.cjs slides-creator --status --runtime auto --json
```

Ultimo log:

```bash
ls -1t .aiox/squad-runtime/create-squad/slides-creator/logs/wave-loop | head
```

## Cobertura automatizada

O `wave-loop` possui cobertura para:

- estado terminal
- erro de runtime explicito ausente
- execucao via fake `codex`
- execucao via fake `claude`
- caminho delegado via `squad-workflow-runner.cjs`

Tests:

```bash
node squads/squad-creator-pro/scripts/tests/test_wave_loop_runtime_unit.cjs
node squads/squad-creator-pro/scripts/tests/test_wave_loop_runtime_e2e.cjs
```
