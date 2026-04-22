#!/usr/bin/env node

/**
 * SSH-style external wave loop for create-squad runtime.
 *
 * Each wave runs in a fresh LLM session (`codex exec` or `claude -p`) and the
 * loop progress is persisted alongside the canonical runtime state.
 */

const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');
const {
  DEFAULT_WORKFLOW,
  getCanonicalStatePath,
  getRuntimeDirForSlug,
  readActiveSquad,
  readStateWithLegacyFallback,
  toWorkspaceRelative,
} = require(path.resolve(__dirname, '..', '..', 'squad-creator', 'scripts', 'lib', 'squad-runtime-paths.cjs'));

const ROOT = path.resolve(__dirname, '..', '..', '..');
const DEFAULT_MODE = 'ssh';
const DEFAULT_REQUESTED_RUNTIME = process.env.AIOX_WAVE_LOOP_RUNTIME || 'auto';
const DEFAULT_RETRY_BASE_SECONDS = Number(process.env.AIOX_WAVE_LOOP_RETRY_BASE_SECONDS || 3);
const SUCCESS_STATUSES = new Set(['status', 'planned', 'completed']);

function usage() {
  console.log(`SSH Wave Loop - external fresh-session runner for create-squad waves

Usage:
  node squads/squad-creator-pro/scripts/wave-loop.cjs [slug] [--mode ssh] [--runtime auto|codex|claude]
  node squads/squad-creator-pro/scripts/wave-loop.cjs [slug] --status [--json]
  node squads/squad-creator-pro/scripts/wave-loop.cjs [slug] --dry-run [--from N] [--to N] [--max-waves N] [--json]

Options:
  --mode ssh         External fresh-session mode (current default and only mode)
  --runtime          Runtime selection: auto | codex | claude
  --from             First wave to run (defaults to next wave inferred from state.json)
  --to               Last wave to run (defaults to total waves in state.json)
  --max-waves        Maximum waves to run in this loop
  --status           Inspect current runtime + inferred plan without executing
  --dry-run          Build plan and persist loop state without executing waves
  --json             Emit machine-readable JSON
  --help             Show this help

Environment:
  AIOX_RUNTIME_ROOT              Override canonical runtime root
  AIOX_WAVE_LOOP_RUNTIME         Default runtime (auto|codex|claude)
  AIOX_WAVE_LOOP_RETRY_BASE_SECONDS  Base delay for retry backoff
  AIOX_WAVE_LOOP_EXECUTOR_SCRIPT Optional test/mock executor script
  AIOX_WAVE_LOOP_CODEX_MODEL     Optional Codex model override
  AIOX_WAVE_LOOP_CLAUDE_MODEL    Optional Claude model override
`);
}

function outputJson(payload) {
  console.log(JSON.stringify(payload, null, 2));
}

function outputError(code, message, details = {}) {
  outputJson({
    success: false,
    error: { code, message, details },
  });
}

function parseArg(args, flag) {
  const idx = args.indexOf(flag);
  if (idx === -1 || idx + 1 >= args.length) return null;
  return args[idx + 1];
}

function parseOptionalInteger(value) {
  if (value === null || value === undefined || value === '') return null;
  const parsed = Number.parseInt(value, 10);
  return Number.isFinite(parsed) ? parsed : null;
}

function parseArgs(argv) {
  if (argv.includes('--help') || argv.includes('-h')) {
    usage();
    process.exit(0);
  }

  const args = {
    slug: null,
    mode: DEFAULT_MODE,
    runtime: DEFAULT_REQUESTED_RUNTIME,
    from: null,
    to: null,
    maxWaves: null,
    status: false,
    dryRun: false,
    json: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const token = argv[index];
    switch (token) {
      case '--mode':
        args.mode = argv[index + 1] || args.mode;
        index += 1;
        break;
      case '--runtime':
        args.runtime = argv[index + 1] || args.runtime;
        index += 1;
        break;
      case '--from':
        args.from = parseOptionalInteger(argv[index + 1]);
        index += 1;
        break;
      case '--to':
        args.to = parseOptionalInteger(argv[index + 1]);
        index += 1;
        break;
      case '--max-waves':
        args.maxWaves = parseOptionalInteger(argv[index + 1]);
        index += 1;
        break;
      case '--status':
        args.status = true;
        break;
      case '--dry-run':
        args.dryRun = true;
        break;
      case '--json':
        args.json = true;
        break;
      default:
        if (!token.startsWith('-') && !args.slug) {
          args.slug = token;
          break;
        }
        if (token.startsWith('-')) {
          throw new Error(`Unknown argument: ${token}`);
        }
        throw new Error(`Unexpected positional argument: ${token}`);
    }
  }

  return args;
}

function assertMode(mode) {
  if (mode === DEFAULT_MODE) return;
  throw new Error(`Unsupported mode: ${mode}. Current implementation supports only --mode ${DEFAULT_MODE}.`);
}

function hasCommand(command) {
  const checker = process.platform === 'win32' ? 'where' : 'which';
  const result = spawnSync(checker, [command], { stdio: 'ignore' });
  return result.status === 0;
}

function detectRuntime(requestedRuntime) {
  if (requestedRuntime === 'auto') {
    if (hasCommand('codex')) return 'codex';
    if (hasCommand('claude')) return 'claude';
    return 'none';
  }
  if (requestedRuntime === 'codex' || requestedRuntime === 'claude') {
    return requestedRuntime;
  }
  return 'invalid';
}

function ensureRuntimeAvailability(selectedRuntime, requestedRuntime, options = {}) {
  const { allowNone = false } = options;

  if (selectedRuntime === 'none') {
    if (allowNone) return;
    throw new Error('No supported runtime found in PATH (codex or claude).');
  }

  if (!hasCommand(selectedRuntime)) {
    throw new Error(`Requested runtime "${requestedRuntime}" is not available in PATH.`);
  }
}

function getRuntimeSettings(selectedRuntime) {
  if (selectedRuntime === 'codex') {
    return {
      timeoutSeconds: Number(process.env.AIOX_WAVE_LOOP_TIMEOUT_SECONDS || 5400),
      maxAttempts: Number(process.env.AIOX_WAVE_LOOP_MAX_ATTEMPTS || 3),
      model: process.env.AIOX_WAVE_LOOP_CODEX_MODEL || null,
    };
  }

  return {
    timeoutSeconds: Number(process.env.AIOX_WAVE_LOOP_TIMEOUT_SECONDS || 2400),
    maxAttempts: Number(process.env.AIOX_WAVE_LOOP_MAX_ATTEMPTS || 2),
    model: process.env.AIOX_WAVE_LOOP_CLAUDE_MODEL || null,
  };
}

function loadState(slug) {
  return readStateWithLegacyFallback(slug, {
    workflow: DEFAULT_WORKFLOW,
  });
}

function parseReadyWave(value) {
  if (typeof value !== 'string') return null;
  const match = /ready_for_(?:wave|epic)_(\d+)/i.exec(value);
  return match ? Number.parseInt(match[1], 10) : null;
}

function getTotalWaves(state) {
  return (
    state.total_waves ??
    state.total_epics ??
    state.metadata?.wave?.total ??
    state.metadata?.epic?.total ??
    null
  );
}

function getCurrentWave(state) {
  return (
    state.current_wave ??
    state.current_epic ??
    state.metadata?.wave?.number ??
    state.metadata?.epic?.number ??
    null
  );
}

function getNextWave(state) {
  const explicitReady =
    parseReadyWave(state.wave_status) ??
    parseReadyWave(state.checkpoint_status);

  if (explicitReady !== null) return explicitReady;

  const current = getCurrentWave(state);
  const total = getTotalWaves(state);
  if (current === null) return null;
  if (total !== null && current >= total) return null;
  return current + 1;
}

function inferWaveCommand(state, slug, wave) {
  const pattern =
    state.runtime_taxonomy?.command_pattern ||
    `*create-squad ${slug} --wave={n}`;
  return pattern.replace('{n}', String(wave));
}

function isWaveCompletedInState(state, wave) {
  if (!state || typeof state !== 'object') return false;

  if (state.epics && state.epics[String(wave)]?.status === 'completed') {
    return true;
  }

  if (state.phases && state.phases[`epic_${wave}_completed`]?.status === 'completed') {
    return true;
  }

  if (state.current_phase === `epic_${wave}_completed`) {
    return true;
  }

  const nextWave = getNextWave(state);
  if (typeof nextWave === 'number' && nextWave > wave) {
    return true;
  }

  const currentWave = getCurrentWave(state);
  return typeof currentWave === 'number' && currentWave > wave;
}

function inferPlan(state, args) {
  const total = getTotalWaves(state);
  const nextWave = getNextWave(state);
  const currentWave = getCurrentWave(state);

  const inferredFrom = args.from ?? nextWave;
  if (inferredFrom === null || inferredFrom === undefined) {
    if (total !== null && currentWave !== null && currentWave >= total) {
      return {
        currentWave,
        nextWave: null,
        totalWaves: total,
        from: null,
        to: total,
        waves: [],
        alreadyComplete: true,
      };
    }
    throw new Error('Could not infer the next wave from runtime state. Provide --from <N>.');
  }

  let plannedTo = args.to ?? total ?? inferredFrom;
  if (args.maxWaves !== null) {
    plannedTo = Math.min(plannedTo, inferredFrom + args.maxWaves - 1);
  }

  if (plannedTo < inferredFrom) {
    throw new Error(`Invalid range: from=${inferredFrom} to=${plannedTo}.`);
  }

  const waves = [];
  for (let wave = inferredFrom; wave <= plannedTo; wave += 1) {
    waves.push(wave);
  }

  return {
    currentWave,
    nextWave,
    totalWaves: total,
    from: inferredFrom,
    to: plannedTo,
    waves,
    alreadyComplete: total !== null && inferredFrom > total,
  };
}

function ensureDir(dirPath) {
  fs.mkdirSync(dirPath, { recursive: true });
}

function getLoopPaths(slug) {
  const runtimeDir = getRuntimeDirForSlug(slug, DEFAULT_WORKFLOW);
  const logDir = path.join(runtimeDir, 'logs', 'wave-loop');
  const loopStatePath = path.join(runtimeDir, 'wave-loop-state.json');
  return { runtimeDir, logDir, loopStatePath };
}

function readJson(filePath) {
  if (!fs.existsSync(filePath)) return null;
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function writeLoopState(loopStatePath, payload) {
  ensureDir(path.dirname(loopStatePath));
  fs.writeFileSync(loopStatePath, JSON.stringify(payload, null, 2));
}

function nowIso() {
  return new Date().toISOString();
}

function toLogStamp(value = new Date()) {
  return value.toISOString().replace(/[:.]/g, '-');
}

function sleepMs(milliseconds) {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, milliseconds);
}

function isTransientRuntimeError(output) {
  return /stream disconnected before completion|error sending request for url|connection reset|timed out|timeout|temporarily unavailable|service unavailable|network error|rate limit|429|503|5.. Server Error|overloaded|failed to queue rollout items|failed to shutdown rollout recorder|reconnecting/i.test(
    output || ''
  );
}

function isFatalRuntimeError(output) {
  return /usage limit|purchase more credits|billing|quota exceeded|account suspended/i.test(output || '');
}

function buildWavePrompt({ slug, wave, command, statePath }) {
  return [
    `You are working inside the AIOX workspace at ${ROOT}.`,
    'Follow AGENTS.md, .aiox-core/constitution.md, and the local runtime state as the source of truth.',
    'Activate the orchestrator explicitly with the `$squad-chief` shortcut before executing the wave command unless that persona is already active.',
    `Continue the existing create-squad runtime for slug "${slug}".`,
    '',
    'Execute exactly one wave and stop after it finishes:',
    command,
    '',
    'Execution contract:',
    `- This is external SSH loop mode: complete only wave ${wave} in this fresh session.`,
    `- Respect the canonical runtime file: ${toWorkspaceRelative(statePath)}.`,
    '- If a story/checklist/file list must be updated for this wave, update it and close it properly.',
    '- Run focused validation for the files changed by this wave.',
    '- Do not auto-start the next wave.',
    '- Finish with a short summary including the next recommended command.',
  ].join('\n');
}

function buildExecutorInvocation({ selectedRuntime, prompt, slug, wave, statePath, command, logFile }) {
  const overrideScript = (process.env.AIOX_WAVE_LOOP_EXECUTOR_SCRIPT || '').trim();
  if (overrideScript) {
    return {
      command: 'node',
      args: [
        overrideScript,
        '--slug',
        slug,
        '--wave',
        String(wave),
        '--state-file',
        statePath,
        '--command',
        command,
        '--log-file',
        logFile,
        '--runtime',
        selectedRuntime,
      ],
      input: prompt,
    };
  }

  if (selectedRuntime === 'codex') {
    const args = [
      'exec',
      '--disable',
      'apps',
      '--skip-git-repo-check',
      '--dangerously-bypass-approvals-and-sandbox',
      '--color',
      'never',
    ];
    if (process.env.AIOX_WAVE_LOOP_CODEX_MODEL) {
      args.push('--model', process.env.AIOX_WAVE_LOOP_CODEX_MODEL);
    }
    args.push('-');
    return {
      command: 'codex',
      args,
      input: prompt,
    };
  }

  const args = ['-p', '--dangerously-skip-permissions'];
  if (process.env.AIOX_WAVE_LOOP_CLAUDE_MODEL) {
    args.push('--model', process.env.AIOX_WAVE_LOOP_CLAUDE_MODEL);
  }
  args.push(prompt);
  return {
    command: 'claude',
    args,
    input: null,
  };
}

function runExecutorAttempt(context) {
  const invocation = buildExecutorInvocation(context);
  const result = spawnSync(invocation.command, invocation.args, {
    cwd: ROOT,
    encoding: 'utf8',
    input: invocation.input,
    timeout: context.timeoutSeconds * 1000,
  });

  const stdout = result.stdout || '';
  const stderr = result.stderr || '';
  const combinedOutput = [stdout, stderr].filter(Boolean).join('\n');

  const lines = [
    `# Wave ${context.wave} Attempt ${context.attempt}`,
    `runtime: ${context.selectedRuntime}`,
    `command: ${context.command}`,
    `timestamp: ${nowIso()}`,
    '',
    combinedOutput.trim(),
    '',
  ];
  fs.appendFileSync(context.logFile, `${lines.join('\n')}\n`, 'utf8');

  if (result.error && result.error.code === 'ETIMEDOUT') {
    return {
      exitCode: 124,
      output: `${combinedOutput}\nERROR: executor timed out after ${context.timeoutSeconds}s`,
    };
  }

  return {
    exitCode: result.status ?? 1,
    output: combinedOutput,
  };
}

function printHumanSummary(summary) {
  const lines = [
    'SSH Wave Loop',
    `- Squad: ${summary.slug}`,
    `- Mode: ${summary.mode}`,
    `- Runtime: ${summary.requestedRuntime} -> ${summary.selectedRuntime}`,
    `- Current: wave ${summary.currentWave ?? 'unknown'}/${summary.totalWaves ?? 'unknown'}`,
    `- Next Command: ${summary.nextCommand ?? 'n/a'}`,
    `- Planned Waves: ${summary.plan.waves.length ? summary.plan.waves.join(', ') : '(none)'}`,
    `- Status: ${summary.status}`,
    `- Loop State: ${summary.loopStatePath}`,
    `- Log Dir: ${summary.logDir}`,
  ];

  if (summary.lastLogFile) {
    lines.push(`- Last Log: ${summary.lastLogFile}`);
  }

  console.log(lines.join('\n'));
}

function buildSummary({
  slug,
  args,
  selectedRuntime,
  statePath,
  state,
  plan,
  loopStatePath,
  logDir,
  status,
  lastLogFile = null,
  history = [],
}) {
  const nextWave = getNextWave(state);
  return {
    success: SUCCESS_STATUSES.has(status),
    slug,
    mode: args.mode,
    requestedRuntime: args.runtime,
    selectedRuntime,
    status,
    statePath: toWorkspaceRelative(statePath),
    currentWave: getCurrentWave(state),
    totalWaves: getTotalWaves(state),
    nextWave,
    nextCommand: nextWave !== null ? inferWaveCommand(state, slug, nextWave) : null,
    plan,
    loopStatePath: toWorkspaceRelative(loopStatePath),
    logDir: toWorkspaceRelative(logDir),
    lastLogFile: lastLogFile ? toWorkspaceRelative(lastLogFile) : null,
    history,
  };
}

function createLoopState({
  slug,
  args,
  selectedRuntime,
  statePath,
  plan,
  logDir,
  status,
  history = [],
  lastWaveStarted = null,
  lastWaveCompleted = null,
  lastLogFile = null,
}) {
  return {
    slug,
    workflow: DEFAULT_WORKFLOW,
    mode: args.mode,
    requested_runtime: args.runtime,
    selected_runtime: selectedRuntime,
    status,
    state_file: toWorkspaceRelative(statePath),
    log_dir: toWorkspaceRelative(logDir),
    plan,
    last_wave_started: lastWaveStarted,
    last_wave_completed: lastWaveCompleted,
    last_log_file: lastLogFile ? toWorkspaceRelative(lastLogFile) : null,
    updated_at: nowIso(),
    history,
  };
}

function main() {
  try {
    const args = parseArgs(process.argv.slice(2));
    assertMode(args.mode);

    const slug = args.slug || readActiveSquad();
    if (!slug) {
      throw new Error('No slug provided and no active squad pointer was found.');
    }

    const runtimeState = loadState(slug);
    if (!runtimeState.state) {
      throw new Error(`No runtime state found for slug "${slug}". Expected ${toWorkspaceRelative(getCanonicalStatePath(slug, DEFAULT_WORKFLOW))}.`);
    }

    const state = runtimeState.state;
    const statePath = runtimeState.path;
    const selectedRuntime = detectRuntime(args.runtime);
    if (selectedRuntime === 'invalid') {
      throw new Error(`Invalid runtime: ${args.runtime}. Use auto, codex, or claude.`);
    }
    ensureRuntimeAvailability(selectedRuntime, args.runtime, {
      allowNone: args.runtime === 'auto' && (args.status || args.dryRun),
    });

    const plan = inferPlan(state, args);
    const { logDir, loopStatePath } = getLoopPaths(slug);
    ensureDir(logDir);

    if (plan.alreadyComplete || plan.waves.length === 0) {
      const summary = buildSummary({
        slug,
        args,
        selectedRuntime,
        statePath,
        state,
        plan,
        loopStatePath,
        logDir,
        status: 'completed',
      });
      writeLoopState(loopStatePath, createLoopState({
        slug,
        args,
        selectedRuntime,
        statePath,
        plan,
        logDir,
        status: 'completed',
      }));
      if (args.json) {
        outputJson(summary);
      } else {
        printHumanSummary(summary);
      }
      return;
    }

    if (args.status || args.dryRun) {
      const summary = buildSummary({
        slug,
        args,
        selectedRuntime,
        statePath,
        state,
        plan,
        loopStatePath,
        logDir,
        status: args.status ? 'status' : 'planned',
      });
      writeLoopState(loopStatePath, createLoopState({
        slug,
        args,
        selectedRuntime,
        statePath,
        plan,
        logDir,
        status: args.status ? 'status' : 'planned',
      }));
      if (args.json) {
        outputJson(summary);
      } else {
        printHumanSummary(summary);
      }
      return;
    }

    const runtimeSettings = getRuntimeSettings(selectedRuntime);
    const history = [];
    let currentState = state;
    let lastLogFile = null;
    let lastWaveCompleted = null;

    writeLoopState(loopStatePath, createLoopState({
      slug,
      args,
      selectedRuntime,
      statePath,
      plan,
      logDir,
      status: 'running',
    }));

    for (const wave of plan.waves) {
      currentState = loadState(slug).state || currentState;
      if (isWaveCompletedInState(currentState, wave)) {
        lastWaveCompleted = wave;
        history.push({
          wave,
          status: 'skipped_already_completed',
          updated_at: nowIso(),
        });
        continue;
      }

      const command = inferWaveCommand(currentState, slug, wave);
      const prompt = buildWavePrompt({
        slug,
        wave,
        command,
        statePath,
      });

      const logFile = path.join(logDir, `wave-${String(wave).padStart(2, '0')}-${toLogStamp()}.log`);
      lastLogFile = logFile;

      writeLoopState(loopStatePath, createLoopState({
        slug,
        args,
        selectedRuntime,
        statePath,
        plan,
        logDir,
        status: 'running',
        history,
        lastWaveStarted: wave,
        lastWaveCompleted,
        lastLogFile: logFile,
      }));

      let completed = false;
      for (let attempt = 1; attempt <= runtimeSettings.maxAttempts; attempt += 1) {
        const result = runExecutorAttempt({
          selectedRuntime,
          prompt,
          slug,
          wave,
          statePath,
          command,
          logFile,
          timeoutSeconds: runtimeSettings.timeoutSeconds,
          attempt,
        });

        currentState = loadState(slug).state || currentState;
        if (isWaveCompletedInState(currentState, wave)) {
          completed = true;
          lastWaveCompleted = wave;
          history.push({
            wave,
            status: 'completed',
            attempt,
            command,
            exit_code: result.exitCode,
            log_file: toWorkspaceRelative(logFile),
            updated_at: nowIso(),
          });
          break;
        }

        if (result.exitCode !== 0 && isFatalRuntimeError(result.output)) {
          history.push({
            wave,
            status: 'fatal',
            attempt,
            command,
            exit_code: result.exitCode,
            log_file: toWorkspaceRelative(logFile),
            updated_at: nowIso(),
          });
          writeLoopState(loopStatePath, createLoopState({
            slug,
            args,
            selectedRuntime,
            statePath,
            plan,
            logDir,
            status: 'failed',
            history,
            lastWaveStarted: wave,
            lastWaveCompleted,
            lastLogFile: logFile,
          }));
          const summary = buildSummary({
            slug,
            args,
            selectedRuntime,
            statePath,
            state: currentState,
            plan,
            loopStatePath,
            logDir,
            status: 'failed',
            lastLogFile: logFile,
            history,
          });
          if (args.json) {
            outputJson(summary);
          } else {
            printHumanSummary(summary);
          }
          process.exit(1);
        }

        const shouldRetry = result.exitCode !== 0 && attempt < runtimeSettings.maxAttempts && isTransientRuntimeError(result.output);
        if (shouldRetry) {
          const delaySeconds = DEFAULT_RETRY_BASE_SECONDS * (2 ** (attempt - 1));
          history.push({
            wave,
            status: 'retrying',
            attempt,
            command,
            exit_code: result.exitCode,
            delay_seconds: delaySeconds,
            log_file: toWorkspaceRelative(logFile),
            updated_at: nowIso(),
          });
          writeLoopState(loopStatePath, createLoopState({
            slug,
            args,
            selectedRuntime,
            statePath,
            plan,
            logDir,
            status: 'retrying',
            history,
            lastWaveStarted: wave,
            lastWaveCompleted,
            lastLogFile: logFile,
          }));
          sleepMs(delaySeconds * 1000);
          continue;
        }

        history.push({
          wave,
          status: result.exitCode === 0 ? 'blocked' : 'failed',
          attempt,
          command,
          exit_code: result.exitCode,
          log_file: toWorkspaceRelative(logFile),
          updated_at: nowIso(),
        });
        break;
      }

      if (!completed) {
        writeLoopState(loopStatePath, createLoopState({
          slug,
          args,
          selectedRuntime,
          statePath,
          plan,
          logDir,
          status: 'blocked',
          history,
          lastWaveStarted: wave,
          lastWaveCompleted,
          lastLogFile,
        }));
        const summary = buildSummary({
          slug,
          args,
          selectedRuntime,
          statePath,
          state: currentState,
          plan,
          loopStatePath,
          logDir,
          status: 'blocked',
          lastLogFile,
          history,
        });
        if (args.json) {
          outputJson(summary);
        } else {
          printHumanSummary(summary);
        }
        process.exit(1);
      }
    }

    const finalState = loadState(slug).state || currentState;
    writeLoopState(loopStatePath, createLoopState({
      slug,
      args,
      selectedRuntime,
      statePath,
      plan,
      logDir,
      status: 'completed',
      history,
      lastWaveStarted: plan.waves.at(-1) || null,
      lastWaveCompleted,
      lastLogFile,
    }));

    const summary = buildSummary({
      slug,
      args,
      selectedRuntime,
      statePath,
      state: finalState,
      plan,
      loopStatePath,
      logDir,
      status: 'completed',
      lastLogFile,
      history,
    });

    if (args.json) {
      outputJson(summary);
    } else {
      printHumanSummary(summary);
    }
  } catch (error) {
    outputError('WAVE_LOOP_FAILED', error.message);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

module.exports = {
  parseArgs,
  detectRuntime,
  ensureRuntimeAvailability,
  getTotalWaves,
  getCurrentWave,
  getNextWave,
  inferPlan,
  inferWaveCommand,
  buildWavePrompt,
  buildExecutorInvocation,
  buildSummary,
};
