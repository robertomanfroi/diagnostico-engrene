#!/usr/bin/env node

const fs = require('fs');
const os = require('os');
const path = require('path');
const { spawnSync } = require('child_process');

const ROOT = process.cwd();
const keepTmp = process.env.AIOX_KEEP_WAVE_LOOP_E2E_TMP === '1';
const runtimeRoot = path.join(os.tmpdir(), `aiox-wave-loop-e2e-${process.pid}-${Date.now()}`);
const waveLoopScript = path.join(ROOT, 'squads', 'squad-creator-pro', 'scripts', 'wave-loop.cjs');
const stateFile = path.join(runtimeRoot, 'create-squad', 'slides-creator', 'state.json');
const loopStateFile = path.join(runtimeRoot, 'create-squad', 'slides-creator', 'wave-loop-state.json');

function assert(condition, message, details = {}) {
  if (!condition) {
    const err = new Error(message);
    err.details = details;
    throw err;
  }
}

function writeJson(targetPath, payload) {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, JSON.stringify(payload, null, 2));
}

function getFixtureState() {
  return {
    slug: 'slides-creator',
    workflow: 'create-squad',
    execution_model: 'epic',
    runtime_taxonomy: {
      command_unit: 'wave',
      command_pattern: '*create-squad slides-creator --wave={n}',
    },
    current_phase: 'epic_6_completed',
    checkpoint_status: 'ready_for_wave_7',
    current_epic: 6,
    total_epics: 8,
    current_wave: 6,
    total_waves: 8,
    wave_status: 'ready_for_wave_7',
    epics: {
      '6': { status: 'completed', phase: 'epic_6_completed' },
      '7': { status: 'pending', phase: 'epic_7_pending' },
      '8': { status: 'pending', phase: 'epic_8_pending' },
    },
    phases: {
      epic_6_completed: { status: 'completed' },
    },
    metadata: {
      execution_model: 'epic',
      wave: { number: 6, total: 8, title: 'template-curator + visual-scout' },
      epic: { number: 6, total: 8, title: 'template-curator + visual-scout' },
    },
  };
}

function runWaveLoop(args, extraEnv = {}) {
  return spawnSync('node', [waveLoopScript, 'slides-creator', ...args], {
    cwd: ROOT,
    encoding: 'utf8',
    env: {
      ...process.env,
      AIOX_RUNTIME_ROOT: runtimeRoot,
      ...extraEnv,
    },
  });
}

function parseJsonOutput(result) {
  try {
    return JSON.parse((result.stdout || '').trim());
  } catch (error) {
    throw new Error(`Failed to parse JSON output: ${error.message}\nSTDOUT:\n${result.stdout}\nSTDERR:\n${result.stderr}`);
  }
}

function createMockExecutorScript() {
  const scriptPath = path.join(runtimeRoot, 'mock-wave-executor.cjs');
  const source = `#!/usr/bin/env node
const fs = require('fs');

function getArg(flag) {
  const idx = process.argv.indexOf(flag);
  return idx === -1 ? null : process.argv[idx + 1];
}

const stateFile = getArg('--state-file');
const wave = Number.parseInt(getArg('--wave'), 10);
const raw = fs.readFileSync(stateFile, 'utf8');
const state = JSON.parse(raw);

state.current_phase = \`epic_\${wave}_completed\`;
state.current_epic = wave;
state.current_wave = wave;
state.checkpoint_status = \`ready_for_wave_\${wave + 1}\`;
state.wave_status = \`ready_for_wave_\${wave + 1}\`;
state.epics = state.epics || {};
state.epics[String(wave)] = {
  ...(state.epics[String(wave)] || {}),
  status: 'completed',
  phase: \`epic_\${wave}_completed\`,
  updated_at: '2026-03-16T00:00:00.000Z'
};
state.phases = state.phases || {};
state.phases[\`epic_\${wave}_completed\`] = {
  status: 'completed',
  agent: 'squad-chief',
  completed_at: '2026-03-16T00:00:00.000Z'
};
state.metadata = state.metadata || {};
state.metadata.wave = {
  ...(state.metadata.wave || {}),
  number: wave,
  total: state.total_waves || 8,
  title: \`wave-\${wave}\`
};
state.metadata.epic = {
  ...(state.metadata.epic || {}),
  number: wave,
  total: state.total_epics || 8,
  title: \`wave-\${wave}\`
};
state.updated_at = '2026-03-16T00:00:00.000Z';

fs.writeFileSync(stateFile, JSON.stringify(state, null, 2));
process.stdout.write(\`mock executor completed wave \${wave}\\n\`);
`;

  fs.writeFileSync(scriptPath, source, 'utf8');
  return scriptPath;
}

function main() {
  fs.mkdirSync(runtimeRoot, { recursive: true });
  writeJson(stateFile, getFixtureState());

  const statusResult = runWaveLoop(['--status', '--runtime', 'codex', '--json']);
  assert(statusResult.status === 0, 'wave-loop --status should succeed', {
    status: statusResult.status,
    stdout: statusResult.stdout,
    stderr: statusResult.stderr,
  });
  const statusPayload = parseJsonOutput(statusResult);
  assert(statusPayload.status === 'status', 'status payload mismatch', statusPayload);
  assert(statusPayload.nextWave === 7, 'status nextWave mismatch', statusPayload);
  assert(JSON.stringify(statusPayload.plan.waves) === JSON.stringify([7, 8]), 'status planned waves mismatch', statusPayload.plan);
  assert(statusPayload.nextCommand === '*create-squad slides-creator --wave=7', 'status nextCommand mismatch', statusPayload);

  const dryRunResult = runWaveLoop(['--dry-run', '--runtime', 'codex', '--max-waves', '1', '--json']);
  assert(dryRunResult.status === 0, 'wave-loop --dry-run should succeed', {
    status: dryRunResult.status,
    stdout: dryRunResult.stdout,
    stderr: dryRunResult.stderr,
  });
  const dryRunPayload = parseJsonOutput(dryRunResult);
  assert(dryRunPayload.status === 'planned', 'dry-run payload mismatch', dryRunPayload);
  assert(JSON.stringify(dryRunPayload.plan.waves) === JSON.stringify([7]), 'dry-run planned waves mismatch', dryRunPayload.plan);
  assert(fs.existsSync(loopStateFile), 'dry-run should persist loop state', { loopStateFile });

  const mockScript = createMockExecutorScript();
  const runResult = runWaveLoop(
    ['--runtime', 'codex', '--max-waves', '1', '--json'],
    { AIOX_WAVE_LOOP_EXECUTOR_SCRIPT: mockScript }
  );
  assert(runResult.status === 0, 'wave-loop execution should succeed with mock executor', {
    status: runResult.status,
    stdout: runResult.stdout,
    stderr: runResult.stderr,
  });
  const runPayload = parseJsonOutput(runResult);
  assert(runPayload.status === 'completed', 'execution status mismatch', runPayload);
  assert(runPayload.currentWave === 7, 'execution currentWave mismatch', runPayload);
  assert(runPayload.nextWave === 8, 'execution nextWave mismatch', runPayload);
  assert(Array.isArray(runPayload.history), 'execution history missing', runPayload);
  assert(runPayload.history.some(entry => entry.wave === 7 && entry.status === 'completed'), 'execution history should include completed wave 7', runPayload.history);
  assert(runPayload.lastLogFile, 'execution should report last log file', runPayload);

  const finalState = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
  assert(finalState.current_wave === 7, 'final state current_wave mismatch', finalState);
  assert(finalState.wave_status === 'ready_for_wave_8', 'final state wave_status mismatch', finalState);

  const savedLoopState = JSON.parse(fs.readFileSync(loopStateFile, 'utf8'));
  assert(savedLoopState.status === 'completed', 'saved loop state mismatch', savedLoopState);
  assert(savedLoopState.last_wave_completed === 7, 'saved loop state last_wave_completed mismatch', savedLoopState);

  const lastLogPath = runPayload.lastLogFile.startsWith('/')
    ? runPayload.lastLogFile
    : path.join(ROOT, runPayload.lastLogFile);
  assert(fs.existsSync(lastLogPath), 'execution log file should exist', { lastLogPath });

  console.log('PASS: wave-loop runtime e2e passed');
  console.log(JSON.stringify({ runtime_root: runtimeRoot, state_file: stateFile, loop_state_file: loopStateFile }, null, 2));
}

try {
  main();
} catch (error) {
  console.error('ERROR: wave-loop runtime e2e failed');
  console.error(error.message);
  if (error.details) {
    console.error(JSON.stringify(error.details, null, 2));
  }
  console.error(JSON.stringify({ runtime_root: runtimeRoot, state_file: stateFile, loop_state_file: loopStateFile }, null, 2));
  process.exitCode = 1;
} finally {
  if (!keepTmp) {
    try {
      fs.rmSync(runtimeRoot, { recursive: true, force: true });
    } catch {
      // best effort cleanup
    }
  }
}
