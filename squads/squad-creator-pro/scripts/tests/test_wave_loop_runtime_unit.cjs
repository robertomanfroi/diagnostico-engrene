#!/usr/bin/env node

const fs = require('fs');
const os = require('os');
const path = require('path');
const { spawnSync } = require('child_process');

const ROOT = process.cwd();
const keepTmp = process.env.AIOX_KEEP_WAVE_LOOP_UNIT_TMP === '1';
const waveLoop = require(path.join(ROOT, 'squads', 'squad-creator-pro', 'scripts', 'wave-loop.cjs'));
const waveLoopScript = path.join(ROOT, 'squads', 'squad-creator-pro', 'scripts', 'wave-loop.cjs');
const workflowRunnerScript = path.join(ROOT, 'squads', 'squad-creator-pro', 'scripts', 'squad-workflow-runner.cjs');
const tmpRoot = path.join(os.tmpdir(), `aiox-wave-loop-unit-${process.pid}-${Date.now()}`);

function assert(condition, message, details = {}) {
  if (!condition) {
    const error = new Error(message);
    error.details = details;
    throw error;
  }
}

function writeJson(targetPath, payload) {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, JSON.stringify(payload, null, 2));
}

function getRuntimeState({ currentWave, totalWaves, nextReadyWave = null, completed = false }) {
  return {
    slug: 'slides-creator',
    workflow: 'create-squad',
    execution_model: 'epic',
    runtime_taxonomy: {
      command_unit: 'wave',
      command_pattern: '*create-squad slides-creator --wave={n}',
    },
    current_phase: completed ? `epic_${currentWave}_completed` : `epic_${currentWave}_completed`,
    checkpoint_status: nextReadyWave ? `ready_for_wave_${nextReadyWave}` : 'completed',
    current_epic: currentWave,
    total_epics: totalWaves,
    current_wave: currentWave,
    total_waves: totalWaves,
    wave_status: nextReadyWave ? `ready_for_wave_${nextReadyWave}` : 'completed',
    epics: {
      [String(currentWave)]: { status: 'completed', phase: `epic_${currentWave}_completed` },
    },
    phases: {
      [`epic_${currentWave}_completed`]: { status: 'completed' },
    },
    metadata: {
      execution_model: 'epic',
      wave: { number: currentWave, total: totalWaves, title: `wave-${currentWave}` },
      epic: { number: currentWave, total: totalWaves, title: `wave-${currentWave}` },
    },
  };
}

function parseJsonOutput(result) {
  try {
    return JSON.parse((result.stdout || '').trim());
  } catch (error) {
    throw new Error(`Failed to parse JSON output: ${error.message}\nSTDOUT:\n${result.stdout}\nSTDERR:\n${result.stderr}`);
  }
}

function createIsolatedRuntimeRoot(name) {
  const runtimeRoot = path.join(tmpRoot, name);
  fs.mkdirSync(runtimeRoot, { recursive: true });
  return runtimeRoot;
}

function writeRuntimeState(runtimeRoot, state) {
  const statePath = path.join(runtimeRoot, 'create-squad', 'slides-creator', 'state.json');
  writeJson(statePath, state);
  return statePath;
}

function createFakeRuntimeBinary(binDir, runtimeName) {
  const scriptPath = path.join(binDir, runtimeName);
  const source = `#!${process.execPath}
const fs = require('fs');
const path = require('path');

const runtimeName = ${JSON.stringify(runtimeName)};
const args = process.argv.slice(2);
const runtimeRoot = process.env.AIOX_RUNTIME_ROOT;
const capturePath = path.join(runtimeRoot, \`capture-\${runtimeName}.json\`);
const statePath = path.join(runtimeRoot, 'create-squad', 'slides-creator', 'state.json');
const prompt = runtimeName === 'codex' ? fs.readFileSync(0, 'utf8') : args[args.length - 1];

fs.writeFileSync(capturePath, JSON.stringify({ runtime: runtimeName, args, prompt }, null, 2));

const state = JSON.parse(fs.readFileSync(statePath, 'utf8'));
state.current_phase = 'epic_7_completed';
state.current_epic = 7;
state.current_wave = 7;
state.checkpoint_status = 'ready_for_wave_8';
state.wave_status = 'ready_for_wave_8';
state.epics = state.epics || {};
state.epics['7'] = {
  ...(state.epics['7'] || {}),
  status: 'completed',
  phase: 'epic_7_completed',
  updated_at: '2026-03-16T00:00:00.000Z'
};
state.phases = state.phases || {};
state.phases['epic_7_completed'] = {
  status: 'completed',
  agent: 'squad-chief',
  completed_at: '2026-03-16T00:00:00.000Z'
};
state.metadata = state.metadata || {};
state.metadata.wave = { ...(state.metadata.wave || {}), number: 7, total: 8, title: 'wave-7' };
state.metadata.epic = { ...(state.metadata.epic || {}), number: 7, total: 8, title: 'wave-7' };
state.updated_at = '2026-03-16T00:00:00.000Z';

fs.writeFileSync(statePath, JSON.stringify(state, null, 2));
process.stdout.write(\`\${runtimeName} fake runtime completed wave 7\\n\`);
`;

  fs.writeFileSync(scriptPath, source, 'utf8');
  fs.chmodSync(scriptPath, 0o755);
}

function buildProviderEnv(runtimeRoot, binDir) {
  return {
    ...process.env,
    AIOX_RUNTIME_ROOT: runtimeRoot,
    PATH: `${binDir}${path.delimiter}/usr/bin${path.delimiter}/bin`,
  };
}

function runNodeScript(scriptPath, args, env) {
  return spawnSync(process.execPath, [scriptPath, ...args], {
    cwd: ROOT,
    encoding: 'utf8',
    env,
  });
}

function testHelperContracts() {
  const completedState = getRuntimeState({ currentWave: 8, totalWaves: 8, completed: true });
  const completedPlan = waveLoop.inferPlan(completedState, {
    from: null,
    to: null,
    maxWaves: null,
  });

  assert(completedPlan.alreadyComplete === true, 'completed plan should be marked alreadyComplete', completedPlan);
  assert(Array.isArray(completedPlan.waves) && completedPlan.waves.length === 0, 'completed plan should have no waves', completedPlan);
  assert(completedPlan.nextWave === null, 'completed plan nextWave should be null', completedPlan);

  const failedSummary = waveLoop.buildSummary({
    slug: 'slides-creator',
    args: { mode: 'ssh', runtime: 'codex' },
    selectedRuntime: 'codex',
    statePath: path.join(ROOT, '.aiox', 'dummy-state.json'),
    state: completedState,
    plan: completedPlan,
    loopStatePath: path.join(ROOT, '.aiox', 'dummy-loop-state.json'),
    logDir: path.join(ROOT, '.aiox', 'dummy-logs'),
    status: 'failed',
  });
  assert(failedSummary.success === false, 'failed summary should not report success', failedSummary);
  assert(failedSummary.nextWave === null, 'failed summary for completed state should not advertise nextWave', failedSummary);
  assert(failedSummary.nextCommand === null, 'failed summary for completed state should not advertise nextCommand', failedSummary);

  const prompt = waveLoop.buildWavePrompt({
    slug: 'slides-creator',
    wave: 7,
    command: '*create-squad slides-creator --wave=7',
    statePath: path.join(ROOT, '.aiox', 'dummy-state.json'),
  });
  assert(prompt.includes('$squad-chief'), 'wave prompt should use explicit squad-chief activation shortcut', { prompt });

  const codexInvocation = waveLoop.buildExecutorInvocation({
    selectedRuntime: 'codex',
    prompt: 'codex prompt',
    slug: 'slides-creator',
    wave: 7,
    statePath: 'state.json',
    command: '*create-squad slides-creator --wave=7',
    logFile: 'wave.log',
  });
  assert(codexInvocation.command === 'codex', 'codex invocation command mismatch', codexInvocation);
  assert(codexInvocation.args.includes('exec'), 'codex invocation should use exec', codexInvocation);
  assert(codexInvocation.args.at(-1) === '-', 'codex invocation should receive prompt via stdin', codexInvocation);
  assert(codexInvocation.input === 'codex prompt', 'codex invocation input mismatch', codexInvocation);

  const claudeInvocation = waveLoop.buildExecutorInvocation({
    selectedRuntime: 'claude',
    prompt: 'claude prompt',
    slug: 'slides-creator',
    wave: 7,
    statePath: 'state.json',
    command: '*create-squad slides-creator --wave=7',
    logFile: 'wave.log',
  });
  assert(claudeInvocation.command === 'claude', 'claude invocation command mismatch', claudeInvocation);
  assert(claudeInvocation.args[0] === '-p', 'claude invocation should start with -p', claudeInvocation);
  assert(claudeInvocation.args.at(-1) === 'claude prompt', 'claude invocation should receive prompt as argv', claudeInvocation);
  assert(claudeInvocation.input === null, 'claude invocation should not pipe stdin prompt', claudeInvocation);
}

function testCompletedStatusCli() {
  const runtimeRoot = createIsolatedRuntimeRoot('completed-status');
  writeRuntimeState(runtimeRoot, getRuntimeState({ currentWave: 8, totalWaves: 8, completed: true }));

  const result = runNodeScript(
    waveLoopScript,
    ['slides-creator', '--status', '--runtime', 'auto', '--json'],
    {
      ...process.env,
      AIOX_RUNTIME_ROOT: runtimeRoot,
      PATH: `/usr/bin${path.delimiter}/bin`,
    }
  );

  assert(result.status === 0, 'completed status should succeed', result);
  const payload = parseJsonOutput(result);
  assert(payload.status === 'completed', 'completed status payload mismatch', payload);
  assert(payload.success === true, 'completed status should report success', payload);
  assert(payload.nextWave === null, 'completed status should not advertise nextWave', payload);
  assert(payload.nextCommand === null, 'completed status should not advertise nextCommand', payload);
  assert(Array.isArray(payload.plan.waves) && payload.plan.waves.length === 0, 'completed status should have no planned waves', payload.plan);
}

function testMissingExplicitRuntimeFailsEarly() {
  const runtimeRoot = createIsolatedRuntimeRoot('missing-runtime');
  writeRuntimeState(runtimeRoot, getRuntimeState({ currentWave: 6, totalWaves: 8, nextReadyWave: 7 }));

  const result = runNodeScript(
    waveLoopScript,
    ['slides-creator', '--status', '--runtime', 'codex', '--json'],
    {
      ...process.env,
      AIOX_RUNTIME_ROOT: runtimeRoot,
      PATH: `/usr/bin${path.delimiter}/bin`,
    }
  );

  assert(result.status === 1, 'missing explicit runtime should fail', result);
  const payload = parseJsonOutput(result);
  assert(payload.success === false, 'missing runtime payload should report success=false', payload);
  assert(/not available in PATH/i.test(payload.error.message), 'missing runtime message mismatch', payload);
}

function testProviderExecution(runtimeName) {
  const runtimeRoot = createIsolatedRuntimeRoot(`provider-${runtimeName}`);
  const binDir = path.join(runtimeRoot, 'bin');
  fs.mkdirSync(binDir, { recursive: true });
  createFakeRuntimeBinary(binDir, runtimeName);
  writeRuntimeState(runtimeRoot, getRuntimeState({ currentWave: 6, totalWaves: 8, nextReadyWave: 7 }));

  const result = runNodeScript(
    waveLoopScript,
    ['slides-creator', '--runtime', runtimeName, '--max-waves', '1', '--json'],
    buildProviderEnv(runtimeRoot, binDir)
  );

  assert(result.status === 0, `${runtimeName} execution should succeed`, result);
  const payload = parseJsonOutput(result);
  assert(payload.success === true, `${runtimeName} payload should report success`, payload);
  assert(payload.status === 'completed', `${runtimeName} payload status mismatch`, payload);
  assert(payload.selectedRuntime === runtimeName, `${runtimeName} payload selectedRuntime mismatch`, payload);
  assert(payload.currentWave === 7, `${runtimeName} payload currentWave mismatch`, payload);
  assert(payload.nextWave === 8, `${runtimeName} payload nextWave mismatch`, payload);
  assert(payload.history.some(entry => entry.wave === 7 && entry.status === 'completed'), `${runtimeName} history missing completed wave`, payload.history);

  const capturePath = path.join(runtimeRoot, `capture-${runtimeName}.json`);
  assert(fs.existsSync(capturePath), `${runtimeName} capture file should exist`, { capturePath });
  const capture = JSON.parse(fs.readFileSync(capturePath, 'utf8'));
  assert(capture.prompt.includes('$squad-chief'), `${runtimeName} prompt should contain explicit activation`, capture);

  if (runtimeName === 'codex') {
    assert(capture.args.includes('exec'), 'codex fake binary should receive exec subcommand', capture);
    assert(capture.args.at(-1) === '-', 'codex fake binary should receive stdin marker', capture);
  } else {
    assert(capture.args[0] === '-p', 'claude fake binary should receive -p', capture);
    assert(capture.args.includes('--dangerously-skip-permissions'), 'claude fake binary should receive permissions bypass flag', capture);
  }
}

function testWorkflowRunnerDelegation() {
  const runtimeRoot = createIsolatedRuntimeRoot('runner-delegation');
  const binDir = path.join(runtimeRoot, 'bin');
  fs.mkdirSync(binDir, { recursive: true });
  createFakeRuntimeBinary(binDir, 'codex');
  writeRuntimeState(runtimeRoot, getRuntimeState({ currentWave: 6, totalWaves: 8, nextReadyWave: 7 }));

  const result = runNodeScript(
    workflowRunnerScript,
    ['wave-loop', 'slides-creator', '--runtime', 'codex', '--max-waves', '1', '--json'],
    buildProviderEnv(runtimeRoot, binDir)
  );

  assert(result.status === 0, 'workflow runner delegation should succeed', result);
  const payload = parseJsonOutput(result);
  assert(payload.success === true, 'workflow runner delegated payload should report success', payload);
  assert(payload.status === 'completed', 'workflow runner delegated payload status mismatch', payload);
  assert(payload.selectedRuntime === 'codex', 'workflow runner delegated payload runtime mismatch', payload);
}

function main() {
  fs.mkdirSync(tmpRoot, { recursive: true });

  testHelperContracts();
  testCompletedStatusCli();
  testMissingExplicitRuntimeFailsEarly();
  testProviderExecution('codex');
  testProviderExecution('claude');
  testWorkflowRunnerDelegation();

  console.log('PASS: wave-loop runtime unit tests passed');
  console.log(JSON.stringify({ tmp_root: tmpRoot }, null, 2));
}

try {
  main();
} catch (error) {
  console.error('ERROR: wave-loop runtime unit tests failed');
  console.error(error.message);
  if (error.details) {
    console.error(JSON.stringify(error.details, null, 2));
  }
  console.error(JSON.stringify({ tmp_root: tmpRoot }, null, 2));
  process.exitCode = 1;
} finally {
  if (!keepTmp) {
    try {
      fs.rmSync(tmpRoot, { recursive: true, force: true });
    } catch {
      // best effort cleanup
    }
  }
}
