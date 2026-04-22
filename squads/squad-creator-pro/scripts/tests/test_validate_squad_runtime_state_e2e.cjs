#!/usr/bin/env node

const fs = require('fs');
const os = require('os');
const path = require('path');
const { spawnSync } = require('child_process');

const ROOT = process.cwd();
const keepTmp = process.env.AIOX_KEEP_VALIDATE_RT_E2E_TMP === '1';
const runtimeRoot = path.join(os.tmpdir(), `aiox-validate-runtime-e2e-${process.pid}-${Date.now()}`);
const stateFile = path.join(runtimeRoot, 'validate-squad', 'spy', 'state.json');
const validateScript = path.join(ROOT, 'squads', 'squad-creator-pro', 'scripts', 'validate-squad.sh');

function assert(condition, message, details = {}) {
  if (!condition) {
    const err = new Error(message);
    err.details = details;
    throw err;
  }
}

function runValidate() {
  return spawnSync('bash', [validateScript, 'spy', '--quick', '--json'], {
    cwd: ROOT,
    env: {
      ...process.env,
      AIOX_RUNTIME_ROOT: runtimeRoot,
    },
    encoding: 'utf8',
  });
}

function main() {
  fs.mkdirSync(runtimeRoot, { recursive: true });

  const result = runValidate();
  const stdout = result.stdout || '';
  const match = stdout.match(/\{\s*"squad":[\s\S]*\}\s*$/);
  const payload = match ? JSON.parse(match[0]) : null;

  assert(result.status === 0, 'validate-squad should succeed for spy fixture', {
    status: result.status,
    stdout: result.stdout,
    stderr: result.stderr,
  });
  assert(payload && payload.result === 'PASS', 'validate-squad result mismatch for spy fixture', {
    payload,
    stdout: result.stdout,
  });

  assert(fs.existsSync(stateFile), 'validate runtime state file not created', { stateFile });

  const raw = fs.readFileSync(stateFile, 'utf8');
  const state = JSON.parse(raw);

  assert(state.workflow === 'validate-squad', 'workflow mismatch', { workflow: state.workflow });
  assert(state.squad_name === 'spy', 'squad_name mismatch', { squad_name: state.squad_name });
  assert(state.current_phase === 'phase_7_final_scoring', 'current_phase mismatch', { current_phase: state.current_phase });
  assert(state.status === 'completed', 'status mismatch', { status: state.status });
  assert(state.result === 'PASS', 'result mismatch', { result: state.result });
  assert(typeof state.final_score === 'number', 'final_score should be numeric', { final_score: state.final_score });

  const expectedPhases = [
    'phase_1_structure',
    'phase_2_security_scan',
    'phase_3_cross_reference',
    'phase_4_type_detection',
    'phase_5_production_validation',
    'phase_6_quality_analysis',
    'phase_7_final_scoring',
  ];

  for (const phase of expectedPhases) {
    assert(state.phases && state.phases[phase], 'phase missing in state', { phase });
  }

  console.log('PASS: validate-squad runtime state e2e passed');
  console.log(JSON.stringify({ runtime_root: runtimeRoot, state_file: stateFile }, null, 2));
}

try {
  main();
} catch (error) {
  console.error('ERROR: validate-squad runtime state e2e failed');
  console.error(error.message);
  if (error.details) {
    console.error(JSON.stringify(error.details, null, 2));
  }
  console.error(JSON.stringify({ runtime_root: runtimeRoot, state_file: stateFile }, null, 2));
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
