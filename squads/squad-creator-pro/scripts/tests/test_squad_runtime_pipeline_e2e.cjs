#!/usr/bin/env node

const fs = require('fs');
const os = require('os');
const path = require('path');
const { spawnSync } = require('child_process');

const ROOT = process.cwd();
const STATE_MANAGER = path.join(ROOT, 'squads', 'squad-creator-pro', 'scripts', 'squad-state-manager.cjs');
const WORKFLOW_RUNNER = path.join(ROOT, 'squads', 'squad-creator-pro', 'scripts', 'squad-workflow-runner.cjs');
const CONTEXT_LOADER = path.join(ROOT, 'squads', 'squad-creator-pro', 'scripts', 'squad-context-loader.cjs');

const slug = `sc_rt6_e2e_${Date.now().toString().slice(-6)}`;
const epicSlug = `test-photo-lab-${Date.now().toString().slice(-6)}`;
const legacySlug = `legacy-photo-lab-${Date.now().toString().slice(-6)}`;
const runtimeRoot = path.join(os.tmpdir(), `aiox-squad-runtime-e2e-${process.pid}-${Date.now()}`);
const epicPrdPath = path.join(runtimeRoot, 'photo-lab-prd.md');
const epicDocsDir = path.join(ROOT, 'docs', 'projects', epicSlug);
const legacyStatePath = path.join(ROOT, 'outputs', 'squad-creator', 'create-squad', legacySlug, 'state.json');
const keepTmp = process.env.AIOX_KEEP_RT_E2E_TMP === '1';

const env = {
  ...process.env,
  AIOX_RUNTIME_ROOT: runtimeRoot,
  AIOX_RUNTIME_CONCURRENCY_THRESHOLD_MS: '0',
};

function parseJson(stdout) {
  const text = (stdout || '').trim();
  if (!text) return null;

  const start = text.indexOf('{');
  const end = text.lastIndexOf('}');
  if (start === -1 || end === -1 || end < start) return null;

  const candidate = text.slice(start, end + 1);
  return JSON.parse(candidate);
}

function runNode(scriptPath, args) {
  const result = spawnSync('node', [scriptPath, ...args], {
    cwd: ROOT,
    env,
    encoding: 'utf8',
  });

  const payload = parseJson(result.stdout);

  if (result.status !== 0) {
    throw new Error(`Command failed: node ${path.relative(ROOT, scriptPath)} ${args.join(' ')}\nstdout=${result.stdout}\nstderr=${result.stderr}`);
  }

  if (!payload) {
    throw new Error(`JSON output missing for command: node ${path.relative(ROOT, scriptPath)} ${args.join(' ')}\nstdout=${result.stdout}\nstderr=${result.stderr}`);
  }

  return payload;
}

function runNodeExpectFailure(scriptPath, args) {
  const result = spawnSync('node', [scriptPath, ...args], {
    cwd: ROOT,
    env,
    encoding: 'utf8',
  });

  const payload = parseJson(result.stdout) || parseJson(result.stderr);
  assert(result.status !== 0, 'Command was expected to fail', { scriptPath, args, stdout: result.stdout, stderr: result.stderr });
  assert(payload && payload.error, 'Failed command did not return structured error payload', { scriptPath, args, stdout: result.stdout, stderr: result.stderr });
  return payload;
}

function assert(condition, message, details = {}) {
  if (!condition) {
    const err = new Error(message);
    err.details = details;
    throw err;
  }
}

function phaseCompleted(phase) {
  runNode(STATE_MANAGER, ['update', slug, '--phase', phase, '--status', 'completed', '--force']);
}

function assertCurrentPhase(expected) {
  const state = runNode(STATE_MANAGER, ['get', slug]);
  assert(state.current_phase === expected, 'Unexpected current_phase', {
    expected,
    received: state.current_phase,
  });
}

function advanceFromCompleted(expectedNext) {
  const next = runNode(WORKFLOW_RUNNER, ['next', slug]);
  assert(next.current_phase === expectedNext, 'Unexpected next phase', {
    expectedNext,
    received: next.current_phase,
  });
}

function writeEpicPrdFixture() {
  const content = `# Photo Lab PRD

### Epic 1: Foundation + Orchestrator

**Goal:** Create the first epic of the squad.

**Deliverables:**
- [ ] squads/${epicSlug}/

#### Story 1.1: Create Squad Structure

**Acceptance Criteria:**
- [ ] Squad structure created
- [ ] Runtime state initialized
`;

  fs.mkdirSync(path.dirname(epicPrdPath), { recursive: true });
  fs.writeFileSync(epicPrdPath, content, 'utf8');
}

function writeLegacyStateFixture() {
  const payload = {
    slug: legacySlug,
    display_name: 'Legacy Photo Lab',
    current_phase: 'research',
    checkpoint_status: 'in_progress',
    phases: {},
    metadata: {
      execution_model: 'legacy'
    }
  };

  fs.mkdirSync(path.dirname(legacyStatePath), { recursive: true });
  fs.writeFileSync(legacyStatePath, JSON.stringify(payload, null, 2), 'utf8');
}

function main() {
  fs.mkdirSync(runtimeRoot, { recursive: true });
  writeEpicPrdFixture();
  writeLegacyStateFixture();

  const start = runNode(WORKFLOW_RUNNER, ['start', slug, '--name', 'SC RT6 E2E']);
  assert(start.success === true, 'Start failed', start);
  assert(start.current_phase === 'research', 'Start did not move to research', start);

  const expectedActive = path.join(runtimeRoot, 'active-squad.json');
  const expectedState = path.join(runtimeRoot, 'create-squad', slug, 'state.json');
  assert(fs.existsSync(expectedActive), 'active-squad.json not created', { expectedActive });
  assert(fs.existsSync(expectedState), 'state.json not created', { expectedState });

  const resume = runNode(WORKFLOW_RUNNER, ['resume', slug]);
  assert(resume.current_phase === 'research', 'Resume phase mismatch', resume);

  phaseCompleted('research');
  advanceFromCompleted('source_validation');

  phaseCompleted('source_validation');
  advanceFromCompleted('dna_extraction');

  phaseCompleted('dna_extraction');
  advanceFromCompleted('agent_scaffolding');

  phaseCompleted('agent_scaffolding');
  advanceFromCompleted('task_anatomy');

  phaseCompleted('task_anatomy');
  const checkpoint = runNode(WORKFLOW_RUNNER, ['next', slug]);
  assert(checkpoint.current_phase === 'quality_gate', 'Did not reach quality_gate', checkpoint);
  assert(checkpoint.status === 'checkpoint', 'quality_gate should be checkpoint', checkpoint);

  const approved = runNode(WORKFLOW_RUNNER, ['approve', slug]);
  assert(approved.current_phase === 'integration', 'Approve should move to integration', approved);

  phaseCompleted('integration');
  advanceFromCompleted('smoke_test');

  phaseCompleted('smoke_test');
  advanceFromCompleted('completed');

  // Mark terminal state as completed for strict status checks.
  phaseCompleted('completed');
  assertCurrentPhase('completed');

  const status = runNode(WORKFLOW_RUNNER, ['status', slug]);
  assert(status.current_phase === 'completed', 'Status phase mismatch at end', status);

  const ctx = runNode(CONTEXT_LOADER, ['squad-chief', slug]);
  assert(ctx.slug === slug, 'Context loader slug mismatch', ctx);
  assert(typeof ctx.state_file === 'string' && ctx.state_file.endsWith(`/create-squad/${slug}/state.json`), 'Context loader state_file mismatch', {
    state_file: ctx.state_file,
  });

  const epicStart = runNode(WORKFLOW_RUNNER, ['start-epic', epicSlug, '--wave', '1', '--prd', epicPrdPath, '--workflows-mapped', '22']);
  assert(epicStart.execution_model === 'epic', 'Epic flow should use execution_model epic', epicStart);
  assert(epicStart.current_phase === 'story_ready', 'Epic flow should move to story_ready', epicStart);
  assert(epicStart.epic && epicStart.epic.number === 1, 'Epic metadata missing from start output', epicStart);

  const epicState = runNode(STATE_MANAGER, ['get', epicSlug]);
  assert(epicState.slug === epicSlug, 'Epic state slug mismatch', epicState);
  assert(epicState.current_epic === 1, 'Epic state should track current_epic', epicState);
  assert(epicState.total_epics === 1, 'Epic state should track total_epics', epicState);

  const epicPhaseUpdate = runNode(STATE_MANAGER, ['update', epicSlug, '--phase', 'epic_1_in_progress', '--status', 'in_progress', '--force']);
  assert(epicPhaseUpdate.current.current_phase === 'epic_1_in_progress', 'Dynamic epic phase update failed', epicPhaseUpdate);

  const epicStateAfterUpdate = runNode(STATE_MANAGER, ['get', epicSlug]);
  assert(epicStateAfterUpdate.current_epic === 1, 'Dynamic epic update should preserve current_epic', epicStateAfterUpdate);
  assert(epicStateAfterUpdate.epics && epicStateAfterUpdate.epics['1'] && epicStateAfterUpdate.epics['1'].status === 'in_progress', 'Epic status tracking missing', epicStateAfterUpdate);

  const epicStatus = runNode(WORKFLOW_RUNNER, ['status', epicSlug]);
  assert(epicStatus.execution_model === 'epic', 'Epic status should expose execution_model epic', epicStatus);
  assert(epicStatus.current_epic === 1, 'Epic status should expose current_epic', epicStatus);

  const epicResume = runNode(WORKFLOW_RUNNER, ['resume', epicSlug]);
  assert(epicResume.execution_model === 'epic', 'Epic resume should expose execution_model epic', epicResume);
  assert(epicResume.epic && epicResume.epic.number === 1, 'Epic resume should surface epic metadata', epicResume);

  const epicCtx = runNode(CONTEXT_LOADER, ['squad-chief', epicSlug]);
  assert(epicCtx.execution_model === 'epic', 'Context loader should expose epic execution_model', epicCtx);
  assert(epicCtx.epic && epicCtx.epic.current === 1, 'Context loader should expose epic metadata', epicCtx);

  const prdGateFailure = runNodeExpectFailure(WORKFLOW_RUNNER, ['start', 'missing-prd-large-squad', '--workflows-mapped', '22']);
  assert(prdGateFailure.error.code === 'PRD_REQUIRED', 'Missing PRD should trigger PRD_REQUIRED gate', prdGateFailure);

  const legacyState = runNode(STATE_MANAGER, ['get', legacySlug]);
  assert(legacyState.slug === legacySlug, 'Legacy fallback should read legacy state file', legacyState);

  console.log('PASS: squad runtime pipeline e2e passed');
  console.log(JSON.stringify({
    slug,
    epic_slug: epicSlug,
    runtime_root: runtimeRoot,
    state_file: expectedState,
    active_file: expectedActive,
  }, null, 2));
}

try {
  main();
} catch (error) {
  console.error('ERROR: squad runtime pipeline e2e failed');
  console.error(error.message);
  if (error.details) {
    console.error(JSON.stringify(error.details, null, 2));
  }
  console.error(JSON.stringify({ slug, runtime_root: runtimeRoot }, null, 2));
  process.exitCode = 1;
} finally {
  if (!keepTmp) {
    try {
      fs.rmSync(epicDocsDir, { recursive: true, force: true });
    } catch {
      // best effort cleanup
    }
    try {
      fs.rmSync(path.join(ROOT, 'outputs', 'squad-creator', 'create-squad', legacySlug), { recursive: true, force: true });
    } catch {
      // best effort cleanup
    }
    try {
      fs.rmSync(runtimeRoot, { recursive: true, force: true });
    } catch {
      // best effort cleanup
    }
  }
}
