#!/usr/bin/env node
/**
 * Squad State Manager - Pipeline state for squad creation.
 * Adapted from MMOS state manager for squad-creator workflow.
 * @llm-context CLI tool for tracking squad creation pipeline progress.
 */

const fs = require('fs');
const path = require('path');
const {
  DEFAULT_WORKFLOW,
  getCanonicalStatePath,
  getWorkflowRuntimeRoot,
  readActiveSquad: readActiveSquadFromRuntime,
  writeActiveSquad: writeActiveSquadToRuntime,
  readStateWithLegacyFallback,
  writeCanonicalState,
  toWorkspaceRelative,
} = require(path.resolve(__dirname, '..', '..', 'squad-creator', 'scripts', 'lib', 'squad-runtime-paths.cjs'));

// ═══════════════════════════════════════════════════════════════════════════
// CONSTANTS
// ═══════════════════════════════════════════════════════════════════════════

const CONCURRENCY_THRESHOLD_MS = Number(process.env.AIOX_RUNTIME_CONCURRENCY_THRESHOLD_MS || 5000); // --force bypasses this check

const SLUG_PATTERN = /^[a-z0-9]+(?:[-_][a-z0-9]+)*$/;
const EXECUTION_MODELS = ['legacy', 'epic'];

const LEGACY_PHASES = [
  'init',
  'research',
  'source_validation',
  'dna_extraction',
  'agent_scaffolding',
  'task_anatomy',
  'quality_gate',
  'integration',
  'smoke_test',
  'completed',
  'failed'
];

const EPIC_PHASES = [
  'init',
  'epic_init',
  'story_ready',
  'story_in_progress',
  'epic_validation',
  'completed',
  'failed'
];

const VALID_PHASES = Array.from(new Set([...LEGACY_PHASES, ...EPIC_PHASES]));

const VALID_STATUSES = [
  'pending',
  'in_progress',
  'checkpoint',    // Awaiting human approval
  'approved',
  'rejected',
  'completed'
];

const PHASE_AGENTS = {
  'research': 'oalanicolas',
  'source_validation': 'oalanicolas',
  'dna_extraction': 'oalanicolas',
  'agent_scaffolding': 'oalanicolas',
  'task_anatomy': 'pedro-valerio',
  'quality_gate': 'pedro-valerio',
  'integration': 'squad-chief',
  'smoke_test': 'squad-chief',
  'epic_init': 'squad-chief',
  'story_ready': 'squad-chief',
  'story_in_progress': 'squad-chief',
  'epic_validation': 'squad-chief'
};

// ═══════════════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════════════

function outputJson(data) {
  console.log(JSON.stringify(data));
}

function outputError(code, message, details = {}) {
  outputJson({
    success: false,
    error: { code, message, details }
  });
}

function slugToDisplayName(slug) {
  return slug
    .split(/[-_]/)
    .filter(Boolean)
    .map(word => word.charAt(0).toUpperCase() + word.slice(1))
    .join(' ');
}

function parseOptionalNumber(value) {
  if (value === null || value === undefined || value === '') return null;
  const parsed = Number.parseInt(value, 10);
  return Number.isFinite(parsed) ? parsed : null;
}

function isDynamicEpicPhase(phase) {
  return /^epic_\d+_(init|planning|story_ready|in_progress|validated|completed)$/.test(phase || '');
}

function parseDynamicEpicPhase(phase) {
  const match = /^epic_(\d+)_(init|planning|story_ready|in_progress|validated|completed)$/.exec(phase || '');
  if (!match) return null;
  return {
    number: Number.parseInt(match[1], 10),
    suffix: match[2]
  };
}

function inferExecutionModel(state, phase = null) {
  const explicit = state?.execution_model || state?.metadata?.execution_model;
  if (explicit && EXECUTION_MODELS.includes(explicit)) return explicit;

  const targetPhase = phase || state?.current_phase;
  if (
    ['epic_init', 'story_ready', 'story_in_progress', 'epic_validation'].includes(targetPhase) ||
    isDynamicEpicPhase(targetPhase)
  ) {
    return 'epic';
  }

  return 'legacy';
}

function getRuntimeTaxonomy(state) {
  return state?.runtime_taxonomy || state?.metadata?.runtime_taxonomy || {};
}

function usesWaveCommandUnit(state) {
  return getRuntimeTaxonomy(state).command_unit === 'wave';
}

function syncWaveAliases(state) {
  if (!usesWaveCommandUnit(state)) return;

  const epicNumber = state.current_epic ?? state.metadata?.epic?.number ?? null;
  const totalEpics = state.total_epics ?? state.metadata?.epic?.total ?? null;
  if (!state.metadata || typeof state.metadata !== 'object') {
    state.metadata = {};
  }

  state.display_execution_model = 'wave';
  if (epicNumber !== null) state.current_wave = epicNumber;
  if (totalEpics !== null) state.total_waves = totalEpics;

  if (epicNumber !== null || totalEpics !== null || state.metadata?.epic?.title) {
    state.metadata.wave = {
      ...(state.metadata.wave || {}),
      ...(epicNumber !== null ? { number: epicNumber } : {}),
      ...(totalEpics !== null ? { total: totalEpics } : {}),
      ...(state.metadata?.epic?.title ? { title: state.metadata.epic.title } : {})
    };
  }

  if (typeof state.current_phase === 'string') {
    state.display_phase = state.current_phase.replace(/^epic_(\d+)_/i, 'wave_$1_');
  }
  if (typeof state.checkpoint_status === 'string') {
    state.wave_status = state.checkpoint_status.replace(/^ready_for_epic_/i, 'ready_for_wave_');
  }
}

function getStatePath(slug) {
  return getCanonicalStatePath(slug, DEFAULT_WORKFLOW);
}

function readActiveSquad() {
  return readActiveSquadFromRuntime();
}

function writeActiveSquad(slug) {
  writeActiveSquadToRuntime(slug, DEFAULT_WORKFLOW);
}

/**
 * Resolve slug: use provided slug or fallback to active squad pointer.
 */
function resolveSlug(slug) {
  if (slug && !slug.startsWith('-')) return slug;
  return readActiveSquad();
}

function readState(slug) {
  const result = readStateWithLegacyFallback(slug, {
    workflow: DEFAULT_WORKFLOW,
  });

  if (!result.state) return null;

  if (result.state.__corrupted) {
    return { __corrupted: true };
  }

  return result.state;
}

function writeState(slug, state) {
  writeCanonicalState(slug, state, DEFAULT_WORKFLOW);
}

/**
 * Check if state.json was modified recently (concurrency detection).
 */
function checkConcurrency(slug) {
  const statePath = getStatePath(slug);
  if (!fs.existsSync(statePath)) return false;
  const stat = fs.statSync(statePath);
  return (Date.now() - stat.mtimeMs) < CONCURRENCY_THRESHOLD_MS;
}

// ═══════════════════════════════════════════════════════════════════════════
// COMMANDS
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Initialize a new squad pipeline state.
 */
function cmdInit(slug, options = {}) {
  const {
    name = null,
    sourceMind = null,
    targetDomain = null,
    executionModel = null,
    prdPath = null,
    epicNumber = null,
    epicTitle = null,
    storyId = null,
    storyTitle = null,
    storyPath = null,
    scopeType = null,
    workflowsMapped = null,
    agentsNeeded = null,
    contextEntrypoint = null,
    totalEpics = null,
    squadType = null
  } = options;

  if (!SLUG_PATTERN.test(slug)) {
    outputError('INVALID_SLUG', 'Slug must be kebab-case or snake_case', {
      received: slug,
      expected_pattern: '^[a-z0-9]+(?:[-_][a-z0-9]+)*$'
    });
    process.exit(1);
  }

  if (executionModel && !EXECUTION_MODELS.includes(executionModel)) {
    outputError('INVALID_EXECUTION_MODEL', 'execution model must be one of: legacy, epic', {
      received: executionModel,
      valid_models: EXECUTION_MODELS
    });
    process.exit(1);
  }

  const now = new Date().toISOString();
  const displayName = name || slugToDisplayName(slug);
  const normalizedEpicNumber = parseOptionalNumber(epicNumber);
  const normalizedTotalEpics = parseOptionalNumber(totalEpics);
  const normalizedWorkflowsMapped = parseOptionalNumber(workflowsMapped);
  const normalizedAgentsNeeded = parseOptionalNumber(agentsNeeded);

  // Create or update state
  const existingState = readState(slug);
  const resolvedExecutionModel =
    executionModel ||
    inferExecutionModel(existingState, normalizedEpicNumber ? 'epic_init' : null);
  const state = (existingState && !existingState.__corrupted) ? existingState : {
    slug,
    display_name: displayName,
    workflow: DEFAULT_WORKFLOW,
    execution_model: resolvedExecutionModel,
    created_at: now,
    current_phase: 'init',
    checkpoint_status: 'pending',
    current_epic: null,
    total_epics: null,
    epics: {},
    phases: {},
    completed_outputs: [],
    agent_history: [],
    metadata: {}
  };

  if (!state.metadata || typeof state.metadata !== 'object') {
    state.metadata = {};
  }

  state.updated_at = now;
  state.workflow = DEFAULT_WORKFLOW;
  state.execution_model = resolvedExecutionModel;
  state.current_phase = 'init';
  state.checkpoint_status = 'pending';
  if (name) state.display_name = displayName;
  if (!state.display_name) state.display_name = displayName;

  state.metadata.execution_model = resolvedExecutionModel;
  if (sourceMind) state.metadata.source_mind = sourceMind;
  if (targetDomain) state.metadata.target_domain = targetDomain;
  if (prdPath) state.metadata.prd_path = prdPath;
  if (scopeType) state.metadata.scope_type = scopeType;
  if (contextEntrypoint) state.metadata.context_entrypoint = contextEntrypoint;
  if (squadType) state.metadata.squad_type = squadType;

  if (normalizedWorkflowsMapped !== null || normalizedAgentsNeeded !== null) {
    state.metadata.scope_metrics = {
      ...(state.metadata.scope_metrics || {}),
      ...(normalizedWorkflowsMapped !== null ? { workflows_mapped: normalizedWorkflowsMapped } : {}),
      ...(normalizedAgentsNeeded !== null ? { agents_needed: normalizedAgentsNeeded } : {})
    };
  }

  if (normalizedEpicNumber !== null || epicTitle) {
    state.metadata.epic = {
      ...(state.metadata.epic || {}),
      ...(normalizedEpicNumber !== null ? { number: normalizedEpicNumber } : {}),
      ...(normalizedTotalEpics !== null ? { total: normalizedTotalEpics } : {}),
      ...(epicTitle ? { title: epicTitle } : {})
    };
  }

  if (normalizedEpicNumber !== null) state.current_epic = normalizedEpicNumber;
  if (normalizedTotalEpics !== null) state.total_epics = normalizedTotalEpics;
  if (!state.epics || typeof state.epics !== 'object') state.epics = {};
  if (normalizedEpicNumber !== null) {
    state.epics[String(normalizedEpicNumber)] = {
      ...(state.epics[String(normalizedEpicNumber)] || {}),
      number: normalizedEpicNumber,
      ...(epicTitle ? { title: epicTitle } : {}),
      ...(storyPath ? { story_path: storyPath } : {})
    };
  }

  if (storyId || storyTitle || storyPath) {
    state.metadata.story = {
      ...(state.metadata.story || {}),
      ...(storyId ? { id: storyId } : {}),
      ...(storyTitle ? { title: storyTitle } : {}),
      ...(storyPath ? { path: storyPath } : {})
    };
  }

  syncWaveAliases(state);
  writeState(slug, state);
  writeActiveSquad(slug);

  outputJson({
    success: true,
    slug,
    path: toWorkspaceRelative(getStatePath(slug)),
    display_name: state.display_name
  });
}

/**
 * Update pipeline phase/status.
 */
function cmdUpdate(slug, phase, status, options = {}) {
  const { force = false, output = null } = options;

  // Validate phase
  if (!VALID_PHASES.includes(phase) && !isDynamicEpicPhase(phase)) {
    outputError('INVALID_PHASE', `Invalid phase: ${phase}`, {
      received: phase,
      valid_phases: [...VALID_PHASES, 'epic_<N>_init', 'epic_<N>_planning', 'epic_<N>_story_ready', 'epic_<N>_in_progress', 'epic_<N>_validated', 'epic_<N>_completed']
    });
    process.exit(1);
  }

  // Validate status
  if (status && !VALID_STATUSES.includes(status)) {
    outputError('INVALID_STATUS', `Invalid status: ${status}`, {
      received: status,
      valid_statuses: VALID_STATUSES
    });
    process.exit(1);
  }

  // Read existing state
  const state = readState(slug);
  if (!state) {
    outputError('STATE_NOT_FOUND', `No state found for slug: ${slug}. Run init first.`);
    process.exit(1);
  }

  if (state.__corrupted) {
    outputError('CORRUPTED_STATE', `state.json for ${slug} is corrupted (invalid JSON)`);
    process.exit(1);
  }

  // Concurrency check
  if (checkConcurrency(slug) && !force) {
    console.error('WARNING: state.json modified in last 5s - possible concurrent access');
    console.error('Use --force to override');
    outputError('CONCURRENT_MODIFICATION', 'state.json was modified in the last 5 seconds', {
      hint: 'Use --force to override'
    });
    process.exit(1);
  }

  const now = new Date().toISOString();
  const previous = {
    current_phase: state.current_phase,
    checkpoint_status: state.checkpoint_status
  };

  // Update phase tracking
  const resolvedStatus = status || 'in_progress';
  const resolvedExecutionModel = inferExecutionModel(state, phase);
  if (!state.phases) state.phases = {};
  state.phases[phase] = {
    status: resolvedStatus,
    started_at: state.phases[phase] ? state.phases[phase].started_at : now,
    agent: PHASE_AGENTS[phase] || null,
    ...(resolvedStatus === 'completed' ? { completed_at: now } : {})
  };

  if (!state.metadata || typeof state.metadata !== 'object') {
    state.metadata = {};
  }
  if (!state.epics || typeof state.epics !== 'object') {
    state.epics = {};
  }
  state.execution_model = resolvedExecutionModel;
  state.metadata.execution_model = resolvedExecutionModel;

  const dynamicEpic = parseDynamicEpicPhase(phase);
  if (dynamicEpic) {
    state.phases[phase].agent = 'squad-chief';
    state.current_epic = dynamicEpic.number;
    state.metadata.epic = {
      ...(state.metadata.epic || {}),
      number: dynamicEpic.number,
      ...(state.total_epics !== null && state.total_epics !== undefined ? { total: state.total_epics } : {})
    };
    state.epics[String(dynamicEpic.number)] = {
      ...(state.epics[String(dynamicEpic.number)] || {}),
      number: dynamicEpic.number,
      status: resolvedStatus,
      phase,
      suffix: dynamicEpic.suffix,
      updated_at: now
    };
  }
  state.current_phase = phase;
  state.checkpoint_status = resolvedStatus;
  state.updated_at = now;
  syncWaveAliases(state);

  // Track agent history
  const phaseAgent = dynamicEpic ? 'squad-chief' : PHASE_AGENTS[phase];
  if (phaseAgent && !state.agent_history.includes(phaseAgent)) {
    state.agent_history.push(phaseAgent);
  }

  // Track completed outputs
  if (output && !state.completed_outputs.includes(output)) {
    state.completed_outputs.push(output);
  }

  writeState(slug, state);
  writeActiveSquad(slug);

  outputJson({
    success: true,
    slug,
    previous,
    current: {
      current_phase: phase,
      checkpoint_status: resolvedStatus,
      agent: phaseAgent || null
    }
  });
}

/**
 * Get current state for a squad.
 */
function cmdGet(slug) {
  const resolvedSlug = resolveSlug(slug);
  if (!resolvedSlug) {
    outputError('NO_ACTIVE_SQUAD', 'No slug provided and no active squad pointer found', {
      hint: 'Run: node squad-state-manager.cjs init <slug>'
    });
    process.exit(1);
  }

  const state = readState(resolvedSlug);
  if (!state) {
    outputError('STATE_NOT_FOUND', `No state found for slug: ${resolvedSlug}`);
    process.exit(1);
  }

  if (state.__corrupted) {
    outputError('CORRUPTED_STATE', `state.json for ${resolvedSlug} is corrupted (invalid JSON)`, {
      path: toWorkspaceRelative(getStatePath(resolvedSlug))
    });
    process.exit(1);
  }

  outputJson(state);
}

/**
 * List all squads with optional status filter.
 */
function cmdList(statusFilter) {
  const workflowRoot = getWorkflowRuntimeRoot(DEFAULT_WORKFLOW);
  if (!fs.existsSync(workflowRoot)) {
    outputJson({ squads: [], count: 0, filter: statusFilter || 'all' });
    return;
  }

  const entries = fs.readdirSync(workflowRoot, { withFileTypes: true });
  const squads = [];
  const activeSquad = readActiveSquad();

  for (const entry of entries) {
    if (!entry.isDirectory()) continue;
    if (entry.name.startsWith('.')) continue;

    const slug = entry.name;
    const state = readState(slug);
    if (!state || state.__corrupted) continue;

    const phase = state.current_phase || 'unknown';
    const status = state.checkpoint_status || 'unknown';
    const isActive = (status !== 'completed' && phase !== 'completed');

    // Apply filter
    if (statusFilter === 'active' && !isActive) continue;
    if (statusFilter === 'completed' && isActive) continue;

    squads.push({
      slug,
      display_name: state.display_name || slug,
      execution_model: inferExecutionModel(state),
      current_phase: phase,
      checkpoint_status: status,
      epic_number: state.metadata?.epic?.number || null,
      updated_at: state.updated_at || null,
      is_active_squad: slug === activeSquad,
      agent_history: state.agent_history || []
    });
  }

  // Sort by updated_at descending
  squads.sort((a, b) => {
    if (!a.updated_at) return 1;
    if (!b.updated_at) return -1;
    return new Date(b.updated_at) - new Date(a.updated_at);
  });

  outputJson({ squads, count: squads.length, filter: statusFilter || 'all' });
}

// ═══════════════════════════════════════════════════════════════════════════
// MAIN
// ═══════════════════════════════════════════════════════════════════════════

function parseArg(args, flag) {
  const idx = args.indexOf(flag);
  if (idx === -1 || idx + 1 >= args.length) return null;
  return args[idx + 1];
}

function main() {
  const args = process.argv.slice(2);

  if (args.length === 0 || args[0] === '--help' || args[0] === '-h') {
    console.log(`Squad State Manager - Pipeline state management for squad creation

Usage:
  node squad-state-manager.cjs init <slug> [options]     Initialize new squad
  node squad-state-manager.cjs update [slug] [options]   Update phase/status
  node squad-state-manager.cjs get [slug]                Read current state
  node squad-state-manager.cjs list [options]            List all squads

Init options:
  --name "Display Name"     Squad's display name (default: slug title-cased)
  --source-mind <slug>      Source mind for cloning (optional)
  --target-domain <domain>  Target domain/expertise (optional)
  --execution-model <mode>  legacy | epic
  --prd <path>              PRD path for epic execution
  --epic <number>           Epic number for epic execution
  --epic-title <title>      Epic title for epic execution
  --story <id>              Story identifier for epic execution
  --story-title <title>     Story title for epic execution
  --story-path <path>       Story file path for epic execution
  --total-epics <n>         Total epic count for epic execution
  --squad-type <type>       operational | expert | hybrid
  --scope-type <type>       direct | epic_required
  --workflows-mapped <n>    Scope metric used for gate enforcement
  --agents-needed <n>       Scope metric used for gate enforcement
  --context-entrypoint <id> Canonical workflow/entrypoint identifier

Update options:
  --phase <phase>           Pipeline phase (required)
  --status <status>         Checkpoint status (default: in_progress)
  --output <filename>       Register completed output file
  --force                   Bypass concurrency check

List options:
  --status active|completed|all   Filter by status (default: all)

Valid phases: ${VALID_PHASES.join(', ')}, epic_<N>_init, epic_<N>_planning, epic_<N>_story_ready, epic_<N>_in_progress, epic_<N>_validated, epic_<N>_completed
Valid statuses: ${VALID_STATUSES.join(', ')}

Phase → Agent mapping:
  research, source_validation, dna_extraction, agent_scaffolding → oalanicolas
  task_anatomy, quality_gate → pedro-valerio
  integration, smoke_test, epic_init, story_ready, story_in_progress, epic_validation → squad-chief

Canonical state path: .aiox/squad-runtime/create-squad/{slug}/state.json
Active squad file:    .aiox/squad-runtime/active-squad.json`);
    process.exit(0);
  }

  const command = args[0];
  const force = args.includes('--force');

  if (command === 'init') {
    const slug = args[1] && !args[1].startsWith('-') ? args[1] : null;
    if (!slug) {
      outputError('MISSING_ARG', 'Usage: init <slug> [--name "Name"] [--source-mind <slug>] [--target-domain <domain>]');
      process.exit(1);
    }
    const name = parseArg(args, '--name');
    const sourceMind = parseArg(args, '--source-mind');
    const targetDomain = parseArg(args, '--target-domain');
    const executionModel = parseArg(args, '--execution-model');
    const prdPath = parseArg(args, '--prd');
    const epicNumber = parseArg(args, '--epic');
    const epicTitle = parseArg(args, '--epic-title');
    const storyId = parseArg(args, '--story');
    const storyTitle = parseArg(args, '--story-title');
    const storyPath = parseArg(args, '--story-path');
    const totalEpics = parseArg(args, '--total-epics');
    const squadType = parseArg(args, '--squad-type');
    const scopeType = parseArg(args, '--scope-type');
    const workflowsMapped = parseArg(args, '--workflows-mapped');
    const agentsNeeded = parseArg(args, '--agents-needed');
    const contextEntrypoint = parseArg(args, '--context-entrypoint');
    cmdInit(slug, {
      name,
      sourceMind,
      targetDomain,
      executionModel,
      prdPath,
      epicNumber,
      epicTitle,
      storyId,
      storyTitle,
      storyPath,
      totalEpics,
      squadType,
      scopeType,
      workflowsMapped,
      agentsNeeded,
      contextEntrypoint
    });

  } else if (command === 'update') {
    const slugArg = args[1] && !args[1].startsWith('-') ? args[1] : null;
    const slug = resolveSlug(slugArg);
    if (!slug) {
      outputError('NO_ACTIVE_SQUAD', 'No slug provided and no active squad pointer found');
      process.exit(1);
    }

    const phase = parseArg(args, '--phase');
    if (!phase) {
      outputError('MISSING_ARG', 'Usage: update [slug] --phase <phase> [--status <status>] [--output <file>] [--force]');
      process.exit(1);
    }

    const status = parseArg(args, '--status');
    const output = parseArg(args, '--output');
    cmdUpdate(slug, phase, status, { force, output });

  } else if (command === 'get') {
    const slug = args[1] && !args[1].startsWith('-') ? args[1] : null;
    cmdGet(slug);

  } else if (command === 'list') {
    const statusFilter = parseArg(args, '--status') || 'all';
    cmdList(statusFilter);

  } else {
    outputError('INVALID_COMMAND', `Unknown command: ${command}`, {
      valid_commands: ['init', 'update', 'get', 'list']
    });
    process.exit(1);
  }
}

main();
