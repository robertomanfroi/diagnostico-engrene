#!/usr/bin/env node
/**
 * Squad Context Loader
 * ====================
 * Loads squad pipeline context for agent wrappers.
 * Called as Step 1 in agent wrappers during squad creation.
 *
 * Usage:
 *   node squad-context-loader.cjs <agent_key> [slug]
 *
 * Output: JSON to stdout with pipeline context.
 * Errors: JSON with { "success": false, "error": { "code": "...", "message": "...", "details": {} } }
 *
 * Agent keys: oalanicolas, pedro-valerio, squad-chief
 * Slug detection: CLI arg > active-squad.json > error
 */

const fs = require('fs');
const path = require('path');
const {
  DEFAULT_WORKFLOW,
  getCanonicalStatePath,
  readActiveSquad: readActiveSquadFromRuntime,
  readStateWithLegacyFallback,
  toWorkspaceRelative,
} = require(path.resolve(__dirname, '..', '..', 'squad-creator', 'scripts', 'lib', 'squad-runtime-paths.cjs'));

// ═══════════════════════════════════════════════════════════════════════════
// CONSTANTS
// ═══════════════════════════════════════════════════════════════════════════

const SQUADS_BASE = path.resolve(__dirname, '..', '..'); // squads/

/**
 * Maps agent_key to { persona_name, role, phases, handoff_to }
 * phases: which pipeline phases this agent operates in
 * handoff_to: next agent in pipeline sequence
 */
const AGENT_MAP = {
  oalanicolas: {
    persona_name: 'Alan Nicolas',
    role: 'Mind Cloning Architect',
    phases: ['research', 'source_validation', 'dna_extraction', 'agent_scaffolding'],
    handoff_to: 'pedro-valerio',
    source: 'squads/squad-creator-pro/agents/oalanicolas.md'
  },
  'pedro-valerio': {
    persona_name: 'Pedro Valério',
    role: 'Process Absolutist',
    phases: ['task_anatomy', 'quality_gate'],
    handoff_to: 'squad-chief',
    source: 'squads/squad-creator-pro/agents/pedro-valerio.md'
  },
  'squad-chief': {
    persona_name: 'Squad Chief',
    role: 'Integration Orchestrator',
    phases: ['integration', 'smoke_test', 'epic_init', 'story_ready', 'story_in_progress', 'epic_validation'],
    handoff_to: null,
    source: 'squads/squad-creator/agents/squad-chief.md'
  }
};

// Pipeline order for handoff_from calculation
const PIPELINE_ORDER = ['oalanicolas', 'pedro-valerio', 'squad-chief'];

// ═══════════════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════════════

function outputJson(data) {
  console.log(JSON.stringify(data));
}

function outputError(code, message, details = {}) {
  outputJson({ success: false, error: { code, message, details } });
}

function getStatePath(slug) {
  return getCanonicalStatePath(slug, DEFAULT_WORKFLOW);
}

function resolveSlug(cliSlug) {
  if (cliSlug && !cliSlug.startsWith('-')) return cliSlug;
  return readActiveSquadFromRuntime();
}

function scanCompletedOutputs(slug) {
  const squadDir = path.join(SQUADS_BASE, slug);
  const outputs = [];
  const scanDirs = ['sources', 'agents', 'tasks', 'templates', 'data'];

  for (const dir of scanDirs) {
    const dirPath = path.join(squadDir, dir);
    if (!fs.existsSync(dirPath)) continue;
    try {
      const files = fs.readdirSync(dirPath);
      for (const file of files) {
        if (file.startsWith('.')) continue;
        outputs.push(`${dir}/${file}`);
      }
    } catch {
      // skip unreadable directories
    }
  }
  return outputs;
}

function getHandoffFrom(agentKey) {
  const idx = PIPELINE_ORDER.indexOf(agentKey);
  if (idx <= 0) return null;
  return PIPELINE_ORDER[idx - 1];
}

function getHandoffTo(agentKey) {
  const agent = AGENT_MAP[agentKey];
  return agent ? agent.handoff_to : null;
}

function inferExecutionModel(state) {
  const explicit = state?.execution_model || state?.metadata?.execution_model;
  if (explicit) return explicit;
  return /^epic_/.test(state?.current_phase || '') ? 'epic' : 'legacy';
}

// ═══════════════════════════════════════════════════════════════════════════
// MAIN
// ═══════════════════════════════════════════════════════════════════════════

function main() {
  const args = process.argv.slice(2);

  if (args.length === 0 || args[0] === '--help' || args[0] === '-h') {
    process.stderr.write(`Squad Context Loader

Usage: node squad-context-loader.cjs <agent_key> [slug]

Agent keys: ${Object.keys(AGENT_MAP).join(', ')}

Slug detection: CLI arg > active-squad.json > error
Output: JSON context to stdout
`);
    process.exit(0);
  }

  const agentKey = args[0];
  const cliSlug = args[1];

  // Validate agent key
  if (!AGENT_MAP[agentKey]) {
    outputError('INVALID_AGENT', `Invalid agent key: ${agentKey}`, {
      received: agentKey,
      valid_keys: Object.keys(AGENT_MAP)
    });
    process.exit(1);
  }

  // Resolve slug
  const slug = resolveSlug(cliSlug);
  if (!slug) {
    outputError('NO_ACTIVE_SQUAD', 'No slug provided and no active squad pointer found', {
      hint: 'Run: node squad-state-manager.cjs init <slug>'
    });
    process.exit(1);
  }

  // Read state.json
  const stateLookup = readStateWithLegacyFallback(slug, {
    workflow: DEFAULT_WORKFLOW,
  });
  const statePath = stateLookup.path || getStatePath(slug);
  if (!stateLookup.state) {
    outputError('STATE_NOT_FOUND', `State file not found: ${toWorkspaceRelative(statePath)}`, {
      hint: `Run: node squad-state-manager.cjs init ${slug}`
    });
    process.exit(1);
  }

  const state = stateLookup.state;
  if (state.__corrupted) {
    outputError('CORRUPTED_STATE', `Corrupted state.json for ${slug}`, {
      path: toWorkspaceRelative(statePath),
      hint: 'Delete and re-init.'
    });
    process.exit(1);
  }

  // Build context
  const agent = AGENT_MAP[agentKey];
  const completedOutputs = state.completed_outputs || scanCompletedOutputs(slug);
  const metadata = state.metadata || {};
  const epicMetadata = metadata.epic || null;
  const storyMetadata = metadata.story || null;

  const context = {
    slug: state.slug || slug,
    display_name: state.display_name || slug,
    execution_model: inferExecutionModel(state),
    current_phase: state.current_phase || 'unknown',
    checkpoint_status: state.checkpoint_status || 'unknown',
    output_dir: `squads/${slug}/`,
    state_file: toWorkspaceRelative(getStatePath(slug)),
    state_source: stateLookup.source || 'canonical',
    completed_outputs: completedOutputs,
    agent_history: state.agent_history || [],
    handoff_from: getHandoffFrom(agentKey),
    handoff_to: getHandoffTo(agentKey),
    metadata,
    epic: epicMetadata ? {
      current: epicMetadata.number || null,
      total: epicMetadata.total || null,
      title: epicMetadata.title || null,
      prd_path: metadata.prd_path || null
    } : null,
    story: storyMetadata ? {
      id: storyMetadata.id || null,
      title: storyMetadata.title || null,
      path: storyMetadata.path || null
    } : null,
    squad_type: metadata.squad_type || null,
    agent: {
      key: agentKey,
      persona: agent.persona_name,
      role: agent.role,
      phases: agent.phases,
      source: agent.source
    }
  };

  outputJson(context);
}

main();
