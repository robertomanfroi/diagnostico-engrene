#!/usr/bin/env node
/**
 * Squad Greeting Generator
 *
 * Generates contextual greetings for squad agents (external squads in squads/).
 * Follows the same pattern as generate-greeting.js but for squad-based agents.
 *
 * Features:
 * - Loads agent definition from squads/{squad}/agents/{agent}.md
 * - Loads squad config.yaml for settings
 * - Generates ecosystem report if enabled in settings
 * - Uses GreetingBuilder for contextual greeting
 *
 * Performance Targets:
 * - With cache: <100ms
 * - Without cache: <200ms
 * - Fallback: <20ms
 *
 * Usage:
 *   node generate-squad-greeting.js <squad-name> [agent-name]
 *
 * Examples:
 *   node generate-squad-greeting.js squad-creator
 *   node generate-squad-greeting.js squad-creator squad-chief
 *
 * @module generate-squad-greeting
 * @version 1.1.0
 * @location squads/squad-creator/scripts/
 */

const fs = require('fs').promises;
const path = require('path');
const yaml = require('js-yaml');
const {
  detectEnvironmentContract,
  detectProPack,
} = require('./detect-environment-contract.cjs');
const {
  readActiveSquadRecord,
  readStateWithLegacyFallback,
  resolveRuntimeRoot,
  toWorkspaceRelative,
  writeActiveSquad,
} = require('./lib/squad-runtime-paths.cjs');

// Framework dependencies (from .aiox-core/ — optional, graceful fallback if not present)
let SquadLoader, GreetingBuilder, SessionContextLoader, loadProjectStatus;
try {
  ({ SquadLoader } = require('../../../.aiox-core/development/scripts/squad/squad-loader'));
  GreetingBuilder = require('../../../.aiox-core/development/scripts/greeting-builder');
  SessionContextLoader = require('../../../.aiox-core/scripts/session-context-loader');
  ({ loadProjectStatus } = require('../../../.aiox-core/infrastructure/scripts/project-status-loader'));
} catch {
  // Running standalone (OSS mode) — framework modules not available
  SquadLoader = null;
  GreetingBuilder = null;
  SessionContextLoader = null;
  loadProjectStatus = null;
}

const SQUADS_PATH = './squads';
const REGISTRY_PATH_ENV = 'AIOX_ECOSYSTEM_REGISTRY_PATH';
const DEFAULT_REGISTRY_REL_PATH = path.join('squads', 'sinkra-squad', 'data', 'ecosystem-registry.yaml');
const DEFAULT_TIMEOUT_MS = 5000;
const TIMEOUT_ENV = 'AIOX_SQUAD_GREETING_TIMEOUT_MS';
const TIMEOUT_MS = (() => {
  const raw = process.env[TIMEOUT_ENV];
  if (!raw) {
    return DEFAULT_TIMEOUT_MS;
  }

  const parsed = Number.parseInt(raw, 10);
  return Number.isFinite(parsed) && parsed > 0 ? parsed : DEFAULT_TIMEOUT_MS;
})();

const PRO_COMMAND_OVERRIDES = {
  'plan-squad': 'squads/squad-creator-pro/workflows/wf-plan-squad.yaml',
  'create-squad': 'squads/squad-creator-pro/workflows/wf-context-aware-create-squad.yaml',
  'create-agent': 'squads/squad-creator-pro/workflows/wf-research-then-create-agent.yaml',
  'discover-tools': 'squads/squad-creator-pro/workflows/wf-discover-tools.yaml',
  'upgrade-squad': 'squads/squad-creator-pro/workflows/wf-brownfield-upgrade-squad.yaml',
  'validate-squad': 'squads/squad-creator-pro/workflows/validate-squad.yaml',
  'optimize-yolo': 'squads/squad-creator-pro/workflows/wf-optimize-yolo.yaml',
};
const CREATE_SQUAD_WORKFLOW = 'create-squad';
const PLAN_SQUAD_WORKFLOW = 'plan-squad';
const RUNTIME_TEST_SLUG_PATTERNS = [/^sc_rt_/i];

async function detectProMode() {
  return detectProPack();
}

function isRuntimeTestSlug(slug) {
  return RUNTIME_TEST_SLUG_PATTERNS.some((pattern) => pattern.test(slug || ''));
}

function parseTimestamp(value) {
  if (!value || typeof value !== 'string') {
    return null;
  }

  const parsed = Date.parse(value);
  return Number.isFinite(parsed) ? parsed : null;
}

async function getFileMtimeMs(filePath) {
  try {
    const stat = await fs.stat(filePath);
    return stat.mtimeMs;
  } catch {
    return null;
  }
}

function toIsoTimestamp(rawTimestamp, fallbackMs) {
  const parsed = parseTimestamp(rawTimestamp);
  if (parsed !== null) {
    return new Date(parsed).toISOString();
  }

  if (Number.isFinite(fallbackMs) && fallbackMs > 0) {
    return new Date(fallbackMs).toISOString();
  }

  return null;
}

function inferCreateSquadNextCommand(candidate) {
  const currentEpic = candidate.currentEpic;
  const totalEpics = candidate.totalEpics;
  const checkpointStatus = candidate.checkpointStatus || '';
  const currentPhase = candidate.currentPhase || '';
  const commandUnit = candidate.commandUnit === 'wave' ? 'wave' : 'epic';
  const readyForWaveMatch = /^ready_for_wave_(\d+)$/i.exec(checkpointStatus);
  const readyForEpicMatch = /^ready_for_epic_(\d+)$/i.exec(checkpointStatus);

  if (readyForWaveMatch) {
    return `*create-squad ${candidate.slug} --${commandUnit}=${readyForWaveMatch[1]}`;
  }
  if (readyForEpicMatch) {
    return `*create-squad ${candidate.slug} --${commandUnit}=${readyForEpicMatch[1]}`;
  }

  if (
    candidate.executionModel === 'epic' &&
    currentEpic &&
    totalEpics &&
    currentEpic < totalEpics &&
    /_completed$/i.test(currentPhase)
  ) {
    return `*create-squad ${candidate.slug} --${commandUnit}=${currentEpic + 1}`;
  }

  if (currentPhase === 'completed' || checkpointStatus === 'completed') {
    return `*status ${candidate.slug}`;
  }

  return `*resume ${candidate.slug}`;
}

async function loadCreateSquadRuntimeCandidate(slug) {
  if (!slug || isRuntimeTestSlug(slug)) {
    return null;
  }

  const lookup = readStateWithLegacyFallback(slug, { workflow: CREATE_SQUAD_WORKFLOW });
  const state = lookup.state;
  if (!state || state.__corrupted) {
    return null;
  }

  const metadata = state.metadata || {};
  const runtimeTaxonomy = state.runtime_taxonomy || metadata.runtime_taxonomy || {};
  const updatedMs =
    parseTimestamp(state.updated_at) ??
    parseTimestamp(state.last_updated) ??
    (await getFileMtimeMs(lookup.path)) ??
    0;

  const candidate = {
    slug: state.slug || slug,
    displayName: state.display_name || slug,
    workflow: CREATE_SQUAD_WORKFLOW,
    executionModel:
      state.execution_model ||
      metadata.execution_model ||
      (/^epic_/i.test(state.current_phase || '') ? 'epic' : 'legacy'),
    currentPhase: state.current_phase || 'unknown',
    checkpointStatus: state.checkpoint_status || 'unknown',
    currentEpic: state.current_epic || metadata.epic?.number || null,
    totalEpics: state.total_epics || metadata.epic?.total || null,
    epicTitle: metadata.epic?.title || null,
    storyTitle: metadata.story?.title || null,
    protocolUnit: runtimeTaxonomy.protocol_unit || null,
    progressUnit: runtimeTaxonomy.progress_unit || null,
    commandUnit: runtimeTaxonomy.command_unit || null,
    executionGranularity: runtimeTaxonomy.granularity || null,
    updatedMs,
    updatedAt: toIsoTimestamp(state.updated_at || state.last_updated, updatedMs),
    sourcePath: lookup.path,
    stateSource: lookup.source || 'canonical',
  };

  candidate.nextCommand = inferCreateSquadNextCommand(candidate);
  return candidate;
}

async function loadPlanSquadRuntimeCandidate(slug) {
  if (!slug || isRuntimeTestSlug(slug)) {
    return null;
  }

  const summaryPath = path.join(resolveRuntimeRoot(), PLAN_SQUAD_WORKFLOW, slug, 'planning-summary.yaml');

  try {
    const content = await fs.readFile(summaryPath, 'utf8');
    const summary = yaml.load(content) || {};
    const updatedMs = parseTimestamp(summary?.planning?.created) ?? (await getFileMtimeMs(summaryPath)) ?? 0;

    return {
      slug: summary?.squad?.name || summary?.plan_squad?.domain || slug,
      displayName: summary?.squad?.name || slug,
      workflow: PLAN_SQUAD_WORKFLOW,
      executionModel: summary?.epic_roadmap?.execution_mode || 'planning',
      currentPhase: summary?.planning?.prd_status || summary?.squad?.status || 'unknown',
      checkpointStatus: summary?.plan_squad?.handoff_ready ? 'handoff_ready' : 'in_progress',
      currentEpic: null,
      totalEpics: summary?.architecture?.total_epics || summary?.plan_squad?.epics_planned || null,
      epicTitle: null,
      storyTitle: null,
      updatedMs,
      updatedAt: toIsoTimestamp(summary?.planning?.created, updatedMs),
      sourcePath: summaryPath,
      stateSource: 'canonical',
      nextCommand: summary?.handoff?.next_command || `*create-squad ${slug}`,
    };
  } catch (error) {
    if (error.code === 'ENOENT') {
      return null;
    }

    throw error;
  }
}

async function collectWorkflowRuntimeCandidates(workflow) {
  const runtimeRoot = path.join(resolveRuntimeRoot(), workflow);

  try {
    const entries = await fs.readdir(runtimeRoot, { withFileTypes: true });
    const slugs = entries
      .filter((entry) => entry.isDirectory())
      .map((entry) => entry.name)
      .filter((slug) => !isRuntimeTestSlug(slug));

    const candidates = await Promise.all(
      slugs.map((slug) =>
        workflow === CREATE_SQUAD_WORKFLOW
          ? loadCreateSquadRuntimeCandidate(slug)
          : loadPlanSquadRuntimeCandidate(slug),
      ),
    );

    return candidates
      .filter(Boolean)
      .sort((left, right) => (right.updatedMs || 0) - (left.updatedMs || 0));
  } catch (error) {
    if (error.code === 'ENOENT') {
      return [];
    }

    throw error;
  }
}

function findCandidateByRecord(candidates, record) {
  if (!record?.slug) {
    return null;
  }

  const workflow = record.workflow || CREATE_SQUAD_WORKFLOW;
  return candidates.find((candidate) => candidate.slug === record.slug && candidate.workflow === workflow) || null;
}

function shouldReconcileActivePointer(activeRecord, activeCreateCandidate, latestCreateCandidate) {
  if (!latestCreateCandidate) {
    return false;
  }

  if (!activeRecord || !activeCreateCandidate) {
    return true;
  }

  if ((activeRecord.workflow || CREATE_SQUAD_WORKFLOW) !== CREATE_SQUAD_WORKFLOW) {
    return true;
  }

  return (
    activeRecord.slug !== latestCreateCandidate.slug &&
    (latestCreateCandidate.updatedMs || 0) > (activeCreateCandidate.updatedMs || 0)
  );
}

async function loadSquadCreatorRuntimeSummary() {
  const activeRecord = readActiveSquadRecord();
  const [createSquadCandidates, planSquadCandidates] = await Promise.all([
    collectWorkflowRuntimeCandidates(CREATE_SQUAD_WORKFLOW),
    collectWorkflowRuntimeCandidates(PLAN_SQUAD_WORKFLOW),
  ]);

  const activeCreateCandidate = findCandidateByRecord(createSquadCandidates, {
    slug: activeRecord?.slug,
    workflow: CREATE_SQUAD_WORKFLOW,
  });
  const latestCreateCandidate = createSquadCandidates[0] || null;

  let pointerReconciled = null;
  if (shouldReconcileActivePointer(activeRecord, activeCreateCandidate, latestCreateCandidate)) {
    writeActiveSquad(latestCreateCandidate.slug, CREATE_SQUAD_WORKFLOW, {
      source: 'generate-squad-greeting',
      previous_slug: activeRecord?.slug || null,
      previous_workflow: activeRecord?.workflow || null,
    });
    pointerReconciled = {
      previousSlug: activeRecord?.slug || null,
      previousWorkflow: activeRecord?.workflow || null,
      nextSlug: latestCreateCandidate.slug,
      nextWorkflow: CREATE_SQUAD_WORKFLOW,
    };
  }

  const effectiveActiveRecord = pointerReconciled
    ? {
        slug: pointerReconciled.nextSlug,
        workflow: pointerReconciled.nextWorkflow,
      }
    : activeRecord;

  const allCandidates = [...createSquadCandidates, ...planSquadCandidates];
  if (allCandidates.length === 0) {
    return null;
  }

  const activeCandidate = findCandidateByRecord(allCandidates, effectiveActiveRecord);
  const latestCandidate = allCandidates[0];
  const selectedCandidate =
    activeCandidate && (activeCandidate.updatedMs || 0) >= (latestCandidate.updatedMs || 0)
      ? activeCandidate
      : latestCandidate;

  return {
    activeRecord: effectiveActiveRecord || null,
    activeCandidate,
    latestCandidate,
    selectedCandidate,
    pointerReconciled,
  };
}

function buildSquadCreatorRuntimeSection(summary) {
  const candidate = summary?.selectedCandidate;
  if (!candidate) {
    return '';
  }

  const lines = ['**Resume Context:**'];
  lines.push(`- Squad: \`${candidate.slug}\``);
  lines.push(`- Workflow: \`${candidate.workflow}\``);

  if (candidate.currentEpic && candidate.totalEpics) {
    const progressUnit =
      candidate.progressUnit ||
      candidate.commandUnit ||
      candidate.protocolUnit ||
      (candidate.executionModel === 'epic' ? 'epic' : 'step');
    const epicSuffix = candidate.epicTitle ? ` - ${candidate.epicTitle}` : '';
    lines.push(`- Progress: \`${progressUnit} ${candidate.currentEpic}/${candidate.totalEpics}\`${epicSuffix}`);
  }

  if (candidate.commandUnit) {
    lines.push(`- Command Unit: \`${candidate.commandUnit}\``);
  }

  if (candidate.protocolUnit && candidate.commandUnit && candidate.protocolUnit !== candidate.commandUnit) {
    lines.push(`- Compatibility: \`${candidate.protocolUnit}\``);
  }

  if (candidate.executionGranularity) {
    lines.push(`- Granularity: \`${candidate.executionGranularity}\``);
  }

  lines.push(`- Phase: \`${candidate.currentPhase}\``);
  lines.push(`- Status: \`${candidate.checkpointStatus}\``);

  if (candidate.storyTitle) {
    lines.push(`- Story: ${candidate.storyTitle}`);
  }

  if (candidate.updatedAt) {
    lines.push(`- Updated: \`${candidate.updatedAt}\``);
  }

  if (candidate.nextCommand) {
    lines.push(`- Next: \`${candidate.nextCommand}\``);
  }

  if (summary.pointerReconciled) {
    const previousSlug = summary.pointerReconciled.previousSlug || 'none';
    const previousWorkflow = summary.pointerReconciled.previousWorkflow || CREATE_SQUAD_WORKFLOW;
    lines.push(
      `- Pointer: auto-healed from \`${previousWorkflow}:${previousSlug}\` to \`${candidate.workflow}:${candidate.slug}\``,
    );
  }

  if (candidate.sourcePath) {
    lines.push(`- Runtime File: \`${toWorkspaceRelative(candidate.sourcePath)}\``);
  }

  return lines.join('\n');
}

function buildSquadCreatorNextActionCallout(summary) {
  const candidate = summary?.selectedCandidate;
  if (!candidate?.nextCommand) {
    return '';
  }

  return `**Next Action:** \`${candidate.nextCommand}\``;
}

/**
 * Format runtime directives block for LLM consumption.
 * This is the single source of truth for greeting runtime state.
 *
 * @param {{pro_mode: boolean, version?: string, missing?: string[], error?: string, access_tier?: string, runtime_mode?: string, source_of_truth?: string, reason?: string, evidence_paths?: string[]}} detection
 * @returns {string}
 */
function formatRuntimeDirectives(detection) {
  const lines = ['<!-- SQUAD_RUNTIME_DIRECTIVES'];

  if (detection.access_tier) {
    lines.push(`access_tier: ${detection.access_tier}`);
  }
  if (detection.runtime_mode) {
    lines.push(`runtime_mode: ${detection.runtime_mode}`);
  }
  if (detection.source_of_truth) {
    lines.push(`source_of_truth: ${detection.source_of_truth}`);
  }
  if (typeof detection.reason === 'string') {
    lines.push(`reason: ${JSON.stringify(detection.reason)}`);
  }
  if (Array.isArray(detection.evidence_paths) && detection.evidence_paths.length > 0) {
    lines.push('evidence_paths:');
    for (const evidencePath of detection.evidence_paths) {
      lines.push(`  - ${evidencePath}`);
    }
  } else {
    lines.push('evidence_paths: []');
  }

  lines.push(`pro_mode: ${detection.pro_mode}`);

  if (detection.pro_mode) {
    lines.push(`pro_version: ${detection.version}`);
    lines.push('command_overrides:');
    for (const [cmd, wfPath] of Object.entries(PRO_COMMAND_OVERRIDES)) {
      lines.push(`  ${cmd}: ${wfPath}`);
    }
    lines.push('pro_specialists: oalanicolas, pedro-valerio, thiago_finch');
    lines.push('override_mechanism: >');
    lines.push('  For ANY command: 1) check command_overrides map, 2) check squads/squad-creator-pro/tasks/{task}.md,');
    lines.push('  3) fallback to squads/squad-creator/tasks/{task}.md');
  } else if (detection.missing) {
    lines.push(`warning: Pro config found but installation incomplete (missing: ${detection.missing.join(', ')})`);
  } else if (detection.error) {
    lines.push(`warning: ${detection.error}`);
  }

  lines.push('-->');
  return lines.join('\n');
}

function hasStructuredCommandsSection(greeting) {
  return /\*\*(Available Commands|Quick Commands|Key Commands|Commands):\*\*/.test(greeting);
}

function normalizeCommandName(command) {
  return command.trim().replace(/^\*+/, '').split(/\s+/)[0];
}

function parseCommandEntry(entry) {
  if (typeof entry === 'string') {
    const trimmed = entry.trim();
    const separatorIndex = trimmed.indexOf(' - ');
    const name = separatorIndex === -1 ? trimmed : trimmed.slice(0, separatorIndex);
    const description = separatorIndex === -1 ? '' : trimmed.slice(separatorIndex + 3);
    return {
      rawName: name,
      name: normalizeCommandName(name),
      displayName: name.startsWith('*') ? name : `*${name}`,
      description,
    };
  }

  if (entry && typeof entry === 'object') {
    const rawName = entry.name || entry.command || '';
    const normalized = normalizeCommandName(rawName);
    return {
      rawName,
      name: normalized,
      displayName: rawName.startsWith('*') ? rawName : `*${rawName}`,
      description: entry.description || '',
    };
  }

  return null;
}

function buildBaseCommandsSection(agentDef) {
  const parsedCommands = (agentDef.commands || [])
    .map(parseCommandEntry)
    .filter(Boolean);

  if (parsedCommands.length === 0) {
    return '';
  }

  const commandsByName = new Map(parsedCommands.map((command) => [command.name, command]));
  const preferredCommands = agentDef.command_visibility?.quick_commands || agentDef.command_visibility?.key_commands || [];
  const orderedCommands = [];

  for (const preferred of preferredCommands) {
    const normalized = normalizeCommandName(preferred);
    const command = commandsByName.get(normalized);
    if (command) {
      orderedCommands.push(command);
      commandsByName.delete(normalized);
    }
  }

  for (const command of parsedCommands) {
    if (commandsByName.has(command.name)) {
      orderedCommands.push(command);
      commandsByName.delete(command.name);
    }
  }

  const lines = ['**Quick Commands:**'];

  for (const command of orderedCommands.slice(0, 8)) {
    if (command.description) {
      lines.push(`- \`${command.displayName}\` — ${command.description}`);
    } else {
      lines.push(`- \`${command.displayName}\``);
    }
  }

  return lines.join('\n');
}

function resolveRegistryPath() {
  const configuredPath = process.env[REGISTRY_PATH_ENV];
  if (configuredPath && configuredPath.trim().length > 0) {
    return path.isAbsolute(configuredPath)
      ? configuredPath
      : path.join(process.cwd(), configuredPath);
  }
  return path.join(process.cwd(), DEFAULT_REGISTRY_REL_PATH);
}

/**
 * Load agent definition from squad
 *
 * @param {string} squadName - Squad directory name
 * @param {string} agentName - Agent file name (without .md)
 * @returns {Promise<Object>} Parsed agent definition
 */
async function loadSquadAgent(squadName, agentName) {
  const agentPath = path.join(process.cwd(), SQUADS_PATH, squadName, 'agents', `${agentName}.md`);

  try {
    const content = await fs.readFile(agentPath, 'utf8');

    // Extract YAML block
    const yamlMatch = content.match(/```ya?ml\n([\s\S]*?)\n```/);
    if (!yamlMatch) {
      throw new Error(`No YAML block found in ${agentName}.md`);
    }

    const agentDef = yaml.load(yamlMatch[1]);

    // Validate required fields
    if (!agentDef.agent || !agentDef.agent.id) {
      throw new Error('Invalid agent definition: missing agent.id');
    }

    // Normalize with defaults
    return normalizeAgentDefinition(agentDef);
  } catch (error) {
    if (error.code === 'ENOENT') {
      throw new Error(`Agent file not found: ${agentPath}`);
    }
    throw error;
  }
}

/**
 * Normalize agent definition with defaults
 *
 * @param {Object} agentDef - Raw agent definition
 * @returns {Object} Normalized definition
 */
function normalizeAgentDefinition(agentDef) {
  const agent = agentDef.agent;

  // Ensure required fields
  agent.id = agent.id || 'unknown';
  agent.name = agent.name || agent.id;
  agent.icon = agent.icon || '🤖';

  // Ensure persona_profile with greeting_levels
  if (!agentDef.persona_profile) {
    agentDef.persona_profile = {
      greeting_levels: {
        minimal: `${agent.icon} ${agent.id} ready`,
        named: `${agent.icon} ${agent.name} ready`,
        archetypal: `${agent.icon} ${agent.name} ready`,
      },
    };
  } else if (!agentDef.persona_profile.greeting_levels) {
    agentDef.persona_profile.greeting_levels = {
      minimal: `${agent.icon} ${agent.id} ready`,
      named: `${agent.icon} ${agent.name} ready`,
      archetypal: `${agent.icon} ${agent.name} ready`,
    };
  }

  // Ensure commands array
  if (!agentDef.commands || !Array.isArray(agentDef.commands)) {
    agentDef.commands = [];
  } else {
    // GreetingBuilder always prefixes commands with "*".
    // Strip leading "*" here to avoid rendering "**help".
    agentDef.commands = agentDef.commands.map((cmd) => {
      if (typeof cmd === 'string') {
        return cmd.replace(/^\*+/, '');
      }
      if (cmd && typeof cmd === 'object') {
        const out = { ...cmd };
        if (typeof out.name === 'string') {
          out.name = out.name.replace(/^\*+/, '');
        }
        if (typeof out.command === 'string') {
          out.command = out.command.replace(/^\*+/, '');
        }
        return out;
      }
      return cmd;
    });
  }

  return agentDef;
}

/**
 * Load squad config.yaml
 *
 * @param {string} squadName - Squad directory name
 * @returns {Promise<Object>} Squad configuration
 */
async function loadSquadConfig(squadName) {
  const loader = new SquadLoader({ squadsPath: SQUADS_PATH });

  try {
    const { manifestPath } = await loader.resolve(squadName);
    const content = await fs.readFile(manifestPath, 'utf8');
    return yaml.load(content);
  } catch (error) {
    console.warn(`[generate-squad-greeting] Failed to load config: ${error.message}`);
    return { settings: { activation: {} } };
  }
}

/**
 * Load ecosystem registry data
 *
 * @returns {Promise<Object>} Registry data
 */
async function loadSquadRegistry() {
  const registryPath = resolveRegistryPath();

  try {
    const content = await fs.readFile(registryPath, 'utf8');
    return yaml.load(content);
  } catch (error) {
    if (error.code !== 'ENOENT') {
      console.warn(
        `[generate-squad-greeting] Failed to load ecosystem registry (${registryPath}): ${error.message}`
      );
    }
    return null;
  }
}

/**
 * Get ecosystem counts from registry
 *
 * @param {Object} registry - Squad registry data
 * @returns {Object} Asset counts
 */
function getEcosystemCounts(registry) {
  if (!registry) {
    return {
      squadCount: 0,
      agentCount: 0,
      taskCount: 0,
      templateCount: 0,
      checklistCount: 0,
      workflowCount: 0,
    };
  }

  // Support both legacy format (registry.metadata/summary) and
  // canonical ecosystem-registry.yaml format (registry.registry + squads[]).
  const summary = registry.summary || {};
  const meta = registry.metadata || {};
  const registryBlock = registry.registry || {};
  const squadsArray = Array.isArray(registry.squads) ? registry.squads : [];

  const squadCount = meta.total_squads || registryBlock.total_squads || squadsArray.length || 0;

  // If summary exists (legacy *refresh-registry output), use it.
  // Otherwise, aggregate from squads[] entries.
  let agentCount = summary.total_agents || 0;
  let taskCount = summary.total_tasks || 0;
  let templateCount = summary.total_templates || 0;
  let checklistCount = summary.total_checklists || 0;
  let workflowCount = summary.total_workflows || 0;

  if (!agentCount && squadsArray.length > 0) {
    agentCount = squadsArray.reduce((sum, s) => sum + (s.agents || 0), 0);
  }
  if (!taskCount && squadsArray.length > 0) {
    taskCount = squadsArray.reduce((sum, s) => sum + (s.tasks || 0), 0);
  }
  if (!templateCount && squadsArray.length > 0) {
    templateCount = squadsArray.reduce((sum, s) => sum + (s.templates || 0), 0);
  }
  if (!checklistCount && squadsArray.length > 0) {
    checklistCount = squadsArray.reduce((sum, s) => sum + (s.checklists || 0), 0);
  }
  if (!workflowCount && squadsArray.length > 0) {
    workflowCount = squadsArray.reduce((sum, s) => sum + (s.workflows || 0), 0);
  }

  return { squadCount, agentCount, taskCount, templateCount, checklistCount, workflowCount };
}

/**
 * Get top squads from registry
 *
 * @param {Object} registry - Squad registry data
 * @param {number} limit - Max squads to return
 * @returns {Array} Top squads with counts
 */
function getTopSquads(registry, limit = 5) {
  if (!registry || !registry.squads) {
    return [];
  }

  // Support both array format (canonical ecosystem-registry) and object format (legacy).
  const entries = Array.isArray(registry.squads)
    ? registry.squads.map((s) => ({
        name: s.name || 'unknown',
        agents: s.agents || 0,
        domain: s.bu_mapping || '',
        purpose: (s.capabilities?.[0] || '').substring(0, 35),
        isQualityRef: s.quality_reference || false,
      }))
    : Object.entries(registry.squads).map(([name, data]) => ({
        name,
        agents: data.counts?.agents || data.agents || 0,
        domain: data.domain || data.bu_mapping || '',
        purpose: (data.purpose || data.capabilities?.[0] || '').substring(0, 35),
        isQualityRef: data.quality_reference || false,
      }));

  return entries
    .sort((a, b) => b.agents - a.agents)
    .slice(0, limit);
}

/**
 * Generate ecosystem report from registry
 *
 * @param {Object} settings - Ecosystem report settings
 * @returns {Promise<string>} Formatted report
 */
async function generateEcosystemReport(settings = {}) {
  const registry = await loadSquadRegistry();
  const counts = getEcosystemCounts(registry);

  let report = `## 📊 AIOX Squad Ecosystem

**${counts.squadCount} Squads** | **${counts.agentCount} Agents** | **${counts.taskCount} Tasks** | **${counts.checklistCount} Checklists** | **${counts.workflowCount} Workflows**`;

  if (settings.show_top_squads !== false) {
    const topSquads = getTopSquads(registry, settings.top_squads_limit || 5);

    if (topSquads.length > 0) {
      report += `

### Top Squads
| Squad | Agents | Domain |
|-------|--------|--------|`;

      for (const squad of topSquads) {
        const marker = squad.isQualityRef ? ' ⭐' : '';
        report += `
| ${squad.name}${marker} | ${squad.agents} | ${squad.domain} |`;
      }
    }
  }

  // Show quality references if enabled
  if (settings.show_quality_refs !== false && registry?.quality_references) {
    report += `

### Quality References`;
    for (const ref of registry.quality_references.slice(0, 3)) {
      report += `
- **${ref.squad}**: ${ref.reason}`;
    }
  }

  // Show gaps if enabled
  if (settings.show_gaps && registry?.gaps) {
    const highPriorityGaps = registry.gaps.filter(g => g.priority === 'high');
    if (highPriorityGaps.length > 0) {
      report += `

### Domain Gaps (High Priority)`;
      for (const gap of highPriorityGaps.slice(0, 3)) {
        report += `
- **${gap.domain}**: ${gap.potential_minds?.slice(0, 2).join(', ') || 'needs research'}`;
      }
    }
  }

  return report;
}

/**
 * Load session context
 *
 * @param {string} agentId - Agent ID
 * @returns {Promise<Object>} Session context
 */
async function loadSessionContext(agentId) {
  try {
    const loader = new SessionContextLoader();
    return await loader.loadContext(agentId);
  } catch (error) {
    console.warn(`[generate-squad-greeting] Session context failed: ${error.message}`);
    return {
      sessionType: 'new',
      message: null,
      previousAgent: null,
      lastCommands: [],
      workflowActive: null,
    };
  }
}

/**
 * Generate greeting for squad agent
 *
 * @param {string} squadName - Squad directory name
 * @param {string} [agentName] - Agent name (defaults to main orchestrator)
 * @returns {Promise<string>} Formatted greeting
 */
async function generateSquadGreeting(squadName, agentName) {
  const startTime = Date.now();

  try {
    // Load squad config
    const config = await loadSquadConfig(squadName);
    const settings = config.settings || {};
    const activationSettings = settings.activation || {};

    // Determine agent name (default to squad-chief or first agent)
    if (!agentName) {
      agentName = 'squad-chief'; // Default orchestrator
    }

    // Load agent definition
    const agentDef = await loadSquadAgent(squadName, agentName);

    // Deterministic pro detection (filesystem check, not LLM-driven)
    const environmentContract = await detectEnvironmentContract({ squad: squadName });
    const proDetection = {
      ...await detectProMode(),
      access_tier: environmentContract.access_tier,
      runtime_mode: environmentContract.runtime_mode,
      source_of_truth: environmentContract.source_of_truth,
      reason: environmentContract.reason,
      evidence_paths: environmentContract.evidence_paths,
    };

    // Build greeting parts
    const parts = [];

    // 0. Runtime directives (authoritative pro_mode state for LLM)
    parts.push(formatRuntimeDirectives(proDetection));

    // 1. Ecosystem report (if enabled)
    if (activationSettings.show_ecosystem_report) {
      const ecosystemSettings = settings.ecosystem_report || {};
      const report = await generateEcosystemReport(ecosystemSettings);
      parts.push(report);
    }

    // 2. Load context for greeting builder
    const shouldLoadRuntimeSummary = squadName === 'squad-creator' && agentName === 'squad-chief';
    const [sessionContext, projectStatus, runtimeSummary] = await Promise.all([
      loadSessionContext(agentDef.agent.id),
      loadProjectStatus ? loadProjectStatus().catch(() => null) : Promise.resolve(null),
      shouldLoadRuntimeSummary
        ? loadSquadCreatorRuntimeSummary().catch((error) => {
            console.warn(`[generate-squad-greeting] Runtime summary failed: ${error.message}`);
            return null;
          })
        : Promise.resolve(null),
    ]);

    const context = {
      conversationHistory: [],
      sessionType: sessionContext.sessionType,
      projectStatus: projectStatus,
      lastCommands: sessionContext.lastCommands || [],
      previousAgent: sessionContext.previousAgent,
      sessionMessage: sessionContext.message,
      workflowActive: sessionContext.workflowActive,
    };

    // 3. Build greeting using GreetingBuilder
    //    If pro mode, augment agent commands with pro-specific commands
    const agentWithPersona = {
      ...agentDef.agent,
      persona_profile: agentDef.persona_profile,
      persona: agentDef.persona,
      commands: agentDef.commands || [],
    };

    const builder = new GreetingBuilder();
    const greeting = await builder.buildGreeting(agentWithPersona, context);

    const runtimeSection = buildSquadCreatorRuntimeSection(runtimeSummary);
    const runtimeNextActionCallout = buildSquadCreatorNextActionCallout(runtimeSummary);

    if (runtimeSection) {
      parts.push(runtimeSection);
    }

    if (proDetection.pro_mode) {
      // Post-process greeting for pro mode:
      // 1. Inject "PRO" badge into the presentation line
      // 2. Replace truncated commands section with full pro commands list
      let proGreeting = greeting.replace(
        / ready/,
        ' **PRO** (v' + proDetection.version + ') ready',
      );

      const proCommandsSection = buildProCommandsSection(proDetection);
      const cmdStart = proGreeting.indexOf('**Available Commands:**');
      const cmdAlt = cmdStart === -1 ? proGreeting.indexOf('**Quick Commands:**') : cmdStart;
      const cmdAlt2 = cmdAlt === -1 ? proGreeting.indexOf('**Key Commands:**') : cmdAlt;
      const cmdAlt3 = cmdAlt2 === -1 ? proGreeting.indexOf('**Commands:**') : cmdAlt2;

      if (cmdAlt3 !== -1) {
        const footerMarker = proGreeting.indexOf('\nType ', cmdAlt3);
        const endIdx = footerMarker !== -1 ? footerMarker : proGreeting.length;
        const before = proGreeting.substring(0, cmdAlt3);
        const after = proGreeting.substring(endIdx);
        parts.push(before + proCommandsSection + after);
      } else {
        parts.push(proGreeting + '\n\n' + proCommandsSection);
      }
    } else {
      const baseCommandsSection = hasStructuredCommandsSection(greeting)
        ? greeting
        : `${greeting}\n\n${buildBaseCommandsSection(agentDef)}`;
      parts.push(baseCommandsSection);
    }

    if (runtimeNextActionCallout) {
      parts.push(runtimeNextActionCallout);
    }

    const duration = Date.now() - startTime;
    if (duration > 150) {
      console.warn(`[generate-squad-greeting] Slow generation: ${duration}ms`);
    }

    return parts.join('\n\n');
  } catch (error) {
    console.error('[generate-squad-greeting] Error:', {
      squadName,
      agentName,
      error: error.message,
      stack: error.stack,
    });

    // Fallback greeting
    return generateFallbackGreeting(squadName, agentName);
  }
}

/**
 * Build complete pro commands section to replace the GreetingBuilder's truncated version.
 * Shows all base + pro commands organized by category, with [PRO] tags on pro-exclusive commands.
 *
 * @param {{version: string}} detection - Pro detection result
 * @returns {string} Formatted commands section
 */
function buildProCommandsSection(detection) {
  const v = detection?.version || '?';
  return `**AIOX Pro v${v} ativado** — Mind cloning, DNA extraction, optimization, quality gates, specialist delegation

**Commands:**

  **Creation**
   - \`*plan-squad\` — Create deep planning PRD before execution
   - \`*create-squad\` — Create squad (direct for small scopes, epic mode for PRD-backed scopes)
   - \`*create-agent\` — Create agent (Pro: deep research before creation)
   - \`*create-workflow\` — Create multi-phase workflow
   - \`*create-task\` — Create atomic task
   - \`*create-template\` — Create output template
   - \`*create-pipeline\` — Generate pipeline code scaffolding
   - \`*create-squad-smart\` — Create squad with context detection (greenfield/resume routing)
   - \`*brownfield-upgrade\` — Upgrade existing squad with safe brownfield workflow
   - \`*create-from-sop {business}\` — Load canonical workspace SOPs and derive squad creation inputs

  **Mind Cloning (Pro Only)**
   - \`*clone-mind\` — Clone expert mind (Voice DNA + Thinking DNA)
   - \`*extract-voice-dna\` — Extract communication style from expert sources
   - \`*extract-thinking-dna\` — Extract frameworks, heuristics, decision patterns
   - \`*update-mind\` — Update existing mind DNA with new sources
   - \`*auto-acquire-sources\` — Auto-acquire sources (YouTube, podcasts, articles)
   - \`*extraction-pipeline\` — Full pipeline: collect > extract > validate
   - \`*review-extraction\` — Review specialist output before the next phase
   - \`*review-artifacts\` — Review specialist output before finalizing

  **Optimization & Quality (Pro Only)**
   - \`*optimize\` — Optimize squad/task (Worker vs Agent) + token savings
   - \`*optimize-yolo\` — One-gate optimize flow that runs autonomously after approval
   - \`*optimize-workflow\` — Optimize workflow across 6 dimensions
   - \`*quality-dashboard\` — Quality metrics dashboard
   - \`*squad-fusion\` — Merge multiple squads into one

  **Analysis & Validation**
   - \`*discover-tools {domain}\` — Internal-first tool discovery (Pro: extended sources)
   - \`*upgrade-squad {name}\` — Upgrade squad to current standards (Pro: brownfield workflow)
   - \`*validate-squad {name}\` — Validate entire squad (Pro: axioma assessment)
   - \`*validate-final-artifacts {name}\` — Validate final deliverables

  **Utility**
   - \`*status\` — Show current native create-squad runtime state
   - \`*resume\` — Continue interrupted native create-squad flow
   - \`*help\` — Show all commands
   - \`*guide\` — Interactive onboarding guide
   - \`*refresh-registry\` — Update ecosystem registry
   - \`*squad-analytics\` — Analytics dashboard

  **Pro Specialists:** @oalanicolas (Mind Cloning) · @pedro-valerio (Quality & Optimization) · @thiago_finch (Strategy)`;
}

/**
 * Generate fallback greeting
 *
 * @param {string} squadName - Squad name
 * @param {string} agentName - Agent name
 * @returns {string} Simple fallback greeting
 */
function generateFallbackGreeting(squadName, agentName) {
  const displayName = agentName || squadName;
  return `🎨 ${displayName} ready

Type \`*help\` to see available commands.`;
}

function isGreetingTimeoutError(error) {
  return error instanceof Error && error.message === 'Greeting timeout';
}

// CLI interface
if (require.main === module) {
  const squadName = process.argv[2];
  const agentName = process.argv[3];

  if (!squadName) {
    console.error('Usage: node generate-squad-greeting.js <squad-name> [agent-name]');
    console.error('\nExamples:');
    console.error('  node generate-squad-greeting.js squad-creator');
    console.error('  node generate-squad-greeting.js squad-creator squad-chief');
    process.exit(1);
  }

  // Execute with timeout protection
  const timeoutPromise = new Promise((_, reject) =>
    setTimeout(() => reject(new Error('Greeting timeout')), TIMEOUT_MS),
  );

  Promise.race([generateSquadGreeting(squadName, agentName), timeoutPromise])
    .then(greeting => {
      console.log(greeting);
      process.exit(0);
    })
    .catch(error => {
      if (isGreetingTimeoutError(error)) {
        console.log(generateFallbackGreeting(squadName, agentName));
        process.exit(0);
      }

      console.error('Error:', error.message);
      console.log(generateFallbackGreeting(squadName, agentName));
      process.exit(1);
    });
}

module.exports = {
  buildBaseCommandsSection,
  buildSquadCreatorNextActionCallout,
  buildSquadCreatorRuntimeSection,
  detectEnvironmentContract,
  generateSquadGreeting,
  detectProMode,
  formatRuntimeDirectives,
  loadCreateSquadRuntimeCandidate,
  loadPlanSquadRuntimeCandidate,
  loadSquadCreatorRuntimeSummary,
  hasStructuredCommandsSection,
  loadSquadAgent,
  loadSquadConfig,
  generateEcosystemReport,
  loadSquadRegistry,
  getEcosystemCounts,
  getTopSquads,
};
