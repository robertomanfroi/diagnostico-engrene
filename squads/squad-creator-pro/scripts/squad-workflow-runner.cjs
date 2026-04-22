#!/usr/bin/env node
/**
 * Squad Workflow Runner
 * =====================
 * Orchestrates squad creation runtime for both legacy linear flow and
 * epic-aware native flow used by large PRD-backed squads.
 *
 * Usage:
 *   node squad-workflow-runner.cjs start <slug> [--name "Name"] [--prd <path>] [--wave <N>|--epic <N>]
 *   node squad-workflow-runner.cjs resume [slug]
 *   node squad-workflow-runner.cjs next [slug] [--force]
 *   node squad-workflow-runner.cjs status [slug]
 *   node squad-workflow-runner.cjs approve [slug]
 *   node squad-workflow-runner.cjs revise [slug] --to <phase>
 *   node squad-workflow-runner.cjs abort [slug]
 */

const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');
const {
  readActiveSquad: readActiveSquadFromRuntime,
  toWorkspaceRelative,
} = require(path.resolve(__dirname, '..', '..', 'squad-creator', 'scripts', 'lib', 'squad-runtime-paths.cjs'));

const SCRIPTS_DIR = __dirname;
const ROOT = path.resolve(__dirname, '..', '..', '..');
const NODE_BIN = process.execPath;
const STATE_MANAGER = path.join(SCRIPTS_DIR, 'squad-state-manager.cjs');
const WAVE_LOOP = path.join(SCRIPTS_DIR, 'wave-loop.cjs');

const SCOPE_GATE = {
  workflowsRequirePrd: 10,
  agentsRequirePrd: 8,
};

const LEGACY_PIPELINE_PHASES = [
  { id: 'init', agent: null, human_checkpoint: false },
  { id: 'research', agent: 'oalanicolas', human_checkpoint: false },
  { id: 'source_validation', agent: 'oalanicolas', human_checkpoint: false },
  { id: 'dna_extraction', agent: 'oalanicolas', human_checkpoint: false },
  { id: 'agent_scaffolding', agent: 'oalanicolas', human_checkpoint: false },
  { id: 'task_anatomy', agent: 'pedro-valerio', human_checkpoint: false },
  { id: 'quality_gate', agent: 'pedro-valerio', human_checkpoint: true },
  { id: 'integration', agent: 'squad-chief', human_checkpoint: false },
  { id: 'smoke_test', agent: 'squad-chief', human_checkpoint: false },
  { id: 'completed', agent: null, human_checkpoint: false }
];

const EPIC_PIPELINE_PHASES = [
  { id: 'init', agent: null, human_checkpoint: false },
  { id: 'epic_init', agent: 'squad-chief', human_checkpoint: false },
  { id: 'story_ready', agent: 'squad-chief', human_checkpoint: false },
  { id: 'story_in_progress', agent: 'squad-chief', human_checkpoint: false },
  { id: 'epic_validation', agent: 'squad-chief', human_checkpoint: false },
  { id: 'completed', agent: null, human_checkpoint: false }
];

const EPIC_PHASE_IDS = new Set(EPIC_PIPELINE_PHASES.map(phase => phase.id));

function outputJson(data) {
  console.log(JSON.stringify(data, null, 2));
}

function outputError(code, message, details = {}) {
  outputJson({ success: false, error: { code, message, details } });
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

function slugToDisplayName(slug) {
  return slug
    .split(/[-_]/)
    .filter(Boolean)
    .map(part => part.charAt(0).toUpperCase() + part.slice(1))
    .join(' ');
}

function slugify(value) {
  return String(value || '')
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '')
    .replace(/-{2,}/g, '-');
}

function resolveSlug(cliSlug) {
  if (cliSlug && !cliSlug.startsWith('-')) return cliSlug;
  return readActiveSquadFromRuntime();
}

function parseJson(stdout) {
  const text = (stdout || '').trim();
  if (!text) return null;

  const start = text.indexOf('{');
  const end = text.lastIndexOf('}');
  if (start === -1 || end === -1 || end < start) return null;

  return JSON.parse(text.slice(start, end + 1));
}

function runStateManager(args) {
  const result = spawnSync(NODE_BIN, [STATE_MANAGER, ...args], {
    cwd: ROOT,
    encoding: 'utf8',
  });

  const payload = parseJson(result.stdout);
  if (payload) return payload;

  return {
    success: false,
    error: {
      code: 'STATE_MANAGER_FAILED',
      message: result.stderr || result.stdout || 'State manager did not return JSON',
      details: {
        args,
        exit_code: result.status,
      }
    }
  };
}

function inferExecutionModel(state) {
  const explicit = state?.execution_model || state?.metadata?.execution_model;
  if (explicit === 'epic') return 'epic';
  if (EPIC_PHASE_IDS.has(state?.current_phase) || /^epic_\d+_/.test(state?.current_phase || '')) return 'epic';
  return 'legacy';
}

function getPipeline(state) {
  return inferExecutionModel(state) === 'epic'
    ? EPIC_PIPELINE_PHASES
    : LEGACY_PIPELINE_PHASES;
}

function getPhaseIndex(phaseId, pipeline) {
  return pipeline.findIndex(phase => phase.id === phaseId);
}

function getNextPhase(currentPhase, pipeline) {
  const idx = getPhaseIndex(currentPhase, pipeline);
  if (idx === -1 || idx >= pipeline.length - 1) return null;
  return pipeline[idx + 1];
}

function getCurrentPhaseInfo(phaseId, pipeline) {
  return pipeline.find(phase => phase.id === phaseId) || null;
}

function normalizePhaseForPipeline(phaseId, executionModel) {
  if (executionModel !== 'epic') return phaseId;
  const dynamicMatch = /^epic_\d+_(init|planning|story_ready|in_progress|validated|completed)$/.exec(phaseId || '');
  if (!dynamicMatch) return phaseId;

  const suffix = dynamicMatch[1];
  if (suffix === 'init' || suffix === 'planning') return 'epic_init';
  if (suffix === 'story_ready') return 'story_ready';
  if (suffix === 'in_progress') return 'story_in_progress';
  if (suffix === 'validated') return 'epic_validation';
  if (suffix === 'completed') return 'completed';
  return phaseId;
}

function resolvePrdPath(slug, prdArg = null) {
  if (prdArg && prdArg.trim()) {
    return path.isAbsolute(prdArg) ? prdArg : path.resolve(ROOT, prdArg);
  }
  return path.join(ROOT, 'docs', 'projects', slug, 'prd.md');
}

function readPrd(prdPath) {
  if (!fs.existsSync(prdPath)) return null;
  return fs.readFileSync(prdPath, 'utf8');
}

function extractMaxMetric(content, regex) {
  const values = [];
  for (const match of content.matchAll(regex)) {
    const parsed = Number.parseInt(match[1], 10);
    if (Number.isFinite(parsed)) values.push(parsed);
  }
  if (values.length === 0) return null;
  return Math.max(...values);
}

function getScopeMetrics(content, explicitWorkflows, explicitAgents) {
  const workflowsMapped =
    parseOptionalInteger(explicitWorkflows) ??
    (content ? extractMaxMetric(content, /(\d+)\s+workflows?/gi) : null);
  const agentsNeeded =
    parseOptionalInteger(explicitAgents) ??
    (content ? extractMaxMetric(content, /(\d+)\s+agents?/gi) : null);

  return { workflowsMapped, agentsNeeded };
}

function scopeRequiresPrd(metrics) {
  return (
    (metrics.workflowsMapped !== null && metrics.workflowsMapped >= SCOPE_GATE.workflowsRequirePrd) ||
    (metrics.agentsNeeded !== null && metrics.agentsNeeded >= SCOPE_GATE.agentsRequirePrd)
  );
}

function parseEpicSections(prdContent) {
  const epicMatches = [...prdContent.matchAll(/^### Epic (\d+): (.+)$/gm)];
  return epicMatches.map((match, index) => {
    const start = match.index;
    const end = index + 1 < epicMatches.length ? epicMatches[index + 1].index : prdContent.length;
    const block = prdContent.slice(start, end).trim();
    const number = Number.parseInt(match[1], 10);
    const title = match[2].trim();
    const goal = (block.match(/\*\*Goal:\*\*\s*(.+)/) || [null, ''])[1].trim();
    const deliverablesMatch = block.match(/\*\*Deliverables:\*\*([\s\S]*?)(?=\n#### Story |\n### Epic |\n## |\Z)/);
    const deliverables = deliverablesMatch ? deliverablesMatch[1].trim() : '';
    const storyMatches = [...block.matchAll(/^#### Story ([\d.]+): (.+)$/gm)];

    const stories = storyMatches.map((storyMatch, storyIndex) => {
      const storyStart = storyMatch.index;
      const storyEnd = storyIndex + 1 < storyMatches.length
        ? storyMatches[storyIndex + 1].index
        : block.length;
      const storyBlock = block.slice(storyStart, storyEnd).trim();
      const acceptanceCriteriaMatch = storyBlock.match(/\*\*Acceptance Criteria:\*\*([\s\S]*?)(?=\n\*\*[A-Z]|\n---|\Z)/);
      return {
        number: storyMatch[1].trim(),
        title: storyMatch[2].trim(),
        body: storyBlock,
        acceptanceCriteria: acceptanceCriteriaMatch ? acceptanceCriteriaMatch[1].trim() : ''
      };
    });

    return { number, title, goal, deliverables, block, stories };
  });
}

function buildEpicReadme(slug, prdPath, epic, storyArtifacts) {
  const lines = [
    `# Epic ${epic.number}: ${epic.title}`,
    '',
    '## Metadata',
    '```yaml',
    `epic_number: ${epic.number}`,
    `domain: ${slug}`,
    `source_prd: ${toWorkspaceRelative(prdPath)}`,
    'status: Draft',
    '```',
    '',
    '## Goal',
    epic.goal || 'Goal to be refined from PRD.',
    '',
    '## Deliverables',
    epic.deliverables || '- [ ] Refine deliverables from source PRD.',
    '',
    '## Stories',
    ...storyArtifacts.map(story => `- [${story.fileName}](./${story.fileName})`),
    '',
    '## Runtime Handoff',
    `- Execute: \`@squad-chief *create-squad ${slug} --epic=${epic.number}\``,
    '- Track progress with `*status` and `*resume`.',
  ];

  return `${lines.join('\n')}\n`;
}

function buildStoryArtifact(slug, prdPath, epic, story) {
  const storySlug = slugify(story.title);
  const storyFileName = `story-${story.number.replace(/\./g, '-')}-${storySlug}.md`;
  const storyId = `${slug}-epic-${epic.number}-story-${story.number.replace(/\./g, '-')}`;
  const lines = [
    `# Story ${story.number}: ${story.title}`,
    '',
    '## Story Metadata',
    '```yaml',
    `story_id: ${storyId}`,
    'status: Draft',
    `domain: ${slug}`,
    `epic_number: ${epic.number}`,
    `epic_title: ${epic.title}`,
    `source_prd: ${toWorkspaceRelative(prdPath)}`,
    '```',
    '',
    '## Context',
    `Derived from Epic ${epic.number} in \`${toWorkspaceRelative(prdPath)}\`.`,
    '',
    '## Scope',
    `- Implement the scope defined by Story ${story.number} in the source PRD.`,
    `- Keep work bounded to Epic ${epic.number}: ${epic.title}.`,
    '',
    '## Source PRD Excerpt',
    story.body,
    '',
    '## Acceptance Criteria',
    story.acceptanceCriteria || '- [ ] Refine acceptance criteria from the PRD excerpt above.',
    '',
    '## Tasks',
    '- [ ] Refine implementation tasks from the PRD excerpt above.',
    '- [ ] Update file list, validation results, and QA notes after execution.',
    '',
    '## File Targets',
    '- [ ] Populate during implementation.',
    '',
    '## Validation',
    '- [ ] Populate during implementation.',
  ];

  return {
    id: storyId,
    title: story.title,
    fileName: storyFileName,
    content: `${lines.join('\n')}\n`,
  };
}

function ensureEpicArtifacts(slug, prdPath, epicNumber, prdContent) {
  const epics = parseEpicSections(prdContent);
  const epic = epics.find(candidate => candidate.number === epicNumber);
  if (!epic) {
    return {
      success: false,
      error: {
        code: 'EPIC_NOT_FOUND',
        message: `Epic ${epicNumber} not found in PRD`,
        details: {
          prd_path: toWorkspaceRelative(prdPath),
          available_epics: epics.map(candidate => candidate.number),
        }
      }
    };
  }

  const epicDirName = `epic-${epic.number}-${slugify(epic.title)}`;
  const epicDir = path.join(ROOT, 'docs', 'projects', slug, 'epics', epicDirName);
  fs.mkdirSync(epicDir, { recursive: true });

  const storyArtifacts = epic.stories.map(story => buildStoryArtifact(slug, prdPath, epic, story));
  const createdFiles = [];

  for (const storyArtifact of storyArtifacts) {
    const storyPath = path.join(epicDir, storyArtifact.fileName);
    fs.writeFileSync(storyPath, storyArtifact.content);
    createdFiles.push(toWorkspaceRelative(storyPath));
  }

  const readmePath = path.join(epicDir, 'README.md');
  fs.writeFileSync(readmePath, buildEpicReadme(slug, prdPath, epic, storyArtifacts));
  createdFiles.unshift(toWorkspaceRelative(readmePath));

  return {
    success: true,
    epic,
    epicDir,
    epicDirRelative: toWorkspaceRelative(epicDir),
    totalEpics: epics.length,
    createdFiles,
    storyArtifacts,
  };
}

function buildNextStepForEpic(metadata) {
  const story = metadata?.story || {};
  return {
    agent: 'squad-chief',
    task: story.title ? `Implement ${story.title}` : 'Implement the current epic story',
    story_id: story.id || null,
    story_path: story.path || null,
  };
}

function startLegacyFlow(slug, options, metrics) {
  const initArgs = ['init', slug];
  if (options.name) initArgs.push('--name', options.name);
  initArgs.push('--execution-model', 'legacy');
  initArgs.push('--scope-type', 'direct');
  initArgs.push('--context-entrypoint', 'wf-context-aware-create-squad');
  if (metrics.workflowsMapped !== null) initArgs.push('--workflows-mapped', String(metrics.workflowsMapped));
  if (metrics.agentsNeeded !== null) initArgs.push('--agents-needed', String(metrics.agentsNeeded));

  const initResult = runStateManager(initArgs);
  if (!initResult.success) {
    outputError('INIT_FAILED', 'Failed to initialize squad', initResult.error || {});
    process.exit(1);
  }

  const updateResult = runStateManager(['update', slug, '--phase', 'research', '--status', 'in_progress', '--force']);
  if (!updateResult.success) {
    outputError('UPDATE_FAILED', 'Failed to advance to research phase', updateResult.error || {});
    process.exit(1);
  }

  outputJson({
    success: true,
    action: 'start',
    execution_model: 'legacy',
    slug,
    display_name: initResult.display_name || slugToDisplayName(slug),
    current_phase: 'research',
    status: 'in_progress',
    scope_metrics: metrics,
    next_step: {
      agent: 'oalanicolas',
      task: `Research sources for ${slug}`,
    }
  });
}

function startEpicFlow(slug, options, prdPath, prdContent, metrics) {
  const epicNumber = parseOptionalInteger(options.epic);
  const artifactResult = ensureEpicArtifacts(slug, prdPath, epicNumber, prdContent);
  if (!artifactResult.success) {
    outputError(
      artifactResult.error.code,
      artifactResult.error.message,
      artifactResult.error.details || {}
    );
    process.exit(1);
  }

  const firstStory = artifactResult.storyArtifacts[0] || null;
  const initArgs = ['init', slug];
  if (options.name) initArgs.push('--name', options.name);
  initArgs.push('--execution-model', 'epic');
  initArgs.push('--scope-type', 'epic_required');
  initArgs.push('--context-entrypoint', 'wf-context-aware-create-squad');
  initArgs.push('--prd', toWorkspaceRelative(prdPath));
  initArgs.push('--epic', String(epicNumber));
  initArgs.push('--total-epics', String(artifactResult.totalEpics));
  initArgs.push('--epic-title', artifactResult.epic.title);
  if (metrics.workflowsMapped !== null) initArgs.push('--workflows-mapped', String(metrics.workflowsMapped));
  if (metrics.agentsNeeded !== null) initArgs.push('--agents-needed', String(metrics.agentsNeeded));
  if (firstStory) {
    initArgs.push('--story', firstStory.id);
    initArgs.push('--story-title', firstStory.title);
    initArgs.push('--story-path', `${artifactResult.epicDirRelative}/${firstStory.fileName}`);
  }

  const initResult = runStateManager(initArgs);
  if (!initResult.success) {
    outputError('INIT_FAILED', 'Failed to initialize epic runtime', initResult.error || {});
    process.exit(1);
  }

  const epicInitResult = runStateManager(['update', slug, '--phase', 'epic_init', '--status', 'completed', '--force']);
  if (!epicInitResult.success) {
    outputError('UPDATE_FAILED', 'Failed to record epic_init', epicInitResult.error || {});
    process.exit(1);
  }

  const readyResult = runStateManager(['update', slug, '--phase', 'story_ready', '--status', 'in_progress', '--force']);
  if (!readyResult.success) {
    outputError('UPDATE_FAILED', 'Failed to move epic runtime to story_ready', readyResult.error || {});
    process.exit(1);
  }

  outputJson({
    success: true,
    action: 'start',
    execution_model: 'epic',
    slug,
    display_name: initResult.display_name || slugToDisplayName(slug),
    current_phase: 'story_ready',
    status: 'in_progress',
    prd_path: toWorkspaceRelative(prdPath),
    scope_metrics: metrics,
    epic: {
      number: artifactResult.epic.number,
      title: artifactResult.epic.title,
      dir: artifactResult.epicDirRelative,
      total_epics: artifactResult.totalEpics,
    },
    artifacts: artifactResult.createdFiles,
    next_step: buildNextStepForEpic({
      story: firstStory
        ? {
            id: firstStory.id,
            title: firstStory.title,
            path: `${artifactResult.epicDirRelative}/${firstStory.fileName}`,
          }
        : null
    })
  });
}

function cmdStart(slug, options = {}) {
  const prdPath = resolvePrdPath(slug, options.prd);
  const prdContent = readPrd(prdPath);
  const metrics = getScopeMetrics(prdContent, options.workflowsMapped, options.agentsNeeded);
  const requiresPrd = scopeRequiresPrd(metrics);
  const epicNumber = parseOptionalInteger(options.epic);

  if (requiresPrd && !prdContent) {
    outputError('PRD_REQUIRED', 'Large-scope squad creation requires a valid PRD before execution', {
      slug,
      expected_prd: toWorkspaceRelative(prdPath),
      scope_metrics: metrics,
      handoff: `*plan-squad ${slug}`,
      no_partial_scaffold: true,
    });
    process.exit(1);
  }

  if (requiresPrd && epicNumber === null) {
    outputError('EPIC_REQUIRED', 'Large-scope PRD-backed squads must start epic by epic', {
      slug,
      prd_path: toWorkspaceRelative(prdPath),
      scope_metrics: metrics,
      handoff: `*create-squad ${slug} --epic=1`,
      no_partial_scaffold: true,
    });
    process.exit(1);
  }

  if (epicNumber !== null) {
    if (!prdContent) {
      outputError('PRD_REQUIRED', 'Epic execution requires a valid PRD', {
        slug,
        expected_prd: toWorkspaceRelative(prdPath),
      });
      process.exit(1);
    }
    startEpicFlow(slug, options, prdPath, prdContent, metrics);
    return;
  }

  startLegacyFlow(slug, options, metrics);
}

function cmdNext(slug, options = {}) {
  const { force = false } = options;
  const state = runStateManager(['get', slug]);
  if (state.error) {
    outputError('STATE_NOT_FOUND', `No state found for ${slug}`, state.error);
    process.exit(1);
  }

  const pipeline = getPipeline(state);
  const currentPhase = state.current_phase;
  const currentStatus = state.checkpoint_status;

  if (currentStatus !== 'completed' && currentStatus !== 'approved' && !force) {
    outputError('PHASE_NOT_COMPLETE', `Current phase "${currentPhase}" is not complete`, {
      current_status: currentStatus,
      hint: 'Complete the current phase first, or use --force to skip'
    });
    process.exit(1);
  }

  const nextPhase = getNextPhase(currentPhase, pipeline);
  if (!nextPhase) {
    outputJson({
      success: true,
      action: 'next',
      slug,
      execution_model: inferExecutionModel(state),
      message: 'Pipeline already completed',
      current_phase: currentPhase
    });
    return;
  }

  const nextStatus = nextPhase.human_checkpoint ? 'checkpoint' : 'in_progress';
  const updateResult = runStateManager([
    'update',
    slug,
    '--phase',
    nextPhase.id,
    '--status',
    nextStatus,
    ...(force ? ['--force'] : [])
  ]);

  if (!updateResult.success) {
    outputError('UPDATE_FAILED', `Failed to move to ${nextPhase.id}`, updateResult.error || {});
    process.exit(1);
  }

  const metadata = state.metadata || {};
  outputJson({
    success: true,
    action: 'next',
    slug,
    execution_model: inferExecutionModel(state),
    previous_phase: currentPhase,
    current_phase: nextPhase.id,
    status: nextStatus,
    agent: nextPhase.agent,
    human_checkpoint: nextPhase.human_checkpoint,
    next_step: inferExecutionModel(state) === 'epic'
      ? buildNextStepForEpic(metadata)
      : nextPhase.agent
        ? { agent: nextPhase.agent, task: `Execute ${nextPhase.id} phase` }
        : { message: 'Pipeline completed' }
  });
}

function cmdResume(slug) {
  const state = runStateManager(['get', slug]);
  if (state.error) {
    outputError('STATE_NOT_FOUND', `No state found for ${slug}`, state.error);
    process.exit(1);
  }

  const pipeline = getPipeline(state);
  const currentPhase = state.current_phase;
  const currentStatus = state.checkpoint_status;
  const executionModel = inferExecutionModel(state);
  const normalizedPhase = normalizePhaseForPipeline(currentPhase, executionModel);
  const phaseInfo = getCurrentPhaseInfo(normalizedPhase, pipeline);

  outputJson({
    success: true,
    action: 'resume',
    slug,
    display_name: state.display_name,
    execution_model: executionModel,
    display_execution_model: state.display_execution_model || null,
    current_phase: currentPhase,
    display_phase: state.display_phase || null,
    status: currentStatus,
    wave_status: state.wave_status || null,
    agent: phaseInfo ? phaseInfo.agent : null,
    human_checkpoint: phaseInfo ? phaseInfo.human_checkpoint : false,
    metadata: state.metadata || {},
    epic: state.metadata?.epic || null,
    wave: state.metadata?.wave || null,
    current_wave: state.current_wave || state.metadata?.wave?.number || null,
    total_waves: state.total_waves || state.metadata?.wave?.total || null,
    completed_outputs: state.completed_outputs || [],
    agent_history: state.agent_history || [],
    next_step: executionModel === 'epic'
      ? buildNextStepForEpic(state.metadata || {})
      : currentStatus === 'checkpoint'
        ? { message: 'Awaiting human decision (approve/revise/abort)' }
        : phaseInfo && phaseInfo.agent
          ? { agent: phaseInfo.agent, task: `Continue ${currentPhase} phase` }
          : { message: 'Ready to advance to next phase' }
  });
}

function cmdStatus(slug) {
  const state = runStateManager(['get', slug]);
  if (state.error) {
    outputError('STATE_NOT_FOUND', `No state found for ${slug}`, state.error);
    process.exit(1);
  }

  const executionModel = inferExecutionModel(state);
  const pipeline = getPipeline(state);
  const normalizedPhase = normalizePhaseForPipeline(state.current_phase, executionModel);
  const currentPhaseIdx = getPhaseIndex(normalizedPhase, pipeline);

  const phases = pipeline.map((phase, idx) => {
    let status = 'pending';
    if (idx < currentPhaseIdx) status = 'completed';
    else if (idx === currentPhaseIdx) status = state.checkpoint_status;

    return {
      id: phase.id,
      agent: phase.agent,
      status,
      human_checkpoint: phase.human_checkpoint,
      current: idx === currentPhaseIdx
    };
  });

  const progress = currentPhaseIdx <= 0
    ? 0
    : Math.round((currentPhaseIdx / (pipeline.length - 1)) * 100);

  outputJson({
    success: true,
    action: 'status',
    slug,
    display_name: state.display_name,
    execution_model: executionModel,
    display_execution_model: state.display_execution_model || null,
    progress: `${progress}%`,
    current_phase: state.current_phase,
    display_phase: state.display_phase || null,
    checkpoint_status: state.checkpoint_status,
    wave_status: state.wave_status || null,
    phases,
    metadata: state.metadata || {},
    epic: state.metadata?.epic || null,
    wave: state.metadata?.wave || null,
    current_epic: state.current_epic || state.metadata?.epic?.number || null,
    total_epics: state.total_epics || state.metadata?.epic?.total || null,
    current_wave: state.current_wave || state.metadata?.wave?.number || null,
    total_waves: state.total_waves || state.metadata?.wave?.total || null,
    agent_history: state.agent_history || [],
    completed_outputs: state.completed_outputs || [],
    created_at: state.created_at,
    updated_at: state.updated_at
  });
}

function cmdApprove(slug) {
  const state = runStateManager(['get', slug]);
  if (state.error) {
    outputError('STATE_NOT_FOUND', `No state found for ${slug}`, state.error);
    process.exit(1);
  }

  if (state.checkpoint_status !== 'checkpoint') {
    outputError('NOT_AT_CHECKPOINT', 'Not at a human checkpoint', {
      current_phase: state.current_phase,
      current_status: state.checkpoint_status
    });
    process.exit(1);
  }

  const approveResult = runStateManager(['update', slug, '--phase', state.current_phase, '--status', 'approved']);
  if (!approveResult.success) {
    outputError('UPDATE_FAILED', 'Failed to approve checkpoint', approveResult.error || {});
    process.exit(1);
  }

  cmdNext(slug, { force: true });
}

function cmdRevise(slug, targetPhase) {
  if (!targetPhase) {
    outputError('MISSING_TARGET', 'Specify target phase with --to <phase>');
    process.exit(1);
  }

  const state = runStateManager(['get', slug]);
  if (state.error) {
    outputError('STATE_NOT_FOUND', `No state found for ${slug}`, state.error);
    process.exit(1);
  }

  const pipeline = getPipeline(state);
  const phaseInfo = getCurrentPhaseInfo(targetPhase, pipeline);
  if (!phaseInfo) {
    outputError('INVALID_PHASE', `Invalid phase: ${targetPhase}`, {
      valid_phases: pipeline.map(phase => phase.id)
    });
    process.exit(1);
  }

  const reviseResult = runStateManager(['update', slug, '--phase', targetPhase, '--status', 'in_progress', '--force']);
  if (!reviseResult.success) {
    outputError('UPDATE_FAILED', `Failed to revise to ${targetPhase}`, reviseResult.error || {});
    process.exit(1);
  }

  outputJson({
    success: true,
    action: 'revise',
    slug,
    execution_model: inferExecutionModel(state),
    target_phase: targetPhase,
    status: 'in_progress',
    agent: phaseInfo.agent,
    message: `Returned to ${targetPhase} for revision`
  });
}

function cmdAbort(slug, reason = 'Aborted by user') {
  const abortResult = runStateManager(['update', slug, '--phase', 'failed', '--status', 'completed', '--force']);
  if (!abortResult.success) {
    outputError('UPDATE_FAILED', 'Failed to abort pipeline', abortResult.error || {});
    process.exit(1);
  }

  outputJson({
    success: true,
    action: 'abort',
    slug,
    status: 'failed',
    reason
  });
}

function cmdWaveLoop(argv) {
  const result = spawnSync(NODE_BIN, [WAVE_LOOP, ...argv], {
    cwd: ROOT,
    stdio: 'inherit',
  });

  process.exit(result.status ?? 1);
}

function main() {
  const args = process.argv.slice(2);

  if (args.length === 0 || args[0] === '--help' || args[0] === '-h') {
    console.log(`Squad Workflow Runner - Pipeline orchestration for squad creation

Usage:
  node squad-workflow-runner.cjs start <slug> [--name "Name"] [--prd <path>] [--epic <N>] [--workflows-mapped <n>] [--agents-needed <n>]
  node squad-workflow-runner.cjs start-epic <slug> --epic <N> [--prd <path>]
  node squad-workflow-runner.cjs wave-loop [slug] [--runtime auto|codex|claude] [--from <N>] [--to <N>] [--max-waves <n>] [--status|--dry-run] [--json]
  node squad-workflow-runner.cjs resume [slug]
  node squad-workflow-runner.cjs next [slug] [--force]
  node squad-workflow-runner.cjs status [slug]
  node squad-workflow-runner.cjs approve [slug]
  node squad-workflow-runner.cjs revise [slug] --to <phase>
  node squad-workflow-runner.cjs abort [slug]

Large-scope gate:
  workflows_mapped >= ${SCOPE_GATE.workflowsRequirePrd} OR agents_needed >= ${SCOPE_GATE.agentsRequirePrd}
  => valid PRD required + start with --wave=N (legacy alias: --epic=N)

Legacy phases:
  init -> research -> source_validation -> dna_extraction -> agent_scaffolding ->
  task_anatomy -> quality_gate -> integration -> smoke_test -> completed

Epic phases:
  init -> epic_init -> story_ready -> story_in_progress -> epic_validation -> completed`);
    process.exit(0);
  }

  const command = args[0];
  const force = args.includes('--force');

  if (command === 'start' || command === 'start-epic') {
    const slug = args[1] && !args[1].startsWith('-') ? args[1] : null;
    if (!slug) {
      outputError('MISSING_SLUG', 'Usage: start <slug> [--name "Name"] [--prd <path>] [--wave <N>|--epic <N>]');
      process.exit(1);
    }
    if (command === 'start-epic' && !parseWaveOrEpicArg(args)) {
      outputError('MISSING_EPIC', 'Usage: start-epic <slug> --wave <N>|--epic <N> [--prd <path>]');
      process.exit(1);
    }

    cmdStart(slug, {
      name: parseArg(args, '--name'),
      prd: parseArg(args, '--prd'),
      epic: parseWaveOrEpicArg(args),
      workflowsMapped: parseArg(args, '--workflows-mapped'),
      agentsNeeded: parseArg(args, '--agents-needed'),
    });
    return;
  }

  if (command === 'wave-loop') {
    cmdWaveLoop(args.slice(1));
    return;
  }

  const slug = resolveSlug(args[1]);
  if (!slug) {
    outputError('NO_ACTIVE_SQUAD', 'No slug provided and no active squad pointer found');
    process.exit(1);
  }

  if (command === 'resume') {
    cmdResume(slug);
  } else if (command === 'next') {
    cmdNext(slug, { force });
  } else if (command === 'status') {
    cmdStatus(slug);
  } else if (command === 'approve') {
    cmdApprove(slug);
  } else if (command === 'revise') {
    cmdRevise(slug, parseArg(args, '--to'));
  } else if (command === 'abort') {
    cmdAbort(slug);
  } else {
    outputError('INVALID_COMMAND', `Unknown command: ${command}`, {
      valid_commands: ['start', 'start-epic', 'wave-loop', 'resume', 'next', 'status', 'approve', 'revise', 'abort']
    });
    process.exit(1);
  }
}

main();
function parseWaveOrEpicArg(args) {
  return parseArg(args, '--wave') || parseArg(args, '--epic');
}
