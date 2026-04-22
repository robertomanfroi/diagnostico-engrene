#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

const CANONICAL_BUNDLE_BY_ALIAS = {
  AioxSop: 'AioxSop',
  Sop: 'AioxSop',
  AioxWorkspace: 'AioxWorkspace',
  Workspace: 'AioxWorkspace',
  Copy: 'Copy',
  Design: 'Design',
  SquadCreator: 'SquadCreator',
  SquadCreatorPro: 'SquadCreator',
};

function parseArgs(argv) {
  const args = { target: null };

  for (const arg of argv) {
    if (arg.startsWith('--target=')) {
      args.target = arg.slice('--target='.length);
    }
  }

  if (!args.target) {
    throw new Error('Missing required --target=<path>');
  }

  return args;
}

function findRepoRoot(startDir) {
  let current = path.resolve(startDir);

  for (let depth = 0; depth < 10; depth += 1) {
    if (fs.existsSync(path.join(current, '.agents', 'workflows')) && fs.existsSync(path.join(current, 'squads'))) {
      return current;
    }
    const parent = path.dirname(current);
    if (parent === current) {
      break;
    }
    current = parent;
  }

  throw new Error('Could not resolve repo root with .agents/workflows and squads/');
}

function listDirNames(dirPath) {
  if (!fs.existsSync(dirPath)) {
    return [];
  }

  return fs
    .readdirSync(dirPath, { withFileTypes: true })
    .filter((entry) => entry.isDirectory())
    .map((entry) => entry.name);
}

function ensureDir(dirPath) {
  fs.mkdirSync(dirPath, { recursive: true });
}

function resetDir(dirPath) {
  fs.rmSync(dirPath, { recursive: true, force: true });
  fs.mkdirSync(dirPath, { recursive: true });
}

function copyDir(sourceDir, targetDir) {
  resetDir(targetDir);
  fs.cpSync(sourceDir, targetDir, { recursive: true });
}

const ALIAS_HINTS = new Map([
  ['aioxsop', 'AioxSop'],
  ['sop', 'Sop'],
  ['aioxworkspace', 'AioxWorkspace'],
  ['workspace', 'Workspace'],
  ['copy', 'Copy'],
  ['design', 'Design'],
  ['designsystem', 'Design'],
  ['ds', 'Design'],
  ['squadcreator', 'SquadCreator'],
  ['squadcreatorpro', 'SquadCreatorPro'],
  ['squadpro', 'SquadCreatorPro'],
]);

function normalizeAliasToken(value) {
  return String(value || '').toLowerCase().replace(/[^a-z0-9]/g, '');
}

function inferAliasCandidates(entry) {
  const raw = String(entry || '');
  const stem = raw.replace(/\.md$/i, '');
  const candidates = new Set([raw, stem]);

  if (stem.includes('--')) {
    candidates.add(stem.split('--', 1)[0]);
  }
  if (stem.includes('-')) {
    candidates.add(stem.split('-', 1)[0]);
  }
  if (stem.includes('_')) {
    candidates.add(stem.split('_', 1)[0]);
  }

  return [...candidates]
    .map(normalizeAliasToken)
    .filter(Boolean);
}

function resolveAlias(entry) {
  for (const token of inferAliasCandidates(entry)) {
    if (ALIAS_HINTS.has(token)) {
      return ALIAS_HINTS.get(token);
    }
  }
  return null;
}

function collectRequestedAliases(targetRoot) {
  const claudeSkillAliases = listDirNames(path.join(targetRoot, '.claude', 'skills')).map(resolveAlias).filter(Boolean);
  const claudeAgentAliases = fs.existsSync(path.join(targetRoot, '.claude', 'agents'))
    ? fs.readdirSync(path.join(targetRoot, '.claude', 'agents')).map(resolveAlias).filter(Boolean)
    : [];
  const agentsSkillAliases = listDirNames(path.join(targetRoot, '.agents', 'skills')).map(resolveAlias).filter(Boolean);

  const requested = new Set(
    [...claudeSkillAliases, ...claudeAgentAliases, ...agentsSkillAliases].filter(
      (alias) => Object.prototype.hasOwnProperty.call(CANONICAL_BUNDLE_BY_ALIAS, alias),
    ),
  );

  if (requested.has('Sop')) {
    requested.add('AioxSop');
  }

  if (requested.has('Workspace')) {
    requested.add('AioxWorkspace');
  }

  if (requested.has('SquadCreatorPro')) {
    requested.add('SquadCreator');
  }

  return [...requested].sort();
}

function main() {
  const { target } = parseArgs(process.argv.slice(2));
  const repoRoot = findRepoRoot(process.cwd());
  const sourceRoot = path.join(repoRoot, '.agents', 'workflows');
  const targetRoot = path.resolve(process.cwd(), target);
  const targetWorkflowsRoot = path.join(targetRoot, '.agents', 'workflows');

  if (!fs.existsSync(targetRoot)) {
    throw new Error(`Target root not found: ${targetRoot}`);
  }

  ensureDir(targetWorkflowsRoot);

  const aliases = collectRequestedAliases(targetRoot);
  if (aliases.length === 0) {
    throw new Error(`No compatible Claude/Codex aliases found in target: ${targetRoot}`);
  }

  const exported = [];

  for (const alias of aliases) {
    const canonical = CANONICAL_BUNDLE_BY_ALIAS[alias];
    const sourceDir = path.join(sourceRoot, canonical);
    const targetDir = path.join(targetWorkflowsRoot, alias);

    if (!fs.existsSync(sourceDir)) {
      throw new Error(`Canonical workflow bundle not found: ${sourceDir}`);
    }

    copyDir(sourceDir, targetDir);
    exported.push({
      alias,
      canonical,
      targetDir,
    });
  }

  console.log(`Exported ${exported.length} Antigravity workflow bundles to ${targetWorkflowsRoot}`);
  for (const item of exported) {
    const aliasNote = item.alias === item.canonical ? '' : ` (alias of ${item.canonical})`;
    console.log(`- ${item.alias}${aliasNote}`);
  }
}

try {
  main();
} catch (error) {
  console.error(`ERROR: ${error.message}`);
  process.exit(1);
}
