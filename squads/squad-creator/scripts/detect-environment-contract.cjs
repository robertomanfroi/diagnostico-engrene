#!/usr/bin/env node

const fs = require('fs');
const fsp = require('fs').promises;
const path = require('path');
const yaml = require('js-yaml');

const PRO_SQUAD_NAME = 'squad-creator-pro';
const PRO_CONFIG_REL = path.join('squads', PRO_SQUAD_NAME, 'config.yaml');
const PRO_REQUIRED_DIRS = ['agents', 'tasks', 'workflows'];
const ENTERPRISE_MARKER_REL = path.join('workspace', 'license', 'enterprise-runtime.capability.yaml');
const C_LEVEL_DIR_REL = path.join('squads', 'c-level');
const WORKSPACE_CONFIG_REL = path.join('workspace', '_system', 'config.yaml');
const REQUIRED_WORKSPACE_ROOTS = [
  path.join('workspace', 'businesses'),
  path.join('workspace', '_system'),
  path.join('workspace', '_templates'),
];

function toPosix(value) {
  return value.split(path.sep).join('/');
}

function uniq(items) {
  return [...new Set(items.filter(Boolean))];
}

function loadSquadManifest(root, squad) {
  if (!squad) {
    return null;
  }

  const manifestCandidates = [
    path.join('squads', squad, 'config.yaml'),
    path.join('squads', squad, 'squad.yaml'),
  ];

  for (const relativePath of manifestCandidates) {
    if (!existsFile(root, relativePath)) {
      continue;
    }

    try {
      return {
        relative_path: toPosix(relativePath),
        document: readYaml(path.join(root, relativePath)),
      };
    } catch {
      return {
        relative_path: toPosix(relativePath),
        document: null,
      };
    }
  }

  return null;
}

function resolveProjectionPath(options = {}) {
  if (typeof options.projectionPath === 'string' && options.projectionPath.trim().length > 0) {
    return {
      projection_path: options.projectionPath.trim(),
      evidence_paths: [],
    };
  }

  const root = options.root || process.cwd();
  const manifest = loadSquadManifest(root, options.squad);
  const declaredProjectionPath = manifest?.document?.distribution_contract?.docs_projection_path;
  if (typeof declaredProjectionPath === 'string' && declaredProjectionPath.trim().length > 0) {
    return {
      projection_path: declaredProjectionPath.trim(),
      evidence_paths: manifest?.relative_path ? [manifest.relative_path] : [],
    };
  }

  if (options.squad) {
    return {
      projection_path: path.join('docs', options.squad, 'operational-projection.yaml'),
      evidence_paths: manifest?.relative_path ? [manifest.relative_path] : [],
    };
  }

  return {
    projection_path: null,
    evidence_paths: manifest?.relative_path ? [manifest.relative_path] : [],
  };
}

function existsFile(root, relativePath) {
  const absolutePath = path.join(root, relativePath);
  try {
    return fs.statSync(absolutePath).isFile();
  } catch {
    return false;
  }
}

function existsDirectory(root, relativePath) {
  const absolutePath = path.join(root, relativePath);
  try {
    return fs.statSync(absolutePath).isDirectory();
  } catch {
    return false;
  }
}

function readYaml(filePath) {
  return yaml.load(fs.readFileSync(filePath, 'utf8')) || {};
}

function detectProjectionContract(root, projectionPath) {
  if (!projectionPath) {
    return {
      projection_path: null,
      projection_state: 'missing',
      projection_freshness: 'missing',
      projection_updated_at: null,
      evidence_paths: [],
    };
  }

  if (!existsFile(root, projectionPath)) {
    return {
      projection_path: toPosix(projectionPath),
      projection_state: 'missing',
      projection_freshness: 'missing',
      projection_updated_at: null,
      evidence_paths: [],
    };
  }

  try {
    const document = readYaml(path.join(root, projectionPath));
    const freshness = document?.projection_freshness || {};
    return {
      projection_path: toPosix(projectionPath),
      projection_state: 'present',
      projection_freshness: freshness.status || 'unknown',
      projection_updated_at: freshness.updated_at || null,
      evidence_paths: [toPosix(projectionPath)],
    };
  } catch {
    return {
      projection_path: toPosix(projectionPath),
      projection_state: 'present',
      projection_freshness: 'unknown',
      projection_updated_at: null,
      evidence_paths: [toPosix(projectionPath)],
    };
  }
}

async function detectProPack(options = {}) {
  const root = options.root || process.cwd();
  const configPath = path.join(root, PRO_CONFIG_REL);

  try {
    await fsp.access(configPath);
  } catch {
    return {
      pro_mode: false,
      evidence_paths: [],
    };
  }

  let version = 'unknown';
  try {
    const content = await fsp.readFile(configPath, 'utf8');
    const config = yaml.load(content) || {};
    version = config.version || config.metadata?.version || 'unknown';
  } catch {
    return {
      pro_mode: false,
      error: 'config.yaml exists but failed to parse',
      evidence_paths: [toPosix(PRO_CONFIG_REL)],
    };
  }

  const missing = [];
  const proBase = path.join(root, 'squads', PRO_SQUAD_NAME);
  for (const dir of PRO_REQUIRED_DIRS) {
    if (!existsDirectory(proBase, dir)) {
      missing.push(dir);
    }
  }

  if (missing.length > 0) {
    return {
      pro_mode: false,
      version,
      missing,
      evidence_paths: [toPosix(PRO_CONFIG_REL)],
    };
  }

  return {
    pro_mode: true,
    version,
    evidence_paths: [toPosix(PRO_CONFIG_REL)],
  };
}

function validateEnterpriseCapabilityDocument(document) {
  const capability = document?.enterprise_runtime_capability;
  if (!capability || typeof capability !== 'object') {
    return {
      valid: false,
      error: 'enterprise_runtime_capability block missing',
    };
  }

  const surfaces = Array.isArray(capability.allowed_surfaces) ? capability.allowed_surfaces : [];
  const requiredSurfaces = new Set(['workspace_canonical', 'private_projection_generation']);
  for (const surface of requiredSurfaces) {
    if (!surfaces.includes(surface)) {
      return {
        valid: false,
        error: `allowed_surfaces missing "${surface}"`,
      };
    }
  }

  if (capability.enabled !== true) {
    return { valid: false, error: 'enabled must be true' };
  }
  if (capability.issued_by !== 'aiox') {
    return { valid: false, error: 'issued_by must equal "aiox"' };
  }
  if (capability.scope !== 'private_runtime') {
    return { valid: false, error: 'scope must equal "private_runtime"' };
  }
  if (capability.access_tier !== 'enterprise') {
    return { valid: false, error: 'access_tier must equal "enterprise"' };
  }
  if (capability.allow_full_workspace_mode !== true) {
    return { valid: false, error: 'allow_full_workspace_mode must be true' };
  }
  if (typeof capability.issued_at !== 'string' || capability.issued_at.trim().length === 0) {
    return { valid: false, error: 'issued_at must be a non-empty string' };
  }

  return { valid: true };
}

async function detectEnterpriseCapability(options = {}) {
  const root = options.root || process.cwd();
  const markerPath = path.join(root, ENTERPRISE_MARKER_REL);

  if (!existsFile(root, ENTERPRISE_MARKER_REL)) {
    return {
      proven: false,
      marker_path: toPosix(ENTERPRISE_MARKER_REL),
      evidence_paths: [],
    };
  }

  try {
    const document = readYaml(markerPath);
    const validation = validateEnterpriseCapabilityDocument(document);
    if (!validation.valid) {
      return {
        proven: false,
        marker_path: toPosix(ENTERPRISE_MARKER_REL),
        error: validation.error,
        evidence_paths: [toPosix(ENTERPRISE_MARKER_REL)],
      };
    }

    return {
      proven: true,
      marker_path: toPosix(ENTERPRISE_MARKER_REL),
      evidence_paths: [toPosix(ENTERPRISE_MARKER_REL)],
    };
  } catch (error) {
    return {
      proven: false,
      marker_path: toPosix(ENTERPRISE_MARKER_REL),
      error: error.message,
      evidence_paths: [toPosix(ENTERPRISE_MARKER_REL)],
    };
  }
}

function detectWorkspaceCapability(options = {}) {
  const root = options.root || process.cwd();
  const missingRoots = REQUIRED_WORKSPACE_ROOTS.filter((relativePath) => !existsDirectory(root, relativePath));

  return {
    c_level_present: existsDirectory(root, C_LEVEL_DIR_REL),
    workspace_config_present: existsFile(root, WORKSPACE_CONFIG_REL),
    missing_workspace_roots: missingRoots.map(toPosix),
    evidence_paths: uniq([
      existsDirectory(root, C_LEVEL_DIR_REL) ? toPosix(C_LEVEL_DIR_REL) : null,
      existsFile(root, WORKSPACE_CONFIG_REL) ? toPosix(WORKSPACE_CONFIG_REL) : null,
      ...REQUIRED_WORKSPACE_ROOTS
        .filter((relativePath) => existsDirectory(root, relativePath))
        .map((relativePath) => toPosix(relativePath)),
    ]),
  };
}

function hasExplicitRuntimeContext(options = {}) {
  return Boolean(options.business || options.product || options.app);
}

function buildPortableContract(accessTier, reason, evidencePaths, extras = {}) {
  return {
    access_tier: accessTier,
    runtime_mode: 'portable_docs_mode',
    source_of_truth: 'docs_projection',
    reason,
    evidence_paths: uniq(evidencePaths),
    ...extras,
  };
}

function loadReadinessResolver(root) {
  const resolverPath = path.join(root, 'squads', 'c-level', 'scripts', 'resolve-squad-workspace-readiness.cjs');
  if (!existsFile(root, path.join('squads', 'c-level', 'scripts', 'resolve-squad-workspace-readiness.cjs'))) {
    return null;
  }

  const previousCwd = process.cwd();
  try {
    process.chdir(root);
    delete require.cache[require.resolve(resolverPath)];
    return require(resolverPath);
  } finally {
    process.chdir(previousCwd);
  }
}

function resolveWorkspaceReadiness(root, options) {
  const resolver = loadReadinessResolver(root);
  if (!resolver || typeof resolver.resolveSquadWorkspaceReadiness !== 'function') {
    return {
      status: 'inconclusive',
      reason: 'Workspace readiness resolver unavailable',
      evidence_paths: [],
    };
  }

  const previousCwd = process.cwd();
  try {
    process.chdir(root);
    const output = resolver.resolveSquadWorkspaceReadiness({
      squad: options.squad || null,
      business: options.business || null,
      product: options.product || null,
      app: options.app || null,
      contextType: options.contextType || null,
      format: options.format || 'json',
    });

    return {
      status: output.status || 'inconclusive',
      reason: output.reason || '',
      evidence_paths: uniq([
        'squads/c-level/scripts/resolve-squad-workspace-readiness.cjs',
        output.integration_config_path || null,
        ...(Array.isArray(output.canonical_config_paths) ? output.canonical_config_paths : []),
      ]),
      payload: output,
    };
  } catch (error) {
    return {
      status: 'inconclusive',
      reason: error.message,
      evidence_paths: ['squads/c-level/scripts/resolve-squad-workspace-readiness.cjs'],
    };
  } finally {
    process.chdir(previousCwd);
  }
}

async function detectEnvironmentContract(options = {}) {
  const root = options.root || process.cwd();
  const squad = options.squad || null;
  const projectionResolution = resolveProjectionPath({ ...options, root, squad });
  const projectionContract = detectProjectionContract(root, projectionResolution.projection_path);

  const [proPack, enterpriseCapability] = await Promise.all([
    detectProPack({ root }),
    detectEnterpriseCapability({ root }),
  ]);

  let accessTier = 'opensource';
  let accessReason = 'Pro pack not proven.';
  const tierEvidencePaths = [];

  if (enterpriseCapability.proven) {
    accessTier = 'enterprise';
    accessReason = 'Enterprise capability marker validated.';
    tierEvidencePaths.push(...enterpriseCapability.evidence_paths);
  } else if (proPack.pro_mode) {
    accessTier = 'pro';
    accessReason = 'Pro pack detected; enterprise not proven.';
    tierEvidencePaths.push(...proPack.evidence_paths);
    if (enterpriseCapability.error) {
      tierEvidencePaths.push(...enterpriseCapability.evidence_paths);
      accessReason = `Pro pack detected; enterprise marker not proven (${enterpriseCapability.error}).`;
    }
  } else if (proPack.error) {
    tierEvidencePaths.push(...proPack.evidence_paths);
    accessReason = `Pro pack not proven (${proPack.error}).`;
  } else if (Array.isArray(proPack.missing) && proPack.missing.length > 0) {
    tierEvidencePaths.push(...proPack.evidence_paths);
    accessReason = `Pro pack not proven (installation incomplete: missing ${proPack.missing.join(', ')}).`;
  }

  const sharedExtras = {
    pro_mode: proPack.pro_mode,
    pro_version: proPack.version || null,
    enterprise_proven: enterpriseCapability.proven,
    enterprise_marker_path: enterpriseCapability.marker_path,
    projection_path: projectionContract.projection_path,
    projection_state: projectionContract.projection_state,
    projection_freshness: projectionContract.projection_freshness,
    projection_updated_at: projectionContract.projection_updated_at,
  };

  if (accessTier === 'opensource') {
    return buildPortableContract(
      accessTier,
      `${accessReason} portable_docs_mode enforced.`,
      [...tierEvidencePaths, ...projectionResolution.evidence_paths, ...projectionContract.evidence_paths],
      sharedExtras,
    );
  }

  const workspaceCapability = detectWorkspaceCapability({ root });
  const runtimeEvidencePaths = [
    ...tierEvidencePaths,
    ...workspaceCapability.evidence_paths,
    ...projectionResolution.evidence_paths,
    ...projectionContract.evidence_paths,
  ];

  if (!workspaceCapability.c_level_present) {
    return buildPortableContract(
      accessTier,
      `${accessReason} squads/c-level/ missing, remaining in portable_docs_mode.`,
      runtimeEvidencePaths,
      sharedExtras,
    );
  }

  if (!workspaceCapability.workspace_config_present) {
    return buildPortableContract(
      accessTier,
      `${accessReason} workspace/_system/config.yaml missing, remaining in portable_docs_mode.`,
      runtimeEvidencePaths,
      sharedExtras,
    );
  }

  if (workspaceCapability.missing_workspace_roots.length > 0) {
    return buildPortableContract(
      accessTier,
      `${accessReason} workspace roots missing (${workspaceCapability.missing_workspace_roots.join(', ')}), remaining in portable_docs_mode.`,
      runtimeEvidencePaths,
      sharedExtras,
    );
  }

  if (!squad) {
    return buildPortableContract(
      accessTier,
      `${accessReason} target squad not provided, remaining in portable_docs_mode.`,
      runtimeEvidencePaths,
      sharedExtras,
    );
  }

  if (!hasExplicitRuntimeContext(options)) {
    return buildPortableContract(
      accessTier,
      `${accessReason} explicit business/product/app context missing, remaining in portable_docs_mode.`,
      runtimeEvidencePaths,
      sharedExtras,
    );
  }

  const readiness = resolveWorkspaceReadiness(root, options);
  const readinessEvidencePaths = [...runtimeEvidencePaths, ...readiness.evidence_paths];

  if (readiness.status !== 'ready') {
    return buildPortableContract(
      accessTier,
      `${accessReason} readiness not ready (${readiness.reason || readiness.status}), remaining in portable_docs_mode.`,
      readinessEvidencePaths,
      {
        ...sharedExtras,
        readiness_status: readiness.status,
      },
    );
  }

  return {
    access_tier: accessTier,
    runtime_mode: 'full_workspace_mode',
    source_of_truth: 'workspace_canonical',
    reason: `${accessReason} readiness resolved as ready for squad "${squad}".`,
    evidence_paths: uniq(readinessEvidencePaths),
    readiness_status: readiness.status,
    ...sharedExtras,
  };
}

function parseArgs(argv) {
  const args = {
    squad: null,
    business: null,
    product: null,
    app: null,
    contextType: null,
    format: 'json',
  };

  for (const raw of argv) {
    if (raw.startsWith('--squad=')) {
      args.squad = raw.slice('--squad='.length).trim() || null;
      continue;
    }
    if (raw.startsWith('--business=')) {
      args.business = raw.slice('--business='.length).trim() || null;
      continue;
    }
    if (raw.startsWith('--product=')) {
      args.product = raw.slice('--product='.length).trim() || null;
      continue;
    }
    if (raw.startsWith('--app=')) {
      args.app = raw.slice('--app='.length).trim() || null;
      continue;
    }
    if (raw.startsWith('--context-type=')) {
      args.contextType = raw.slice('--context-type='.length).trim() || null;
      continue;
    }
    if (raw.startsWith('--projection-path=')) {
      args.projectionPath = raw.slice('--projection-path='.length).trim() || null;
      continue;
    }
    if (raw.startsWith('--format=')) {
      args.format = raw.slice('--format='.length).trim() || 'json';
    }
  }

  return args;
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  const output = await detectEnvironmentContract(args);

  if (args.format === 'yaml') {
    process.stdout.write(yaml.dump(output, { lineWidth: 120, noRefs: true, sortKeys: false }));
    return;
  }

  process.stdout.write(`${JSON.stringify(output, null, 2)}\n`);
}

if (require.main === module) {
  main().catch((error) => {
    console.error(`ERROR: ${error.message}`);
    process.exit(1);
  });
}

module.exports = {
  detectEnvironmentContract,
  detectEnterpriseCapability,
  detectProjectionContract,
  detectProPack,
  detectWorkspaceCapability,
  hasExplicitRuntimeContext,
  parseArgs,
  resolveWorkspaceReadiness,
  validateEnterpriseCapabilityDocument,
};
