#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const yaml = require('js-yaml');

const ROOT = path.resolve(__dirname, '..', '..', '..');
const WORKSPACE_CONFIG_REL = 'workspace/_system/config.yaml';

const {
  detectEnvironmentContract,
} = require(path.join(ROOT, 'squads', 'squad-creator', 'scripts', 'detect-environment-contract.cjs'));

const {
  resolveSquadWorkspaceReadiness,
} = require(path.join(ROOT, 'workspace', 'scripts', 'resolve-squad-workspace-readiness.cjs'));

function parseList(value) {
  return String(value || '')
    .split(',')
    .map((item) => item.trim())
    .filter(Boolean);
}

function uniq(items) {
  return [...new Set((items || []).filter(Boolean))];
}

function toPosix(value) {
  return value.split(path.sep).join('/');
}

function relativeToRoot(targetPath) {
  return toPosix(path.relative(ROOT, targetPath));
}

function exists(relativePath) {
  return fs.existsSync(path.join(ROOT, relativePath));
}

function readYaml(filePath) {
  return yaml.load(fs.readFileSync(filePath, 'utf8')) || {};
}

function isYamlFile(filePath) {
  return /\.ya?ml$/i.test(filePath);
}

function isWithin(basePath, targetPath) {
  const relative = path.relative(basePath, targetPath);
  return relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative));
}

function resolveBusinessSelector(businessRoot, selector) {
  const absolutePath = path.resolve(businessRoot, selector);
  if (!isWithin(businessRoot, absolutePath)) {
    return null;
  }
  return absolutePath;
}

function collectYamlFiles(directoryPath) {
  const files = [];
  if (!fs.existsSync(directoryPath)) {
    return files;
  }

  const stat = fs.statSync(directoryPath);
  if (stat.isFile()) {
    return isYamlFile(directoryPath) ? [directoryPath] : [];
  }

  for (const entry of fs.readdirSync(directoryPath, { withFileTypes: true })) {
    if (entry.name.startsWith('.')) {
      continue;
    }
    const absolutePath = path.join(directoryPath, entry.name);
    if (entry.isDirectory()) {
      files.push(...collectYamlFiles(absolutePath));
      continue;
    }
    if (entry.isFile() && isYamlFile(entry.name)) {
      files.push(absolutePath);
    }
  }

  return files.sort((left, right) => left.localeCompare(right));
}

function inferDocumentScope(businessRelativePath) {
  const parts = businessRelativePath.split('/').filter(Boolean);
  if (parts[0] === 'L3-product' && parts[1]) {
    return `L3-product/${parts[1]}`;
  }
  if (parts[0] === 'L2-tactical' && parts[1] === 'movement') {
    return parts[2] ? `L2-tactical/movement/${parts[2]}` : 'L2-tactical/movement';
  }
  return parts[0] || 'business';
}

function inferTitle(document, businessRelativePath) {
  const metadata = document && typeof document === 'object' ? document.metadata || {} : {};
  return (
    metadata.title ||
    metadata.product_name ||
    metadata.company_name ||
    metadata.name ||
    document?.title ||
    document?.name ||
    path.basename(businessRelativePath, path.extname(businessRelativePath))
  );
}

function buildBusinessSummary(businessSlug) {
  const companyDnaPath = path.join(ROOT, 'workspace', 'businesses', businessSlug, 'L0-identity', 'company-dna.yaml');
  if (!fs.existsSync(companyDnaPath)) {
    return {
      company_name: null,
      one_liner: null,
    };
  }

  const companyDna = readYaml(companyDnaPath);
  return {
    company_name:
      companyDna?.metadata?.company_name ||
      companyDna?.company_essence?.trade_name ||
      companyDna?.company_essence?.legal_name ||
      null,
    one_liner: companyDna?.company_essence?.one_liner || null,
  };
}

function buildSourceRecord({
  absolutePath,
  businessRoot,
  selectorOrigin,
  includeRaw,
}) {
  const relativeInsideBusiness = toPosix(path.relative(businessRoot, absolutePath));
  const relativePath = relativeToRoot(absolutePath);
  const document = readYaml(absolutePath);
  const metadata = document && typeof document === 'object' ? document.metadata || {} : {};

  return {
    id: relativeInsideBusiness.replace(/[^a-zA-Z0-9]+/g, '_').replace(/^_+|_+$/g, ''),
    path: relativePath,
    business_relative_path: relativeInsideBusiness,
    selector_origin: selectorOrigin,
    document_scope: inferDocumentScope(relativeInsideBusiness),
    title: inferTitle(document, relativeInsideBusiness),
    owner: metadata.owner || metadata.guardian || document?.owner || null,
    status: metadata.status || document?.status || null,
    version: metadata.version || null,
    last_updated: metadata.last_updated || metadata.updated_at || null,
    source_count: Array.isArray(metadata.sources) ? metadata.sources.length : 0,
    raw: includeRaw ? document : undefined,
  };
}

function loadWorkspaceConfig() {
  if (!exists(WORKSPACE_CONFIG_REL)) {
    return {};
  }

  return readYaml(path.join(ROOT, WORKSPACE_CONFIG_REL));
}

function safeResolveReadiness(business) {
  try {
    return resolveSquadWorkspaceReadiness({
      squad: 'squad-creator-pro',
      business,
      contextType: 'operations',
      format: 'json',
    });
  } catch (error) {
    return {
      status: 'blocked',
      reason: error.message,
      required_sources_loaded: [],
      missing_required_sources: [],
      canonical_config_paths: [],
    };
  }
}

async function buildBusinessSopContext(inputArgs = {}) {
  const args = {
    business: null,
    namespaces: [],
    paths: [],
    includeRaw: false,
    format: 'json',
    ...inputArgs,
  };

  if (!args.business) {
    throw new Error('load-business-sops requires --business=<slug>');
  }

  const selectors = {
    namespaces: uniq(args.namespaces),
    explicit_paths: uniq(args.paths),
  };

  const workspaceConfig = loadWorkspaceConfig();
  const businessRoot = path.join(ROOT, 'workspace', 'businesses', args.business);
  const businessRegistered = Boolean(
    Array.isArray(workspaceConfig?.businesses)
      ? workspaceConfig.businesses.find((b) => b.slug === args.business)
      : workspaceConfig?.businesses?.[args.business]
  );
  const readiness = safeResolveReadiness(args.business);
  const environment = await detectEnvironmentContract({
    root: ROOT,
    squad: 'squad-creator-pro',
    business: args.business,
    contextType: 'operations',
  });

  const blockers = [];
  const missingRequestedSources = [];

  if (selectors.namespaces.length === 0 && selectors.explicit_paths.length === 0) {
    blockers.push('At least one selector is required: --namespace=<dir> and/or --paths=<a,b>.');
  }
  if (!businessRegistered) {
    blockers.push(`Business "${args.business}" is not registered in workspace/_system/config.yaml.`);
  }
  if (!fs.existsSync(businessRoot)) {
    blockers.push(`Business workspace root is missing: workspace/businesses/${args.business}`);
  }
  if (readiness.status !== 'ready') {
    blockers.push(`COO readiness blocked: ${readiness.reason}`);
  }
  if (environment.runtime_mode !== 'full_workspace_mode') {
    blockers.push(`Environment runtime_mode is ${environment.runtime_mode}, expected full_workspace_mode`);
  }
  if (environment.source_of_truth !== 'workspace_canonical') {
    blockers.push(`Environment source_of_truth is ${environment.source_of_truth}, expected workspace_canonical`);
  }

  const resolvedFiles = new Map();

  if (fs.existsSync(businessRoot)) {
    for (const namespaceSelector of selectors.namespaces) {
      const resolvedPath = resolveBusinessSelector(businessRoot, namespaceSelector);
      if (!resolvedPath) {
        missingRequestedSources.push({
          selector_origin: 'namespace',
          selector: namespaceSelector,
          reason: 'Selector escapes workspace/business root.',
        });
        continue;
      }
      if (!fs.existsSync(resolvedPath)) {
        missingRequestedSources.push({
          selector_origin: 'namespace',
          selector: namespaceSelector,
          reason: 'Namespace path does not exist.',
        });
        continue;
      }

      const yamlFiles = collectYamlFiles(resolvedPath);
      if (yamlFiles.length === 0) {
        missingRequestedSources.push({
          selector_origin: 'namespace',
          selector: namespaceSelector,
          reason: 'Namespace contains no YAML files.',
        });
        continue;
      }

      for (const filePath of yamlFiles) {
        resolvedFiles.set(filePath, 'namespace');
      }
    }

    for (const explicitPath of selectors.explicit_paths) {
      const resolvedPath = resolveBusinessSelector(businessRoot, explicitPath);
      if (!resolvedPath) {
        missingRequestedSources.push({
          selector_origin: 'explicit_path',
          selector: explicitPath,
          reason: 'Path escapes workspace/business root.',
        });
        continue;
      }
      if (!fs.existsSync(resolvedPath) || !fs.statSync(resolvedPath).isFile()) {
        missingRequestedSources.push({
          selector_origin: 'explicit_path',
          selector: explicitPath,
          reason: 'Requested file does not exist.',
        });
        continue;
      }
      if (!isYamlFile(resolvedPath)) {
        missingRequestedSources.push({
          selector_origin: 'explicit_path',
          selector: explicitPath,
          reason: 'Requested file is not YAML.',
        });
        continue;
      }

      resolvedFiles.set(resolvedPath, 'explicit_path');
    }
  }

  if (missingRequestedSources.length > 0) {
    blockers.push('One or more requested SOP selectors could not be resolved under the business workspace root.');
  }

  const sources = [...resolvedFiles.entries()]
    .sort(([left], [right]) => left.localeCompare(right))
    .map(([absolutePath, selectorOrigin]) =>
      buildSourceRecord({
        absolutePath,
        businessRoot,
        selectorOrigin,
        includeRaw: args.includeRaw,
      })
    );

  if (sources.length === 0 && (selectors.namespaces.length > 0 || selectors.explicit_paths.length > 0)) {
    blockers.push('No YAML SOP sources were resolved from the requested selectors.');
  }

  return {
    business_sops: {
      generated_at: new Date().toISOString(),
      business_slug: args.business,
      coo_readiness_status: readiness.status,
      runtime_mode: environment.runtime_mode,
      source_of_truth: environment.source_of_truth,
      access_tier: environment.access_tier,
      selectors,
      blockers,
      readiness_reason: readiness.reason,
      business_summary: buildBusinessSummary(args.business),
      loaded_sources: {
        workspace: readiness.required_sources_loaded || [],
        sops: sources.map((source) => ({
          id: source.id,
          path: source.path,
          business_relative_path: source.business_relative_path,
          selector_origin: source.selector_origin,
          document_scope: source.document_scope,
          title: source.title,
          owner: source.owner,
          status: source.status,
          version: source.version,
          last_updated: source.last_updated,
          source_count: source.source_count,
        })),
      },
      missing_required_sources: readiness.missing_required_sources || [],
      missing_requested_sources: missingRequestedSources,
      environment_contract: {
        access_tier: environment.access_tier,
        runtime_mode: environment.runtime_mode,
        source_of_truth: environment.source_of_truth,
        reason: environment.reason,
        evidence_paths: environment.evidence_paths,
      },
      raw_documents: args.includeRaw
        ? Object.fromEntries(sources.map((source) => [source.business_relative_path, source.raw || null]))
        : undefined,
    },
  };
}

async function loadBusinessSops(inputArgs = {}) {
  const payload = await buildBusinessSopContext(inputArgs);
  if (payload.business_sops.blockers.length > 0) {
    const error = new Error('Workspace SOP package is not available for squad-creator-pro.');
    error.details = payload;
    throw error;
  }
  return payload;
}

function parseArgs(argv) {
  const args = {
    business: null,
    namespaces: [],
    paths: [],
    includeRaw: false,
    format: 'json',
  };

  for (const raw of argv) {
    if (raw.startsWith('--business=')) {
      args.business = raw.slice('--business='.length).trim() || null;
      continue;
    }
    if (raw.startsWith('--bu=')) {
      args.business = raw.slice('--bu='.length).trim() || null;
      continue;
    }
    if (raw.startsWith('--namespace=')) {
      args.namespaces.push(...parseList(raw.slice('--namespace='.length)));
      continue;
    }
    if (raw.startsWith('--paths=')) {
      args.paths.push(...parseList(raw.slice('--paths='.length)));
      continue;
    }
    if (raw === '--include-raw') {
      args.includeRaw = true;
      continue;
    }
    if (raw.startsWith('--format=')) {
      args.format = raw.slice('--format='.length).trim() || 'json';
    }
  }

  args.namespaces = uniq(args.namespaces);
  args.paths = uniq(args.paths);
  return args;
}

function printOutput(payload, format) {
  if (format === 'yaml') {
    process.stdout.write(yaml.dump(payload, { lineWidth: 120, noRefs: true, sortKeys: false }));
    return;
  }

  process.stdout.write(`${JSON.stringify(payload, null, 2)}\n`);
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  try {
    const payload = await loadBusinessSops(args);
    printOutput(payload, args.format);
  } catch (error) {
    if (error.details) {
      printOutput(error.details, args.format);
    } else {
      console.error(`ERROR: ${error.message}`);
    }
    process.exit(1);
  }
}

if (require.main === module) {
  main().catch((error) => {
    console.error(`ERROR: ${error.message}`);
    process.exit(1);
  });
}

module.exports = {
  buildBusinessSopContext,
  loadBusinessSops,
  parseArgs,
};
