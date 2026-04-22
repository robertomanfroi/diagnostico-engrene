#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

const {
  buildBusinessSopContext,
  loadBusinessSops,
} = require(path.resolve(
  __dirname,
  '..',
  'load-business-sops.cjs'
));

const ROOT = path.resolve(__dirname, '..', '..', '..', '..');

function assert(condition, message, details = {}) {
  if (!condition) {
    const error = new Error(message);
    error.details = details;
    throw error;
  }
}

function listDirectories(directoryPath) {
  if (!fs.existsSync(directoryPath)) {
    return [];
  }

  return fs.readdirSync(directoryPath, { withFileTypes: true })
    .filter((entry) => entry.isDirectory() && !entry.name.startsWith('.'))
    .map((entry) => entry.name)
    .sort((left, right) => left.localeCompare(right));
}

async function findBusinessFixture() {
  const businessesRoot = path.join(ROOT, 'workspace', 'businesses');

  for (const business of listDirectories(businessesRoot)) {
    const businessRoot = path.join(businessesRoot, business);
    const teamStructureAbs = path.join(businessRoot, 'L1-strategy', 'team-structure.yaml');
    if (!fs.existsSync(teamStructureAbs)) {
      continue;
    }

    const productsRoot = path.join(businessRoot, 'L3-product');
    for (const product of listDirectories(productsRoot)) {
      const offerbookRel = `L3-product/${product}/offerbook.yaml`;
      const offerbookAbs = path.join(businessRoot, offerbookRel);
      if (!fs.existsSync(offerbookAbs)) {
        continue;
      }

      try {
        await loadBusinessSops({
          business,
          namespaces: ['L1-strategy'],
        });

        return {
          business,
          product,
          teamStructurePath: `workspace/businesses/${business}/L1-strategy/team-structure.yaml`,
          offerbookPath: `workspace/businesses/${business}/${offerbookRel}`,
        };
      } catch {
        continue;
      }
    }
  }

  throw new Error('No business fixture found with ready operations context and product offerbook.');
}

async function main() {
  const fixture = await findBusinessFixture();

  const operationsPayload = await loadBusinessSops({
    business: fixture.business,
    namespaces: ['L1-strategy'],
  });

  assert(
    operationsPayload.business_sops.runtime_mode === 'full_workspace_mode',
    'operations package should require full_workspace_mode',
    operationsPayload
  );
  assert(
    operationsPayload.business_sops.source_of_truth === 'workspace_canonical',
    'operations package should use workspace_canonical as source of truth',
    operationsPayload
  );
  assert(
    operationsPayload.business_sops.loaded_sources.sops.some(
      (source) => source.path === fixture.teamStructurePath
    ),
    'operations package should include team-structure.yaml',
    operationsPayload
  );

  const mixedPayload = await loadBusinessSops({
    business: fixture.business,
    namespaces: ['L1-strategy'],
    paths: [`L3-product/${fixture.product}/offerbook.yaml`],
  });

  assert(
    mixedPayload.business_sops.loaded_sources.sops.some(
      (source) => source.path === fixture.offerbookPath
    ),
    'mixed package should include the explicitly requested product offerbook',
    mixedPayload
  );
  assert(
    mixedPayload.business_sops.loaded_sources.sops.some(
      (source) =>
        source.path === fixture.offerbookPath &&
        source.selector_origin === 'explicit_path'
    ),
    'explicit product offerbook should preserve selector_origin',
    mixedPayload
  );

  const missingSelectorPayload = await buildBusinessSopContext({
    business: fixture.business,
  });
  assert(
    missingSelectorPayload.business_sops.blockers.some((item) => item.includes('At least one selector is required')),
    'missing selectors should block the loader',
    missingSelectorPayload
  );

  const missingFilePayload = await buildBusinessSopContext({
    business: fixture.business,
    paths: ['L1-strategy/does-not-exist.yaml'],
  });
  assert(
    missingFilePayload.business_sops.missing_requested_sources.length === 1,
    'missing explicit path should be reported',
    missingFilePayload
  );
  assert(
    missingFilePayload.business_sops.blockers.some((item) => item.includes('requested SOP selectors')),
    'missing explicit path should block package creation',
    missingFilePayload
  );

  console.log('PASS: load-business-sops tests passed');
}

main().catch((error) => {
  console.error('ERROR: load-business-sops test failed');
  console.error(error.message);
  if (error.details) {
    console.error(JSON.stringify(error.details, null, 2));
  }
  process.exit(1);
});
