#!/usr/bin/env node

const path = require('path');
const yaml = require('js-yaml');

const BASE_SCRIPT = path.resolve(
  __dirname,
  '..',
  '..',
  'squad-creator',
  'scripts',
  'detect-environment-contract.cjs',
);

const base = require(BASE_SCRIPT);

if (require.main === module) {
  const args = base.parseArgs(process.argv.slice(2));

  base.detectEnvironmentContract(args)
    .then((output) => {
      if (args.format === 'yaml') {
        process.stdout.write(
          yaml.dump(output, { lineWidth: 120, noRefs: true, sortKeys: false }),
        );
        return;
      }

      process.stdout.write(`${JSON.stringify(output, null, 2)}\n`);
    })
    .catch((error) => {
      console.error(`ERROR: ${error.message}`);
      process.exit(1);
    });
}

module.exports = base;
