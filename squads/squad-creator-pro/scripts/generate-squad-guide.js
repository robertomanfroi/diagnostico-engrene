#!/usr/bin/env node

const path = require('path');

const BASE_SCRIPT = path.resolve(
  __dirname,
  '..',
  '..',
  'squad-creator',
  'scripts',
  'generate-squad-guide.js',
);

const base = require(BASE_SCRIPT);

if (require.main === module) {
  const squadName = process.argv[2];

  if (!squadName) {
    console.error(
      'Usage: node squads/squad-creator-pro/scripts/generate-squad-guide.js <squad-name>',
    );
    process.exit(1);
  }

  base.generateSquadGuide(squadName)
    .then((guide) => {
      console.log(guide);
      process.exit(0);
    })
    .catch((error) => {
      console.error('Error:', error.message);
      console.log(base.generateFallbackGuide());
      process.exit(1);
    });
}

module.exports = base;
