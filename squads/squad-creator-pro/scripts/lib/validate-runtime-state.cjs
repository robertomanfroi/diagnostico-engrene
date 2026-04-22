#!/usr/bin/env node

const path = require('path');

require(path.resolve(
  __dirname,
  '..',
  '..',
  '..',
  'squad-creator',
  'scripts',
  'lib',
  'validate-runtime-state.cjs',
));
