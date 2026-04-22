#!/usr/bin/env node

const path = require('path');

module.exports = require(path.resolve(
  __dirname,
  '..',
  '..',
  '..',
  'squad-creator',
  'scripts',
  'lib',
  'squad-runtime-paths.cjs',
));
