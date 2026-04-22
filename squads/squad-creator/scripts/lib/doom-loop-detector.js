/**
 * doom-loop-detector.js
 *
 * Detects when a squad-creation pipeline step produces identical output
 * across consecutive iterations -- a "doom loop". Uses SHA-256 hashing
 * with a circular buffer of 10 entries per step.
 *
 * Stateful in-memory (Map). Does NOT persist between process restarts.
 * This is intentional: each pipeline run starts clean.
 *
 * Exports: checkDoomLoop, resetStep, resetAll
 *
 * [STORY-109.1] AC1, AC2, AC3
 */
'use strict';

const crypto = require('node:crypto');

/** @type {Map<string, string[]>} stepId -> circular buffer of hashes */
const _buffers = new Map();

const BUFFER_SIZE = 10;
const DEFAULT_THRESHOLD = 3; // consecutive identical hashes to trigger

/**
 * Hash an output string with SHA-256.
 * Fail-open: if hashing throws, return null so we skip detection.
 *
 * @param {string} output
 * @returns {string|null}
 */
function _hash(output) {
  try {
    return crypto.createHash('sha256').update(String(output)).digest('hex');
  } catch (_err) {
    return null;
  }
}

/**
 * Count trailing consecutive occurrences of `hash` in the buffer.
 *
 * @param {string[]} buffer
 * @param {string} hash
 * @returns {number}
 */
function _countConsecutive(buffer, hash) {
  let count = 0;
  for (let i = buffer.length - 1; i >= 0; i--) {
    if (buffer[i] === hash) {
      count++;
    } else {
      break;
    }
  }
  return count;
}

/**
 * Check whether a step is stuck in a doom loop.
 *
 * @param {string} stepId    - Unique identifier for the pipeline step.
 * @param {string} output    - The raw output text from this iteration.
 * @param {object} [options]
 * @param {number} [options.threshold] - Consecutive identical count to trigger
 *                                        (default: 3).
 * @returns {{ detected: boolean, consecutive_count: number, action: string }}
 */
function checkDoomLoop(stepId, output, options) {
  const threshold = (options && options.threshold) || DEFAULT_THRESHOLD;

  const hash = _hash(output);

  // Fail-open: if we cannot hash, report no doom loop (AC3)
  if (hash === null) {
    return { detected: false, consecutive_count: 0, action: 'continue' };
  }

  // Get or create the circular buffer for this step
  if (!_buffers.has(stepId)) {
    _buffers.set(stepId, []);
  }
  const buffer = _buffers.get(stepId);

  // Push and trim to BUFFER_SIZE (circular)
  buffer.push(hash);
  if (buffer.length > BUFFER_SIZE) {
    buffer.shift();
  }

  const consecutive = _countConsecutive(buffer, hash);
  const detected = consecutive >= threshold;

  let action = 'continue';
  if (detected) {
    action = 'break_loop';
  } else if (consecutive >= threshold - 1) {
    action = 'warn';
  }

  return { detected, consecutive_count: consecutive, action };
}

/**
 * Reset the buffer for a single step.
 *
 * @param {string} stepId
 */
function resetStep(stepId) {
  _buffers.delete(stepId);
}

/**
 * Reset all buffers. Call between pipeline runs to free memory.
 */
function resetAll() {
  _buffers.clear();
}

module.exports = { checkDoomLoop, resetStep, resetAll };
