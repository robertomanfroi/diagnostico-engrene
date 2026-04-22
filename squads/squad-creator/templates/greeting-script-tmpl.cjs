#!/usr/bin/env node

/**
 * generate-{{SQUAD_NAME}}-greeting.cjs
 *
 * Greeting determinístico para {{ENTRY_AGENT}}.
 * Padrão: GREETING-CONTINUITY-001
 *
 * Uso:
 *   node squads/{{SQUAD_NAME}}/scripts/generate-{{SQUAD_NAME}}-greeting.cjs
 */

const fs = require('fs');
const path = require('path');

let yaml;
try {
  yaml = require('js-yaml');
} catch {
  console.error('ERROR: js-yaml not found.');
  process.exit(1);
}

const ROOT = process.cwd();
const SQUAD_NAME = '{{SQUAD_NAME}}';
const ENTRY_AGENT = '{{ENTRY_AGENT}}';
const SQUAD_DIR = path.join(ROOT, 'squads', SQUAD_NAME);

// ========================================================================
// HELPERS
// ========================================================================

function loadYaml(filePath) {
  if (!fs.existsSync(filePath)) return null;
  try {
    return yaml.load(fs.readFileSync(filePath, 'utf8')) || {};
  } catch { return null; }
}

function fileExists(relativePath) {
  return fs.existsSync(path.join(ROOT, relativePath));
}

// ========================================================================
// DATA COLLECTION (deterministic, no LLM)
// ========================================================================

function collectContext() {
  const context = {
    squad_name: SQUAD_NAME,
    entry_agent: ENTRY_AGENT,
    config: loadYaml(path.join(SQUAD_DIR, 'config.yaml')),
    // {{CONTEXT_SOURCES}}
    // Add squad-specific data collection here:
    // - Workspace state (businesses, diagnostics)
    // - Runtime state (session context, active state)
    // - Backlog state (pending items)
    // - Domain-specific signals
  };

  return context;
}

// ========================================================================
// NEXT ACTION INFERENCE (deterministic heuristics)
// ========================================================================

/**
 * Gap Map — Heurística de prioridade:
 *   P1: Gap bloqueante → remediação
 *   P2: Gap não-bloqueante → completude
 *   P3: Intake → comando principal do squad
 *
 * REGRA: Se blocker existe, NUNCA sugerir CTA genérico.
 */
function inferNextAction(context) {
  // {{GAP_MAP}}

  // P1: Blocking gaps
  // Example:
  // if (!context.some_critical_thing) {
  //   return {
  //     action: '*fix-critical-thing',
  //     reason: 'Critical thing is missing.',
  //     severity: 'blocking'
  //   };
  // }

  // P2: Non-blocking gaps
  // Example:
  // if (context.incomplete_but_usable) {
  //   return {
  //     action: '*show-context',
  //     reason: 'Context loaded but incomplete.',
  //     severity: 'non_blocking'
  //   };
  // }

  // P3: Intake (everything ready)
  return {
    action: '*help',
    reason: 'Descreva sua necessidade.',
    severity: 'intake'
  };
}

// ========================================================================
// GREETING BUILDER
// ========================================================================

function buildGreeting(context, nextAction) {
  const lines = [];

  // {{GREETING_SECTIONS}}
  // Add squad-specific context sections here:
  // - Active context display (business, product, campaign, DS, etc.)
  // - Backlog/diagnostic summary
  // - Status indicators

  // Commands table
  lines.push('## Comandos');
  lines.push('');
  lines.push('| Comando | Descrição |');
  lines.push('|---------|-----------|');
  // {{COMMANDS_TABLE}}
  // Fill from entry_agent commands
  lines.push('| `*help` | Todos os comandos |');
  lines.push('');

  // Next Action CTA (MANDATORY — GREETING-CONTINUITY-001)
  const icons = { blocking: '🔴', non_blocking: '🟡', intake: '🔵', ready: '🟢' };
  lines.push(`**Next Action:** ${icons[nextAction.severity] || '⚪'} \`${nextAction.action}\``);
  lines.push(`> ${nextAction.reason}`);

  return lines.join('\n');
}

// ========================================================================
// RUNTIME DIRECTIVES
// ========================================================================

function buildDirectives(context, nextAction) {
  return [
    `<!-- {{RUNTIME_DIRECTIVES_PREFIX}}_RUNTIME_DIRECTIVES`,
    `squad: "${SQUAD_NAME}"`,
    `entry_agent: "${ENTRY_AGENT}"`,
    `next_action: "${nextAction.action}"`,
    `next_action_severity: "${nextAction.severity}"`,
    `next_action_reason: "${nextAction.reason}"`,
    '-->'
  ].join('\n');
}

// ========================================================================
// MAIN
// ========================================================================

function main() {
  const context = collectContext();
  const nextAction = inferNextAction(context);
  const directives = buildDirectives(context, nextAction);
  const greeting = buildGreeting(context, nextAction);

  console.log(directives);
  console.log('');
  console.log(greeting);
}

main();
