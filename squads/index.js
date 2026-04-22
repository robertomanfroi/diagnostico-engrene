/**
 * Pro Squads Module
 *
 * Example module demonstrating feature gate integration pattern.
 * This pattern should be followed by all pro modules.
 *
 * Usage:
 *   const { PremiumSquads } = require('@aios-fullstack/pro/squads');
 *
 *   // The module will throw ProFeatureError if not licensed
 *   const squads = new PremiumSquads();
 *
 * @module pro/squads
 * @see ADR-PRO-003 - Feature Gating & Licensing
 * @see Story PRO-6 - License Key & Feature Gating System
 */

'use strict';

const { featureGate, ProFeatureError } = require('../license');

/**
 * Premium Squads - Example pro module with feature gating.
 *
 * This class demonstrates the recommended pattern for pro modules:
 *
 * 1. Check feature availability in constructor
 * 2. Use featureGate.require() for hard requirements
 * 3. Use featureGate.isAvailable() for optional enhancements
 * 4. Provide graceful fallbacks where appropriate
 */
class PremiumSquads {
  /**
   * Create PremiumSquads instance.
   *
   * @throws {ProFeatureError} If pro.squads.premium is not licensed
   */
  constructor() {
    // PATTERN 1: Hard requirement - throw if not available
    // Use this for features that cannot work without a license
    featureGate.require('pro.squads.premium', 'Premium Squads');

    this._initialized = true;
  }

  /**
   * List available squad templates.
   *
   * @returns {string[]} Array of template names
   */
  listTemplates() {
    const templates = ['basic', 'standard', 'advanced'];

    // PATTERN 2: Optional enhancement - check availability
    // Use this to enable additional features when licensed
    if (featureGate.isAvailable('pro.squads.marketplace')) {
      templates.push('marketplace-template-1', 'marketplace-template-2');
    }

    return templates;
  }

  /**
   * Export squad configuration.
   *
   * @param {string} squadName - Name of the squad to export
   * @returns {{ name: string, config: object }}
   * @throws {ProFeatureError} If export feature is not licensed
   */
  exportSquad(squadName) {
    // PATTERN 3: Per-method requirement
    // Use this when specific methods require additional features
    featureGate.require('pro.squads.export', 'Squad Export');

    return {
      name: squadName,
      config: {
        /* squad configuration */
      },
      exportedAt: new Date().toISOString(),
      exportedBy: 'AIOS Pro',
    };
  }

  /**
   * Check if custom squads are available.
   *
   * @returns {boolean}
   */
  hasCustomSquads() {
    // PATTERN 4: Feature availability check for conditional UI
    // Use this to show/hide UI elements based on license
    return featureGate.isAvailable('pro.squads.custom');
  }
}

/**
 * Create a premium squad with license check.
 *
 * This is a factory function pattern alternative to class constructor.
 *
 * @param {object} config - Squad configuration
 * @returns {object} Squad instance
 * @throws {ProFeatureError} If not licensed
 */
function createPremiumSquad(config) {
  // Factory function pattern
  featureGate.require('pro.squads.premium', 'Premium Squads');

  return {
    name: config.name || 'Unnamed Squad',
    type: 'premium',
    config,
    createdAt: new Date().toISOString(),
  };
}

/**
 * Conditionally load premium features.
 *
 * This pattern allows core code to conditionally use pro features
 * without throwing errors.
 *
 * @returns {object|null} Premium features or null if not available
 */
function loadPremiumFeaturesIfAvailable() {
  // PATTERN 5: Conditional loading
  // Use this in core code to optionally enhance with pro features
  if (!featureGate.isAvailable('pro.squads.premium')) {
    return null;
  }

  return {
    premiumSquads: new PremiumSquads(),
    hasExport: featureGate.isAvailable('pro.squads.export'),
    hasCustom: featureGate.isAvailable('pro.squads.custom'),
    hasMarketplace: featureGate.isAvailable('pro.squads.marketplace'),
  };
}

module.exports = {
  PremiumSquads,
  createPremiumSquad,
  loadPremiumFeaturesIfAvailable,
};
