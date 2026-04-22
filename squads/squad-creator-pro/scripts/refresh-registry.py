#!/usr/bin/env python3
"""
Squad Registry Refresh Script

Deterministic operations for updating squad-registry.yaml:
- Scan squads/ directory
- Count components (agents, tasks, workflows, etc.)
- Read config.yaml metadata
- Update registry with factual data

LLM handles (non-deterministic):
- Extract keywords from README
- Infer domain category
- Generate highlights
- Generate example_use

Usage:
    python scripts/refresh-registry.py [--output json|yaml] [--squads-path PATH]
"""

import os
import sys
import yaml
import json
import glob
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Any, Optional


def get_squads_path() -> Path:
    """Get the squads directory path"""
    # Try to find squads/ relative to script location
    script_dir = Path(__file__).parent.parent.parent  # squads/squad-creator-pro/scripts -> squads
    if (script_dir / "squad-creator").exists():
        return script_dir

    # Fallback to current directory
    cwd = Path.cwd()
    if (cwd / "squads").exists():
        return cwd / "squads"
    elif cwd.name == "squads":
        return cwd

    raise FileNotFoundError("Could not find squads/ directory")


def count_files(directory: Path, patterns: List[str]) -> int:
    """Count files matching patterns in directory"""
    count = 0
    for pattern in patterns:
        count += len(list(directory.glob(pattern)))
    return count


def read_config_yaml(squad_path: Path) -> Optional[Dict]:
    """Read and parse config.yaml from squad"""
    config_file = squad_path / "config.yaml"
    if not config_file.exists():
        return None

    try:
        with open(config_file, 'r', encoding='utf-8') as f:
            return yaml.safe_load(f)
    except Exception as e:
        print(f"Warning: Could not parse {config_file}: {e}", file=sys.stderr)
        return None


def list_agents(squad_path: Path) -> List[str]:
    """List all agent names in a squad"""
    agents_dir = squad_path / "agents"
    if not agents_dir.exists():
        return []

    agents = []
    for f in agents_dir.glob("*.md"):
        # Skip templates and READMEs
        if f.name.lower() in ['readme.md', 'template.md']:
            continue
        agents.append(f.stem)
    return agents


def _collect_agents(config: Dict) -> List[Dict]:
    """Collect agent dicts from various config.yaml formats.

    Supports:
    - agents: [{id: x, ...}]           — list of agent dicts (most common)
    - agents: {specialists: [{id: x}]} — nested dict with specialist lists
    - component.agents: [...]          — component-style references
    - tier_system.tier_N.agents: [...]  — tier-based nested agents
    - Deep recursive search for executor_profile in nested structures
    """
    collected = []

    agents_val = config.get("agents", None)

    if isinstance(agents_val, list):
        collected.extend(a for a in agents_val if isinstance(a, dict))

    elif isinstance(agents_val, dict):
        for key, val in agents_val.items():
            if isinstance(val, list):
                collected.extend(a for a in val if isinstance(a, dict))
            elif isinstance(val, dict) and "executor_profile" in val:
                if "id" not in val:
                    val["id"] = key
                collected.append(val)

    # Try component.agents pattern
    component = config.get("component", config.get("components", {}))
    if isinstance(component, dict):
        comp_agents = component.get("agents", [])
        if isinstance(comp_agents, list):
            collected.extend(a for a in comp_agents if isinstance(a, dict))

    # Recursively search tier_system and other nested structures for agents with executor_profile
    _deep_collect_agents(config, collected, depth=0)

    # Deduplicate by agent id
    seen_ids = set()
    unique = []
    for a in collected:
        aid = a.get("id", id(a))
        if aid not in seen_ids:
            seen_ids.add(aid)
            unique.append(a)

    return unique


def _deep_collect_agents(obj: Any, collected: List[Dict], depth: int = 0) -> None:
    """Recursively search nested structures for agent dicts with executor_profile."""
    if depth > 5:  # Prevent infinite recursion
        return

    if isinstance(obj, dict):
        # If this dict has executor_profile and an id (or agent field), it's an agent
        if "executor_profile" in obj and ("id" in obj or "agent" in obj):
            agent = dict(obj)
            if "id" not in agent and "agent" in agent:
                agent["id"] = agent["agent"]
            collected.append(agent)
            return

        # Recurse into all dict values
        for key, val in obj.items():
            if key in ("executor_profile",):  # Don't recurse into profile itself
                continue
            _deep_collect_agents(val, collected, depth + 1)

    elif isinstance(obj, list):
        for item in obj:
            _deep_collect_agents(item, collected, depth + 1)


def extract_executor_profiles(config: Optional[Dict]) -> Dict[str, Any]:
    """Extract executor_profile data from config.yaml agents section.

    Returns:
        Dict with executor_capable_agents, executor_reviewers, and
        aggregated_work_contexts extracted from agent executor_profiles.
    """
    result = {
        "executor_capable_agents": [],
        "executor_reviewers": [],
        "aggregated_work_contexts": [],
    }

    if not config:
        return result

    # Collect agent dicts from various config formats
    agent_list = _collect_agents(config)

    all_work_contexts = set()

    for agent in agent_list:
        if not isinstance(agent, dict):
            continue

        profile = agent.get("executor_profile")
        if not profile or not isinstance(profile, dict):
            continue

        agent_id = agent.get("id", "unknown")
        story_role = profile.get("story_role", "")
        can_execute = profile.get("can_execute", False)
        fw_type = profile.get("fw_type", "Agent")
        work_contexts = profile.get("work_contexts", [])
        core_replaces = profile.get("core_replaces")
        can_review = profile.get("can_review", [])

        if can_execute and story_role == "executor":
            result["executor_capable_agents"].append({
                "id": agent_id,
                "story_role": story_role,
                "fw_type": fw_type,
                "work_contexts": work_contexts if isinstance(work_contexts, list) else [],
                "core_replaces": core_replaces,
                "can_review": can_review if isinstance(can_review, list) else [],
            })
            if isinstance(work_contexts, list):
                all_work_contexts.update(work_contexts)

        if can_review and isinstance(can_review, list) and len(can_review) > 0:
            if story_role in ("reviewer", "consultant") or (story_role == "executor" and not can_execute):
                result["executor_reviewers"].append({
                    "id": agent_id,
                    "can_review": can_review,
                })

    result["aggregated_work_contexts"] = sorted(all_work_contexts)
    return result


def scan_squad(squad_path: Path) -> Dict[str, Any]:
    """Scan a single squad and extract deterministic data"""
    squad_name = squad_path.name

    # Read config.yaml
    config = read_config_yaml(squad_path)

    # Count components
    counts = {
        "agents": count_files(squad_path / "agents", ["*.md"]) if (squad_path / "agents").exists() else 0,
        "tasks": count_files(squad_path / "tasks", ["*.md"]) if (squad_path / "tasks").exists() else 0,
        "workflows": count_files(squad_path / "workflows", ["*.md", "*.yaml"]) if (squad_path / "workflows").exists() else 0,
        "templates": count_files(squad_path / "templates", ["*.md", "*.yaml"]) if (squad_path / "templates").exists() else 0,
        "checklists": count_files(squad_path / "checklists", ["*.md"]) if (squad_path / "checklists").exists() else 0,
        "data_files": count_files(squad_path / "data", ["*.md", "*.yaml"]) if (squad_path / "data").exists() else 0,
    }

    # List agent names
    agent_names = list_agents(squad_path)

    # Check for key files
    has_readme = (squad_path / "README.md").exists()
    has_changelog = (squad_path / "CHANGELOG.md").exists()

    # Extract executor profiles from config.yaml (Story 45.1)
    executor_data = extract_executor_profiles(config)

    # Warn if no executor_profile found
    if config and not executor_data["executor_capable_agents"]:
        print(f"Warning: {squad_name} has no executor_profile in config.yaml", file=sys.stderr)

    # Build result
    result = {
        "name": squad_name,
        "path": f"squads/{squad_name}/",
        "has_config": config is not None,
        "config": {
            "name": config.get("name", squad_name) if config else squad_name,
            "version": config.get("version", "unknown") if config else "unknown",
            "short_title": config.get("short-title", "") if config else "",
            "description": config.get("description", "") if config else "",
            "slashPrefix": config.get("slashPrefix", "") if config else "",
        },
        "counts": counts,
        "agent_names": agent_names,
        "has_readme": has_readme,
        "has_changelog": has_changelog,
        "total_components": sum(counts.values()),
        "executor_data": executor_data,
    }

    return result


def scan_all_squads(squads_path: Path) -> Dict[str, Any]:
    """Scan all squads in the squads/ directory"""
    results = {
        "metadata": {
            "scan_date": datetime.now().isoformat(),
            "squads_path": str(squads_path),
            "total_squads": 0,
        },
        "squads": {},
        "summary": {
            "total_agents": 0,
            "total_tasks": 0,
            "total_workflows": 0,
            "total_templates": 0,
            "total_checklists": 0,
            "total_data_files": 0,
        }
    }

    # Directories to skip
    skip_dirs = {'.DS_Store', '__pycache__', 'node_modules', '.git', 'artifacts'}

    # Scan each directory in squads/
    for item in sorted(squads_path.iterdir()):
        if not item.is_dir():
            continue
        if item.name in skip_dirs:
            continue
        if item.name.startswith('.'):
            continue

        # Check if it's a valid squad (has config.yaml or agents/)
        has_config = (item / "config.yaml").exists()
        has_agents = (item / "agents").exists()

        if not (has_config or has_agents):
            continue

        # Scan the squad
        squad_data = scan_squad(item)
        results["squads"][item.name] = squad_data

        # Update summary
        results["summary"]["total_agents"] += squad_data["counts"]["agents"]
        results["summary"]["total_tasks"] += squad_data["counts"]["tasks"]
        results["summary"]["total_workflows"] += squad_data["counts"]["workflows"]
        results["summary"]["total_templates"] += squad_data["counts"]["templates"]
        results["summary"]["total_checklists"] += squad_data["counts"]["checklists"]
        results["summary"]["total_data_files"] += squad_data["counts"]["data_files"]

    results["metadata"]["total_squads"] = len(results["squads"])

    return results


def format_for_registry(scan_results: Dict) -> Dict:
    """Format scan results for squad-registry.yaml structure"""
    registry = {
        "metadata": {
            "version": "1.0.0",
            "last_updated": datetime.now().strftime("%Y-%m-%d"),
            "total_squads": scan_results["metadata"]["total_squads"],
            "maintainer": "squad-creator",
            "generated_by": "scripts/refresh-registry.py",
        },
        "squads": {},
        "summary": scan_results["summary"],
    }

    for name, data in scan_results["squads"].items():
        squad_entry = {
            "path": data["path"],
            "version": data["config"]["version"],
            "description": data["config"]["description"],
            "slashPrefix": data["config"]["slashPrefix"],
            "counts": data["counts"],
            "agent_names": data["agent_names"],
            "has_readme": data["has_readme"],
            "has_changelog": data["has_changelog"],
            # These fields need LLM to populate:
            "domain": "_TO_BE_INFERRED_",
            "keywords": [],
            "highlights": [],
            "example_use": "",
        }

        # Include executor_profile data if available (Story 45.1)
        executor_data = data.get("executor_data", {})
        if executor_data.get("executor_capable_agents"):
            squad_entry["executor_capable_agents"] = executor_data["executor_capable_agents"]
        if executor_data.get("executor_reviewers"):
            squad_entry["executor_reviewers"] = executor_data["executor_reviewers"]
        if executor_data.get("aggregated_work_contexts"):
            squad_entry["aggregated_work_contexts"] = executor_data["aggregated_work_contexts"]

        registry["squads"][name] = squad_entry

    return registry


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Scan squads and generate registry data")
    parser.add_argument("--output", choices=["json", "yaml", "summary"], default="yaml",
                        help="Output format")
    parser.add_argument("--squads-path", type=Path, default=None,
                        help="Path to squads/ directory")
    parser.add_argument("--registry-format", action="store_true",
                        help="Output in squad-registry.yaml format")

    args = parser.parse_args()

    # Find squads path
    try:
        squads_path = args.squads_path or get_squads_path()
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    # Scan all squads
    results = scan_all_squads(squads_path)

    # Format output
    if args.registry_format:
        results = format_for_registry(results)

    # Output (force UTF-8 on Windows)
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')

    if args.output == "json":
        print(json.dumps(results, indent=2, ensure_ascii=False))
    elif args.output == "yaml":
        print(yaml.dump(results, allow_unicode=True, default_flow_style=False, sort_keys=False))
    elif args.output == "summary":
        print(f"Squad Registry Scan Results")
        print(f"===========================")
        print(f"Scan Date: {results['metadata']['scan_date']}")
        print(f"Total Squads: {results['metadata']['total_squads']}")
        print()
        print(f"Component Totals:")
        for key, value in results['summary'].items():
            print(f"  {key}: {value}")
        print()
        print(f"Squads Found:")
        for name, data in sorted(results['squads'].items()):
            agents = data['counts']['agents']
            tasks = data['counts']['tasks']
            print(f"  {name}: {agents} agents, {tasks} tasks")


if __name__ == "__main__":
    main()
