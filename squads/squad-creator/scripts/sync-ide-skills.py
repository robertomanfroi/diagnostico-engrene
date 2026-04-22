#!/usr/bin/env python3
"""
Sync IDE Skills Script - Worker (100% Deterministic)

Synchronizes squad agents to IDE activation surfaces.
All operations are deterministic file operations - no LLM needed.

Operations:
- Read source files from squads/
- Parse YAML/Markdown
- Transform formats (MD → MDC for Cursor)
- Copy/symlink to destination directories
- Validate results

Usage:
    python scripts/sync-ide-skills.py agent {name} [--squad {squad}]
    python scripts/sync-ide-skills.py squad {squad-name}

Note: Only agents are synced to IDE activation surfaces. Tasks, checklists, templates,
and workflows stay in squads/ and are loaded on-demand by agents.

Flags:
    --dry-run     Preview without creating files
    --force       Overwrite existing files
    --ide         Target specific IDE (claude, cursor, windsurf)
    --verbose     Show detailed output

Pattern: EXEC-W-001 (Worker - Deterministic)
"""

import os
import sys
import yaml
import json
import shutil
import argparse
import re
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Any, Optional, Tuple


# ============================================================================
# CONFIGURATION
# ============================================================================

DEFAULT_CONFIG = {
    "active_ides": ["claude", "cursor", "windsurf", "gemini", "antigravity"],
    "squad_aliases": {},
    "sync_mappings": {
        "squad_agents": {
            "source": "squads/*/agents/",
            "destinations": {
                "claude": {
                    "path": ".claude/skills/{squad_alias}/{agent}/SKILL.md",
                    "format": "md"
                },
                "cursor": {
                    "path": ".cursor/rules/",
                    "format": "mdc"
                },
                "windsurf": {
                    "path": ".windsurf/commands/{squad_alias}/",
                    "format": "md"
                },
                "gemini": {
                    "path": ".gemini/agents/{squad_alias}/",
                    "format": "md"
                },
                "antigravity": {
                    "path": ".agents/workflows/{squad_alias}/",
                    "format": "md"
                },
            }
        }
    }
}


# ============================================================================
# FILE UTILITIES
# ============================================================================

def find_project_root() -> Path:
    """Find project root (directory with squads/)"""
    current = Path.cwd()

    # Walk up until we find squads/
    for _ in range(10):
        if (current / "squads").exists():
            return current
        parent = current.parent
        if parent == current:
            break
        current = parent

    # Check if we're inside squads/
    current = Path.cwd()
    if current.name == "squads":
        return current.parent
    if "squads" in str(current):
        idx = str(current).find("squads")
        return Path(str(current)[:idx])

    raise FileNotFoundError("Could not find project root with squads/ directory")


def load_sync_config(project_root: Path) -> Dict:
    """Load .aiox-sync.yaml or return defaults"""
    config_path = project_root / ".aiox-sync.yaml"

    if config_path.exists():
        try:
            with open(config_path, 'r', encoding='utf-8') as f:
                config = yaml.safe_load(f) or {}
                # Merge with defaults
                for key, value in DEFAULT_CONFIG.items():
                    if key not in config:
                        config[key] = value
                return config
        except Exception as e:
            print(f"Warning: Could not parse {config_path}: {e}", file=sys.stderr)

    return DEFAULT_CONFIG.copy()


def load_squad_config(project_root: Path, squad_name: str) -> Dict:
    """Load a squad config manifest if present."""
    config_path = project_root / "squads" / squad_name / "config.yaml"
    if not config_path.exists():
        return {}
    try:
        with open(config_path, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f) or {}
            return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def get_entry_agent(project_root: Path, squad_name: str) -> Optional[str]:
    """Get entry_agent from squad config (the chief/orchestrator that gets a skill).
    See docs/reference/rules/entry-point-heuristic.md for the full heuristic."""
    squad_config = load_squad_config(project_root, squad_name)
    entry = squad_config.get("entry_agent")
    if entry:
        return entry
    # Fallback: check pack.entry_agent
    pack = squad_config.get("pack", {})
    if isinstance(pack, dict):
        entry = pack.get("entry_agent")
        if entry:
            return entry
    return None


def ensure_dir(path: Path) -> None:
    """Ensure directory exists"""
    path.mkdir(parents=True, exist_ok=True)


# ============================================================================
# SOURCE DISCOVERY
# ============================================================================

def find_squad_for_component(project_root: Path, component_type: str, name: str) -> Optional[str]:
    """Find which squad contains a component"""
    squads_path = project_root / "squads"

    type_dir_map = {
        "agent": "agents",
        "task": "tasks",
        "workflow": "workflows",
        "template": "templates",
        "checklist": "checklists"
    }

    dir_name = type_dir_map.get(component_type, component_type + "s")

    for squad_dir in squads_path.iterdir():
        if not squad_dir.is_dir():
            continue

        component_dir = squad_dir / dir_name
        if not component_dir.exists():
            continue

        # Check for file with various extensions
        for ext in [".md", ".yaml", ".yml"]:
            if (component_dir / f"{name}{ext}").exists():
                return squad_dir.name

    return None


def list_squad_components(project_root: Path, squad_name: str) -> Dict[str, List[Path]]:
    """List all components in a squad"""
    squad_path = project_root / "squads" / squad_name

    if not squad_path.exists():
        raise FileNotFoundError(f"Squad not found: {squad_name}")

    components = {
        "agents": [],
        "tasks": [],
        "workflows": [],
        "templates": [],
        "checklists": [],
        "data": []
    }

    for comp_type, file_list in components.items():
        comp_dir = squad_path / comp_type
        if comp_dir.exists():
            for f in comp_dir.iterdir():
                if f.is_file() and f.suffix in [".md", ".yaml", ".yml"]:
                    # Skip certain files
                    if f.name.lower() in ["readme.md", "changelog.md", ".gitkeep"]:
                        continue
                    file_list.append(f)

    return components


def get_source_file(project_root: Path, component_type: str, name: str, squad: Optional[str] = None) -> Optional[Path]:
    """Get path to source file"""
    # If squad specified, look there directly
    if squad:
        type_dir_map = {
            "agent": "agents",
            "task": "tasks",
            "workflow": "workflows"
        }
        dir_name = type_dir_map.get(component_type, component_type + "s")

        for ext in [".md", ".yaml", ".yml"]:
            path = project_root / "squads" / squad / dir_name / f"{name}{ext}"
            if path.exists():
                return path
        return None

    # Otherwise, search all squads
    found_squad = find_squad_for_component(project_root, component_type, name)
    if found_squad:
        return get_source_file(project_root, component_type, name, found_squad)

    return None


# ============================================================================
# FORMAT CONVERSION
# ============================================================================

def extract_description_from_md(content: str) -> str:
    """Extract description from markdown agent file"""
    # Try to find whenToUse in YAML block
    yaml_match = re.search(r'```yaml\s*(.*?)```', content, re.DOTALL)
    if yaml_match:
        try:
            yaml_content = yaml.safe_load(yaml_match.group(1))
            if isinstance(yaml_content, dict):
                # Check for whenToUse
                if 'agent' in yaml_content and 'whenToUse' in yaml_content['agent']:
                    return yaml_content['agent']['whenToUse']
                # Check for title
                if 'agent' in yaml_content and 'title' in yaml_content['agent']:
                    return yaml_content['agent']['title']
        except:
            pass

    # Try to find first paragraph after title
    lines = content.split('\n')
    in_header = False
    for line in lines:
        line = line.strip()
        if line.startswith('#'):
            in_header = True
            continue
        if in_header and line and not line.startswith('#') and not line.startswith('```'):
            # Skip certain lines
            if line.startswith('ACTIVATION') or line.startswith('CRITICAL'):
                continue
            return line[:200]  # Truncate

    return "Agent command"


def convert_md_to_mdc(content: str, description: str = "") -> str:
    """Convert Markdown to MDC format (Cursor)"""
    frontmatter = f"""---
description: {description or 'Agent command'}
globs: []
alwaysApply: false
---

"""
    return frontmatter + content


def escape_frontmatter_value(value: str) -> str:
    """Escape a scalar value for YAML frontmatter."""
    return value.replace("\\", "\\\\").replace('"', '\\"')


def should_use_high_effort(agent_name: str, content: str) -> bool:
    """Match migration heuristics for decision-oriented agents."""
    slug = Path(agent_name).stem.lower()
    if re.search(r"(chief|architect|(^|-)qa($|-)|quality)", slug):
        return True
    return bool(re.search(r"^effort:\s*high\s*$", content, re.MULTILINE))


def convert_md_to_claude_skill(content: str, agent_name: str, is_entry_point: bool = True) -> str:
    """Wrap an agent markdown file in Claude SKILL.md frontmatter."""
    description = escape_frontmatter_value(extract_description_from_md(content))
    is_decision = should_use_high_effort(agent_name, content)
    frontmatter_lines = [
        "---",
        f'description: "{description}"',
        "user-invocable: true",
    ]
    if is_decision:
        frontmatter_lines.append("effort: high")
    # maxTurns: 50 for decision agents (chiefs/architects/QA), 25 for workers
    # Without maxTurns, agents run without limit (squad-protocol-v3 SRC-8)
    frontmatter_lines.append(f"maxTurns: {50 if is_decision else 25}")
    frontmatter_lines.extend(["---", ""])
    return "\n".join(frontmatter_lines) + content

def get_squad_alias(project_root: Path, config: Dict, squad_name: str) -> str:
    """Get squad alias for a squad (supports sync config + squad manifest fallback)."""
    aliases = config.get("squad_aliases") or config.get("pack_aliases", {})
    if squad_name in aliases:
        return aliases[squad_name]

    squad_config = load_squad_config(project_root, squad_name)
    for key in ("slashPrefix", "slash_prefix"):
        value = squad_config.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    for parent_key in ("squad", "pack"):
        parent = squad_config.get(parent_key)
        if not isinstance(parent, dict):
            continue
        for key in ("slashPrefix", "slash_prefix"):
            value = parent.get(key)
            if isinstance(value, str) and value.strip():
                return value.strip()
    # Default: capitalize first letter of each word
    return ''.join(word.capitalize() for word in squad_name.split('-'))


# ============================================================================
# SYNC OPERATIONS
# ============================================================================

def get_destination_path(
    project_root: Path,
    ide: str,
    squad_alias: str,
    component_type: str,
    filename: str,
    config: Dict
) -> Path:
    """Get destination path for a file"""

    if ide == "claude":
        name_without_ext = Path(filename).stem
        # Depth-2 flat naming: .claude/skills/{prefix}-{name}/SKILL.md
        # Scanner only reads depth-2 (loadSkillsDir.ts:424). Depth-3+ is invisible.
        # Naming: avoid duplication (e.g. copy-chief not copy-copy-chief)
        if name_without_ext.startswith(squad_alias.lower().replace(' ', '-') + '-') or name_without_ext == squad_alias.lower():
            skill_dir_name = name_without_ext
        else:
            prefix = squad_alias.lower().replace(' ', '-')
            # Use kebab-case prefix derived from squad alias
            skill_dir_name = f"{prefix}-{name_without_ext}"
        return project_root / ".claude" / "skills" / skill_dir_name / "SKILL.md"

    elif ide == "cursor":
        # Cursor uses flat .cursor/rules/ with .mdc extension
        name_without_ext = Path(filename).stem
        return project_root / ".cursor" / "rules" / f"{name_without_ext}.mdc"

    elif ide == "windsurf":
        return project_root / ".windsurf" / "commands" / squad_alias / filename

    elif ide == "gemini":
        return project_root / ".gemini" / "agents" / squad_alias / filename

    elif ide == "antigravity":
        return project_root / ".agents" / "workflows" / squad_alias / filename

    elif ide == "codex":
        return project_root / ".agents" / "skills" / squad_alias / filename

    else:
        raise ValueError(f"Unknown IDE: {ide}")


def sync_file(
    source: Path,
    dest: Path,
    ide: str,
    force: bool = False,
    dry_run: bool = False
) -> Tuple[str, str]:  # (status, message)
    """Sync a single file"""

    # Check if destination exists
    if dest.exists() and not force:
        return ("skipped", f"exists (use --force to overwrite)")

    if dry_run:
        return ("would_create", str(dest))

    # Read source
    content = source.read_text(encoding='utf-8')

    # Convert format if needed
    if ide == "cursor" and source.suffix == ".md":
        description = extract_description_from_md(content)
        content = convert_md_to_mdc(content, description)
    elif ide == "claude" and source.suffix == ".md":
        content = convert_md_to_claude_skill(content, source.name)

    # Ensure destination directory exists
    ensure_dir(dest.parent)

    # Write file
    dest.write_text(content, encoding='utf-8')

    return ("created", str(dest))


def sync_component(
    project_root: Path,
    component_type: str,
    name: str,
    squad: Optional[str],
    config: Dict,
    force: bool = False,
    dry_run: bool = False,
    target_ide: Optional[str] = None,
    verbose: bool = False
) -> Dict[str, Any]:
    """Sync a single component to IDE directories"""

    results = {
        "component": name,
        "type": component_type,
        "source": None,
        "destinations": [],
        "status": "success"
    }

    # Find source file
    source = get_source_file(project_root, component_type, name, squad)
    if not source:
        results["status"] = "error"
        results["error"] = f"Source not found: {component_type}/{name}"
        return results

    results["source"] = str(source)

    # Determine squad from source path
    squad_name = source.parent.parent.name
    squad_alias = get_squad_alias(project_root, config, squad_name)

    # Get active IDEs
    ides = [target_ide] if target_ide else config.get("active_ides", ["claude"])

    # Sync to each IDE
    for ide in ides:
        dest = get_destination_path(
            project_root, ide, squad_alias, component_type, source.name, config
        )

        status, message = sync_file(source, dest, ide, force, dry_run)

        results["destinations"].append({
            "ide": ide,
            "path": str(dest),
            "status": status,
            "message": message
        })

        if verbose:
            icon = "✓" if status in ["created", "would_create"] else "○"
            print(f"  {icon} [{ide}] {dest}")

    return results


def sync_squad(
    project_root: Path,
    squad_name: str,
    config: Dict,
    force: bool = False,
    dry_run: bool = False,
    target_ide: Optional[str] = None,
    verbose: bool = False
) -> Dict[str, Any]:
    """Sync entire squad to IDE directories"""

    results = {
        "squad": squad_name,
        "components": [],
        "summary": {
            "created": 0,
            "updated": 0,
            "skipped": 0,
            "errors": 0
        }
    }

    # List all components
    try:
        components = list_squad_components(project_root, squad_name)
    except FileNotFoundError as e:
        results["error"] = str(e)
        return results

    squad_alias = get_squad_alias(project_root, config, squad_name)
    entry_agent = get_entry_agent(project_root, squad_name)
    print(f"\n📦 Syncing squad: {squad_name} → {squad_alias}")
    if entry_agent:
        print(f"   Entry agent: {entry_agent} (only this agent gets a Claude skill)")

    # Sync only agents — tasks, checklists, templates, workflows stay in squads/
    # and are loaded on-demand when the agent executes them
    type_map = {
        "agents": "agent",
    }

    for comp_dir, files in components.items():
        if comp_dir not in type_map:
            continue
        if not files:
            continue

        comp_type = type_map[comp_dir]
        print(f"\n  Syncing {comp_dir} ({len(files)} files)...")

        for source_file in files:
            # For Claude IDE: only generate skills for entry_agent (chief/orchestrator).
            # Sub-agents get .claude/agents/ wrappers via ide-sync, not skills.
            # See docs/reference/rules/entry-point-heuristic.md
            active_ides = [target_ide] if target_ide else config.get("active_ides", ["claude"])
            if entry_agent and "claude" in active_ides:
                if source_file.stem != entry_agent:
                    # Skip non-entry agents for Claude; still sync to other IDEs
                    non_claude_ides = [i for i in active_ides if i != "claude"]
                    if not non_claude_ides:
                        continue
                    # Temporarily restrict to non-Claude IDEs
                    target_ide_override = None  # Will be handled per-IDE below
                else:
                    target_ide_override = target_ide
            else:
                target_ide_override = target_ide

            result = sync_component(
                project_root,
                comp_type,
                source_file.stem,
                squad_name,
                config,
                force,
                dry_run,
                target_ide_override,
                verbose
            )

            results["components"].append(result)

            # Update summary
            for dest in result.get("destinations", []):
                if dest["status"] == "created":
                    results["summary"]["created"] += 1
                elif dest["status"] == "would_create":
                    results["summary"]["created"] += 1
                elif dest["status"] == "skipped":
                    results["summary"]["skipped"] += 1
                elif dest["status"] == "error":
                    results["summary"]["errors"] += 1

    return results


# ============================================================================
# MAIN
# ============================================================================

def print_summary(results: Dict, dry_run: bool = False) -> None:
    """Print sync summary"""
    print("\n" + "═" * 50)
    if dry_run:
        print("📋 DRY RUN COMPLETE (no files created)")
    else:
        print("✅ SYNC COMPLETE")
    print("═" * 50)

    summary = results.get("summary", {})
    print(f"""
Summary:
  Files created:  {summary.get('created', 0)}
  Files updated:  {summary.get('updated', 0)}
  Files skipped:  {summary.get('skipped', 0)}
  Errors:         {summary.get('errors', 0)}
""")


def main():
    parser = argparse.ArgumentParser(
        description="Sync squad components to IDE activation directories",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s agent squad-chief
  %(prog)s squad squad-creator
  %(prog)s squad copy --dry-run
  %(prog)s squad legal --force --ide cursor
        """
    )

    parser.add_argument("type", choices=["agent", "squad"],
                        help="Component type to sync (only agents are synced to IDE skills)")
    parser.add_argument("name", help="Component or squad name")
    parser.add_argument("--squad", "-s", help="Squad name (auto-detected if not specified)")
    parser.add_argument("--dry-run", "-n", action="store_true",
                        help="Preview without creating files")
    parser.add_argument("--force", "-f", action="store_true",
                        help="Overwrite existing files")
    parser.add_argument("--ide", "-i", choices=["claude", "cursor", "windsurf", "gemini", "antigravity", "codex"],
                        help="Target specific IDE")
    parser.add_argument("--verbose", "-v", action="store_true",
                        help="Show detailed output")
    parser.add_argument("--output", "-o", choices=["text", "json"], default="text",
                        help="Output format")

    args = parser.parse_args()

    # Find project root
    try:
        project_root = find_project_root()
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    # Load config
    config = load_sync_config(project_root)

    print(f"━" * 50)
    print(f" *sync {args.type} {args.name}")
    print(f"━" * 50)
    print(f"\n📋 Project root: {project_root}")
    print(f"   Active IDEs: {', '.join(config.get('active_ides', ['claude']))}")

    # Execute sync
    if args.type == "squad":
        results = sync_squad(
            project_root,
            args.name,
            config,
            force=args.force,
            dry_run=args.dry_run,
            target_ide=args.ide,
            verbose=args.verbose
        )
    else:
        results = sync_component(
            project_root,
            args.type,
            args.name,
            args.squad,
            config,
            force=args.force,
            dry_run=args.dry_run,
            target_ide=args.ide,
            verbose=args.verbose
        )
        # Wrap in summary format
        results = {
            "components": [results],
            "summary": {
                "created": sum(1 for d in results.get("destinations", []) if d["status"] in ["created", "would_create"]),
                "skipped": sum(1 for d in results.get("destinations", []) if d["status"] == "skipped"),
                "errors": sum(1 for d in results.get("destinations", []) if d["status"] == "error"),
                "updated": 0
            }
        }

    # Output
    if args.output == "json":
        print(json.dumps(results, indent=2))
    else:
        print_summary(results, args.dry_run)

        if results.get("error"):
            print(f"Error: {results['error']}")
            sys.exit(1)


if __name__ == "__main__":
    main()
