#!/usr/bin/env python3
"""
Update .aiox-sync.yaml from current squad manifests.

Deterministic worker used by squad-creator publish flows.
It scans squads/*/config.yaml, extracts slashPrefix-like aliases, and
reconciles the root .aiox-sync.yaml so IDE sync has a canonical alias map
for slash skills.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict

import yaml


DEFAULT_ACTIVE_IDES = ["claude", "cursor", "windsurf", "gemini", "antigravity"]
DEFAULT_SYNC_MAPPINGS = {
    "squad_agents": {
        "source": "squads/*/agents/",
        "destinations": {
            "claude": {"path": ".claude/skills/{squad_alias}/{agent}/SKILL.md", "format": "md"},
            "cursor": {"path": ".cursor/rules/", "format": "mdc"},
            "windsurf": {"path": ".windsurf/commands/{squad_alias}/", "format": "md"},
            "gemini": {"path": ".gemini/agents/{squad_alias}/", "format": "md"},
            "antigravity": {"path": ".agents/workflows/{squad_alias}/", "format": "md"},
        },
    }
}


def find_project_root(start: Path) -> Path:
    current = start.resolve()
    for candidate in [current, *current.parents]:
        if (candidate / "squads").exists():
            return candidate
    raise FileNotFoundError("Could not find project root containing squads/")


def load_yaml(path: Path) -> Dict[str, Any]:
    if not path.exists():
        return {}
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    except Exception:
        return {}
    return data if isinstance(data, dict) else {}


def to_camel_case(value: str) -> str:
    parts = [part for part in value.replace("_", "-").split("-") if part]
    if not parts:
        return value
    return parts[0] + "".join(part.capitalize() for part in parts[1:])


def extract_alias(config: Dict[str, Any], squad_name: str) -> str:
    candidates = [
        config.get("slashPrefix"),
        config.get("slash_prefix"),
        (config.get("squad") or {}).get("slashPrefix"),
        (config.get("squad") or {}).get("slash_prefix"),
        (config.get("pack") or {}).get("slashPrefix"),
        (config.get("pack") or {}).get("slash_prefix"),
    ]
    for candidate in candidates:
        if isinstance(candidate, str) and candidate.strip():
            return candidate.strip()
    return to_camel_case(squad_name)


def collect_aliases(project_root: Path) -> Dict[str, str]:
    aliases: Dict[str, str] = {}
    squads_dir = project_root / "squads"

    for squad_dir in sorted(p for p in squads_dir.iterdir() if p.is_dir()):
        config_path = squad_dir / "config.yaml"
        if not config_path.exists():
            continue
        config = load_yaml(config_path)
        if not config:
            continue
        aliases[squad_dir.name] = extract_alias(config, squad_dir.name)

    return aliases


def build_sync_config(existing: Dict[str, Any], aliases: Dict[str, str]) -> Dict[str, Any]:
    merged = dict(existing)
    merged["active_ides"] = list(existing.get("active_ides") or DEFAULT_ACTIVE_IDES)
    merged["squad_aliases"] = aliases
    merged["sync_mappings"] = existing.get("sync_mappings") or DEFAULT_SYNC_MAPPINGS
    return merged


def main() -> int:
    parser = argparse.ArgumentParser(description="Reconcile root .aiox-sync.yaml from squad manifests")
    parser.add_argument("--project-root", default=".", help="Project root or any nested path")
    parser.add_argument("--squad", help="Optional squad name to assert during reconciliation")
    parser.add_argument("--dry-run", action="store_true", help="Preview without writing")
    parser.add_argument("--json", action="store_true", help="Emit JSON summary")
    args = parser.parse_args()

    project_root = find_project_root(Path(args.project_root))
    aliases = collect_aliases(project_root)

    if args.squad and args.squad not in aliases:
        raise SystemExit(f"Squad not found or missing config.yaml: {args.squad}")

    config_path = project_root / ".aiox-sync.yaml"
    existing = load_yaml(config_path)
    merged = build_sync_config(existing, aliases)

    if not args.dry_run:
        config_path.write_text(
            yaml.safe_dump(merged, sort_keys=False, allow_unicode=True),
            encoding="utf-8",
        )

    payload = {
        "project_root": str(project_root),
        "config_path": str(config_path),
        "squad_count": len(aliases),
        "aliases": aliases,
        "written": not args.dry_run,
    }

    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        action = "updated" if not args.dry_run else "preview"
        print(f"OK: {action} {config_path.relative_to(project_root)} with {len(aliases)} squad aliases")
        if args.squad:
            print(f"  target squad: {args.squad} -> {aliases[args.squad]}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
