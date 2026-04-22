#!/usr/bin/env python3
"""
Update the generated squad activation appendix inside root CLAUDE.md.

The script scans squad manifests, resolves slashPrefix + entry_agent, and keeps
an explicit generated block in CLAUDE.md so newly published chiefs become
discoverable at the repo level.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict, List

import yaml


BEGIN_MARKER = "<!-- BEGIN GENERATED SQUAD ACTIVATION REGISTRY -->"
END_MARKER = "<!-- END GENERATED SQUAD ACTIVATION REGISTRY -->"
SECTION_TITLE = "## Generated Squad Activation Registry"


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


def extract_field(config: Dict[str, Any], *keys: str) -> str:
    for key in keys:
        value = config.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    for parent in ("squad", "pack"):
        nested = config.get(parent)
        if not isinstance(nested, dict):
            continue
        for key in keys:
            value = nested.get(key)
            if isinstance(value, str) and value.strip():
                return value.strip()
    return ""


def collect_registry(project_root: Path) -> List[Dict[str, str]]:
    rows: List[Dict[str, str]] = []
    squads_dir = project_root / "squads"

    for squad_dir in sorted(p for p in squads_dir.iterdir() if p.is_dir()):
        config_path = squad_dir / "config.yaml"
        if not config_path.exists():
            continue

        config = load_yaml(config_path)
        if not config:
            continue
        entry_agent = extract_field(config, "entry_agent")
        slash_prefix = extract_field(config, "slashPrefix", "slash_prefix")
        if not entry_agent or not slash_prefix:
            continue

        chief_path = squad_dir / "agents" / f"{entry_agent}.md"
        if not chief_path.exists():
            continue

        command_path = project_root / ".claude" / "commands" / slash_prefix / f"{entry_agent}.md"
        rows.append(
            {
                "squad": squad_dir.name,
                "prefix": slash_prefix,
                "entry_agent": entry_agent,
                "command_surface": f"/{slash_prefix}:{entry_agent}",
                "command_path": str(command_path.relative_to(project_root)),
                "status": "published" if command_path.exists() else "pending_sync",
            }
        )

    return rows


def build_section(rows: List[Dict[str, str]]) -> str:
    lines = [
        SECTION_TITLE,
        "",
        BEGIN_MARKER,
        "| Squad | Prefix | Entry Agent | Command Surface | Status |",
        "|---|---|---|---|---|",
    ]

    for row in rows:
        lines.append(
            "| "
            f"`{row['squad']}` | "
            f"`/{row['prefix']}` | "
            f"`{row['entry_agent']}` | "
            f"`{row['command_surface']}` | "
            f"`{row['status']}` |"
        )

    lines.append(END_MARKER)
    return "\n".join(lines)


def replace_or_append(content: str, section: str) -> str:
    if BEGIN_MARKER in content and END_MARKER in content:
        start = content.index(BEGIN_MARKER)
        section_start = content.rfind(SECTION_TITLE, 0, start)
        end = content.index(END_MARKER) + len(END_MARKER)
        prefix = content[:section_start].rstrip() if section_start != -1 else content[:start].rstrip()
        suffix = content[end:].lstrip()
        parts = [prefix, section]
        if suffix:
            parts.append(suffix)
        return "\n\n".join(part for part in parts if part)

    return content.rstrip() + "\n\n" + section + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description="Update generated squad activation registry in root CLAUDE.md")
    parser.add_argument("--project-root", default=".", help="Project root or any nested path")
    parser.add_argument("--dry-run", action="store_true", help="Preview without writing")
    parser.add_argument("--json", action="store_true", help="Emit JSON summary")
    args = parser.parse_args()

    project_root = find_project_root(Path(args.project_root))
    claude_path = project_root / "CLAUDE.md"
    if not claude_path.exists():
        raise SystemExit(f"CLAUDE.md not found at project root: {claude_path}")

    rows = collect_registry(project_root)
    section = build_section(rows)
    updated = replace_or_append(claude_path.read_text(encoding="utf-8"), section)

    if not args.dry_run:
        claude_path.write_text(updated, encoding="utf-8")

    payload = {
        "project_root": str(project_root),
        "claude_path": str(claude_path),
        "registry_entries": len(rows),
        "written": not args.dry_run,
        "published": sum(1 for row in rows if row["status"] == "published"),
        "pending_sync": sum(1 for row in rows if row["status"] == "pending_sync"),
    }

    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        action = "updated" if not args.dry_run else "preview"
        print(f"OK: {action} CLAUDE.md registry with {len(rows)} squad surfaces")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
