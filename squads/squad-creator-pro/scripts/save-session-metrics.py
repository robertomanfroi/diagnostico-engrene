#!/usr/bin/env python3
"""
Hook: Stop
Triggered when the session ends.

Actions:
1. Calculate session metrics
2. Update canonical runtime state in .aiox/squad-runtime
3. Log session summary to MEMORY.md
"""

import json
import os
import sys
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, Optional, Tuple


WORKSPACE_ROOT = Path(__file__).resolve().parents[3]
MEMORY_FILE = WORKSPACE_ROOT / ".claude" / "agent-memory" / "squad" / "MEMORY.md"


def resolve_runtime_root() -> Path:
    override = os.getenv("AIOX_RUNTIME_ROOT", "").strip()
    if not override:
        return WORKSPACE_ROOT / ".aiox" / "squad-runtime"
    candidate = Path(override)
    if candidate.is_absolute():
        return candidate
    return (WORKSPACE_ROOT / candidate).resolve()


def canonical_active_path() -> Path:
    return resolve_runtime_root() / "active-squad.json"


def canonical_state_path(slug: str) -> Path:
    return resolve_runtime_root() / "create-squad" / slug / "state.json"


def read_json(path: Path) -> Optional[Dict[str, Any]]:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def read_active_slug() -> Optional[str]:
    active = read_json(canonical_active_path())
    if isinstance(active, dict):
        slug = str(active.get("slug", "")).strip()
        if slug:
            return slug
    elif isinstance(active, str) and active.strip():
        return active.strip()
    return None


def load_state() -> Tuple[Dict[str, Any], Optional[str]]:
    """Load current workflow state from canonical path only."""
    active_slug = read_active_slug()
    if not active_slug:
        return {}, None
    state = read_json(canonical_state_path(active_slug))
    if state is None:
        return {}, active_slug
    slug = state.get("slug") if isinstance(state, dict) else None
    return state, (slug or active_slug)


def save_state(state: Dict[str, Any], slug_hint: Optional[str]) -> Path:
    """Save workflow state to canonical runtime path."""
    slug = str(state.get("slug") or slug_hint or read_active_slug() or "global").strip()
    state["slug"] = slug

    state_file = canonical_state_path(slug)
    state_file.parent.mkdir(parents=True, exist_ok=True)
    state_file.write_text(json.dumps(state, indent=2), encoding="utf-8")
    return state_file


def update_memory_stats(state: dict):
    """Update Quick Stats in MEMORY.md."""
    if not MEMORY_FILE.exists():
        return

    content = MEMORY_FILE.read_text(encoding="utf-8")

    # Calculate stats
    metrics = state.get('metrics', {})
    agents_created = metrics.get('agents_created', 0)
    quality_scores = metrics.get('quality_scores', [])
    avg_score = sum(quality_scores) / len(quality_scores) if quality_scores else 0

    # Update Quick Stats section
    # This is a simple implementation - could be more sophisticated
    lines = content.split('\n')
    new_lines = []
    in_stats = False

    for line in lines:
        if line.startswith('## Quick Stats'):
            in_stats = True
            new_lines.append(line)
            continue

        if in_stats and line.startswith('## '):
            in_stats = False

        if in_stats and line.startswith('- '):
            # Update stat lines
            if 'Total squads criados:' in line:
                # Keep existing, this should be incremented elsewhere
                pass
            elif 'Quality score médio:' in line and avg_score > 0:
                line = f"- Quality score médio: {avg_score:.1f}/10"

        new_lines.append(line)

    MEMORY_FILE.write_text('\n'.join(new_lines), encoding="utf-8")


def append_workflow_log(state: dict):
    """Append workflow execution to memory."""
    if not MEMORY_FILE.exists():
        return

    workflow = state.get('workflow', 'unknown')
    if not workflow:
        return

    started = state.get('started_at', '')
    status = 'complete' if all(
        s == 'complete' for s in state.get('phase_status', {}).values()
    ) else 'incomplete'

    content = MEMORY_FILE.read_text(encoding="utf-8")

    # Find "Workflows Executados" section
    if "## Workflows Executados" in content:
        timestamp = datetime.now().strftime('%Y-%m-%d')
        entry = f"- [{timestamp}] {workflow}: {status}"

        parts = content.split("## Workflows Executados")
        if len(parts) == 2:
            new_content = parts[0] + "## Workflows Executados\n" + entry + "\n" + parts[1].lstrip()
            MEMORY_FILE.write_text(new_content, encoding="utf-8")


def main():
    try:
        # Read input from stdin (may be empty for Stop hook)
        try:
            input_data = json.loads(sys.stdin.read())
        except:
            input_data = {}

        # Load state
        state, state_slug = load_state()

        # Update final timestamp
        state['last_updated'] = datetime.now().isoformat()

        # Save state
        state_path = save_state(state, state_slug)

        # Update memory
        update_memory_stats(state)
        append_workflow_log(state)

        # Allow session to end
        print(json.dumps({
            "decision": "allow",
            "additionalContext": f"state={state_path.as_posix()}"
        }))

    except Exception as e:
        # On error, allow (fail open)
        print(json.dumps({
            "decision": "allow",
            "additionalContext": f"Metrics save error: {str(e)}"
        }))


if __name__ == "__main__":
    main()
