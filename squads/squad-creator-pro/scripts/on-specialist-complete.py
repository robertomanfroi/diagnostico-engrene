#!/usr/bin/env python3
"""
Hook: SubagentStop
Triggered when a specialist subagent completes.

Actions:
1. Check for <promise>COMPLETE</promise> signal
2. Extract learnings from output
3. Update canonical runtime state in .aiox/squad-runtime
4. Append to orchestrator's MEMORY.md
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


def append_to_memory(entry: str):
    """Append entry to orchestrator's memory."""
    if MEMORY_FILE.exists():
        content = MEMORY_FILE.read_text(encoding="utf-8")

        # Find "Notas Recentes" section and append
        if "## Notas Recentes" in content:
            parts = content.split("## Notas Recentes")
            new_content = parts[0] + "## Notas Recentes\n" + entry + "\n" + parts[1].lstrip()
            MEMORY_FILE.write_text(new_content, encoding="utf-8")


def main():
    try:
        # Read input from stdin
        input_data = json.loads(sys.stdin.read())

        agent_name = input_data.get('agent_name', 'unknown')
        output = input_data.get('output', '')

        # Check for completion signal
        completed = '<promise>COMPLETE</promise>' in output

        # Load current state
        state, state_slug = load_state()

        # Update state with subagent result
        if 'subagent_results' not in state:
            state['subagent_results'] = {}

        if agent_name not in state['subagent_results']:
            state['subagent_results'][agent_name] = {}

        timestamp = datetime.now().isoformat()
        state['subagent_results'][agent_name][timestamp] = {
            "completed": completed,
            "output_length": len(output)
        }
        state['last_updated'] = timestamp

        # Save state
        state_path = save_state(state, state_slug)

        # Append to memory
        status = "OK" if completed else "NO-COMPLETE-SIGNAL"
        append_to_memory(f"- [{timestamp[:10]}] {agent_name}: {status} (output: {len(output)} chars)")

        # Always allow (logging only)
        print(json.dumps({
            "decision": "allow",
            "additionalContext": (
                f"Subagent {agent_name} "
                f"{'completed' if completed else 'did not complete'}; "
                f"state={state_path.as_posix()}"
            )
        }))

    except Exception as e:
        # On error, allow (fail open)
        print(json.dumps({
            "decision": "allow",
            "additionalContext": f"Hook error (allowing): {str(e)}"
        }))


if __name__ == "__main__":
    main()
