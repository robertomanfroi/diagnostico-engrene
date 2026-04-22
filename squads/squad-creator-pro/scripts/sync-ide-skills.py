#!/usr/bin/env python3
"""Compatibility proxy for the canonical squad-creator sync script."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


BASE_SCRIPT = (
    Path(__file__).resolve().parents[2]
    / "squad-creator"
    / "scripts"
    / "sync-ide-skills.py"
)


def _load_base_module():
    if not BASE_SCRIPT.exists():
        raise FileNotFoundError(
            f"Canonical base script not found: {BASE_SCRIPT}"
        )

    base_dir = str(BASE_SCRIPT.parent)
    if base_dir not in sys.path:
        sys.path.insert(0, base_dir)

    spec = importlib.util.spec_from_file_location(
        "squad_creator_base_sync_ide_skills",
        BASE_SCRIPT,
    )
    if spec is None or spec.loader is None:
        raise ImportError(f"Could not load module spec from {BASE_SCRIPT}")

    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_BASE = _load_base_module()


def _reexport_public_symbols() -> None:
    for name in dir(_BASE):
        if name.startswith("__") and name not in {"__doc__", "__all__"}:
            continue
        globals()[name] = getattr(_BASE, name)


_reexport_public_symbols()


def main():
    return _BASE.main()


if __name__ == "__main__":
    raise SystemExit(main())
