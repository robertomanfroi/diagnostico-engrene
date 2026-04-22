#!/usr/bin/env python3
"""Behavior tests for contextual lifecycle reporting in validate-squad.sh."""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import uuid
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[4]
SQUADS_DIR = REPO_ROOT / "squads"
VALIDATE_SCRIPT = REPO_ROOT / "squads" / "squad-creator" / "scripts" / "validate-squad.sh"


def _strip_ansi(text: str) -> str:
    return re.sub(r"\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])", "", text)


def _extract_result_json(stdout: str) -> dict:
    cleaned = _strip_ansi(stdout)
    decoder = json.JSONDecoder()
    found: list[dict] = []

    for index, char in enumerate(cleaned):
        if char != "{":
            continue
        try:
            payload, _ = decoder.raw_decode(cleaned[index:])
        except Exception:
            continue
        if isinstance(payload, dict) and "final_score" in payload:
            found.append(payload)

    if not found:
        raise AssertionError("No validation JSON payload found in validator output")

    return found[-1]


def _create_test_squad(name: str) -> Path:
    squad_dir = SQUADS_DIR / name
    (squad_dir / "agents").mkdir(parents=True, exist_ok=False)
    (squad_dir / "outputs").mkdir(parents=True, exist_ok=False)
    (squad_dir / "tasks").mkdir(parents=True, exist_ok=False)

    config = f"""name: {name}
version: 1.0.0
entry_agent: squad-chief
tested: true
workspace_integration:
  level: none
settings:
  activation:
    yolo_required: false
"""
    (squad_dir / "config.yaml").write_text(config, encoding="utf-8")
    (squad_dir / "README.md").write_text("# Temp squad\n", encoding="utf-8")
    (squad_dir / "CHANGELOG.md").write_text("# Changelog\n", encoding="utf-8")
    (squad_dir / "ARCHITECTURE.md").write_text("# Architecture\n", encoding="utf-8")
    (squad_dir / "agents" / "squad-chief.md").write_text("output_examples: yes\n", encoding="utf-8")
    (squad_dir / "outputs" / "run.txt").write_text("ok\n", encoding="utf-8")
    (squad_dir / "validation-report.md").write_text("validated\n", encoding="utf-8")

    return squad_dir


def _run_validator(squad_name: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["bash", str(VALIDATE_SCRIPT), squad_name, "--quick", "--json"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


def test_contextual_lifecycle_checks_are_reported_separately() -> None:
    squad_name = f"tmp-contextual-life-{uuid.uuid4().hex[:8]}"
    squad_dir = _create_test_squad(squad_name)
    try:
        result = _run_validator(squad_name)
        payload = _extract_result_json(result.stdout)

        mandatory = payload["structure"]["mandatory_checks"]
        contextual = payload["structure"]["contextual_lifecycle_checks"]

        assert mandatory["pass"] == 2
        assert mandatory["total"] == 2
        assert mandatory["tested_flag_present"] is True
        assert mandatory["architecture_doc_present"] is True

        assert contextual["pass"] == 0
        assert contextual["total"] == 2
        assert contextual["warnings"] == 2
        assert contextual["update_task_present"] is False
        assert contextual["delete_task_present"] is False

        assert payload["dimensions"]["structural_completeness"]["score"] == 10
        assert "Missing update-*.md task" in result.stdout
        assert "Missing delete-*.md task" in result.stdout
    finally:
        shutil.rmtree(squad_dir, ignore_errors=True)


if __name__ == "__main__":
    test_contextual_lifecycle_checks_are_reported_separately()
    print("PASS: contextual lifecycle reporting is correct")
