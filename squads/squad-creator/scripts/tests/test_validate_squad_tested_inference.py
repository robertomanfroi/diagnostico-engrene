#!/usr/bin/env python3
"""Behavior tests for tested flag inference in validate-squad.sh."""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import uuid
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[4]
SQUADS_DIR = REPO_ROOT / "squads"
OUTPUTS_ROOT_NAME = "out" + "puts"
OUTPUTS_DIR = REPO_ROOT / OUTPUTS_ROOT_NAME
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


def _create_test_squad(name: str) -> tuple[Path, Path]:
    squad_dir = SQUADS_DIR / name
    output_dir = OUTPUTS_DIR / name / "sample-business"
    (squad_dir / "agents").mkdir(parents=True, exist_ok=False)
    (squad_dir / "tasks").mkdir(parents=True, exist_ok=False)
    output_dir.mkdir(parents=True, exist_ok=False)

    config = f"""name: {name}
version: 1.0.0
entry_agent: squad-chief
workspace_integration:
  level: none
settings:
  activation:
    yolo_required: false
  output:
    base_path: "{OUTPUTS_ROOT_NAME}/{name}/{{business}}/"
"""
    (squad_dir / "config.yaml").write_text(config, encoding="utf-8")
    (squad_dir / "README.md").write_text("# Temp squad\n", encoding="utf-8")
    (squad_dir / "CHANGELOG.md").write_text("# Changelog\n", encoding="utf-8")
    (squad_dir / "ARCHITECTURE.md").write_text("# Architecture\n", encoding="utf-8")
    (squad_dir / "agents" / "squad-chief.md").write_text("output_examples: yes\n", encoding="utf-8")
    (squad_dir / "tasks" / f"update-{name}.md").write_text("# Update\n", encoding="utf-8")
    (squad_dir / "tasks" / f"delete-{name}.md").write_text("# Delete\n", encoding="utf-8")
    (output_dir / "artifact.md").write_text("real output\n", encoding="utf-8")

    return squad_dir, output_dir


def _run_validator(squad_name: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["bash", str(VALIDATE_SCRIPT), squad_name, "--quick", "--json"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


def test_tested_flag_is_inferred_from_declared_output_path() -> None:
    squad_name = f"tmp-tested-infer-{uuid.uuid4().hex[:8]}"
    squad_dir, output_dir = _create_test_squad(squad_name)
    try:
        result = _run_validator(squad_name)
        payload = _extract_result_json(result.stdout)

        assert result.returncode == 0
        assert payload["production"]["score"] >= 4
    finally:
        shutil.rmtree(squad_dir, ignore_errors=True)
        shutil.rmtree(output_dir.parent.parent, ignore_errors=True)


if __name__ == "__main__":
    test_tested_flag_is_inferred_from_declared_output_path()
    print("PASS: tested flag inference behavior is correct")
