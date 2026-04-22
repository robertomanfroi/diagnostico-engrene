#!/usr/bin/env python3
"""
Validate Squad Quality - Principle-Based Analysis (Hybrid-Ready)

Phase 3 of validate-squad pipeline — checks task COMPLETENESS by principle:
- Task completeness: purpose + inputs + outputs + completion signals (format-agnostic)
- Acceptance Criteria coverage (AC sections in tasks)
- Workflow state_machine presence
- Workflow task_ref wiring

Checks content quality by PRINCIPLE, not by header pattern.
A task is complete if an executor can understand what to do, not if it has "## Task Anatomy".

Usage:
    python scripts/validate-squad-quality.py {squad-path}
    python scripts/validate-squad-quality.py {squad-name}
    python scripts/validate-squad-quality.py {squad-path} --output json
    python scripts/validate-squad-quality.py {squad-path} --verbose

Output format (--output json):
{
  "phase": "quality",
  "task_anatomy_coverage": "N/N",
  "acceptance_criteria_coverage": "N/N",
  "workflows_with_state_machine": "N/N",
  "workflows_with_task_ref": "N/N",
  "monolithic_files": [],
  "issues": [],
  "score": 0-100
}

Exit codes: 0 = pass, 1 = issues found, 2 = error

Pattern: EXEC-W-001 (Worker - Deterministic)
"""

import os
import sys
import json
import re
import argparse
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Any, Optional, Tuple


# ============================================================================
# CONFIGURATION
# ============================================================================

# MONOLITHIC_THRESHOLD removed — quality is measured by principles, not line count


# ============================================================================
# UTILITIES
# ============================================================================

def find_squads_root() -> Path:
    """Find the squads/ directory"""
    current = Path(__file__).parent.parent.parent  # scripts -> squad-creator -> squads
    if current.name == "squads" or (current / "squad-creator").exists():
        return current

    # Try from cwd
    cwd = Path.cwd()
    if (cwd / "squads").exists():
        return cwd / "squads"
    if cwd.name == "squads":
        return cwd

    raise FileNotFoundError("Could not find squads/ directory")


def resolve_squad_path(squad_input: str) -> Path:
    """Resolve squad input - accepts either a name or a path."""
    input_path = Path(squad_input)

    # If it looks like a path (contains / or is an existing directory)
    if '/' in squad_input or input_path.is_dir():
        squad_path = input_path.resolve()
        if squad_path.exists():
            return squad_path
        # Try as relative
        if not input_path.is_absolute():
            cwd_path = Path.cwd() / squad_input
            if cwd_path.exists():
                return cwd_path.resolve()
        raise FileNotFoundError(f"Squad path not found: {squad_input}")

    # Otherwise treat as squad name
    try:
        squads_root = find_squads_root()
    except FileNotFoundError:
        raise FileNotFoundError(f"Could not find squads/ directory for squad: {squad_input}")

    squad_path = squads_root / squad_input
    if not squad_path.exists():
        raise FileNotFoundError(f"Squad not found: {squad_input} (tried {squad_path})")

    return squad_path


def read_file_content(file_path: Path) -> str:
    """Read file content safely."""
    try:
        return file_path.read_text(encoding='utf-8', errors='ignore')
    except Exception:
        return ""


def count_lines(file_path: Path) -> int:
    """Count lines in a file."""
    content = read_file_content(file_path)
    return len(content.split('\n')) if content else 0


# ============================================================================
# QUALITY CHECKS
# ============================================================================

def check_task_completeness(squad_path: Path) -> Dict[str, Any]:
    """Check if task files have sufficient content for execution — by PRINCIPLE, not by header.

    A task is complete if it has:
    1. Purpose/identity (what it does) — any heading or structured description
    2. Inputs (what it needs) — input/entrada/context/source references
    3. Outputs (what it produces) — output/saída/deliverable/template references
    4. Completion signal (when it's done) — criteria/checklist/quality gate

    This is format-agnostic: works for SINKRA Task Anatomy, squad-creator tasks,
    copy squad tasks, books squad tasks, etc.
    """
    tasks_dir = squad_path / "tasks"
    result = {
        "total": 0,
        "with_anatomy": 0,  # kept for backward compat
        "complete": 0,
        "partial": 0,
        "minimal": 0,
        "missing": [],
        "details": [],
    }

    if not tasks_dir.exists():
        return result

    # Also check subdirectories (e.g., tasks/plf/)
    task_files = sorted(tasks_dir.glob("**/*.md"))

    for task_file in task_files:
        if task_file.name.lower() in ("readme.md", "changelog.md"):
            continue
        result["total"] += 1

        content = read_file_content(task_file)
        lines = len(content.split('\n'))
        signals = 0
        found = []

        # Signal 1: PURPOSE — has a clear identity/description
        if (re.search(r'##?\s*(Purpose|Mission|Prop[oó]sito|Identity|MISSION|What|When to Use|Quando Usar)', content, re.IGNORECASE)
            or re.search(r'##?\s*Task\s+Anatomy', content, re.IGNORECASE)
            or re.search(r'\|\s*\*\*Task\s+ID\*\*\s*\|', content, re.IGNORECASE)
            or re.search(r'sinkra_task_metadata', content)
            or (lines >= 30 and re.search(r'^#\s+', content, re.MULTILINE))):
            signals += 1
            found.append("purpose")

        # Signal 2: INPUTS — references to what the task needs
        if (re.search(r'(input|entrada|context|source|workspace|require|depend|pre.?condition)', content, re.IGNORECASE)
            or re.search(r'(reads?|loads?|receives?|expects?)\s+(from|the|a|an)', content, re.IGNORECASE)):
            signals += 1
            found.append("inputs")

        # Signal 3: OUTPUTS — references to what the task produces
        if (re.search(r'(output|sa[ií]da|result|deliverable|produce|generate|create|write|template)', content, re.IGNORECASE)
            or re.search(r'(formats?|structure|schema|example)\s*:', content, re.IGNORECASE)):
            signals += 1
            found.append("outputs")

        # Signal 4: COMPLETION — criteria or quality gate
        if (re.search(r'(acceptance.?criteria|crit[eé]rio|completion|done.?when|quality|checklist|gate|validation|score)', content, re.IGNORECASE)
            or re.search(r'-\s*\[\s*[x ]\s*\]', content)  # checkbox items
            or re.search(r'(PASS|FAIL|APPROVE|VETO)', content)):
            signals += 1
            found.append("completion")

        # Classify
        if signals >= 3:
            result["complete"] += 1
            result["with_anatomy"] += 1  # backward compat
        elif signals >= 2:
            result["partial"] += 1
            result["with_anatomy"] += 1  # partial still counts
        elif signals >= 1 and lines >= 50:
            result["minimal"] += 1
            result["with_anatomy"] += 1  # substantial content counts
        else:
            result["missing"].append(task_file.relative_to(tasks_dir).as_posix())

        result["details"].append({
            "file": task_file.relative_to(tasks_dir).as_posix(),
            "signals": signals,
            "found": found,
            "lines": lines,
        })

    return result


def check_acceptance_criteria(squad_path: Path) -> Dict[str, Any]:
    """Check if task files contain Acceptance Criteria sections."""
    tasks_dir = squad_path / "tasks"
    result = {
        "total": 0,
        "with_ac": 0,
        "missing": [],
    }

    if not tasks_dir.exists():
        return result

    for task_file in sorted(tasks_dir.glob("*.md")):
        if task_file.name.lower() in ("readme.md", "changelog.md"):
            continue
        result["total"] += 1

        content = read_file_content(task_file)
        # Check for Acceptance Criteria section
        if re.search(r'##?\s*Acceptance\s+Criteria', content, re.IGNORECASE):
            result["with_ac"] += 1
        elif re.search(r'##?\s*Crit[eé]rios?\s+de\s+Aceita[cç][aã]o', content, re.IGNORECASE):
            result["with_ac"] += 1
        elif re.search(r'-\s*\[\s*[x ]\s*\]', content):
            # Has checkbox items (likely AC even without explicit header)
            result["with_ac"] += 1
        else:
            result["missing"].append(task_file.name)

    return result


def check_workflow_state_machine(squad_path: Path) -> Dict[str, Any]:
    """Check if workflow files contain state_machine definitions."""
    workflows_dir = squad_path / "workflows"
    result = {
        "total": 0,
        "with_state_machine": 0,
        "missing": [],
    }

    if not workflows_dir.exists():
        return result

    for wf_file in sorted(workflows_dir.glob("*.yaml")) + sorted(workflows_dir.glob("*.yml")):
        result["total"] += 1

        content = read_file_content(wf_file)
        if re.search(r'state_machine:|states:|transitions:', content, re.IGNORECASE):
            result["with_state_machine"] += 1
        else:
            result["missing"].append(wf_file.name)

    # Also check .md workflow files
    for wf_file in sorted(workflows_dir.glob("*.md")):
        if wf_file.name.lower() in ("readme.md", "changelog.md"):
            continue
        result["total"] += 1

        content = read_file_content(wf_file)
        if re.search(r'state.?machine|states?\s*:|transitions?\s*:', content, re.IGNORECASE):
            result["with_state_machine"] += 1
        else:
            result["missing"].append(wf_file.name)

    return result


def check_workflow_task_ref(squad_path: Path) -> Dict[str, Any]:
    """Check if workflow files contain task_ref wiring."""
    workflows_dir = squad_path / "workflows"
    result = {
        "total": 0,
        "with_task_ref": 0,
        "missing": [],
    }

    if not workflows_dir.exists():
        return result

    for wf_file in sorted(workflows_dir.glob("*.yaml")) + sorted(workflows_dir.glob("*.yml")):
        result["total"] += 1

        content = read_file_content(wf_file)
        if re.search(r'task_ref:|task:|tasks:', content, re.IGNORECASE):
            result["with_task_ref"] += 1
        else:
            result["missing"].append(wf_file.name)

    # Also check .md workflow files
    for wf_file in sorted(workflows_dir.glob("*.md")):
        if wf_file.name.lower() in ("readme.md", "changelog.md"):
            continue
        result["total"] += 1

        content = read_file_content(wf_file)
        if re.search(r'task_ref:|task:|tasks/', content, re.IGNORECASE):
            result["with_task_ref"] += 1
        else:
            result["missing"].append(wf_file.name)

    return result


def check_monolithic_files(squad_path: Path) -> List[Dict[str, Any]]:
    """DEPRECATED: Line count is not a quality signal.
    Quality is measured by PRINCIPLES (has required sections? has smoke tests?)
    not by byte count. A 1500-line agent with complete voice_dna, heuristics,
    and output_examples is BETTER than a 200-line agent missing all of them.
    Returns empty list — kept for interface compatibility."""
    return []


# ============================================================================
# MAIN ANALYSIS
# ============================================================================

def analyze_quality(squad_path: Path, verbose: bool = False) -> Dict[str, Any]:
    """Run Phase 3 quality analysis."""
    results = {
        "squad_name": squad_path.name,
        "squad_path": str(squad_path),
        "timestamp": datetime.now().isoformat(),
        "validator": "validate-squad-quality.py (Worker)",
    }

    # Run all quality checks
    anatomy = check_task_completeness(squad_path)
    ac = check_acceptance_criteria(squad_path)
    state_machine = check_workflow_state_machine(squad_path)
    task_ref = check_workflow_task_ref(squad_path)
    monolithic = check_monolithic_files(squad_path)

    # Collect issues
    issues = []

    if anatomy["total"] > 0 and anatomy["missing"]:
        for m in anatomy["missing"]:
            issues.append(f"Task insufficient content signals: {m}")

    if ac["total"] > 0 and ac["with_ac"] < ac["total"]:
        for m in ac["missing"]:
            issues.append(f"Task missing Acceptance Criteria: {m}")

    if state_machine["total"] > 0 and state_machine["with_state_machine"] < state_machine["total"]:
        for m in state_machine["missing"]:
            issues.append(f"Workflow missing state_machine: {m}")

    if task_ref["total"] > 0 and task_ref["with_task_ref"] < task_ref["total"]:
        for m in task_ref["missing"]:
            issues.append(f"Workflow missing task_ref wiring: {m}")

    for mono in monolithic:
        issues.append(f"Monolithic file ({mono['lines']} lines): {mono['file']}")

    # Calculate score (0-100)
    score = 100
    total_checks = 0
    passed_checks = 0

    # Task anatomy weight: 25%
    if anatomy["total"] > 0:
        total_checks += anatomy["total"]
        passed_checks += anatomy["with_anatomy"]

    # AC weight: 25%
    if ac["total"] > 0:
        total_checks += ac["total"]
        passed_checks += ac["with_ac"]

    # State machine weight: 20%
    if state_machine["total"] > 0:
        total_checks += state_machine["total"]
        passed_checks += state_machine["with_state_machine"]

    # Task ref weight: 20%
    if task_ref["total"] > 0:
        total_checks += task_ref["total"]
        passed_checks += task_ref["with_task_ref"]

    if total_checks > 0:
        score = int((passed_checks / total_checks) * 100)

    # Monolithic file check removed — quality is measured by principles, not line count

    # Build atomic output
    results["phase"] = "quality"
    results["task_anatomy_coverage"] = f"{anatomy['with_anatomy']}/{anatomy['total']}"  # backward compat key
    results["task_completeness"] = f"{anatomy['complete']}/{anatomy['total']} complete, {anatomy['partial']} partial, {anatomy['minimal']} minimal"
    results["acceptance_criteria_coverage"] = f"{ac['with_ac']}/{ac['total']}"
    results["workflows_with_state_machine"] = f"{state_machine['with_state_machine']}/{state_machine['total']}"
    results["workflows_with_task_ref"] = f"{task_ref['with_task_ref']}/{task_ref['total']}"
    results["monolithic_files"] = monolithic
    results["issues"] = issues
    results["score"] = score

    # Detailed breakdown for verbose/text output
    results["_details"] = {
        "anatomy": anatomy,
        "acceptance_criteria": ac,
        "state_machine": state_machine,
        "task_ref": task_ref,
    }

    return results


def print_report(results: Dict[str, Any]) -> None:
    """Print human-readable report."""
    print("\n" + "=" * 60)
    print(f"VALIDATE-SQUAD-QUALITY: {results['squad_name']}")
    print("=" * 60)
    print(f"Path: {results['squad_path']}")
    print(f"Validator: {results['validator']}")
    print()

    print("PHASE 3: Quality Analysis (Principle-Based)")
    print()

    # Task Completeness (by principle, not by header)
    details = results.get("_details", {})
    anatomy = details.get("anatomy", {})
    print(f"  Task Completeness: {results.get('task_completeness', results['task_anatomy_coverage'])}")
    print(f"    (checks: purpose, inputs, outputs, completion signals)")
    if anatomy.get("missing"):
        print(f"    Insufficient signals ({len(anatomy['missing'])}):")
        for m in anatomy["missing"][:5]:
            print(f"      ! {m}")

    # Acceptance Criteria
    ac = details.get("acceptance_criteria", {})
    print(f"  Acceptance Criteria Coverage: {results['acceptance_criteria_coverage']}")
    if ac.get("missing"):
        for m in ac["missing"][:5]:
            print(f"    ! Missing: {m}")

    # Workflows
    sm = details.get("state_machine", {})
    print(f"  Workflows with state_machine: {results['workflows_with_state_machine']}")
    if sm.get("missing"):
        for m in sm["missing"][:5]:
            print(f"    ! Missing: {m}")

    tr = details.get("task_ref", {})
    print(f"  Workflows with task_ref: {results['workflows_with_task_ref']}")
    if tr.get("missing"):
        for m in tr["missing"][:5]:
            print(f"    ! Missing: {m}")

    # Monolithic check removed — quality measured by principles, not line count

    # Issues summary
    issues = results.get("issues", [])
    print()
    print("=" * 60)
    status = "PASS" if results["score"] >= 70 else "ISSUES FOUND"
    print(f"SUMMARY: {status}")
    print(f"  Score: {results['score']}/100")
    print(f"  Total issues: {len(issues)}")
    print("=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description="Validate squad quality (Phase 3) - Worker script (deterministic)"
    )
    parser.add_argument("squad_input", help="Name of squad or path to squad directory")
    parser.add_argument("--output", "-o", choices=["text", "json"], default="text")
    parser.add_argument("--verbose", "-v", action="store_true")

    args = parser.parse_args()

    try:
        squad_path = resolve_squad_path(args.squad_input)
    except FileNotFoundError as e:
        if args.output == "json":
            print(json.dumps({
                "phase": "quality",
                "error": str(e),
                "issues": [str(e)],
                "score": 0
            }, indent=2))
        else:
            print(f"ERROR: {e}")
        sys.exit(2)

    results = analyze_quality(squad_path, args.verbose)

    if args.output == "json":
        # Remove internal details for clean JSON output
        output = {k: v for k, v in results.items() if not k.startswith("_")}
        print(json.dumps(output, indent=2))
    else:
        print_report(results)

    # Exit code
    if results["score"] >= 70:
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
