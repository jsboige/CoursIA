"""Regression guards for the bounded setup-python pip-cache batch (#19658)."""

from __future__ import annotations

from pathlib import Path
from typing import Any

import yaml


REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOW_FILES = {
    "genai-helpers-tests.yml": "MyIA.AI.Notebooks/GenAI/shared/**",
    "gametheory-tests.yml": "MyIA.AI.Notebooks/GameTheory/**",
    "ml-tests.yml": "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/**",
    "sudoku-tests.yml": "MyIA.AI.Notebooks/Sudoku/dlx_certificates.py",
}
SCHEDULED_ONLY = "leaky-fixture-sweep.yml"
PYTHON_PIN = "3.11.18"


def _load_workflow(name: str) -> dict[str, Any]:
    data = yaml.safe_load((REPO_ROOT / ".github" / "workflows" / name).read_text())
    assert isinstance(data, dict)
    return data


def _triggers(workflow: dict[str, Any]) -> dict[str, Any]:
    # PyYAML's YAML 1.1 resolver may turn the unquoted `on` key into True.
    value = workflow.get("on", workflow.get(True))
    assert isinstance(value, dict)
    return value


def _pip_cache_setup_steps(workflow: dict[str, Any]) -> list[dict[str, Any]]:
    steps: list[dict[str, Any]] = []
    for job in workflow.get("jobs", {}).values():
        if not isinstance(job, dict):
            continue
        for step in job.get("steps", []):
            if not isinstance(step, dict):
                continue
            if str(step.get("uses", "")).startswith("actions/setup-python@") and (
                (step.get("with") or {}).get("cache") == "pip"
            ):
                steps.append(step)
    return steps


def test_cached_setup_python_specs_are_exact_available_patches() -> None:
    """A minor-only selector recreates one pip cache per resolved patch."""
    names = [*WORKFLOW_FILES, SCHEDULED_ONLY]
    for name in names:
        steps = _pip_cache_setup_steps(_load_workflow(name))
        assert steps, f"{name} no longer has the expected pip-cache setup-python step"
        assert all(
            (step.get("with") or {}).get("python-version") == PYTHON_PIN
            for step in steps
        ), f"{name} must pin the source-observed Python {PYTHON_PIN} patch"


def test_path_scoped_workflow_triggers_and_cache_settings_remain_wired() -> None:
    """Pinning does not remove the existing push/PR path gates or dispatch."""
    for name, source_path in WORKFLOW_FILES.items():
        triggers = _triggers(_load_workflow(name))
        assert set(triggers) == {"push", "pull_request", "workflow_dispatch"}
        assert triggers["push"]["paths"] == triggers["pull_request"]["paths"]
        assert source_path in triggers["push"]["paths"]
        assert f".github/workflows/{name}" in triggers["push"]["paths"]

    scheduled = _triggers(_load_workflow(SCHEDULED_ONLY))
    assert set(scheduled) == {"schedule", "workflow_dispatch"}

