"""Regression guards for the bounded setup-python pip-cache batch (#19658)."""

from __future__ import annotations

import re
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

PIP_CACHE_RESTORE = "Restore pip cache"
PIP_CACHE_SAVE = "Save pip cache (main only)"
SAVE_GUARD = "github.ref == 'refs/heads/main' && steps.pip-cache.outputs.cache-hit != 'true'"

# Ce qui installe reellement dans le cache pip du job : une invocation pip
# (`pip install`, `pip3 install`, `python -m pip install`) ou le script
# d'installation partage des suites scripts (PR #25521).
_PIP_INSTALL_RE = re.compile(
    r"(?:^|\s)(?:python[\d.]*\s+-m\s+)?pip3?\s+install\b"
    r"|install_scripts_tests_deps\.sh"
)


def _pip_cache_workflows() -> list[Path]:
    """Workflows portant l'enregistrement du cache pip, decouverts par lecture.

    La decouverte est faite par recherche, pas par liste : un workflow neuf qui
    reprend le motif entre dans la garde sans qu'on edite ce fichier.
    """
    return sorted(
        path
        for path in (REPO_ROOT / ".github" / "workflows").glob("*.yml")
        if PIP_CACHE_SAVE in path.read_text(encoding="utf-8")
    )


def _jobs_with_pip_cache() -> list[tuple[str, str, list[dict[str, Any]]]]:
    found: list[tuple[str, str, list[dict[str, Any]]]] = []
    for path in _pip_cache_workflows():
        workflow = _load_workflow(path.name)
        for job_name, job in (workflow.get("jobs") or {}).items():
            if not isinstance(job, dict):
                continue
            steps = [s for s in (job.get("steps") or []) if isinstance(s, dict)]
            if any(str(step.get("name", "")) == PIP_CACHE_SAVE for step in steps):
                found.append((path.name, str(job_name), steps))
    return found


def _is_pip_install(step: dict[str, Any]) -> bool:
    return bool(_PIP_INSTALL_RE.search(str(step.get("run", ""))))


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


def test_no_setup_python_step_carries_pip_cache() -> None:
    """#27727: the pip cache migrated to actions/cache (main-only save)."""
    names = [*WORKFLOW_FILES, SCHEDULED_ONLY]
    for name in names:
        steps = _pip_cache_setup_steps(_load_workflow(name))
        assert not steps, (
            f"{name} still has a setup-python step with cache: pip "
            "(migrated to actions/cache by #27727)"
        )


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


def test_pip_cache_save_runs_after_the_job_install_step() -> None:
    """#27823: `restore < install < save`, dans chaque job qui enregistre.

    Un enregistrement place avant l'installation n'ecrit rien : sur un runner
    neuf, `~/.cache/pip` n'existe pas encore et `actions/cache/save` sort en
    succes sans enregistrer (« Path(s) specified ... do(es) not exist ») ; sur
    un runner auto-heberge, il enregistre l'etat d'avant l'installation. Le
    motif de reference (#19658, caches `lake-*`) enregistre apres le build.
    """
    violations: list[str] = []
    for workflow_name, job_name, steps in _jobs_with_pip_cache():
        names = [str(step.get("name", "")) for step in steps]
        save_at = names.index(PIP_CACHE_SAVE)
        restores = [i for i, name in enumerate(names) if name == PIP_CACHE_RESTORE]
        if not restores:
            violations.append(f"{workflow_name}:{job_name}: enregistrement sans restauration")
            continue
        restore_at = restores[-1]
        installs = [
            i for i, step in enumerate(steps) if i > restore_at and _is_pip_install(step)
        ]
        if not installs:
            violations.append(
                f"{workflow_name}:{job_name}: aucune etape d'installation apres la restauration"
            )
            continue
        install_at = installs[0]
        if save_at < install_at:
            violations.append(
                f"{workflow_name}:{job_name}: enregistrement (etape {save_at + 1}) "
                f"avant l'installation (etape {install_at + 1}, {names[install_at]!r})"
            )
    assert not violations, "restore < install < save viole:\n" + "\n".join(violations)


def test_pip_cache_save_step_keeps_the_main_only_guard() -> None:
    """#27823: l'enregistrement reste borne a `main` et a un cache manquant."""
    for workflow_name, job_name, steps in _jobs_with_pip_cache():
        saves = [s for s in steps if str(s.get("name", "")) == PIP_CACHE_SAVE]
        for step in saves:
            assert step.get("uses") == "actions/cache/save@v4", (workflow_name, job_name)
            assert step.get("if") == SAVE_GUARD, (workflow_name, job_name)
            settings = step.get("with") or {}
            assert settings.get("path") == "~/.cache/pip", (workflow_name, job_name)
            assert settings.get("key") == "${{ steps.pip-cache.outputs.cache-primary-key }}", (
                workflow_name,
                job_name,
            )

