"""Tests pour scripts/notebook_tools/audit_workflow_path_filters.py.

Verifie que :
- les filtres paths/paths-ignore sont correctement detectes (malgre le
  quirk PyYAML 'on' = cle True)
- les workflows sans filtre sont correctement classes required vs optional
- la sortie JSON contient le summary attendu
- le check-regression detecte les ajouts sans filtre
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "notebook_tools" / "audit_workflow_path_filters.py"


@pytest.fixture
def workflows_dir(tmp_path: Path) -> Path:
    """Cree un repertoire de workflows minimal pour les tests."""
    wf_dir = tmp_path / "workflows"
    wf_dir.mkdir()

    # Workflow filtre standard
    (wf_dir / "filtered.yml").write_text(
        """name: Filtered
on:
  pull_request:
    branches: [main]
    paths: ['**.py', 'scripts/**']
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - run: echo test
""",
        encoding="utf-8",
    )

    # Workflow unfiltered-required (whitelist)
    (wf_dir / "required.yml").write_text(
        """name: Required Gate
on:
  pull_request:
    branches: [main]
jobs:
  gate:
    runs-on: ubuntu-latest
    steps:
      - run: echo gate
""",
        encoding="utf-8",
    )

    # Workflow avec 'on' = True (PyYAML quirk)
    (wf_dir / "quirky.yml").write_text(
        """name: Quirky True Key
'on':
  pull_request:
    branches: [main]
    paths: ['**.lean']
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - run: echo build
""",
        encoding="utf-8",
    )

    # Workflow sans pull_request
    (wf_dir / "schedule_only.yml").write_text(
        """name: Schedule Only
on:
  schedule:
    - cron: '0 0 * * *'
jobs:
  cron:
    runs-on: ubuntu-latest
    steps:
      - run: echo cron
""",
        encoding="utf-8",
    )

    # Workflow unfiltered-optional (nouveau)
    (wf_dir / "new_optional.yml").write_text(
        """name: New Optional
on:
  pull_request:
    branches: [main]
jobs:
  fresh:
    runs-on: ubuntu-latest
    steps:
      - run: echo fresh
""",
        encoding="utf-8",
    )

    # Workflow avec pull_request list (multi-trigger)
    (wf_dir / "list.yml").write_text(
        """name: List PR
on:
  pull_request:
    - branches: [main]
      paths: ['**.md']
    - branches: [develop]
      paths-ignore: ['**.lock']
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - run: echo test
""",
        encoding="utf-8",
    )

    return wf_dir


def test_parses_filtered_workflow(workflows_dir: Path) -> None:
    """Verifie qu'un workflow avec paths est classifie filtered."""
    from scripts.notebook_tools.audit_workflow_path_filters import (
        audit_workflows,
    )

    audit = audit_workflows(workflows_dir)
    workflows_by_name = {w["name"]: w for w in audit["workflows"]}

    filtered = workflows_by_name["filtered.yml"]
    assert filtered["has_pr_trigger"] is True
    assert filtered["has_filter"] is True
    assert filtered["paths_count"] == 2
    assert filtered["classification"] == "filtered"


def test_parses_required_unfiltered(
    workflows_dir: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Verifie qu'un workflow unfiltered dans la whitelist est classifie required."""
    from scripts.notebook_tools import audit_workflow_path_filters as audit_mod
    from scripts.notebook_tools.audit_workflow_path_filters import (
        audit_workflows,
    )

    # Monkeypatch la whitelist pour ajouter le fichier de test
    test_whitelist = audit_mod.REQUIRED_UNFILTERED_WORKFLOWS | {"required.yml"}
    monkeypatch.setattr(audit_mod, "REQUIRED_UNFILTERED_WORKFLOWS", test_whitelist)

    audit = audit_workflows(workflows_dir)
    workflows_by_name = {w["name"]: w for w in audit["workflows"]}

    required = workflows_by_name["required.yml"]
    assert required["has_pr_trigger"] is True
    assert required["has_filter"] is False
    assert required["classification"] == "required"


def test_parses_quirky_yaml_true_key(workflows_dir: Path) -> None:
    """Verifie la gestion du quirk PyYAML 'on' = True."""
    from scripts.notebook_tools.audit_workflow_path_filters import (
        audit_workflows,
    )

    audit = audit_workflows(workflows_dir)
    workflows_by_name = {w["name"]: w for w in audit["workflows"]}

    quirky = workflows_by_name["quirky.yml"]
    assert quirky["has_pr_trigger"] is True
    assert quirky["has_filter"] is True
    assert quirky["paths_count"] == 1


def test_handles_no_pr_trigger(workflows_dir: Path) -> None:
    """Verifie qu'un workflow sans pull_request est classifie tel quel."""
    from scripts.notebook_tools.audit_workflow_path_filters import (
        audit_workflows,
    )

    audit = audit_workflows(workflows_dir)
    workflows_by_name = {w["name"]: w for w in audit["workflows"]}

    schedule = workflows_by_name["schedule_only.yml"]
    assert schedule["has_pr_trigger"] is False
    assert schedule["has_filter"] is False
    assert schedule["classification"] == "no_pr_trigger"


def test_unfiltered_optional_classification(workflows_dir: Path) -> None:
    """Verifie qu'un workflow unfiltered hors whitelist est classifie optional."""
    from scripts.notebook_tools.audit_workflow_path_filters import (
        audit_workflows,
    )

    audit = audit_workflows(workflows_dir)
    workflows_by_name = {w["name"]: w for w in audit["workflows"]}

    # new_optional.yml n'est pas dans REQUIRED_UNFILTERED_WORKFLOWS
    new_optional = workflows_by_name["new_optional.yml"]
    assert new_optional["classification"] == "optional"


def test_list_pull_request_paths(workflows_dir: Path) -> None:
    """Verifie qu'une liste de triggers pull_request est geree correctement."""
    from scripts.notebook_tools.audit_workflow_path_filters import (
        audit_workflows,
    )

    audit = audit_workflows(workflows_dir)
    workflows_by_name = {w["name"]: w for w in audit["workflows"]}

    list_wf = workflows_by_name["list.yml"]
    assert list_wf["has_pr_trigger"] is True
    assert list_wf["has_filter"] is True
    assert list_wf["paths_count"] == 2  # 1 paths + 1 paths-ignore


def test_summary_counts(
    workflows_dir: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Verifie que le summary agrege correctement les categories."""
    from scripts.notebook_tools import audit_workflow_path_filters as audit_mod
    from scripts.notebook_tools.audit_workflow_path_filters import (
        audit_workflows,
    )

    # Monkeypatch la whitelist
    test_whitelist = audit_mod.REQUIRED_UNFILTERED_WORKFLOWS | {"required.yml"}
    monkeypatch.setattr(audit_mod, "REQUIRED_UNFILTERED_WORKFLOWS", test_whitelist)

    audit = audit_workflows(workflows_dir)
    s = audit["summary"]

    assert s["total"] == 6
    assert s["with_pr_trigger"] == 5  # 4 explicites + 1 quirky
    assert s["filtered"] == 3  # filtered.yml, quirky.yml, list.yml
    assert s["unfiltered"] == 2  # required.yml, new_optional.yml
    assert s["unfiltered_required"] == 1  # required.yml
    assert s["unfiltered_optional"] == 1  # new_optional.yml
    assert s["no_pr_trigger"] == 1  # schedule_only.yml


def test_check_regression_detects_new_unfiltered(workflows_dir: Path) -> None:
    """Verifie que le check-regression detecte un nouveau workflow unfiltered-optional."""
    from scripts.notebook_tools.audit_workflow_path_filters import (
        audit_workflows,
        check_regression,
    )

    # Audit precedent SANS new_optional
    workflows_dir_minus = workflows_dir
    for f in workflows_dir_minus.iterdir():
        if f.name == "new_optional.yml":
            f.unlink()

    previous = audit_workflows(workflows_dir_minus)
    # Audit courant AVEC new_optional
    (workflows_dir_minus / "new_optional.yml").write_text(
        """name: New Optional
on:
  pull_request:
    branches: [main]
jobs:
  fresh:
    runs-on: ubuntu-latest
    steps:
      - run: echo fresh
""",
        encoding="utf-8",
    )
    current = audit_workflows(workflows_dir_minus)

    regressions = check_regression(current, previous)
    new_unfiltered = [r for r in regressions if "new_optional" in r["name"]]
    assert len(new_unfiltered) == 1
    assert new_unfiltered[0]["reason"] == "newly_added_unfiltered_optional"


def test_check_regression_no_false_positive(workflows_dir: Path) -> None:
    """Verifie qu'un audit identique ne signale pas de regression."""
    from scripts.notebook_tools.audit_workflow_path_filters import (
        audit_workflows,
        check_regression,
    )

    audit = audit_workflows(workflows_dir)
    # Compare avec lui-meme -> 0 regression
    regressions = check_regression(audit, audit)
    assert regressions == []


def test_cli_runs(tmp_path: Path) -> None:
    """Verifie que le CLI tourne en end-to-end."""
    workflows_dir = tmp_path / "wf"
    workflows_dir.mkdir()
    (workflows_dir / "filtered.yml").write_text(
        """name: F
on:
  pull_request:
    paths: ['**.py']
""",
        encoding="utf-8",
    )

    audit_dir = tmp_path / "audit"
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--workflows-dir",
            str(workflows_dir),
            "--audit-dir",
            str(audit_dir),
            "--quiet",
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, f"stderr: {result.stderr}"
    assert (audit_dir / "latest.json").exists()
    assert (audit_dir / "latest.md").exists()


def test_main_handles_missing_workflows_dir(tmp_path: Path) -> None:
    """Verifie que le CLI echoue proprement si workflows_dir est introuvable."""
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--workflows-dir",
            str(tmp_path / "nonexistent"),
            "--audit-dir",
            str(tmp_path / "audit"),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 1
    assert "not found" in result.stderr.lower()
