from __future__ import annotations

import importlib.util
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve()
SCRIPT = HERE.parents[1] / "check_readme_series_form.py"
FIXTURES = HERE.parent / "fixtures" / "readme_series"
spec = importlib.util.spec_from_file_location("readme_series_form", SCRIPT)
check = importlib.util.module_from_spec(spec)
assert spec.loader
spec.loader.exec_module(check)


def test_conforming_planners_fixture():
    result = check.inspect_text("Planners/01-Foundation/README.md", (FIXTURES / "conforming.md").read_text())
    assert result == {"path": "Planners/01-Foundation/README.md", "conforming": True, "missing": [], "extra": []}


def test_nonconforming_fixture():
    result = check.inspect_text("bad/README.md", (FIXTURES / "nonconforming.md").read_text())
    assert result["conforming"] is False
    assert len(result["missing"]) == 3


def test_v2_catches_lettered_main_table_that_passes_v1():
    result = check.inspect_text("series/README.md", (FIXTURES / "v1_only.md").read_text())
    assert result["missing"] == []
    assert result["conforming"] is False
    assert "lettres_dans_parcours_principal" in result["extra"]


def _git(path: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=path, check=True, capture_output=True)


def test_delta_ignores_existing_backlog_and_detects_regression(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    folder = repo / "MyIA.AI.Notebooks" / "Series"
    folder.mkdir(parents=True)
    (folder / "a.ipynb").write_text("{}")
    (folder / "b.ipynb").write_text("{}")
    (folder / "README.md").write_text((FIXTURES / "conforming.md").read_text())
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "base")
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, text=True, capture_output=True).stdout.strip()
    monkeypatch.setattr(check, "ROOT", repo)
    monkeypatch.setattr(check, "NOTEBOOKS", repo / "MyIA.AI.Notebooks")
    # No changed README: the historical backlog elsewhere cannot create a delta.
    assert check._delta(base, None) == []
    (folder / "README.md").write_text((FIXTURES / "nonconforming.md").read_text())
    assert check._delta(base, None)


def test_delta_pairs_git_proven_series_rename(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    folder = repo / "MyIA.AI.Notebooks" / "Series"
    folder.mkdir(parents=True)
    (folder / "a.ipynb").write_text("{}")
    (folder / "b.ipynb").write_text("{}")
    (folder / "README.md").write_text((FIXTURES / "nonconforming.md").read_text())
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "base")
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, text=True, capture_output=True).stdout.strip()
    monkeypatch.setattr(check, "ROOT", repo)
    monkeypatch.setattr(check, "NOTEBOOKS", repo / "MyIA.AI.Notebooks")
    _git(repo, "mv", "MyIA.AI.Notebooks/Series", "MyIA.AI.Notebooks/Renamed")
    assert check._delta(base, None) == []


def test_delta_allows_partial_improvement(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    folder = repo / "MyIA.AI.Notebooks" / "Series"
    folder.mkdir(parents=True)
    (folder / "a.ipynb").write_text("{}")
    (folder / "b.ipynb").write_text("{}")
    (folder / "README.md").write_text((FIXTURES / "nonconforming.md").read_text())
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "base")
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, text=True, capture_output=True).stdout.strip()
    monkeypatch.setattr(check, "ROOT", repo)
    monkeypatch.setattr(check, "NOTEBOOKS", repo / "MyIA.AI.Notebooks")
    (folder / "README.md").write_text("## Comment lire ce README\n" + (FIXTURES / "nonconforming.md").read_text())
    assert check._delta(base, None) == []


def test_delta_respects_paths_scope(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    notebooks = repo / "MyIA.AI.Notebooks"
    for name in ("Included", "Excluded"):
        folder = notebooks / name
        folder.mkdir(parents=True)
        (folder / "a.ipynb").write_text("{}")
        (folder / "b.ipynb").write_text("{}")
        (folder / "README.md").write_text((FIXTURES / "conforming.md").read_text())
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "base")
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, text=True, capture_output=True).stdout.strip()
    monkeypatch.setattr(check, "ROOT", repo)
    monkeypatch.setattr(check, "NOTEBOOKS", notebooks)
    (notebooks / "Excluded" / "README.md").write_text((FIXTURES / "nonconforming.md").read_text())
    assert check._delta(base, None, ["MyIA.AI.Notebooks/Included"]) == []
    assert check._delta(base, None, ["MyIA.AI.Notebooks/Excluded"])


def test_delta_allows_new_series_with_two_of_three_markers(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    (repo / "MyIA.AI.Notebooks").mkdir(parents=True)
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", ".")
    _git(repo, "commit", "--allow-empty", "-qm", "base")
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, text=True, capture_output=True).stdout.strip()
    monkeypatch.setattr(check, "ROOT", repo)
    monkeypatch.setattr(check, "NOTEBOOKS", repo / "MyIA.AI.Notebooks")
    folder = repo / "MyIA.AI.Notebooks" / "AddedSeries"
    folder.mkdir()
    (folder / "a.ipynb").write_text("{}")
    (folder / "b.ipynb").write_text("{}")
    (folder / "README.md").write_text("## Comment lire ce README\n\n## Approfondissements\n")
    _git(repo, "add", ".")
    assert check.inspect_text("x", (folder / "README.md").read_text())["conforming"]
    assert check._delta(base, None) == []
