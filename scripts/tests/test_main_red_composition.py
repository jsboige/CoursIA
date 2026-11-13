"""Rejeu du rouge issu de deux branches vertes, sans appel GitHub réel (#24828)."""
import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    "merge_ready_fixtures", Path(__file__).with_name("test_merge_ready.py")
)
fixtures = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fixtures
spec.loader.exec_module(fixtures)


def git(repo, *args):
    return subprocess.run(["git", *args], cwd=repo, check=True,
                          capture_output=True, text=True).stdout.strip()


def test_composition_red_survives_pending_and_cancelled(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-q", "-b", "main")
    git(repo, "config", "user.name", "Test")
    git(repo, "config", "user.email", "test@example.invalid")
    (repo / "a.py").write_text("value = 0\n")
    (repo / "b.py").write_text("value = 0\n")
    (repo / "test_guard.py").write_text(
        "import a, b\ndef test_combined():\n    assert a.value + b.value <= 1\n"
    )
    git(repo, "add", ".")
    git(repo, "commit", "-qm", "base")

    def check():
        return subprocess.run(
            [sys.executable, "-m", "pytest", "-q", "test_guard.py"], cwd=repo,
            capture_output=True, text=True,
            env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
        )

    git(repo, "checkout", "-qb", "first")
    (repo / "a.py").write_text("value = 1\n")
    git(repo, "commit", "-qam", "first")
    assert check().returncode == 0
    git(repo, "checkout", "-q", "main")
    git(repo, "checkout", "-qb", "second")
    (repo / "b.py").write_text("value = 1\n")
    git(repo, "commit", "-qam", "second")
    assert check().returncode == 0
    git(repo, "checkout", "-q", "first")
    git(repo, "merge", "--no-ff", "-qm", "both", "second")
    red_sha = git(repo, "rev-parse", "HEAD")
    red = check()
    assert red.returncode == 1
    assert "FAILED test_guard.py::test_combined" in red.stdout
    git(repo, "commit", "--allow-empty", "-qm", "cancelled")
    cancelled_sha = git(repo, "rev-parse", "HEAD")
    git(repo, "commit", "--allow-empty", "-qm", "pending")
    pending_sha = git(repo, "rev-parse", "HEAD")

    monkeypatch.setattr(fixtures.mr.gate, "default_stack_index", lambda: {})
    monkeypatch.setattr(fixtures.mr, "utc_now_iso", lambda: "2026-11-11T05:00:00Z")
    checks = {
        pending_sha: fixtures._scripts_check(None, status="in_progress", summary=""),
        cancelled_sha: fixtures._scripts_check("cancelled", summary=""),
        red_sha: fixtures._scripts_check(
            "failure", summary="FAILED test_guard.py::test_combined - assertion"
        ),
    }
    hold = tmp_path / "hold.txt"
    hold.write_text("16808 attente utilisateur\n")
    journal = tmp_path / "journal.jsonl"
    for _ in range(2):
        runner = fixtures.ScriptedRunner(
            main_sha=pending_sha,
            main_history=[pending_sha, cancelled_sha, red_sha],
            main_checks_by_sha=checks,
        )
        rc = fixtures.mr.run(
            ["--journal", str(journal), "--hold-file", str(hold), "--apply"],
            runner=runner,
        )
        assert rc == 0
        assert not any("gh pr merge" in command for command in runner.flat())
        text = hold.read_text()
        assert "16808 attente utilisateur" in text
        assert f"sha={red_sha}" in text
        assert "test=test_guard.py::test_combined" in text
