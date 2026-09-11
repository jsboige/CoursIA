"""Regression tests for unreadable fast-lane merge bases (#15553)."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import fast_lane  # noqa: E402
from fast_lane_registry import Guard  # noqa: E402


def _completed(args, returncode=0, stdout="", stderr=""):
    return subprocess.CompletedProcess(args, returncode, stdout, stderr)


def test_unreadable_diff_refetches_exact_remote_tracking_ref(monkeypatch):
    calls = []
    results = iter([
        _completed([], 128, stderr="fatal: no merge base"),
        _completed([], 0),
        _completed([], 0, stdout="scripts/bad.py\n"),
    ])

    def fake_run(cmd, **kwargs):
        calls.append(cmd)
        return next(results)

    monkeypatch.setattr(subprocess, "run", fake_run)

    assert fast_lane.changed_files("origin/main") == ["scripts/bad.py"]
    assert calls == [
        ["git", "diff", "--name-only", "origin/main...HEAD"],
        ["git", "fetch", "--refetch", "--filter=blob:none", "origin",
         "+refs/heads/main:refs/remotes/origin/main"],
        ["git", "diff", "--name-only", "origin/main...HEAD"],
    ]


def test_unreadable_diff_stays_fail_closed_with_infrastructure_cause(monkeypatch):
    results = iter([
        _completed([], 128, stderr="fatal: no merge base"),
        _completed([], 0),
        _completed([], 128, stderr="error: Could not read deadbeef"),
    ])
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: next(results))

    with pytest.raises(SystemExit) as exc:
        fast_lane.changed_files("origin/main")

    message = str(exc.value)
    assert "[infrastructure][fail-closed]" in message
    assert "aucun verdict de garde n'a ete calcule" in message
    assert "Could not read deadbeef" in message


def test_readable_real_guard_failure_remains_blocking(
        monkeypatch, tmp_path, capsys):
    """Negative control: a readable diff and failing guard must stay red."""
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t"],
                   check=True)
    subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"],
                   check=True)
    target = tmp_path / "measured.txt"
    target.write_text("base\n", encoding="utf-8")
    subprocess.run(["git", "-C", str(tmp_path), "add", "measured.txt"],
                   check=True)
    subprocess.run(["git", "-C", str(tmp_path), "commit", "-qm", "base"],
                   check=True)
    base_sha = subprocess.run(
        ["git", "-C", str(tmp_path), "rev-parse", "HEAD"],
        check=True, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    ).stdout.strip()
    target.write_text("real defect\n", encoding="utf-8")
    subprocess.run(["git", "-C", str(tmp_path), "commit", "-qam", "defect"],
                   check=True)

    guard = Guard(
        name="negative-control",
        argv=[sys.executable, "-c", "raise SystemExit(1)"],
        source="test",
        paths=["*.txt"],
        blocking=True,
    )
    monkeypatch.setattr(fast_lane, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(fast_lane, "PILOT", [guard])

    rc = fast_lane.main([
        "--base-ref", base_sha,
        "--head-sha", "beef" * 10,
        "--repo", "jsboige/CoursIA",
        "--only", "negative-control",
        "--no-shadow",
        "--dry-run",
    ])

    assert rc == 1
    output = capsys.readouterr().out
    assert "negative-control' -> failure" in output
    assert "au moins un bloquant en echec" in output
