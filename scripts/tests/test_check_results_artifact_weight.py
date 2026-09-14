#!/usr/bin/env python3
"""Tests for scripts/ci/check_results_artifact_weight.py -- #15890.

Each test builds a throwaway git repository (base commit on `main`, work on
a feature branch) and runs the helper as a subprocess with --repo, exactly
as CI runs it against the PR checkout. The verdict JSON on stdout is the
contract under test; the exit code is the blocking semantics.

Run:
    python -m pytest scripts/tests/test_check_results_artifact_weight.py
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

HELPER = (
    Path(__file__).resolve().parents[1]
    / "ci" / "check_results_artifact_weight.py"
)
BAR = 512_000


def _git(repo: Path, *args: str) -> None:
    got = subprocess.run(
        ["git", *args], cwd=repo, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    assert got.returncode == 0, f"git {args}: {got.stderr}"


def _repo_with_base(tmp_path: Path, base_files: dict[str, int]) -> Path:
    """Repo dont le commit `main` porte base_files {path: size}."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-b", "main")
    _git(repo, "config", "user.email", "t@example.com")
    _git(repo, "config", "user.name", "t")
    for rel, size in base_files.items():
        f = repo / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text("x" * size, encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "base")
    _git(repo, "checkout", "-b", "feature")
    return repo


def _run(repo: Path, *extra: str) -> tuple[int, dict]:
    got = subprocess.run(
        [sys.executable, str(HELPER),
         "--repo", str(repo), "--base", "main", *extra],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    # le verdict est le seul objet JSON emis sur stdout (les warnings
    # partent en annotations ::warning, pas en JSON)
    verdict = json.loads(got.stdout[got.stdout.index("{"):])
    return got.returncode, verdict


def _add(repo: Path, rel: str, size: int) -> None:
    f = repo / rel
    f.parent.mkdir(parents=True, exist_ok=True)
    f.write_text("x" * size, encoding="utf-8")
    _git(repo, "add", rel)
    _git(repo, "commit", "-m", f"add {rel}")


def test_new_over_bar_file_is_blocked(tmp_path):
    repo = _repo_with_base(tmp_path, {"README.md": 10})
    _add(repo, "scripts/results/m16_full.json", BAR + 88_000)

    rc, verdict = _run(repo)

    assert rc == 1
    assert verdict["verdict"] == "over_bar"
    assert len(verdict["blocked"]) == 1
    blocked = verdict["blocked"][0]
    assert blocked["path"] == "scripts/results/m16_full.json"
    assert blocked["size_bytes"] == BAR + 88_000
    assert f"{BAR:,}" in blocked["reason"]


def test_new_under_bar_file_passes(tmp_path):
    repo = _repo_with_base(tmp_path, {"README.md": 10})
    _add(repo, "scripts/results/m5_hmm_regime.json", 32_577)

    rc, verdict = _run(repo)

    assert rc == 0
    assert verdict["verdict"] == "ok"
    assert verdict["blocked"] == []


def test_grandfathered_over_bar_modified_is_advisory_only(tmp_path):
    """Artefact deja entre sur la base, modifie : il RESTE, advisory, pas de bloc."""
    repo = _repo_with_base(
        tmp_path, {"scripts/results/m16_legacy.json": BAR + 7_000_000})
    legacy = repo / "scripts/results/m16_legacy.json"
    legacy.write_text("x" * (BAR + 7_100_000), encoding="utf-8")
    _git(repo, "add", "scripts/results/m16_legacy.json")
    _git(repo, "commit", "-m", "rerun m16")

    rc, verdict = _run(repo)

    assert rc == 0, "un artefact grandfathered modifie ne doit PAS bloquer"
    assert verdict["verdict"] == "ok"
    assert len(verdict["advisories"]) == 1
    assert verdict["advisories"][0]["path"] == "scripts/results/m16_legacy.json"
    assert "grandfathered" in verdict["advisories"][0]["reason"]


def test_outside_results_dir_is_ignored(tmp_path):
    repo = _repo_with_base(tmp_path, {"README.md": 10})
    _add(repo, "docs/curriculum/big-but-elsewhere.json", BAR * 4)

    rc, verdict = _run(repo)

    assert rc == 0
    assert verdict["verdict"] == "ok"


def test_deleted_over_bar_file_passes(tmp_path):
    repo = _repo_with_base(
        tmp_path, {"scripts/results/gone.json": BAR * 2, "README.md": 10})
    (repo / "scripts/results/gone.json").unlink()
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", "remove gone")

    rc, verdict = _run(repo)

    assert rc == 0
    assert verdict["verdict"] == "ok"


def test_unknown_base_never_fabricates_a_red(tmp_path):
    repo = _repo_with_base(tmp_path, {"README.md": 10})

    rc, verdict = _run(repo, "--base", "refs/heads/inexistant")

    assert rc == 0, "une panne d'infrastructure ne doit pas rougir le gate"
    assert verdict["verdict"] == "unknown"


def test_bar_is_anchored_on_the_founding_measure():
    """Le bar doit rester ancre : 2.6x le plus gros artefact legitime de main
    (193 333 o, m18_tsfm_benchmark.json, mesure #15890). Un test qui casse
    ici signale que le bar a bouge SANS reancrage -- la politique se discute,
    pas le litteral."""
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))
    from check_results_artifact_weight import RESULTS_BAR_BYTES  # noqa: E402
    assert RESULTS_BAR_BYTES == 512_000
