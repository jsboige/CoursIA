#!/usr/bin/env python3
"""Tests de check_orphan_post_merge_commits.py — depots git synthetiques reels.

Les fixtures construisent de vrais depots git dans `tmp_path` plutot que de simuler
la sortie de git : la classe de faux-positif que l'outil doit eviter (les commits
d'origine d'un squash-merge) n'apparait que dans une vraie topologie.

Executable des deux facons :
    py scripts/tests/test_check_orphan_post_merge_commits.py
    npx pytest scripts/tests/test_check_orphan_post_merge_commits.py
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "audit"))

import check_orphan_post_merge_commits as mod  # noqa: E402


BASE_TS = datetime(2026, 7, 20, 12, 0, 0, tzinfo=timezone.utc)


def iso(dt: datetime) -> str:
    return dt.strftime("%Y-%m-%dT%H:%M:%S+00:00")


def git(repo: Path, *args: str, at: datetime | None = None) -> str:
    env = None
    if at is not None:
        import os

        env = os.environ.copy()
        env["GIT_AUTHOR_DATE"] = iso(at)
        env["GIT_COMMITTER_DATE"] = iso(at)
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True, text=True, env=env, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise AssertionError(f"git {' '.join(args)} -> {proc.stderr.strip()}")
    return proc.stdout.strip()


def write(repo: Path, name: str, content: str) -> None:
    (repo / name).write_text(content, encoding="utf-8")


def init_repo(root: Path) -> Path:
    repo = root / "repo"
    repo.mkdir(parents=True, exist_ok=True)
    git(repo, "init", "-q", "-b", "main")
    git(repo, "config", "user.email", "test@example.invalid")
    git(repo, "config", "user.name", "Test")
    write(repo, "README.md", "base\n")
    git(repo, "add", "README.md")
    git(repo, "commit", "-q", "-m", "base", at=BASE_TS)
    return repo


def make_squash_merged_branch(repo: Path) -> datetime:
    """Branche 'feat' avec 2 commits, squashee dans main. Rend l'instant du merge."""
    git(repo, "checkout", "-q", "-b", "feat")
    write(repo, "feature.txt", "first\n")
    git(repo, "add", "feature.txt")
    git(repo, "commit", "-q", "-m", "wip 1", at=BASE_TS + timedelta(hours=1))
    write(repo, "feature.txt", "first\nsecond\n")
    git(repo, "add", "feature.txt")
    git(repo, "commit", "-q", "-m", "wip 2", at=BASE_TS + timedelta(hours=2))

    merged_at = BASE_TS + timedelta(hours=3)
    git(repo, "checkout", "-q", "main")
    git(repo, "merge", "-q", "--squash", "feat")
    git(repo, "commit", "-q", "-m", "squashed feat (#1)", at=merged_at)
    git(repo, "checkout", "-q", "feat")
    return merged_at


def pr(merged_at: datetime, head: str = "feat", number: int = 1) -> dict:
    return {"number": number, "title": "feat", "headRefName": head,
            "mergedAt": iso(merged_at)}


# --------------------------------------------------------------------------- tests

def test_squash_originals_are_not_orphans(root: Path) -> None:
    """Les commits d'origine d'un squash sont inaccessibles mais PAS orphelins."""
    repo = init_repo(root)
    merged_at = make_squash_merged_branch(repo)

    result = mod.analyse_pr(repo, pr(merged_at), base_ref="main", remote="")

    assert result["unreachable_total"] == 2, result
    assert result["post_merge"] == 0, result
    assert result["status"] == "clean", result


def test_post_merge_commit_is_flagged(root: Path) -> None:
    """Un commit pousse APRES le merge, absent de main, est un finding."""
    repo = init_repo(root)
    merged_at = make_squash_merged_branch(repo)

    write(repo, "capstone.txt", "theorem evolve_shift\n")
    git(repo, "add", "capstone.txt")
    git(repo, "commit", "-q", "-m", "capstone", at=merged_at + timedelta(minutes=11))

    result = mod.analyse_pr(repo, pr(merged_at), base_ref="main", remote="")

    assert result["status"] == "orphan", result
    assert result["post_merge"] == 1, result
    assert result["paths"] == ["capstone.txt"], result
    assert result["commits"][0]["subject"] == "capstone", result


def test_relanded_content_is_not_an_orphan(root: Path) -> None:
    """Un contenu poste-merge re-atterri par une autre route n'est pas orphelin."""
    repo = init_repo(root)
    merged_at = make_squash_merged_branch(repo)

    write(repo, "capstone.txt", "theorem evolve_shift\n")
    git(repo, "add", "capstone.txt")
    git(repo, "commit", "-q", "-m", "capstone", at=merged_at + timedelta(minutes=11))
    sha = git(repo, "rev-parse", "HEAD")

    git(repo, "checkout", "-q", "main")
    git(repo, "cherry-pick", sha)
    git(repo, "checkout", "-q", "feat")

    result = mod.analyse_pr(repo, pr(merged_at), base_ref="main", remote="")

    assert result["post_merge"] == 1, result
    assert result["status"] == "clean", result
    assert "re-landed" in result["reason"], result


def test_deleted_branch_is_reported_not_flagged(root: Path) -> None:
    """Branche supprimee : indetectable, signale sans compter comme finding."""
    repo = init_repo(root)
    merged_at = make_squash_merged_branch(repo)
    git(repo, "checkout", "-q", "main")
    git(repo, "branch", "-q", "-D", "feat")

    result = mod.analyse_pr(repo, pr(merged_at), base_ref="main", remote="")

    assert result["status"] == "branch_gone", result


def test_missing_merged_at_is_skipped(root: Path) -> None:
    repo = init_repo(root)
    result = mod.analyse_pr(repo, {"number": 9, "headRefName": "feat"},
                            base_ref="main", remote="")
    assert result["status"] == "skipped", result


def test_parse_ts_accepts_z_and_offset(root: Path) -> None:
    z = mod.parse_ts("2026-07-29T04:10:39Z")
    off = mod.parse_ts("2026-07-29T06:10:39+02:00")
    assert z == off, (z, off)
    assert mod.parse_ts("2026-07-29T04:10:39").tzinfo is not None


def test_filter_by_age(root: Path) -> None:
    now = datetime(2026, 7, 29, tzinfo=timezone.utc)
    prs = [
        {"number": 1, "mergedAt": iso(now - timedelta(days=3))},
        {"number": 2, "mergedAt": iso(now - timedelta(days=40))},
        {"number": 3},
    ]
    kept = [p["number"] for p in mod.filter_by_age(prs, days=14, now=now)]
    assert kept == [1], kept
    assert len(mod.filter_by_age(prs, days=0, now=now)) == 3


def test_main_end_to_end_advisory_then_strict(root: Path) -> None:
    """L'outil sort 0 par defaut (advisory) et 1 avec --strict sur un orphelin."""
    repo = init_repo(root)
    merged_at = make_squash_merged_branch(repo)
    write(repo, "capstone.txt", "theorem evolve_shift\n")
    git(repo, "add", "capstone.txt")
    git(repo, "commit", "-q", "-m", "capstone", at=merged_at + timedelta(minutes=11))

    prs_json = root / "prs.json"
    prs_json.write_text(json.dumps([pr(merged_at)]), encoding="utf-8")
    out_json = root / "out.json"

    argv = ["--repo-path", str(repo), "--base-ref", "main", "--remote", "",
            "--days", "0", "--from-json", str(prs_json), "--json-out", str(out_json)]

    assert mod.main(argv) == 0
    assert mod.main(argv + ["--strict"]) == 1

    payload = json.loads(out_json.read_text(encoding="utf-8"))
    assert [r["status"] for r in payload["results"]] == ["orphan"], payload


def test_bad_repo_path_exits_2(root: Path) -> None:
    prs_json = root / "empty.json"
    prs_json.write_text("[]", encoding="utf-8")
    code = mod.main(["--repo-path", str(root / "nope"), "--from-json", str(prs_json)])
    assert code == 2, code


# --------------------------------------------------------------------- harnais

try:  # pytest fournit tmp_path ; on mappe root dessus.
    import pytest

    @pytest.fixture()
    def root(tmp_path: Path) -> Path:  # noqa: D103
        return tmp_path
except ImportError:  # pragma: no cover - execution directe sans pytest
    pass


def run_direct() -> int:
    tests = [(n, f) for n, f in sorted(globals().items())
             if n.startswith("test_") and callable(f)]
    failures = 0
    for name, fn in tests:
        with tempfile.TemporaryDirectory() as tmp:
            try:
                fn(Path(tmp))
                print(f"PASS  {name}")
            except Exception as exc:  # noqa: BLE001
                failures += 1
                print(f"FAIL  {name}: {exc}")
    print(f"\n{len(tests) - failures}/{len(tests)} tests passes")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(run_direct())
