"""Tests for scripts/check_docs_reference_lane.py -- the perennial-reference lane (#14623).

Covers both directions of the contract (integrity: the header date must agree
with ``git log -1`` of the file itself, never a recopied value; coverage: the
marked count must not drop below the baseline floor), the exemptions (transient
lane, archive, generated artefacts), the CLI exit codes, and the real
repository tree.

The integrity direction needs real git history, so the fixture is a temporary
repository whose commit date is pinned via ``GIT_COMMITTER_DATE`` -- that makes
the freshness comparison deterministic.
"""

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_docs_reference_lane as ref

# Header whose date agrees with a 2026-10-25 commit.
HEADER = "> REFERENCE — vivante — dernière révision 2026-10-25"


def _git(cwd: Path, *args: str, env: dict | None = None) -> None:
    subprocess.run(
        ["git", *args],
        cwd=cwd,
        check=True,
        env=env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )


@pytest.fixture()
def git_tree(tmp_path: Path) -> Path:
    """A temporary git repository with an empty docs/reference/ tree."""
    _git(tmp_path, "init", "-q")
    _git(tmp_path, "config", "user.email", "t@t")
    _git(tmp_path, "config", "user.name", "t")
    (tmp_path / "docs" / "reference").mkdir(parents=True)
    return tmp_path


def _commit(tree: Path, when: str = "2026-10-25 12:00:00 +0000") -> None:
    env = os.environ.copy()
    env["GIT_AUTHOR_DATE"] = when
    env["GIT_COMMITTER_DATE"] = when
    _git(tree, "add", "-A", env=env)
    _git(tree, "commit", "-q", "-m", "c", env=env)


def _write(tree: Path, rel: str, body: str) -> Path:
    path = tree / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")
    return path


def _reasons(report: dict) -> list[str]:
    return [f["reason"].split(":")[0] for f in report["findings"]]


def test_fresh_header_is_conforme(git_tree: Path) -> None:
    _write(git_tree, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    _commit(git_tree)  # commit date 2026-10-25 == header date
    report = ref.run(root=git_tree, baseline=1)
    assert report["verdict"] == "CONFORME", report["findings"]
    assert report["perenne_covered"] == 1


def test_stale_header_date_is_a_violation(git_tree: Path) -> None:
    # Header says 2026-10-25 but the file was last revised 2026-10-24.
    _write(git_tree, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    _commit(git_tree, when="2026-10-24 12:00:00 +0000")
    report = ref.run(root=git_tree, baseline=1)
    assert report["verdict"] == "VIOLATION"
    assert _reasons(report) == ["STALE_DATE"]


def test_coverage_below_floor_is_a_violation(git_tree: Path) -> None:
    _write(git_tree, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    _commit(git_tree)
    report = ref.run(root=git_tree, baseline=5)  # only 1 marked, floor 5
    assert report["verdict"] == "VIOLATION"
    assert _reasons(report) == ["COVERAGE_BELOW_FLOOR"]


def test_coverage_at_floor_is_conforme(git_tree: Path) -> None:
    _write(git_tree, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    _commit(git_tree)
    report = ref.run(root=git_tree, baseline=1)
    assert report["verdict"] == "CONFORME", report["findings"]


def test_unmarked_doc_is_not_a_finding(git_tree: Path) -> None:
    # A perennial doc without the header is simply not (yet) covered: no finding,
    # and with floor 0 the tree is conforme.
    _write(git_tree, "docs/reference/plain.md", "# Plain reference\n\ntexte\n")
    _commit(git_tree)
    report = ref.run(root=git_tree, baseline=0)
    assert report["verdict"] == "CONFORME", report["findings"]
    assert report["perenne_covered"] == 0
    assert report["perenne_total"] == 1


def test_transient_and_archive_are_excluded(git_tree: Path) -> None:
    # A report header in the transient lane and a dated file in the archive must
    # not be counted as perennial, nor integrity-checked.
    _write(
        git_tree,
        "docs/transients/2026-10-25-rapport.md",
        "> RAPPORT — 2026-10-25 — perimetre — figé\n# Rapport\n",
    )
    _write(git_tree, "docs/archive/vieux.md", f"{HEADER}\n# Vieux\n")
    _commit(git_tree)
    report = ref.run(root=git_tree, baseline=0)
    assert report["perenne_total"] == 0
    assert report["verdict"] == "CONFORME", report["findings"]


def test_generated_artefact_is_excluded(git_tree: Path) -> None:
    # A generated catalog with a stale header is not a hand-maintained reference.
    _write(
        git_tree,
        "docs/COURSE_CATALOG.generated.md",
        "> REFERENCE — vivante — dernière révision 2020-01-01\n# Catalogue\n",
    )
    _commit(git_tree)
    report = ref.run(root=git_tree, baseline=0)
    assert report["perenne_total"] == 0
    assert report["verdict"] == "CONFORME", report["findings"]


def test_dash_and_accent_variants_are_tolerated(git_tree: Path) -> None:
    # Hyphen dashes + unaccented "derniere revision": the writer's variant.
    tolerant = "> REFERENCE - vivante - derniere revision 2026-10-25"
    _write(git_tree, "docs/reference/variant.md", f"{tolerant}\n# V\n")
    _commit(git_tree)
    report = ref.run(root=git_tree, baseline=1)
    assert report["verdict"] == "CONFORME", report["findings"]


def test_quoted_header_deep_in_body_is_ignored(git_tree: Path) -> None:
    # A header quoted well below the header window is not a marking.
    body = (
        "# Doc perenne\n\n" + "\n".join(f"ligne {i}" for i in range(12)) + f"\n\n{HEADER}\n"
    )
    _write(git_tree, "docs/reference/quoted.md", body)
    _commit(git_tree)
    report = ref.run(root=git_tree, baseline=0)
    assert report["verdict"] == "CONFORME", report["findings"]
    assert report["perenne_covered"] == 0


def test_git_failure_is_a_finding_not_a_pass(tmp_path: Path) -> None:
    # Not a git repo: reading the last commit date fails -> finding, not a pass.
    (tmp_path / "docs" / "reference").mkdir(parents=True)
    _write(tmp_path, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    report = ref.run(root=tmp_path, baseline=1)
    assert report["verdict"] == "VIOLATION"
    assert "GIT_LOG_FAILED" in _reasons(report)


def test_cli_exit_codes_and_json(git_tree: Path, capsys: pytest.CaptureFixture) -> None:
    _write(git_tree, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    _commit(git_tree, when="2026-10-24 12:00:00 +0000")  # stale
    assert ref.main(["--root", str(git_tree), "--baseline", "1", "--json"]) == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["verdict"] == "VIOLATION"


def test_real_tree_is_conforme() -> None:
    """Wiring: the repository's own tree must satisfy the convention at its
    first-wave baseline (9 marked docs, all dates agreeing with git)."""
    report = ref.run()
    assert report["verdict"] == "CONFORME", report["findings"]
