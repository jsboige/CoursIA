"""Tests for scripts/check_docs_reference_lane.py -- the perennial-reference lane (#14623).

Covers both directions of the contract in their two modes (review of #22527):

  tree mode (default) : marker presence + coverage floor over the whole
      perennial set -- dates are NOT compared, because a squash-merge rewrites
      ``%cs`` to the merge time and a tree-wide date equality would redden
      ``main`` at each merge crossing a UTC day;
  PR mode (``--base``) : dates are compared, only for the docs the PR modifies,
      against each doc's own last commit (fail-closed on git errors).

The integrity direction needs real git history, so the fixture is a temporary
repository whose commit dates are pinned via ``GIT_COMMITTER_DATE`` -- that
makes the freshness comparison deterministic.
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
    """A temporary git repository with an empty docs/reference/ tree and an
    empty base commit tagged ``base0`` -- the ref PR-mode tests diff against."""
    _git(tmp_path, "init", "-q", "-b", "main")
    _git(tmp_path, "config", "user.email", "t@t")
    _git(tmp_path, "config", "user.name", "t")
    (tmp_path / "docs" / "reference").mkdir(parents=True)
    (tmp_path / ".keep").write_text("", encoding="utf-8")
    _commit(tmp_path)  # base commit, dated 2026-10-25
    _git(tmp_path, "tag", "base0")
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


# ---------------------------------------------------------------------------
# Tree mode: marker + floor only (survives the squash)
# ---------------------------------------------------------------------------


def test_fresh_header_is_conforme(git_tree: Path) -> None:
    _write(git_tree, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    _commit(git_tree)  # commit date 2026-10-25 == header date
    report = ref.run(root=git_tree, baseline=1)
    assert report["verdict"] == "CONFORME", report["findings"]
    assert report["perenne_covered"] == 1
    assert report["mode"] == "tree"


def test_tree_mode_ignores_dates_entirely(git_tree: Path) -> None:
    # Same stale header as below, but tree mode deliberately does not read git
    # dates: on a squash-merged main, %cs is the merge time and a tree-wide
    # date equality would redden main at each merge crossing a UTC day.
    _write(git_tree, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    _commit(git_tree, when="2026-10-24 12:00:00 +0000")
    report = ref.run(root=git_tree, baseline=1)
    assert report["verdict"] == "CONFORME", report["findings"]
    assert report["date_checked"] == 0


def test_squash_dated_next_day_does_not_redden(git_tree: Path) -> None:
    """The defect measured in review of #22527: a squash-merge carries the
    merge time as committer date. Simulate it -- branch head dated D, squash
    commit on main dated D+1 touching the same doc -- and require that the
    organ stays CONFORME on the squashed main (tree mode), while the date
    machinery still holds where it is readable (PR mode on the branch)."""
    doc = "docs/reference/doc.md"
    _write(git_tree, doc, f"{HEADER}\n# Reference\n")
    _commit(git_tree)  # D = 2026-10-25, header agrees

    # Branch: revise the content at D (header still agrees with the branch).
    _git(git_tree, "checkout", "-q", "-b", "pr")
    _write(git_tree, doc, f"{HEADER}\n# Reference\n\nrevu sur la branche\n")
    _commit(git_tree)  # still D
    branch_report = ref.run(root=git_tree, baseline=1, base="base0")
    assert branch_report["verdict"] == "CONFORME", branch_report["findings"]
    assert branch_report["date_checked"] == 1

    # Squash onto main: one commit whose committer date is D+1 (merge time),
    # author preserved -- the exact shape of a GitHub squash-merge.
    _git(git_tree, "checkout", "-q", "main")
    env = os.environ.copy()
    env["GIT_AUTHOR_DATE"] = "2026-10-25 12:00:00 +0000"  # preserved author
    env["GIT_COMMITTER_DATE"] = "2026-10-26 14:00:00 +0000"  # merge time
    _git(git_tree, "checkout", "pr", "--", doc, env=env)
    _git(git_tree, "add", "-A", env=env)
    _git(git_tree, "commit", "-q", "-m", "squash (#N)", env=env)

    # Tree mode on the squashed main: marker + floor only -> CONFORME. The
    # pre-rework organ compared the header (D) to %cs (D+1) and reddened.
    report = ref.run(root=git_tree, baseline=1)
    assert report["verdict"] == "CONFORME", report["findings"]


# ---------------------------------------------------------------------------
# PR mode: dates, only for the docs the PR modifies
# ---------------------------------------------------------------------------


def test_pr_mode_detects_stale_touched_doc(git_tree: Path) -> None:
    # Header says 2026-10-25 but the file was last revised 2026-10-24.
    _write(git_tree, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    _commit(git_tree, when="2026-10-24 12:00:00 +0000")
    report = ref.run(root=git_tree, baseline=1, base="base0")
    assert report["verdict"] == "VIOLATION"
    assert _reasons(report) == ["STALE_DATE"]
    assert report["date_checked"] == 1
    assert report["mode"] == "pr"


def test_pr_mode_checks_only_touched_docs(git_tree: Path) -> None:
    # A stale untouched doc (last revised on the base) must NOT be a finding:
    # the PR did not modify it, and after a squash its %cs is unreadable noise.
    stale = "> REFERENCE — vivante — dernière révision 2026-10-25"
    _write(git_tree, "docs/reference/stale.md", f"{stale}\n# Stale\n")
    _commit(git_tree, when="2026-10-24 12:00:00 +0000")  # base: stale already
    _git(git_tree, "tag", "-f", "base0")

    fresh = "> REFERENCE — vivante — dernière révision 2026-10-25"
    _write(git_tree, "docs/reference/fresh.md", f"{fresh}\n# Fresh\n")
    _commit(git_tree)  # touched by the PR, date agrees

    report = ref.run(root=git_tree, baseline=2, base="base0")
    assert report["verdict"] == "CONFORME", report["findings"]
    assert report["date_checked"] == 1  # fresh.md only


def test_pr_mode_flags_touched_doc_with_unrefreshed_header(git_tree: Path) -> None:
    # The real signal the organ exists for: the PR revises a doc on 10-25 but
    # its header still says 10-24 -- revision without refresh.
    old = "> REFERENCE — vivante — dernière révision 2026-10-24"
    _write(git_tree, "docs/reference/doc.md", f"{old}\n# Reference\n")
    _commit(git_tree)  # 2026-10-25: content revised, header left at 10-24
    report = ref.run(root=git_tree, baseline=1, base="base0")
    assert report["verdict"] == "VIOLATION"
    assert _reasons(report) == ["STALE_DATE"]


def test_git_failure_is_a_find_not_a_pass(tmp_path: Path) -> None:
    # Not a git repo: reading the changed set fails -> finding, never a pass.
    (tmp_path / "docs" / "reference").mkdir(parents=True)
    _write(tmp_path, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    report = ref.run(root=tmp_path, baseline=1, base="main")
    assert report["verdict"] == "VIOLATION"
    assert "GIT_DIFF_FAILED" in _reasons(report)


# ---------------------------------------------------------------------------
# Coverage (both modes)
# ---------------------------------------------------------------------------


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
    report = ref.run(root=git_tree, baseline=0, base="base0")
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
    report = ref.run(root=git_tree, baseline=0, base="base0")
    assert report["perenne_total"] == 0
    assert report["verdict"] == "CONFORME", report["findings"]


# ---------------------------------------------------------------------------
# Header shape
# ---------------------------------------------------------------------------


def test_dash_and_accent_variants_are_tolerated(git_tree: Path) -> None:
    # Hyphen dashes + unaccented "derniere revision": the writer's variant.
    tolerant = "> REFERENCE - vivante - derniere revision 2026-10-25"
    _write(git_tree, "docs/reference/variant.md", f"{tolerant}\n# V\n")
    _commit(git_tree)
    report = ref.run(root=git_tree, baseline=1, base="base0")
    assert report["verdict"] == "CONFORME", report["findings"]


def test_quoted_header_deep_in_body_is_ignored(git_tree: Path) -> None:
    # A header quoted well below the header window is not a marking.
    body = (
        "# Doc perenne\n\n" + "\n".join(f"ligne {i}" for i in range(12)) + f"\n\n{HEADER}\n"
    )
    _write(git_tree, "docs/reference/quoted.md", body)
    _commit(git_tree)
    report = ref.run(root=git_tree, baseline=0, base="base0")
    assert report["verdict"] == "CONFORME", report["findings"]
    assert report["perenne_covered"] == 0


# ---------------------------------------------------------------------------
# CLI + wiring
# ---------------------------------------------------------------------------


def test_cli_exit_codes_and_json(git_tree: Path, capsys: pytest.CaptureFixture) -> None:
    _write(git_tree, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    _commit(git_tree, when="2026-10-24 12:00:00 +0000")  # stale in PR mode
    assert ref.main(
        ["--root", str(git_tree), "--baseline", "1", "--base", "base0", "--json"]
    ) == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["verdict"] == "VIOLATION"
    assert payload["mode"] == "pr"


def test_cli_tree_mode_json(git_tree: Path, capsys: pytest.CaptureFixture) -> None:
    _write(git_tree, "docs/reference/doc.md", f"{HEADER}\n# Reference\n")
    _commit(git_tree, when="2026-10-24 12:00:00 +0000")  # ignored in tree mode
    assert ref.main(["--root", str(git_tree), "--baseline", "1", "--json"]) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["mode"] == "tree"


def test_real_tree_is_conforme() -> None:
    """Wiring: the repository's own tree must satisfy the convention at its
    first-wave baseline (9 marked docs; tree mode = marker + floor, dates are
    the PR guard's job)."""
    report = ref.run()
    assert report["verdict"] == "CONFORME", report["findings"]
    assert report["perenne_covered"] >= 9
