#!/usr/bin/env python3
"""Unit tests for ``count_revisions_follow`` (Phase 0 EPIC #9768, #13776).

The function under test is the **rename-aware** counter used by
``phase0_sample_stratify`` to decide which ``band`` (1 / 2-4 / 5-9 / 10-19 /
20-39 / 40+) a notebook falls into. It runs ``git log --follow`` on the
current path, which traverses renames back to the original commit.

Without ``--follow``, the counter would silently drop revisions made under
the OLD path -- on a real notebook (``GameTheory/GameTheory-01-Setup.ipynb``)
the ratio is 2 vs 52, i.e. a factor of 26. A refactor that removes
``--follow`` from the argv would pass every existing test (none traverse
this function) but corrupt the band classification for any renamed
notebook. The test below pins that ``--follow`` is present.

## Why a fixture git repo, not the corpus

REPO_ROOT is hardcoded module-level in ``phase0_sample_stratify.py``
(``Path(__file__).resolve().parents[2]``). The function takes a notebook
Path and resolves it relative to REPO_ROOT. We monkey-patch REPO_ROOT on
the module for the duration of the test, then point at a tmp_path that
contains the freshly-initialised git repo with a renamed commit history.
That keeps the test fully self-contained -- no corpus dependency, no
breakage if the corpus is renamed again.

## FN-safety (acceptance #13776 acceptance #2)

The assertion is the ONLY thing that makes this test useful. A test that
stays green after removing ``--follow`` from the argv (e.g. an
``or True`` short-circuit) is dead -- exactly the #13667 pattern the issue
calls out. We assert:

  - ``count_revisions_follow`` returns 2 (rename-aware)
  - ``git log`` (no --follow) on the new path returns 1 (no rename-awareness)

If a future refactor drops --follow, ``count_revisions_follow`` returns 1
instead of 2, the assert fails, the test goes red.
"""
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

import phase0_sample_stratify as p0ss  # noqa: E402


# Skip the whole module if git is not available -- the function under test
# shells out to git, the fixture shells out to git. No way to fake that
# without losing the integration value of the test.
_GIT = shutil.which("git")
pytestmark = pytest.mark.skipif(_GIT is None, reason="git binary absent")


@pytest.fixture
def fake_repo(tmp_path, monkeypatch):
    """A fresh git repo in tmp_path with one initial commit + one rename commit.

    Yields the repo root. Patches ``phase0_sample_stratify.REPO_ROOT`` so the
    function under test resolves relative paths against our fixture, not
    against the real CoursIA repo. Restores REPO_ROOT on teardown.

    The two commits share a multi-line ``notebook_content`` body so that
    ``git log --follow`` actually traverses the rename -- ``--follow``
    uses content similarity to detect renames, and a 1-line diff is below
    the default rename-detection threshold. Pinning the content here
    keeps the test deterministic across git versions.
    """
    monkeypatch.setattr(p0ss, "REPO_ROOT", tmp_path)

    def _git(*args):
        return subprocess.run(
            ["git", *args],
            cwd=tmp_path,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=True,
        )

    _git("init", "--quiet")
    # Identity needed so commits don't get the global identity by accident.
    _git("config", "user.email", "test@example.invalid")
    _git("config", "user.name", "test")
    # Disable autocrlf so the commit subject lines don't get rewritten on Windows.
    _git("config", "core.autocrlf", "false")

    # Multi-line content shared by both versions so ``--follow``'s similarity
    # detector fires (single-line files are below the rename threshold and
    # would silently drop the pre-rename commit).
    notebook_content = (
        "# Cell 1 -- notebook setup\n"
        "import numpy as np\n"
        "\n"
        "# Cell 2 -- pedagogical prose\n"
        "# The notebook demonstrates the rename-aware counter behaviour.\n"
        "\n"
        "# Cell 3 -- main logic\n"
        "def main():\n"
        "    return 42\n"
    )

    old = tmp_path / "notebook_old.ipynb"
    old.write_text(notebook_content, encoding="utf-8")
    _git("add", "notebook_old.ipynb")
    _git("commit", "--quiet", "-m", "initial commit of notebook_old.ipynb")

    new = tmp_path / "notebook_new.ipynb"
    _git("mv", "notebook_old.ipynb", "notebook_new.ipynb")
    # Append a line so the second commit isn't empty (some repos reject empties)
    # while preserving enough of the original body for --follow to detect the rename.
    new.write_text(notebook_content + "# Edit after rename\n", encoding="utf-8")
    _git("add", "notebook_new.ipynb")
    _git("commit", "--quiet", "-m", "rename notebook_old to notebook_new")

    return tmp_path


def test_count_revisions_follow_traverses_rename(fake_repo):
    """Acceptance #13776 #1: ``count_revisions_follow`` returns >=2 across rename.

    With ``--follow`` the git log walks the rename history back to the
    original commit, so both commits count. This is the function's whole
    reason to exist.
    """
    new_path = fake_repo / "notebook_new.ipynb"
    n = p0ss.count_revisions_follow(new_path)
    assert n >= 2, (
        f"count_revisions_follow returned {n}, expected >=2 (rename-aware). "
        "Either --follow was dropped from the argv, or the fixture is wrong."
    )


def test_count_revisions_follow_drops_without_follow(fake_repo):
    """Acceptance #13776 #2 (FN-safety): plain ``git log`` on the new path
    does NOT see the rename -- it sees only the second commit. This proves
    the test above really exercises the ``--follow`` flag, not an
    accidental short-circuit (cf. the dead ``or True`` pattern from
    #13667 that the issue explicitly warns about).
    """
    plain = subprocess.run(
        ["git", "log", "HEAD", "--format=oneline", "--", "notebook_new.ipynb"],
        cwd=fake_repo,
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=True,
    )
    plain_count = sum(1 for line in plain.stdout.splitlines() if line.strip())
    assert plain_count == 1, (
        f"plain git log on the new path returned {plain_count}, expected 1. "
        "Fixture sanity check failed -- the rename isn't a real rename."
    )

    new_path = fake_repo / "notebook_new.ipynb"
    n = p0ss.count_revisions_follow(new_path)
    assert n > plain_count, (
        f"count_revisions_follow ({n}) must strictly exceed plain git log "
        f"({plain_count}). If they're equal, --follow is not in the argv."
    )


def test_count_revisions_follow_returns_zero_on_unknown_path(fake_repo):
    """A path that doesn't exist in git history returns 0, not an exception.

    This is the ``CalledProcessError`` branch of the function (l.231-232 of
    phase0_sample_stratify.py). Pinning it prevents a future refactor that
    raises instead of returning 0 -- the caller relies on the 0 return to
    fall back to the fast-path counter.
    """
    bogus = fake_repo / "does_not_exist.ipynb"
    n = p0ss.count_revisions_follow(bogus)
    assert n == 0, f"unknown path returned {n}, expected 0 (fallback branch)"
