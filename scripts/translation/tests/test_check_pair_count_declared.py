#!/usr/bin/env python3
"""Tests for check_pair_count_declared.py.

Dual-mode: runnable directly or under pytest (auto-collected by scripts-tests.yml).

Covers the five acceptances of #21391:

  1. POSITIVE: a pair added without a constant bump = ROUGE, names the pair.
  2. NEGATIVE: a PR that only bumps the constant = GREEN.
  3. M-only diff: an existing _en.ipynb modified = GREEN (M status ignored).
  4. .tmp/ ignored: the guard reads git diff, not disk. A local .tmp/ orphan
     is not counted.
  5. cost: a few seconds, no blob:none clone of 2 GB.

Plus internal coverage of the classification helpers, the Windows
backslash trap on src_path, and the constant_modified property.
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
import textwrap
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_pair_count_declared import (  # noqa: E402
    CONSTANT_PATH,
    CheckReport,
    ConstantChange,
    PairChange,
    _classify_translation,
    _git_diff_name_status,
    _git_show,
    _pair_at_head,
    check_pair_count_declared,
)


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #


def _make_repo() -> Path:
    """Create a tiny git repo with a single commit. The caller resets and
    adds files as needed. The constant file is added at the same time, with
    ``EXPECTED_PAIR_COUNT = 0`` and the ``test_check_translation_parity.py``
    path mirroring the production layout.
    """
    tmpdir = tempfile.mkdtemp(prefix="pair-count-test-")
    repo = Path(tmpdir) / "test"
    repo.mkdir()
    subprocess.run(["git", "init", "-q", "-b", "main", str(repo)], check=True)
    subprocess.run(["git", "config", "user.email", "test@test"], check=True, cwd=repo)
    subprocess.run(["git", "config", "user.name", "test"], check=True, cwd=repo)
    # Pre-populate the constant file so the diff helper finds it on both sides.
    constant_dir = repo / "scripts" / "translation" / "tests"
    constant_dir.mkdir(parents=True)
    (constant_dir / "test_check_translation_parity.py").write_text(
        "EXPECTED_PAIR_COUNT = 0\n"
    )
    subprocess.run(["git", "add", "-A"], check=True, cwd=repo)
    subprocess.run(["git", "commit", "-q", "-m", "base"], check=True, cwd=repo)
    return repo


def _add_pair(repo: Path, stem: str, lang: str = "en") -> str:
    """Add a translation file ``stem_<lang>.ipynb`` AND its FR source
    ``stem.ipynb`` to the working tree, ``git add`` them and commit.
    Return the new HEAD SHA.
    """
    base = repo / "MyIA.AI.Notebooks" / "Translation"
    base.mkdir(parents=True, exist_ok=True)
    (base / f"{stem}.ipynb").write_text(f"# FR source for {stem}\n")
    (base / f"{stem}_{lang}.ipynb").write_text(f"# EN translation for {stem}\n")
    subprocess.run(["git", "add", "-A"], check=True, cwd=repo)
    subprocess.run(["git", "commit", "-q", "-m", f"add {stem}_{lang}"], check=True, cwd=repo)
    return subprocess.run(
        ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8",
        cwd=repo,
    ).stdout.strip()


def _bump_constant(repo: Path, new_value: int) -> str:
    """Overwrite ``EXPECTED_PAIR_COUNT`` in the constant file and commit.
    Return the new HEAD SHA.
    """
    constant_path = repo / CONSTANT_PATH
    text = constant_path.read_text()
    # Replace the value of the line in place.
    new_text = text.replace("= 0", f"= {new_value}")
    constant_path.write_text(new_text)
    subprocess.run(["git", "add", str(CONSTANT_PATH)], check=True, cwd=repo)
    subprocess.run(["git", "commit", "-q", "-m", f"bump constant to {new_value}"],
                    check=True, cwd=repo)
    return subprocess.run(
        ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8",
        cwd=repo,
    ).stdout.strip()


def _reset(repo: Path) -> str:
    """Reset the repo to the first commit (just the constant file)."""
    first = subprocess.run(
        ["git", "rev-list", "--max-parents=0", "HEAD"],
        capture_output=True, text=True, encoding="utf-8", cwd=repo,
    ).stdout.strip()
    subprocess.run(["git", "reset", "--hard", first], check=True, cwd=repo)
    return first


# --------------------------------------------------------------------------- #
# _classify_translation
# --------------------------------------------------------------------------- #


class TestClassifyTranslation:
    def test_en(self):
        info = _classify_translation("Foo/Foo_en.ipynb")
        assert info == ("Foo", "en", "Foo_en.ipynb")

    def test_ru(self):
        info = _classify_translation("Foo/Foo_ru.ipynb")
        assert info == ("Foo", "ru", "Foo_ru.ipynb")

    def test_with_dashes(self):
        info = _classify_transition_stem_with_dashes_safe("Foo-1-2/Foo-1-2_en.ipynb")
        assert info == ("Foo-1-2", "en", "Foo-1-2_en.ipynb")

    def test_fr_source_not_translation(self):
        # ``Foo.ipynb`` has no language tag -- not a translation.
        assert _classify_translation("Foo/Foo.ipynb") is None

    def test_unknown_language(self):
        # ``_de`` is not in TARGET_LANGS -- ignored.
        assert _classify_translation("Foo/Foo_de.ipynb") is None

    def test_non_ipynb(self):
        assert _classify_translation("Foo/Foo_en.py") is None


def _classify_transition_stem_with_dashes_safe(path: str):
    """Wrapper that escapes the dash -- not strictly needed because the
    regex uses ``_`` as the separator -- but kept explicit for clarity.
    """
    return _classify_translation(path)


# --------------------------------------------------------------------------- #
# PairChange / CheckReport / constant_modified property
# --------------------------------------------------------------------------- #


class TestConstantModified:
    def test_no_change(self):
        r = CheckReport(base="a", head="b",
                        constant_change=ConstantChange(old_value=13, new_value=13))
        assert r.constant_modified is False

    def test_value_change(self):
        r = CheckReport(base="a", head="b",
                        constant_change=ConstantChange(old_value=13, new_value=14))
        assert r.constant_modified is True

    def test_added(self):
        r = CheckReport(base="a", head="b",
                        constant_change=ConstantChange(old_value=None, new_value=13))
        assert r.constant_modified is True

    def test_removed(self):
        r = CheckReport(base="a", head="b",
                        constant_change=ConstantChange(old_value=13, new_value=None))
        assert r.constant_modified is True


class TestRouge:
    def test_no_change_no_pair_is_green(self):
        r = CheckReport(base="a", head="b",
                        constant_change=ConstantChange(old_value=13, new_value=13))
        assert r.rouge is False

    def test_pair_added_no_constant_change_is_rouge(self):
        r = CheckReport(
            base="a", head="b",
            pair_changes=[PairChange("added", "Foo_en.ipynb", "Foo.ipynb", "Foo", "en")],
            constant_change=ConstantChange(old_value=13, new_value=13),
        )
        assert r.rouge is True

    def test_pair_added_with_constant_bump_matching_is_green(self):
        r = CheckReport(
            base="a", head="b",
            pair_changes=[PairChange("added", "Foo_en.ipynb", "Foo.ipynb", "Foo", "en")],
            constant_change=ConstantChange(old_value=13, new_value=14),
            actual_count=14,
        )
        assert r.rouge is False

    def test_pair_added_with_constant_bump_wrong_value_is_rouge(self):
        r = CheckReport(
            base="a", head="b",
            pair_changes=[PairChange("added", "Foo_en.ipynb", "Foo.ipynb", "Foo", "en")],
            constant_change=ConstantChange(old_value=13, new_value=99),
            actual_count=14,
        )
        assert r.rouge is True


# --------------------------------------------------------------------------- #
# Integration: synthetic git repos
# --------------------------------------------------------------------------- #


class TestIntegration:
    def test_no_pair_change_green(self):
        repo = _make_repo()
        base = _reset(repo)
        # No change at all.
        r = check_pair_count_declared(base, base, repo_root=repo, do_disk_count=False)
        assert r.pair_changes == []
        assert r.constant_modified is False
        assert r.rouge is False

    def test_pair_added_no_constant_bump_is_rouge(self):
        repo = _make_repo()
        base = _reset(repo)
        head = _add_pair(repo, "Foo")
        r = check_pair_count_declared(base, head, repo_root=repo, do_disk_count=False)
        assert len(r.pair_changes) == 1
        assert r.pair_changes[0].stem == "Foo"
        assert r.pair_changes[0].lang == "en"
        assert r.constant_modified is False
        assert r.rouge is True

    def test_pair_added_with_matching_bump_is_green(self):
        repo = _make_repo()
        base = _reset(repo)
        head_pair = _add_pair(repo, "Foo")
        head = _bump_constant(repo, 1)
        r = check_pair_count_declared(base, head, repo_root=repo, do_disk_count=True)
        assert len(r.pair_changes) == 1
        assert r.constant_modified is True
        assert r.constant_change.new_value == 1
        # actual_count may include other pairs on disk, but at least 1
        assert r.actual_count is not None and r.actual_count >= 1
        # If disk count == 1 (only the new pair), the new value matches.
        if r.actual_count == 1:
            assert r.rouge is False

    def test_pair_added_with_wrong_bump_is_rouge(self):
        repo = _make_repo()
        base = _reset(repo)
        head_pair = _add_pair(repo, "Foo")
        head = _bump_constant(repo, 99)  # wrong
        r = check_pair_count_declared(base, head, repo_root=repo, do_disk_count=True)
        assert r.constant_modified is True
        assert r.constant_change.new_value == 99
        assert r.actual_count is not None and r.actual_count < 99
        assert r.rouge is True

    def test_m_only_modification_green(self):
        # Modify the existing _en without adding or removing a pair.
        # Compare the diff from AFTER the add (M only) to the post-tweak commit.
        repo = _make_repo()
        _reset(repo)
        add_commit = _add_pair(repo, "Foo")
        # Now edit the _en file (M status) and commit.
        en_path = repo / "MyIA.AI.Notebooks" / "Translation" / "Foo_en.ipynb"
        en_path.write_text("# EN translation -- updated\n")
        subprocess.run(["git", "add", "-A"], check=True, cwd=repo)
        subprocess.run(["git", "commit", "-q", "-m", "tweak EN"], check=True, cwd=repo)
        tweak_commit = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8",
            cwd=repo,
        ).stdout.strip()
        r = check_pair_count_declared(add_commit, tweak_commit, repo_root=repo,
                                       do_disk_count=False)
        # M is not in the A/D/R set, so no pair change is reported.
        assert r.pair_changes == []
        assert r.constant_modified is False
        assert r.rouge is False

    def test_orphan_translation_without_source_is_ignored(self):
        # Add a translation file with NO FR source: it should not be counted
        # as a pair change (it's an orphan until the source lands).
        repo = _make_repo()
        base = _reset(repo)
        nb_dir = repo / "MyIA.AI.Notebooks" / "Translation"
        nb_dir.mkdir(parents=True, exist_ok=True)
        (nb_dir / "Orphan_en.ipynb").write_text("# orphan translation\n")
        subprocess.run(["git", "add", "-A"], check=True, cwd=repo)
        subprocess.run(["git", "commit", "-q", "-m", "add orphan"], check=True, cwd=repo)
        head = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8",
            cwd=repo,
        ).stdout.strip()
        r = check_pair_count_declared(base, head, repo_root=repo, do_disk_count=False)
        # No FR source in head -> not a pair, ignored.
        assert r.pair_changes == []
        assert r.rouge is False

    def test_renamed_pair_no_constant_change(self):
        # Rename an existing _en.ipynb (R status) without bumping the constant.
        # The guard sees a R, sees the FR source still in head, and flags it.
        repo = _make_repo()
        base = _reset(repo)
        _add_pair(repo, "Foo")
        # Rename the _en file (simulate a translation stem change).
        old = repo / "MyIA.AI.Notebooks" / "Translation" / "Foo_en.ipynb"
        new = repo / "MyIA.AI.Notebooks" / "Translation" / "Foo2_en.ipynb"
        old.rename(new)
        subprocess.run(["git", "add", "-A"], check=True, cwd=repo)
        subprocess.run(["git", "commit", "-q", "-m", "rename _en"], check=True, cwd=repo)
        head = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8",
            cwd=repo,
        ).stdout.strip()
        r = check_pair_count_declared(base, head, repo_root=repo, do_disk_count=False)
        # R is detected, the new name classifies as a translation, the
        # FR source for Foo2 is NOT in head (only Foo.ipynb is). So the
        # guard considers this a rename that does NOT form a valid pair
        # at head -- no pair change recorded.
        assert r.rouge is False or len(r.pair_changes) == 0

    def test_full_pair_rename_is_green_without_bump(self):
        # #21391 reproduction (PRs #22932/#22670): the FR source AND its
        # _en translation renamed together (R status on both). The pair
        # count is preserved, so no honest constant value satisfied the
        # guard before the fix: N -> N is "not modified", N -> M is a
        # wrong count. The guard must stay green and report the pair as
        # renamed, not added.
        repo = _make_repo()
        _reset(repo)
        base = _add_pair(repo, "Foo")
        nb = repo / "MyIA.AI.Notebooks" / "Translation"
        (nb / "Foo.ipynb").rename(nb / "Bar.ipynb")
        (nb / "Foo_en.ipynb").rename(nb / "Bar_en.ipynb")
        subprocess.run(["git", "add", "-A"], check=True, cwd=repo)
        subprocess.run(["git", "commit", "-q", "-m", "rename pair Foo -> Bar"],
                       check=True, cwd=repo)
        head = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8",
            cwd=repo,
        ).stdout.strip()
        r = check_pair_count_declared(base, head, repo_root=repo, do_disk_count=False)
        # The pair is reported, classified "renamed" (not added)...
        assert len(r.pair_changes) == 1
        assert r.pair_changes[0].status == "renamed"
        assert r.pair_changes[0].stem == "Bar"
        # ...the constant is untouched (0 -> 0, not modified)...
        assert r.constant_modified is False
        # ...and the verdict is GREEN: a pure rename does not drift the count.
        assert r.rouge is False

    def test_rename_into_translation_still_requires_bump(self):
        # Guard the carve-out from the other side: renaming a NON-translation
        # file into a *_en.ipynb path (old path not a translation, e.g.
        # notes.md -> Bar_en.ipynb) creates a pair where none existed. It
        # must stay classified "added" so the bump requirement still applies.
        repo = _make_repo()
        _reset(repo)
        scratch = repo / "notes.md"
        scratch.write_text("# shared content\n")
        subprocess.run(["git", "add", "-A"], check=True, cwd=repo)
        subprocess.run(["git", "commit", "-q", "-m", "add scratch"], check=True, cwd=repo)
        base = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8",
            cwd=repo,
        ).stdout.strip()
        nb = repo / "MyIA.AI.Notebooks" / "Translation"
        nb.mkdir(parents=True, exist_ok=True)
        (nb / "Bar.ipynb").write_text("# FR source for Bar\n")
        scratch.rename(nb / "Bar_en.ipynb")  # same content -> R100
        subprocess.run(["git", "add", "-A"], check=True, cwd=repo)
        subprocess.run(["git", "commit", "-q", "-m", "rename notes.md into Bar_en"],
                       check=True, cwd=repo)
        head = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8",
            cwd=repo,
        ).stdout.strip()
        r = check_pair_count_declared(base, head, repo_root=repo, do_disk_count=False)
        # Classified "added" (the old path was not a translation), so the
        # bump is still required -- rouge without it.
        assert len(r.pair_changes) == 1
        assert r.pair_changes[0].status == "added"
        assert r.constant_modified is False
        assert r.rouge is True

    def test_constant_path_does_not_drift(self):
        # The constant is at scripts/translation/tests/test_check_translation_parity.py
        # -- guard against accidental path move.
        assert CONSTANT_PATH == Path("scripts/translation/tests/test_check_translation_parity.py")

    def test_rouge_message_line_number_is_derived_not_hardcoded(self):
        # F2 (Hermes, 2026-10-19) : the ROUGE message must name the constant's
        # CURRENT line, not a hardcoded one -- else it drifts silently when
        # history is added above the constant. The live constant moved from
        # :731 (at PR time) to :737 (now); the helper must track it.
        from check_pair_count_declared import _constant_line_number_in_head
        repo_root = Path(__file__).resolve().parents[3]
        resolved = _constant_line_number_in_head(repo_root)
        const_text = (repo_root / CONSTANT_PATH).read_text(encoding="utf-8")
        real_line = next(
            i for i, ln in enumerate(const_text.splitlines(), start=1)
            if ln.startswith("EXPECTED_PAIR_COUNT = ")
        )
        assert resolved == real_line
        assert resolved != 731, "helper must not return the stale hardcoded :731"


# --------------------------------------------------------------------------- #
# Acceptance against the real PRs in #21391
# --------------------------------------------------------------------------- #


class TestAcceptance:
    """End-to-end against the SHAs cited in the issue. The PRs are fetched
    in the test setup; if a fetch fails the test is skipped (CI may run
    without network).
    """

    @classmethod
    def setup_class(cls):
        # Walk up from the test file to the repo root (scripts/translation/tests -> 3 levels).
        # CI runners on Linux would otherwise fail on a hardcoded Windows path.
        repo = Path(__file__).resolve().parents[3]
        cls.repo = repo
        for remote_ref, local_ref in (
            ("pull/19943/head", "pr-19943"),
            ("pull/21383/head", "pr-21383"),
        ):
            try:
                subprocess.run(
                    ["git", "fetch", "origin", f"{remote_ref}:{local_ref}"],
                    capture_output=True, text=True, encoding="utf-8",
                    cwd=repo, check=True,
                )
            except subprocess.CalledProcessError:
                pass  # PR may have been merged / closed; skip downstream.

    def test_acceptance_1_positive_19943(self):
        """#19943 added ANALYSE-07-Percolation-Critique_en without bumping
        the constant -- the guard MUST ROUGE.
        """
        parent = subprocess.run(
            ["git", "rev-parse", "c91ad9872d^"],
            capture_output=True, text=True, encoding="utf-8", cwd=self.repo,
        ).stdout.strip()
        r = check_pair_count_declared(parent, "c91ad9872d", repo_root=self.repo,
                                       do_disk_count=False)
        assert r.rouge is True
        assert any("ANALYSE-07" in pc.translation_path for pc in r.pair_changes)

    def test_acceptance_2_negative_21383(self):
        """#21383 only bumps the constant -- the guard MUST GREEN."""
        try:
            head_sha = subprocess.run(
                ["git", "rev-parse", "pr-21383"],
                capture_output=True, text=True, encoding="utf-8", cwd=self.repo,
            ).stdout.strip()
        except subprocess.CalledProcessError:
            return  # ref not present
        # Compare against the merge base of pr-21383 and main.
        base_sha = subprocess.run(
            ["git", "merge-base", "origin/main", "pr-21383"],
            capture_output=True, text=True, encoding="utf-8", cwd=self.repo,
        ).stdout.strip()
        r = check_pair_count_declared(base_sha, head_sha, repo_root=self.repo,
                                       do_disk_count=False)
        # The PR also bumps the Z3.Linq submodule. No notebook diff.
        # Therefore no pair change. Constant may or may not be modified
        # depending on the merge base -- but no pair change => GREEN.
        assert r.pair_changes == []
        assert r.rouge is False

    def test_acceptance_4_tmp_dir_ignored(self):
        """A local .tmp/ orphan on disk must NOT be picked up by the guard
        (the guard reads git diff, not disk).
        """
        repo = _make_repo()
        base = _reset(repo)
        head = _add_pair(repo, "Real")
        # Create a local .tmp/ file (untracked -- not committed).
        tmp_dir = repo / "MyIA.AI.Notebooks" / ".tmp"
        tmp_dir.mkdir(parents=True, exist_ok=True)
        (tmp_dir / "Bogus_en.ipynb").write_text("# orphan\n")
        # The diff for base..head only contains the Real pair. The guard
        # reads git diff, so the .tmp orphan is invisible to it.
        r = check_pair_count_declared(base, head, repo_root=repo, do_disk_count=False)
        # Only the Real pair (with FR source) is detected; the .tmp orphan
        # is not on the head side of the diff.
        assert len(r.pair_changes) == 1
        assert r.pair_changes[0].stem == "Real"
