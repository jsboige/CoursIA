#!/usr/bin/env python3
"""Tests for ``scripts/translation/check_resync_only.py``.

Covers the four core paths:

1. **No diff** (empty change list) → ``verdict="ok"``.
2. **Touches non-CSV files** (notebook, doc, script) → ``verdict="ok"``,
   ``translations_only=False``.
3. **Touches ONLY translations/*.csv** AND adds no non-fr content → ``resync_only``.
4. **Touches ONLY translations/*.csv** AND adds text_en content → ``ok``
   (a genuine translation deposit is NOT a resync-only).

Also covers:
- Column parsing discipline (added lines must have the canonical header length).
- The hunk-header prefix ``+++`` is filtered out (no false-positive from the
  diff header itself).
- Stdin/argv plumbing of ``main()`` returns 0 in OK mode, 2 on git error.

stdlib-only (csv/json/pathlib/shutil/subprocess/argparse). Hermetic.

Mirror of the test pattern established by ``test_check_translation_sync.py``
for the sibling script: importable module, fixture helpers, pure-function
coverage first, then a thin CLI smoke test.
"""

from __future__ import annotations

import csv
import io
import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import check_resync_only as r  # noqa: E402

ALL_LANGS = ("en", "es", "ar", "fa", "zh", "ru", "pt")
PIVOT = "fr"
COLUMNS = (
    ["notebook", "cell_id", "cell_type", "src_lang", "src_hash",
     "text_fr"]
    + [f"text_{L}" for L in ALL_LANGS]
    + ["hash_fr"]
    + [f"hash_{L}" for L in ALL_LANGS]
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _row(cell_id: str, src_hash: str, text_fr: str = "",
         text_en: str = "") -> list[str]:
    """Build a canonical CSV row. text_en non-empty = genuine translation."""
    row = ["nb.ipynb", cell_id, "markdown", "fr", src_hash, text_fr]
    row += [text_en]  # text_en
    row += [""] * 6  # text_es..text_pt
    row += [src_hash]  # hash_fr
    row += [""] * 7  # hash_en..hash_pt
    assert len(row) == len(COLUMNS)
    return row


def _make_csv(rows: list[list[str]]) -> str:
    """Return a CSV file content string with the canonical header."""
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(COLUMNS)
    writer.writerows(rows)
    return buf.getvalue()


def _diff_lines(rows_before: list[list[str]],
                rows_after: list[list[str]]) -> str:
    """Build a synthetic ``git diff -U0`` body for the given before/after rows."""
    before = _make_csv(rows_before).splitlines(keepends=True)
    after = _make_csv(rows_after).splitlines(keepends=True)
    # We simulate a 1-line header + 1-row diff (resync signature).
    return (
        "diff --git a/translations/foo/foo.csv b/translations/foo/foo.csv\n"
        "index 0000001..0000002 100644\n"
        "--- a/translations/foo/foo.csv\n"
        "+++ b/translations/foo/foo.csv\n"
        "@@ -1,2 +1,2 @@\n"
        + "".join(f"-{l}" for l in before[1:])
        + "".join(f"+{l}" for l in after[1:])
    )


# ---------------------------------------------------------------------------
# _added_lang_columns
# ---------------------------------------------------------------------------

def test_added_lang_columns_empty_for_pure_resync():
    """text_fr update with no non-fr content → empty added set."""
    before = [_row("c1", "aaaa", text_fr="avant")]
    after = [_row("c1", "bbbb", text_fr="après")]
    diff_text = _diff_lines(before, after)
    assert r._added_lang_columns(diff_text) == []


def test_added_lang_columns_detects_text_en_addition():
    """text_en non-empty on the + side → 'text_en' is in the result."""
    before = [_row("c1", "aaaa", text_fr="avant", text_en="")]
    after = [_row("c1", "bbbb", text_fr="après", text_en="before/after")]
    diff_text = _diff_lines(before, after)
    assert "text_en" in r._added_lang_columns(diff_text)


def test_added_lang_columns_ignores_hunk_header():
    """The ``+++ b/translations/...`` header must NOT register as content."""
    diff_text = (
        "diff --git a/translations/foo/foo.csv b/translations/foo/foo.csv\n"
        "+++ b/translations/foo/foo.csv\n"
        "@@ -1 +1 @@\n"
        "-x\n"
        "+y\n"
    )
    assert r._added_lang_columns(diff_text) == []


def test_added_lang_columns_skips_malformed_rows():
    """Lines that don't parse to len(COLUMNS) are silently skipped."""
    diff_text = (
        "diff --git a/translations/foo/foo.csv b/translations/foo/foo.csv\n"
        "@@ -1 +1 @@\n"
        "-too,short\n"
        "+also,short\n"
    )
    assert r._added_lang_columns(diff_text) == []


# ---------------------------------------------------------------------------
# TRANSLATIONS_RE / verdict logic
# ---------------------------------------------------------------------------

def test_translations_re_matches_csv_only():
    assert bool(r.TRANSLATIONS_RE.match("translations/foo/foo.csv"))
    assert bool(r.TRANSLATIONS_RE.match("translations/a/b/c.csv"))
    assert not r.TRANSLATIONS_RE.match("MyIA.AI.Notebooks/foo.ipynb")
    assert not r.TRANSLATIONS_RE.match("scripts/translation/check.py")
    assert not r.TRANSLATIONS_RE.match("docs/translation/README.md")


def test_canonical_columns_match_helper():
    """Sanity: ``_csv_columns`` returns the same shape as the test row helper."""
    assert r._csv_columns() == list(COLUMNS)


# ---------------------------------------------------------------------------
# analyse() — git-driven path, in a real worktree
# ---------------------------------------------------------------------------

def _commit_csv(repo: Path, rows: list[list[str]], msg: str) -> None:
    """Write a CSV, ``git add`` + ``git commit`` it (uses the test repo's git env)."""
    import os
    env = os.environ.copy()
    env.update({
        "GIT_AUTHOR_NAME": "tester",
        "GIT_AUTHOR_EMAIL": "tester@test.local",
        "GIT_COMMITTER_NAME": "tester",
        "GIT_COMMITTER_EMAIL": "tester@test.local",
    })
    csv_path = repo / "translations" / "foo" / "foo.csv"
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    csv_path.write_text(_make_csv(rows), encoding="utf-8")
    subprocess.run(["git", "add", str(csv_path)], cwd=repo, check=True,
                   capture_output=True, env=env)
    subprocess.run(["git", "commit", "-m", msg], cwd=repo, check=True,
                   capture_output=True, env=env)


def _setup_minimal_repo(tmp_path: Path) -> Path:
    """Init a git repo with one initial commit so ``git diff main...HEAD`` works."""
    import os
    env = os.environ.copy()
    env.update({
        "GIT_AUTHOR_NAME": "tester",
        "GIT_AUTHOR_EMAIL": "tester@test.local",
        "GIT_COMMITTER_NAME": "tester",
        "GIT_COMMITTER_EMAIL": "tester@test.local",
    })
    subprocess.run(["git", "init", "-q", "-b", "main"], cwd=tmp_path, check=True,
                   capture_output=True, env=env)
    # initial commit: translations/ with a marker so git has something to track
    (tmp_path / "translations").mkdir()
    (tmp_path / "translations" / ".gitkeep").write_text("", encoding="utf-8")
    subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True,
                   capture_output=True, env=env)
    proc = subprocess.run(["git", "commit", "-m", "init"], cwd=tmp_path,
                          capture_output=True, env=env)
    if proc.returncode != 0:
        raise RuntimeError(
            f"git commit init failed: rc={proc.returncode} "
            f"stdout={proc.stdout!r} stderr={proc.stderr!r}"
        )
    # create branch so we can advance HEAD
    subprocess.run(["git", "checkout", "-q", "-b", "feat"], cwd=tmp_path, check=True,
                   capture_output=True, env=env)
    return tmp_path


@pytest.mark.skipif(shutil.which("git") is None, reason="git not installed")
def test_analyse_empty_diff_is_ok(tmp_path, monkeypatch):
    repo = _setup_minimal_repo(tmp_path)
    monkeypatch.chdir(repo)
    rep = r.analyse("main...HEAD")
    assert rep.verdict == "ok"
    assert rep.changed_files == []
    assert rep.translations_only is False


@pytest.mark.skipif(shutil.which("git") is None, reason="git not installed")
def test_analyse_pure_resync_is_resync_only(tmp_path, monkeypatch):
    repo = _setup_minimal_repo(tmp_path)
    monkeypatch.chdir(repo)
    _commit_csv(repo, [_row("c1", "aaaa", text_fr="avant")],
                "resync: text_fr update, no translation")
    rep = r.analyse("main...HEAD")
    assert rep.translations_only is True
    assert rep.verdict == "resync_only"
    assert rep.lang_columns_added == []


@pytest.mark.skipif(shutil.which("git") is None, reason="git not installed")
def test_analyse_resync_plus_translation_is_ok(tmp_path, monkeypatch):
    repo = _setup_minimal_repo(tmp_path)
    monkeypatch.chdir(repo)
    _commit_csv(repo,
                [_row("c1", "aaaa", text_fr="avant", text_en="")],
                "resync: text_fr update only")
    # Second commit adds text_en — this is a genuine translation, NOT resync-only
    _commit_csv(repo,
                [_row("c1", "aaaa", text_fr="avant", text_en="before/after")],
                "translate: deposit text_en")
    rep = r.analyse("main...HEAD")
    assert rep.translations_only is True
    assert rep.verdict == "ok"
    assert "text_en" in rep.lang_columns_added


@pytest.mark.skipif(shutil.which("git") is None, reason="git not installed")
def test_analyse_mixed_files_is_not_resync_only(tmp_path, monkeypatch):
    """A PR that touches a notebook AND a CSV is NOT resync-only."""
    import os
    env = os.environ.copy()
    env.update({
        "GIT_AUTHOR_NAME": "tester",
        "GIT_AUTHOR_EMAIL": "tester@test.local",
        "GIT_COMMITTER_NAME": "tester",
        "GIT_COMMITTER_EMAIL": "tester@test.local",
    })
    repo = _setup_minimal_repo(tmp_path)
    monkeypatch.chdir(repo)
    # Add a notebook file
    nb = repo / "MyIA.AI.Notebooks" / "foo" / "bar.ipynb"
    nb.parent.mkdir(parents=True, exist_ok=True)
    nb.write_text(json.dumps({"cells": [], "metadata": {}, "nbformat": 4,
                              "nbformat_minor": 5}), encoding="utf-8")
    subprocess.run(["git", "add", str(nb)], cwd=repo, check=True,
                   capture_output=True, env=env)
    subprocess.run(["git", "commit", "-m", "add notebook"], cwd=repo, check=True,
                   capture_output=True, env=env)
    # Add a CSV in the same branch
    _commit_csv(repo, [_row("c1", "aaaa", text_fr="avant")],
                "resync: text_fr update only")
    rep = r.analyse("main...HEAD")
    assert rep.translations_only is False
    assert rep.verdict == "ok"


# ---------------------------------------------------------------------------
# CLI smoke
# ---------------------------------------------------------------------------

@pytest.mark.skipif(shutil.which("git") is None, reason="git not installed")
def test_main_cli_exit_code_zero_on_ok(tmp_path, capsys, monkeypatch):
    repo = _setup_minimal_repo(tmp_path)
    monkeypatch.chdir(repo)
    _commit_csv(repo, [_row("c1", "aaaa", text_fr="avant", text_en="")],
                "resync: pure fr update")
    rc = r.main(["--diff-range", "main...HEAD"])
    assert rc == 0
    out = capsys.readouterr()
    payload = json.loads(out.out.split("\n")[0])
    assert payload["verdict"] == "resync_only"
