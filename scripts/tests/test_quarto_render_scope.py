#!/usr/bin/env python
"""Tests for scripts/quarto_render_scope.py.

The script decides how much of the Quarto site a PR check must render. Getting
that decision wrong is not symmetric:

- **too WIDE** costs an hour of a self-hosted slot and starves the PR gate
  (the defect #14429 fixes);
- **too NARROW** renders fewer documents than the PR changed, and reports
  ``success`` for a document nobody built -- a green check that measured
  nothing. That is the failure this suite exists to make impossible.

So every FULL trigger is asserted individually (a trigger silently dropped from
the tuple would not raise -- it would just return a smaller, cleaner-looking
scope), and ``restrict_yaml`` is asserted to preserve the project's other keys
and the whole tail of the file byte-for-byte.

Tests are CPU-only / hermetic: no ``git``, no I/O, no repo checkout needed --
``decide`` and ``restrict_yaml`` are pure, and the changed-file rows are
hand-built.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Ensure scripts/ is importable when invoked from anywhere in the repo.
SCRIPTS_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import quarto_render_scope as qrs  # noqa: E402


YML = """project:
  type: site
  output-dir: _site
  render:
    # Landing pages
    - "index.qmd"
    # READMEs
    - "README.md"
    - "MyIA.AI.Notebooks/Search/README.md"
    # Notebooks
    - "MyIA.AI.Notebooks/Search/Search-02c.ipynb"
    - "MyIA.AI.Notebooks/Search/Search-3.ipynb"

site:
  title: "CoursIA"
  navbar:
    left:
      - text: "Accueil"

format:
  html:
    theme: cosmo
"""

ENTRIES = [
    "index.qmd",
    "README.md",
    "MyIA.AI.Notebooks/Search/README.md",
    "MyIA.AI.Notebooks/Search/Search-02c.ipynb",
    "MyIA.AI.Notebooks/Search/Search-3.ipynb",
]


# ---------------------------------------------------------------------------
# render_list_entries
# ---------------------------------------------------------------------------

def test_render_list_entries_reads_every_quoted_path():
    assert qrs.render_list_entries(YML) == ENTRIES


def test_render_list_entries_stops_at_next_top_level_key():
    """`site:` / `format:` carry quoted strings too -- none may leak in."""
    entries = qrs.render_list_entries(YML)
    assert not any("Accueil" in e or "cosmo" in e or e == "CoursIA" for e in entries)


# ---------------------------------------------------------------------------
# decide -- FULL triggers, each asserted on its own
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("path", list(qrs.FULL_RENDER_TRIGGERS))
def test_every_declared_full_trigger_forces_full(path):
    """Asserted from the tuple itself: adding a trigger adds a test."""
    mode, files, _ = qrs.decide([("M", path)], ENTRIES)
    assert mode == "full"
    assert files == []


def test_preprocessing_script_forces_full():
    for p in ("scripts/quarto_yaml_safe.py",
              "scripts/quarto_csharp_kernel_fix.py",
              "scripts/regen_quarto_render.py"):
        assert qrs.decide([("M", p)], ENTRIES)[0] == "full", p


def test_theme_and_metadata_suffixes_force_full():
    for p in ("custom.scss", "assets/extra.css", "MyIA.AI.Notebooks/_metadata.yml"):
        assert qrs.decide([("M", p)], ENTRIES)[0] == "full", p


def test_deleting_a_rendered_document_forces_full():
    """A deletion cannot be rendered, and it breaks links from pages that stay."""
    mode, _, reason = qrs.decide([("D", "MyIA.AI.Notebooks/Search/Search-3.ipynb")], ENTRIES)
    assert mode == "full"
    assert "link integrity" in reason


def test_deleting_an_unlisted_file_does_not_force_full():
    """Only deletions of RENDERED documents matter -- otherwise every PR is full."""
    assert qrs.decide([("D", "scripts/some_helper.py")], ENTRIES)[0] == "empty"


# ---------------------------------------------------------------------------
# decide -- SCOPED / EMPTY
# ---------------------------------------------------------------------------

def test_scoped_selects_exactly_the_changed_rendered_documents():
    rows = [("M", "MyIA.AI.Notebooks/Search/Search-3.ipynb"),
            ("M", "scripts/unrelated.py")]
    mode, files, _ = qrs.decide(rows, ENTRIES)
    assert mode == "scoped"
    assert files == ["MyIA.AI.Notebooks/Search/Search-3.ipynb"]


def test_scoped_preserves_render_list_order_not_diff_order():
    """Quarto reads the list in order; the diff order must not reshuffle it."""
    rows = [("M", "MyIA.AI.Notebooks/Search/Search-3.ipynb"),
            ("A", "index.qmd")]
    _, files, _ = qrs.decide(rows, ENTRIES)
    assert files == ["index.qmd", "MyIA.AI.Notebooks/Search/Search-3.ipynb"]


def test_added_document_is_scoped_in():
    _, files, _ = qrs.decide([("A", "MyIA.AI.Notebooks/Search/README.md")], ENTRIES)
    assert files == ["MyIA.AI.Notebooks/Search/README.md"]


def test_empty_when_nothing_rendered_changed():
    mode, files, _ = qrs.decide([("M", "scripts/pick_idle_grain.py")], ENTRIES)
    assert mode == "empty"
    assert files == []


def test_no_changes_at_all_is_empty_never_scoped():
    """An empty selection must never reach `quarto render`: with no file
    argument and an empty list, Quarto would render the whole site -- the exact
    inverse of the intent."""
    assert qrs.decide([], ENTRIES)[0] == "empty"


# ---------------------------------------------------------------------------
# restrict_yaml
# ---------------------------------------------------------------------------

def test_restrict_yaml_keeps_only_the_selection():
    keep = ["MyIA.AI.Notebooks/Search/Search-3.ipynb"]
    out = qrs.restrict_yaml(YML, keep)
    assert qrs.render_list_entries(out) == keep


def test_restrict_yaml_preserves_other_project_keys():
    out = qrs.restrict_yaml(YML, ["README.md"])
    assert "  type: site" in out
    assert "  output-dir: _site" in out
    assert out.startswith("project:")


def test_restrict_yaml_preserves_the_tail_byte_for_byte():
    """Everything from the next top-level key on must survive untouched."""
    tail_of = lambda t: t[t.index("site:"):]  # noqa: E731
    out = qrs.restrict_yaml(YML, ["README.md"])
    assert tail_of(out) == tail_of(YML)


def test_restrict_yaml_is_idempotent():
    once = qrs.restrict_yaml(YML, ["README.md"])
    twice = qrs.restrict_yaml(once, ["README.md"])
    assert once == twice


def test_restrict_yaml_drops_the_original_comments_with_the_entries():
    """Leaving `# Notebooks` above a list that no longer has any is misleading."""
    out = qrs.restrict_yaml(YML, ["README.md"])
    assert "# Landing pages" not in out
    assert "# Notebooks" not in out
    assert "SCOPED to this PR" in out
