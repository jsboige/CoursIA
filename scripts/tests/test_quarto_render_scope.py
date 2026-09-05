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

Tests are CPU-only: no ``git``, no subprocess -- ``decide`` and
``restrict_yaml`` are pure and the changed-file rows are hand-built. One
exception, and it is deliberate: ``test_every_glob_in_the_real_render_list_is
_representable`` reads the repo's own ``_quarto.yml``. A fixture cannot catch
someone adding an entry this module's glob translator would silently
under-match, and under-matching is the failure mode above.
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
              # NOT regen_quarto_render.py: it is CI machinery (#14431). Its
              # sibling below keeps the prefix rule honest.
              "scripts/regen_quarto_render_helper.py"):
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


# ---------------------------------------------------------------------------
# glob entries
#
# The real list carries `*.qmd`, covering index.qmd and parcours.qmd -- the two
# root landing pages. An exact-string intersection matched neither: a PR
# editing index.qmd fell through to `empty`, skipped the render step, and
# reported success having built nothing. These pin the fix.
# ---------------------------------------------------------------------------

YML_GLOB = """project:
  type: site
  render:
    - "*.qmd"
    - "docs/**/*.md"
    - "README.md"

site:
  title: "CoursIA"
"""

ENTRIES_GLOB = ["*.qmd", "docs/**/*.md", "README.md"]


def test_render_list_entries_reads_glob_entries_verbatim():
    assert qrs.render_list_entries(YML_GLOB) == ENTRIES_GLOB


def test_glob_entry_selects_the_document_it_covers():
    mode, files, _ = qrs.decide([("M", "index.qmd")], ENTRIES_GLOB)
    assert mode == "scoped"
    assert files == ["index.qmd"]


def test_single_star_does_not_cross_a_path_separator():
    """`*.qmd` is root-only -- matching `sub/deep.qmd` would render too much."""
    assert qrs.decide([("M", "sub/deep.qmd")], ENTRIES_GLOB)[0] == "empty"


def test_double_star_does_cross_path_separators():
    _, files, _ = qrs.decide([("M", "docs/a/b/guide.md")], ENTRIES_GLOB)
    assert files == ["docs/a/b/guide.md"]


def test_deleting_a_glob_covered_document_forces_full():
    """The deletion check must see through globs too, or link rot ships."""
    mode, _, reason = qrs.decide([("D", "parcours.qmd")], ENTRIES_GLOB)
    assert mode == "full"
    assert "link integrity" in reason


def test_glob_expansion_keeps_list_order_and_dedupes():
    rows = [("M", "README.md"), ("M", "parcours.qmd"), ("M", "index.qmd")]
    _, files, _ = qrs.decide(rows, ENTRIES_GLOB)
    assert files == ["index.qmd", "parcours.qmd", "README.md"]


def test_unrepresentable_glob_falls_back_to_full_never_to_a_narrow_scope():
    """Under-matching is the dangerous direction: refuse to guess."""
    mode, _, reason = qrs.decide([("M", "README.md")], ["data-[0-9].qmd", "README.md"])
    assert mode == "full"
    assert "unsupported glob" in reason


def test_every_glob_in_the_real_render_list_is_representable():
    """Guards the production list against an entry the translator would miss."""
    entries = qrs.render_list_entries(qrs.QUARTO_YML.read_text(encoding="utf-8"))
    assert entries, "the repo's _quarto.yml must carry a render list"
    unrepresentable = [e for e in entries
                       if qrs.is_glob(e) and qrs.glob_to_regex(e) is None]
    assert unrepresentable == []


# ---------------------------------------------------------------------------
# CI machinery -> smoke set
#
# Positive control on the remedy: without this exemption, THIS script's own PR
# is classified `full` by its own rule and dies on the 60-min ceiling it exists
# to avoid.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("path", list(qrs.CI_MACHINERY))
def test_ci_machinery_alone_renders_a_smoke_set_not_nothing_and_not_everything(path):
    mode, files, _ = qrs.decide([("M", path)], ENTRIES)
    assert mode == "scoped", path
    assert files, "a machinery-only PR must still exercise the render step"
    assert set(files) <= set(qrs.SMOKE_DOCUMENTS)


def test_this_prs_own_change_set_is_not_a_full_render():
    """The exact rows of the PR introducing this file."""
    rows = [("M", ".github/workflows/quarto-pages-deploy.yml"),
            ("M", "scripts/quarto_render_scope.py"),
            ("M", "scripts/tests/test_quarto_render_scope.py")]
    mode, files, _ = qrs.decide(rows, ENTRIES)
    assert mode == "scoped"
    assert files == ["index.qmd", "README.md"]


def test_smoke_yields_to_real_changed_documents():
    """The smoke set is a floor for an empty selection, never an addition."""
    rows = [("M", ".github/workflows/quarto-pages-deploy.yml"),
            ("M", "MyIA.AI.Notebooks/Search/Search-3.ipynb")]
    _, files, _ = qrs.decide(rows, ENTRIES)
    assert files == ["MyIA.AI.Notebooks/Search/Search-3.ipynb"]


def test_notebook_rewriting_scripts_still_force_full():
    """The exemption is for scripts that SELECT, never for those that REWRITE.

    Both live under `scripts/quarto_`; only this one is exempt.
    """
    assert qrs.decide([("M", "scripts/quarto_yaml_safe.py")], ENTRIES)[0] == "full"
    assert qrs.decide([("M", "scripts/quarto_render_scope.py")], ENTRIES)[0] == "scoped"


def test_smoke_documents_are_covered_by_the_real_render_list():
    """A smoke document Quarto would not render makes the floor a no-op."""
    entries = qrs.render_list_entries(qrs.QUARTO_YML.read_text(encoding="utf-8"))
    _, files, _ = qrs.decide([("M", ".github/workflows/quarto-pages-deploy.yml")], entries)
    assert sorted(files) == sorted(qrs.SMOKE_DOCUMENTS)


# ---------------------------------------------------------------------------
# The generated render list is not project config -- #14431
#
# `project.render` is produced by scripts/regen_quarto_render.py, which the job
# runs one step BEFORE this script, and which `--apply` rewrites one step
# after. A delta confined to it says WHICH documents render, never HOW one
# renders. Treating it as a project-wide change classified a 73-notebook move
# as `full` (1238 documents, 60.9 min, killed at the 60-min ceiling, PR gate
# starved) -- a PR that could not pass, ever, on rerun.
#
# The narrowing is only worth anything if it still refuses: every test that
# widens the scope here is paired with one that keeps a real config change
# `full`. A rule that stops accusing everyone is indistinguishable from a rule
# that was deleted.
# ---------------------------------------------------------------------------

YML_RENDER_LIST_MOVED = (
    YML.replace('    - "MyIA.AI.Notebooks/Search/Search-3.ipynb"',
                '    - "MyIA.AI.Notebooks/Search/moved/Search-3.ipynb"')
       .replace("    # Notebooks", "    # Notebooks (2)"))
YML_THEME_CHANGED = YML.replace("theme: cosmo", "theme: flatly")


def test_outside_render_block_ignores_entries_and_their_comments():
    """The measured shape of #14431: paths move, and the generator rewrites the
    comment counters next to them (`450 READMEs` -> `454 READMEs`)."""
    assert qrs.outside_render_block(YML) == qrs.outside_render_block(YML_RENDER_LIST_MOVED)


def test_outside_render_block_sees_a_project_config_change():
    assert qrs.outside_render_block(YML) != qrs.outside_render_block(YML_THEME_CHANGED)


def test_outside_render_block_keeps_an_unknown_construct_inside_render():
    """Fail-closed: a key this parser does not model reads as a difference."""
    odd = YML.replace('    - "index.qmd"', '''    freeze: auto
    - "index.qmd"''')
    assert qrs.outside_render_block(YML) != qrs.outside_render_block(odd)


def test_quarto_yml_render_list_only_is_machinery_not_full():
    rows = [("M", "_quarto.yml"),
            ("R", "MyIA.AI.Notebooks/Search/Search-3.ipynb")]
    mode, files, _ = qrs.decide(rows, ENTRIES, yml_render_list_only=True)
    assert mode == "scoped"
    assert files == ["MyIA.AI.Notebooks/Search/Search-3.ipynb"]


def test_quarto_yml_still_forces_full_when_the_delta_leaves_the_list():
    """Negative control. Without it, the test above is equally satisfied by a
    build that simply dropped `_quarto.yml` from FULL_RENDER_TRIGGERS."""
    rows = [("M", "_quarto.yml"),
            ("R", "MyIA.AI.Notebooks/Search/Search-3.ipynb")]
    assert qrs.decide(rows, ENTRIES, yml_render_list_only=False)[0] == "full"


def test_quarto_yml_render_list_only_alone_renders_the_smoke_set():
    """It must not fall through to `empty`: the job would report success for a
    render it never performed."""
    mode, files, _ = qrs.decide([("M", "_quarto.yml")], ENTRIES,
                                yml_render_list_only=True)
    assert mode == "scoped"
    assert files == ["index.qmd", "README.md"]


def test_list_generator_is_machinery_not_a_full_trigger():
    mode, files, _ = qrs.decide([("M", "scripts/regen_quarto_render.py")], ENTRIES)
    assert mode == "scoped"
    assert files == ["index.qmd", "README.md"]


def test_deletion_still_forces_full_under_a_render_list_only_delta():
    """The two rules compose. Dropping an entry from the generated list is
    safe; deleting the document it named still breaks every inbound link."""
    rows = [("M", "_quarto.yml"),
            ("D", "MyIA.AI.Notebooks/Search/Search-3.ipynb")]
    assert qrs.decide(rows, ENTRIES, yml_render_list_only=True)[0] == "full"


def test_14431_shape_scopes_to_the_moved_documents():
    """End to end on the measured case: the regenerated list, its generator,
    and the moved documents themselves."""
    rows = [("M", "_quarto.yml"),
            ("M", "scripts/regen_quarto_render.py"),
            ("R", "MyIA.AI.Notebooks/Search/Search-02c.ipynb"),
            ("R", "MyIA.AI.Notebooks/Search/Search-3.ipynb")]
    mode, files, _ = qrs.decide(rows, ENTRIES, yml_render_list_only=True)
    assert mode == "scoped"
    assert files == ["MyIA.AI.Notebooks/Search/Search-02c.ipynb",
                     "MyIA.AI.Notebooks/Search/Search-3.ipynb"]
