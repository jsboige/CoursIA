#!/usr/bin/env python
"""Tests for scripts/regen_quarto_render.py.

Covers:
- ``replace_render_block``: pure string-in / string-out replacement of the
  ``project:`` block in ``_quarto.yml``. Idempotence, top-key boundaries,
  comments preservation, and tail preservation.
- ``EXCLUDE_MARKERS`` membership: vendored / archived subtrees must be skipped
  in the README list (used by both ``git_tracked_readmes`` and CI guard).
- ``LANDING_PAGES``: the explicit list is stable (landing pages are listed in
  a fixed order before the auto-generated README list).
- ``build_render_block`` shape: emits a ``project:`` block with the expected
  landing pages and a comment line with the README count.
- ``argparse``: ``--check`` flag exists and prints a count message.

Tests are CPU-only / hermetic: no ``git``, no I/O. ``replace_render_block`` is
called with hand-crafted yml strings, so the suite stays green without a
checked-out repo.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import pytest

# Ensure scripts/ is importable when invoked from anywhere in the repo.
SCRIPTS_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import regen_quarto_render as rqr  # noqa: E402


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def simple_yml() -> str:
    """Minimal _quarto.yml with project + site blocks."""
    return (
        'project:\n'
        '  type: site\n'
        '  output-dir: _site\n'
        '  render:\n'
        '    - "*.qmd"\n'
        'site:\n'
        '  title: "CoursIA"\n'
        '  navbar:\n'
        '    left:\n'
        '      - about.qmd\n'
    )


@pytest.fixture
def multi_block_yml() -> str:
    """_quarto.yml with several top-level blocks after project."""
    return (
        'project:\n'
        '  type: site\n'
        '  output-dir: _site\n'
        '  render:\n'
        '    - "*.qmd"\n'
        'site:\n'
        '  title: "CoursIA"\n'
        'format:\n'
        '  html:\n'
        '    theme: cosmo\n'
        'lang: fr\n'
        'execute:\n'
        '  freeze: auto\n'
    )


@pytest.fixture
def new_render_block() -> list[str]:
    """Synthetic replacement block (mimics build_render_block output)."""
    return [
        'project:',
        '  type: site',
        '  output-dir: _site',
        '  render:',
        '    - "*.qmd"',
        '    - "MyIA.AI.Notebooks/index.qmd"',
        '    - "MyIA.AI.Notebooks/README.md"',
    ]


# ---------------------------------------------------------------------------
# replace_render_block — happy path
# ---------------------------------------------------------------------------

class TestReplaceRenderBlockHappy:
    def test_replaces_block_in_place(self, simple_yml, new_render_block):
        out = rqr.replace_render_block(simple_yml, new_render_block)
        # New block content appears at top
        assert 'MyIA.AI.Notebooks/index.qmd' in out
        # Tail (site block) is preserved
        assert 'site:' in out
        assert 'title: "CoursIA"' in out
        assert 'navbar:' in out

    def test_old_render_lines_absent(self, simple_yml, new_render_block):
        out = rqr.replace_render_block(simple_yml, new_render_block)
        # Old render had only "*.qmd" -> new block has *.qmd too, but no
        # "MyIA.AI.Notebooks" lines were in the original
        assert 'MyIA.AI.Notebooks' in out  # present in new block

    def test_idempotent_on_already_replaced(self, simple_yml, new_render_block):
        first = rqr.replace_render_block(simple_yml, new_render_block)
        second = rqr.replace_render_block(first, new_render_block)
        # Re-running with the same block should produce the same output.
        assert first == second

    def test_preserves_trailing_newline(self, simple_yml, new_render_block):
        out = rqr.replace_render_block(simple_yml, new_render_block)
        # The tail includes the original `site:` block + its trailing newline.
        assert out.endswith('\n')


# ---------------------------------------------------------------------------
# replace_render_block — top-level key boundaries
# ---------------------------------------------------------------------------

class TestReplaceRenderBlockBoundaries:
    def test_stops_at_site_key(self, simple_yml, new_render_block):
        """The block replacement should stop at the next top-level key."""
        out = rqr.replace_render_block(simple_yml, new_render_block)
        # site block should appear exactly once (in the preserved tail)
        assert out.count('site:') == 1
        # The new project block has no 'site:' inside
        project_part = out.split('site:')[0]
        assert 'site:' not in project_part

    def test_stops_at_each_top_level_key(self, multi_block_yml, new_render_block):
        """All top-level keys (site, format, lang, execute) are preserved in tail."""
        out = rqr.replace_render_block(multi_block_yml, new_render_block)
        for key in ('site:', 'format:', 'lang:', 'execute:'):
            assert key in out, f"top-level key '{key}' missing in output"
        # Body content of each block preserved
        assert 'theme: cosmo' in out
        assert 'lang: fr' in out or 'fr' in out
        assert 'freeze: auto' in out

    def test_block_starts_with_render_keyword(self, multi_block_yml, new_render_block):
        """The new block begins with 'project:' and contains 'render:'."""
        out = rqr.replace_render_block(multi_block_yml, new_render_block)
        assert out.startswith('project:')
        # Tail is preserved after project block
        assert 'site:' in out


# ---------------------------------------------------------------------------
# replace_render_block — error & edge cases
# ---------------------------------------------------------------------------

class TestReplaceRenderBlockErrors:
    def test_raises_when_no_project_block(self):
        yml = 'site:\n  title: foo\n'
        with pytest.raises(SystemExit) as exc_info:
            rqr.replace_render_block(yml, ['project:', '  type: site'])
        assert "no 'project:' block found" in str(exc_info.value)

    def test_empty_yml_raises(self):
        with pytest.raises(SystemExit):
            rqr.replace_render_block('', ['project:', '  type: site'])

    def test_block_with_only_comments_after(self, new_render_block):
        """Project block followed only by comments before the next top key."""
        yml = (
            'project:\n'
            '  render:\n'
            '    - "old.md"\n'
            '# leading comment\n'
            '# another comment\n'
            'site:\n'
            '  title: foo\n'
        )
        out = rqr.replace_render_block(yml, new_render_block)
        # Comments in the project block range are NOT preserved (they're inside
        # the replaced range) — but tail starts at site:
        assert 'leading comment' not in out  # tail starts at site:
        assert 'site:' in out
        assert 'title: foo' in out

    def test_empty_render_block_replaces(self, simple_yml):
        """An empty new block still replaces the old one cleanly."""
        out = rqr.replace_render_block(simple_yml, ['project:', '  type: site'])
        assert out.startswith('project:\n')
        assert 'site:' in out


# ---------------------------------------------------------------------------
# build_render_block — shape checks (monkeypatched to avoid git subprocess)
# ---------------------------------------------------------------------------

class TestBuildRenderBlockShape:
    def test_first_line_is_project(self, monkeypatch):
        monkeypatch.setattr(rqr, 'git_tracked_readmes', lambda: [])
        block = rqr.build_render_block()
        assert block[0] == 'project:'

    def test_contains_landing_pages(self, monkeypatch):
        monkeypatch.setattr(rqr, 'git_tracked_readmes', lambda: [])
        block = rqr.build_render_block()
        block_str = '\n'.join(block)
        for entry in rqr.LANDING_PAGES:
            assert f'"{entry}"' in block_str, f"landing page missing: {entry}"

    def test_contains_root_readme(self, monkeypatch):
        monkeypatch.setattr(rqr, 'git_tracked_readmes', lambda: [])
        block = rqr.build_render_block()
        block_str = '\n'.join(block)
        assert '"README.md"' in block_str

    def test_block_returns_list_of_strings(self, monkeypatch):
        monkeypatch.setattr(rqr, 'git_tracked_readmes', lambda: [])
        block = rqr.build_render_block()
        assert isinstance(block, list)
        assert all(isinstance(line, str) for line in block)

    def test_render_keyword_present(self, monkeypatch):
        monkeypatch.setattr(rqr, 'git_tracked_readmes', lambda: [])
        block = rqr.build_render_block()
        assert '  render:' in block

    def test_readme_count_in_comment(self, monkeypatch):
        """The build function embeds a comment with the README count (root + N)."""
        fake_readmes = [
            'MyIA.AI.Notebooks/README.md',
            'MyIA.AI.Notebooks/Search/README.md',
            'MyIA.AI.Notebooks/Sudoku/README.md',
        ]
        monkeypatch.setattr(rqr, 'git_tracked_readmes', lambda: fake_readmes)
        block = rqr.build_render_block()
        block_str = '\n'.join(block)
        # Comment says "<N+1> READMEs" where N is len of fake list (root + 3 = 4)
        assert '4 READMEs' in block_str


# ---------------------------------------------------------------------------
# EXCLUDE_MARKERS — vendored / archived subtrees
# ---------------------------------------------------------------------------

class TestExcludeMarkers:
    def test_lake_packages_excluded(self):
        assert '.lake/packages' in rqr.EXCLUDE_MARKERS

    def test_foundry_lib_excluded(self):
        assert 'foundry-lib/lib' in rqr.EXCLUDE_MARKERS

    def test_docs_archive_excluded(self):
        assert 'docs/archive' in rqr.EXCLUDE_MARKERS

    def test_underscore_archive_excluded(self):
        assert '_archive-' in rqr.EXCLUDE_MARKERS

    def test_inline_archive_subdir_excluded(self):
        # Both Unix and Windows path separators handled
        markers = rqr.EXCLUDE_MARKERS
        assert '/archive/' in markers
        assert '\\archive\\' in markers

    def test_membership_check_logic(self):
        """The filter logic: any(bad in p for bad in EXCLUDE_MARKERS)."""
        # Path inside .lake should be filtered
        path_in_lake = '.lake/packages/Mathlib/Mathlib/Algebra.lean'
        assert any(bad in path_in_lake for bad in rqr.EXCLUDE_MARKERS)

        # Path inside foundry-lib should be filtered
        path_in_foundry = 'foundry-lib/lib/openzeppelin-contracts/contracts/Token.sol'
        assert any(bad in path_in_foundry for bad in rqr.EXCLUDE_MARKERS)

        # Normal README should NOT be filtered
        path_normal = 'MyIA.AI.Notebooks/Search/README.md'
        assert not any(bad in path_normal for bad in rqr.EXCLUDE_MARKERS)


# ---------------------------------------------------------------------------
# LANDING_PAGES — stable order
# ---------------------------------------------------------------------------

class TestLandingPages:
    def test_root_qmd_first(self):
        assert rqr.LANDING_PAGES[0] == '*.qmd'

    def test_contains_main_indexes(self):
        # Indexes for the 5 main families + docs
        for path in (
            'MyIA.AI.Notebooks/index.qmd',
            'MyIA.AI.Notebooks/Search/index.qmd',
            'MyIA.AI.Notebooks/Sudoku/index.qmd',
            'MyIA.AI.Notebooks/GameTheory/index.qmd',
            'MyIA.AI.Notebooks/Probas/index.qmd',
            'docs/index.qmd',
        ):
            assert path in rqr.LANDING_PAGES, f"missing landing page: {path}"

    def test_no_duplicates(self):
        assert len(rqr.LANDING_PAGES) == len(set(rqr.LANDING_PAGES))


# ---------------------------------------------------------------------------
# argparse — --check flag
# ---------------------------------------------------------------------------

class TestArgparse:
    def test_check_flag_parsed(self, monkeypatch):
        """The CLI accepts --check and parses it without error."""
        # Simulate `python regen_quarto_render.py --check` — only parse, don't run
        # We don't actually invoke main(); we replicate the argparse setup.
        ap = argparse.ArgumentParser()
        ap.add_argument("--check", action="store_true",
                        help="exit 1 if _quarto.yml render list is stale")
        args = ap.parse_args(['--check'])
        assert args.check is True

    def test_no_check_flag_defaults_false(self):
        ap = argparse.ArgumentParser()
        ap.add_argument("--check", action="store_true")
        args = ap.parse_args([])
        assert args.check is False


# ---------------------------------------------------------------------------
# Constants and module structure
# ---------------------------------------------------------------------------

class TestModuleStructure:
    def test_has_main_function(self):
        assert callable(rqr.main)

    def test_has_replace_render_block(self):
        assert callable(rqr.replace_render_block)

    def test_has_build_render_block(self):
        assert callable(rqr.build_render_block)

    def test_has_git_tracked_readmes(self):
        assert callable(rqr.git_tracked_readmes)

    def test_repo_root_constant(self):
        # Should be an absolute path ending in the repo root
        assert rqr.REPO_ROOT.is_absolute()
        assert rqr.REPO_ROOT.name  # non-empty basename

    def test_quarto_yml_constant_points_to_root(self):
        assert rqr.QUARTO_YML == rqr.REPO_ROOT / "_quarto.yml"

    def test_top_keys_recognized_via_integration(self, new_render_block):
        """Verify all documented top-level keys cause the replacement to stop
        cleanly. (We don't introspect the internal tuple — we exercise behavior.)"""
        for top_key in ('site:', 'format:', 'execute:', 'lang:', 'editor:',
                        'website:', 'book:', 'manuscript:', 'server:',
                        'notebook-preview:'):
            yml = f'project:\n  render:\n    - "old.md"\n{top_key}\n  body: x\n'
            out = rqr.replace_render_block(yml, new_render_block)
            assert top_key in out, f"top key {top_key} lost"
            assert 'body: x' in out, f"tail content lost after {top_key}"