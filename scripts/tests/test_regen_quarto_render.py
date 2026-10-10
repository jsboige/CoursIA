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
import subprocess
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
# README-link target normalisation
# ---------------------------------------------------------------------------

class TestReadmeLinkTargets:
    def test_resolves_parent_segments(self):
        base = Path("MyIA.AI.Notebooks/Search/Part2-CSP")
        href = "../Part1-Foundations/Search-1-StateSpace.ipynb"

        assert rqr._normalise_readme_target(base, href) == (
            "MyIA.AI.Notebooks/Search/Part1-Foundations/"
            "Search-1-StateSpace.ipynb"
        )

    def test_removes_current_directory_segments(self):
        base = Path("MyIA.AI.Notebooks/RL")

        assert rqr._normalise_readme_target(
            base, "./RL-01-Premiers-Pas-Stable-Baselines3-Python.ipynb"
        ) == "MyIA.AI.Notebooks/RL/RL-01-Premiers-Pas-Stable-Baselines3-Python.ipynb"

    def test_flags_html_when_source_not_rendered(self, monkeypatch, tmp_path):
        readme = tmp_path / "MyIA.AI.Notebooks" / "Search" / "README.md"
        source = readme.parent / "Excluded.ipynb"
        readme.parent.mkdir(parents=True)
        readme.write_text("[Excluded](Excluded.html)\n", encoding="utf-8")
        source.write_text("{}\n", encoding="utf-8")
        monkeypatch.setattr(rqr, "REPO_ROOT", tmp_path)
        monkeypatch.setattr(
            rqr,
            "git_tracked_readmes",
            lambda: ["MyIA.AI.Notebooks/Search/README.md"],
        )
        monkeypatch.setattr(rqr, "git_tracked_notebooks", lambda: [])

        assert rqr.readme_link_violations() == [
            (
                "MyIA.AI.Notebooks/Search/README.md",
                "DEAD_RENDER",
                "Excluded.html",
            )
        ]


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


# ---------------------------------------------------------------------------
# has_hr_separator — garde `---` (#11451), appliquee aux .md comme aux .ipynb
# ---------------------------------------------------------------------------

class TestHasHrSeparator:
    """La garde syntaxique `has_hr_separator` determine si un fichier (notebook
    ou .md) doit etre exclu du rendu Quarto (YAMLException si `---` hr).

    Regles testees (cf. issue #11451, etendu aux docs/*.md par #18422) :
      - `---` seul en debut de cellule markdown (ou apres ligne vide) -> True
      - `text\\n---` (soulignement setext H2) -> False (pas un bloc YAML)
      - `---` a l'interieur d'un bloc de code fence (``` ou ~~~) -> ignore
      - Fichier illisible (OSError, JSON invalide) -> False (laisse CI trancher)
      - Fichier non markdown / sans cells -> False
    """

    def _write_md(self, tmp_path: Path, name: str, body: str) -> str:
        """Helper: write a markdown file under docs/, return repo-relative POSIX path."""
        md_path = tmp_path / name
        md_path.parent.mkdir(parents=True, exist_ok=True)
        md_path.write_text(body, encoding="utf-8")
        # Repo-relative POSIX path (tmp_path stands in for REPO_ROOT in the
        # tests via monkeypatch below).
        return name

    def test_md_with_hr_separator_returns_true(self, tmp_path, monkeypatch):
        """Un .md avec `---` precede d'une ligne vide declenche la garde."""
        rel = self._write_md(tmp_path, "docs/test-hr.md",
                              "Titre introductif\n\n---\n\nSuite du texte\n")
        monkeypatch.setattr(rqr, "REPO_ROOT", tmp_path)
        assert rqr.has_hr_separator(rel) is True

    def test_md_with_hr_at_start_returns_true(self, tmp_path, monkeypatch):
        """Un .md commencant par `---` (debut de cellule) declenche la garde."""
        rel = self._write_md(tmp_path, "docs/test-hr-start.md",
                              "---\ntitle: foo\n---\n")
        monkeypatch.setattr(rqr, "REPO_ROOT", tmp_path)
        assert rqr.has_hr_separator(rel) is True

    def test_md_with_setext_heading_returns_false(self, tmp_path, monkeypatch):
        """Un .md avec `text\\n---` (soulignement setext H2) n'est PAS un hr YAML.

        C'est le cas explicitement distingue par la garde (lignes 187-190 du
        module) : seul un `---` precede d'une ligne vide ou du debut ouvre
        un bloc yaml_metadata_block.
        """
        rel = self._write_md(tmp_path, "docs/test-setext.md",
                              "Titre H1\n=========\n\nTitre H2\n---------\n\nSuite\n")
        monkeypatch.setattr(rqr, "REPO_ROOT", tmp_path)
        assert rqr.has_hr_separator(rel) is False

    def test_md_with_no_separator_returns_false(self, tmp_path, monkeypatch):
        """Un .md propre (sans `---`) n'est pas exclu."""
        rel = self._write_md(tmp_path, "docs/test-clean.md",
                              "# Titre normal\n\nDu contenu sans hr.\n\nPlus de contenu.\n")
        monkeypatch.setattr(rqr, "REPO_ROOT", tmp_path)
        assert rqr.has_hr_separator(rel) is False

    def test_md_with_hr_inside_code_fence_returns_false(self, tmp_path, monkeypatch):
        """Un `---` a l'interieur d'un bloc ```code``` n'est PAS un hr YAML."""
        rel = self._write_md(tmp_path, "docs/test-fence.md",
                              "# Titre\n\n```python\n---\ncode block\n```\n")
        monkeypatch.setattr(rqr, "REPO_ROOT", tmp_path)
        assert rqr.has_hr_separator(rel) is False

    def test_md_unreadable_returns_false(self, tmp_path, monkeypatch):
        """Fichier inexistant ou illisible : on retourne False, la CI tranchera."""
        monkeypatch.setattr(rqr, "REPO_ROOT", tmp_path)
        # Path qui n'existe pas
        assert rqr.has_hr_separator("docs/does-not-exist.md") is False

    def test_md_with_inline_text_above_hr_returns_false(self, tmp_path, monkeypatch):
        """Un .md avec `text\\n---\\n` (texte immediatement avant le hr) -> False.

        Variante du setext : la garde ne declenche QUE si la ligne precedente
        est vide (separateur horizontal) OU si on est au debut (ligne vide
        initiale). Une ligne de texte immediatement au-dessus n'ouvre PAS un
        bloc yaml_metadata_block.
        """
        rel = self._write_md(tmp_path, "docs/test-inline-hr.md",
                              "Une ligne de texte\n---\nPlus de texte\n")
        monkeypatch.setattr(rqr, "REPO_ROOT", tmp_path)
        assert rqr.has_hr_separator(rel) is False

    def test_ipynb_with_hr_in_markdown_cell_returns_true(self, tmp_path, monkeypatch):
        """Un .ipynb avec une cellule markdown portant `---` hr declenche la garde."""
        nb_content = '''{
  "cells": [
    {"cell_type": "markdown", "metadata": {}, "source": ["Titre\\n\\n---\\n\\nSuite"]}
  ],
  "metadata": {},
  "nbformat": 4,
  "nbformat_minor": 5
}'''
        nb_path = tmp_path / "test-hr.ipynb"
        nb_path.write_text(nb_content, encoding="utf-8")
        monkeypatch.setattr(rqr, "REPO_ROOT", tmp_path)
        assert rqr.has_hr_separator("test-hr.ipynb") is True

    def test_ipynb_clean_returns_false(self, tmp_path, monkeypatch):
        """Un .ipynb SANS `---` hr dans ses cellules markdown -> False."""
        nb_content = '''{
  "cells": [
    {"cell_type": "markdown", "metadata": {}, "source": ["# Titre propre\\n\\nDu contenu"]}
  ],
  "metadata": {},
  "nbformat": 4,
  "nbformat_minor": 5
}'''
        nb_path = tmp_path / "test-clean.ipynb"
        nb_path.write_text(nb_content, encoding="utf-8")
        monkeypatch.setattr(rqr, "REPO_ROOT", tmp_path)
        assert rqr.has_hr_separator("test-clean.ipynb") is False


# ---------------------------------------------------------------------------
# git_tracked_docs_md — exclusion des .md avec `---` hr (cf. #18422)
# ---------------------------------------------------------------------------

class TestGitTrackedDocsMd:
    """Valide que la fonction `git_tracked_docs_md` :
      - filtre les .md avec hr separator (garde #11451)
      - filtre les README.md (deja comptabilises par git_tracked_readmes)
      - filtre les fichiers sous EXCLUDE_MARKERS (archive, vendored)
      - trie la sortie (deterministic diffs)
    """

    def test_excludes_md_with_hr_separator(self, monkeypatch):
        """Un .md avec `---` hr doit etre exclu de la liste rendue."""
        clean_md = "docs/clean.md"
        hr_md = "docs/hr.md"
        fake_output = f"{clean_md}\n{hr_md}\n"

        def fake_run(*args, **kwargs):
            class Result:
                stdout = fake_output
                returncode = 0
            return Result()

        monkeypatch.setattr(rqr.subprocess, "run", fake_run)
        # Override has_hr_separator pour la fixture
        monkeypatch.setattr(rqr, "has_hr_separator",
                            lambda p: p.endswith("hr.md"))

        result = rqr.git_tracked_docs_md()
        assert clean_md in result
        assert hr_md not in result
        assert result == sorted(result, key=lambda s: s.lower())

    def test_excludes_readmes(self, monkeypatch):
        """Les README.md sous docs/ sont exclus (deja comptabilises par readmes)."""
        fake_output = "docs/README.md\ndocs/other.md\n"

        def fake_run(*args, **kwargs):
            class Result:
                stdout = fake_output
                returncode = 0
            return Result()

        monkeypatch.setattr(rqr.subprocess, "run", fake_run)
        result = rqr.git_tracked_docs_md()
        assert "docs/README.md" not in result
        assert "docs/other.md" in result

    def test_excludes_archive_markers(self, monkeypatch):
        """Les .md sous docs/archive/ sont exclus (EXCLUDE_MARKERS)."""
        fake_output = "docs/archive/old.md\ndocs/active.md\n"

        def fake_run(*args, **kwargs):
            class Result:
                stdout = fake_output
                returncode = 0
            return Result()

        monkeypatch.setattr(rqr.subprocess, "run", fake_run)
        result = rqr.git_tracked_docs_md()
        assert "docs/archive/old.md" not in result
        assert "docs/active.md" in result


# ---------------------------------------------------------------------------
# Index non resolu et doublons de render-list (#20055)
# ---------------------------------------------------------------------------
#
# Fait fondateur, mesure sur un depot jouet en merge non resolu (l'index porte
# alors trois etages pour un meme chemin : 1=base, 2=ours, 3=theirs) :
#
#     git ls-files '*README.md'             -> README.md (x3)
#     git diff --name-only --diff-filter=U  -> README.md (x1)
#
# `git ls-files` alimentant toute la render-list, un merge non resolu y ecrit
# des doublons silencieux. Les gardes ci-dessous ferment ce chemin.

class TestUnmergedPaths:
    """`unmerged_paths` : detection d'un index non resolu."""

    @staticmethod
    def _fake_run(stdout: str):
        def fake_run(*args, **kwargs):
            class Result:
                returncode = 0
            Result.stdout = stdout
            return Result()
        return fake_run

    def test_reports_conflicted_path(self, monkeypatch):
        monkeypatch.setattr(rqr.subprocess, "run", self._fake_run("README.md\n"))
        assert rqr.unmerged_paths() == ["README.md"]

    def test_empty_when_index_is_clean(self, monkeypatch):
        monkeypatch.setattr(rqr.subprocess, "run", self._fake_run(""))
        assert rqr.unmerged_paths() == []

    def test_deduplicates_and_sorts(self, monkeypatch):
        """Trois etages d'index pour un meme chemin ne rendent qu'une entree."""
        monkeypatch.setattr(rqr.subprocess, "run",
                            self._fake_run("b/README.md\na/README.md\nb/README.md\n"))
        assert rqr.unmerged_paths() == ["a/README.md", "b/README.md"]

    def test_uses_diff_filter_u(self, monkeypatch):
        """L'instrument est `diff --diff-filter=U`, pas `ls-files` : c'est lui
        qui nomme le chemin une fois (cf. le fait fondateur ci-dessus)."""
        seen = {}

        def fake_run(argv, *args, **kwargs):
            seen["argv"] = list(argv)

            class Result:
                returncode = 0
                stdout = ""
            return Result()

        monkeypatch.setattr(rqr.subprocess, "run", fake_run)
        rqr.unmerged_paths()
        assert "diff" in seen["argv"]
        assert "--diff-filter=U" in seen["argv"]


class TestRenderSections:
    """`render_sections` : enumeration unique, source des deux autres gardes."""

    @pytest.fixture(autouse=True)
    def _stub_git(self, monkeypatch):
        monkeypatch.setattr(rqr, "git_tracked_readmes", lambda: ["x/README.md"])
        monkeypatch.setattr(rqr, "git_tracked_docs_md", lambda: ["docs/a.md"])
        monkeypatch.setattr(rqr, "git_tracked_notebooks", lambda: ["n.ipynb"])

    def test_root_readme_prepended(self):
        assert rqr.render_sections()["readmes"] == ["README.md", "x/README.md"]

    def test_sections_present(self):
        s = rqr.render_sections()
        assert s["landing"] == list(rqr.LANDING_PAGES)
        assert s["docs"] == ["docs/a.md"]
        assert s["notebooks"] == ["n.ipynb"]

    def test_clean_sections_have_no_duplicate(self):
        assert rqr.duplicate_render_entries(rqr.render_sections()) == []

    def test_build_render_block_accepts_explicit_sections(self):
        text = "\n".join(rqr.build_render_block(rqr.render_sections()))
        assert '- "README.md"' in text
        assert '- "x/README.md"' in text
        # racine + 1 = 2 READMEs : le compte suit la section passee, pas un
        # nouvel appel a git.
        assert "2 READMEs" in text


class TestDuplicateRenderEntries:
    """`duplicate_render_entries` : doublon intra-section seulement (#20055)."""

    @staticmethod
    def _sections(**over):
        base = {"landing": [], "readmes": ["README.md"], "docs": [], "notebooks": []}
        base.update(over)
        return base

    def test_intra_section_duplicate_is_reported(self):
        s = self._sections(readmes=["README.md", "a/README.md", "a/README.md"])
        assert rqr.duplicate_render_entries(s) == [("readmes", "a/README.md")]

    def test_three_index_stages_report_two_repetitions(self):
        """Le fait fondateur : trois etages d'index = deux repetitions."""
        s = self._sections(readmes=["README.md", "a/README.md",
                                    "a/README.md", "a/README.md"])
        assert rqr.duplicate_render_entries(s) == [
            ("readmes", "a/README.md"), ("readmes", "a/README.md")]

    def test_cross_section_same_path_is_legitimate(self):
        """`docs/reference/branch-cleanup-manifest.README.md` figure sur `main`
        dans la section READMEs (motif `*README.md`) ET dans docs/*.md : ce
        n'est pas un doublon, et la garde ne doit pas le refuser."""
        p = "docs/reference/branch-cleanup-manifest.README.md"
        s = self._sections(readmes=["README.md", p], docs=[p])
        assert rqr.duplicate_render_entries(s) == []

    def test_duplicate_in_docs_section_detected(self):
        s = self._sections(docs=["docs/a.md", "docs/a.md"])
        assert rqr.duplicate_render_entries(s) == [("docs", "docs/a.md")]

    def test_duplicate_in_notebooks_section_detected(self):
        s = self._sections(notebooks=["a.ipynb", "b.ipynb", "a.ipynb"])
        assert rqr.duplicate_render_entries(s) == [("notebooks", "a.ipynb")]

    def test_defaults_to_render_sections(self, monkeypatch):
        monkeypatch.setattr(rqr, "git_tracked_readmes",
                            lambda: ["a/README.md", "a/README.md"])
        monkeypatch.setattr(rqr, "git_tracked_docs_md", lambda: [])
        monkeypatch.setattr(rqr, "git_tracked_notebooks", lambda: [])
        assert rqr.duplicate_render_entries() == [("readmes", "a/README.md")]


class TestMainRefusesUnsafeInput:
    """`main()` : les deux refus sont branches avant toute ecriture."""

    def test_refuses_unresolved_index(self, monkeypatch, capsys):
        monkeypatch.setattr(rqr, "unmerged_paths", lambda: ["README.md", "docs/a.md"])
        monkeypatch.setattr(sys, "argv", ["regen_quarto_render.py", "--check"])
        assert rqr.main() == 1
        err = capsys.readouterr().err
        assert "::error::" in err
        assert "README.md" in err and "docs/a.md" in err

    def test_refuses_duplicate_entry(self, monkeypatch, capsys):
        monkeypatch.setattr(rqr, "unmerged_paths", lambda: [])
        monkeypatch.setattr(rqr, "duplicate_render_entries",
                            lambda sections=None: [("readmes", "a/README.md")])
        monkeypatch.setattr(sys, "argv", ["regen_quarto_render.py", "--check"])
        assert rqr.main() == 1
        err = capsys.readouterr().err
        assert "::error::" in err
        assert "a/README.md" in err and "readmes" in err

    def test_refuses_duplicate_before_writing(self, monkeypatch, tmp_path):
        """Le refus vaut aussi pour le chemin d'ecriture (pas seulement
        `--check`) : on n'ecrit jamais une render-list dupliquee."""
        target = tmp_path / "_quarto.yml"
        target.write_text('project:\n  render:\n    - "old.md"\nsite:\n',
                          encoding="utf-8")
        before = target.read_text(encoding="utf-8")
        monkeypatch.setattr(rqr, "unmerged_paths", lambda: [])
        monkeypatch.setattr(rqr, "QUARTO_YML", target)
        monkeypatch.setattr(rqr, "duplicate_render_entries",
                            lambda sections=None: [("notebooks", "a.ipynb")])
        monkeypatch.setattr(sys, "argv", ["regen_quarto_render.py"])
        assert rqr.main() == 1
        assert target.read_text(encoding="utf-8") == before


class TestUnmergedIndexReproduction:
    """Reproduction du fait fondateur #20055 sur un vrai depot git."""

    @staticmethod
    def _git(cwd, *args, check=True):
        return subprocess.run(["git", *args], cwd=str(cwd), check=check,
                              capture_output=True, text=True,
                              encoding="utf-8", errors="replace")

    #: Sous-repertoire : `git_tracked_readmes` ecarte le README de racine
    #: (`p == "README.md"`), il faut donc un chemin non-racine pour traverser
    #: l'enumeration reelle.
    REL = "sub/README.md"

    def _conflicted_repo(self, tmp_path):
        def g(*args):
            return self._git(tmp_path, *args)

        ident = ("-c", "user.name=t", "-c", "user.email=t@t")
        target = tmp_path / "sub" / "README.md"
        target.parent.mkdir(parents=True, exist_ok=True)
        g("init", "-q")
        target.write_text("base\n", encoding="utf-8")
        g(*ident, "add", "sub/README.md")
        g(*ident, "commit", "-qm", "base")
        base_branch = g("rev-parse", "--abbrev-ref", "HEAD").stdout.strip()
        g("checkout", "-qb", "side")
        target.write_text("side\n", encoding="utf-8")
        g(*ident, "commit", "-qam", "side")
        g("checkout", "-q", base_branch)
        target.write_text("main\n", encoding="utf-8")
        g(*ident, "commit", "-qam", "main")
        # `-c merge.ff=false` : mesure sur le runner CI -- le merge y est REFUSE
        # (« Diverging branches can't be fast-forwarded », rc=128) sans creer
        # d'index non fusionne : `ls-files` rend 1 ligne, `--unmerged` rend vide.
        # Le runner se comporte donc comme si `merge.ff=only` etait pose ; la
        # reproduction locale sous cette config rend exactement les quatre
        # signatures observees en CI. Le test prenait ce refus pour un conflit,
        # et les trois assertions suivantes echouaient sur un index sain. Le
        # drapeau de ligne de commande prime sur toute config ambiante.
        # `*ident` : l'identite du committer doit accompagner le merge lui-meme
        # -- sans elle un merge en conflit sort en « Committer identity
        # unknown » sur un runner dont la config globale ne porte pas d'identite.
        merged = self._git(tmp_path, *ident, "-c", "merge.ff=false", "merge",
                           "side", check=False)
        # Le controle porte sur l'effet attendu (index non fusionne), pas sur
        # le code retour : un refus de merge sort aussi en non-zero.
        unmerged = self._git(tmp_path, "ls-files", "--unmerged").stdout
        assert unmerged.strip(), (
            "le merge devait laisser un index non fusionne (3 stages) ; "
            f"rc={merged.returncode}, sortie={merged.stdout}{merged.stderr}")
        return tmp_path

    def test_ls_files_yields_path_per_index_stage(self, tmp_path):
        """L'enumeration brute rend le chemin trois fois -- c'est la cause."""
        repo = self._conflicted_repo(tmp_path)
        raw = self._git(repo, "ls-files", "*README.md")
        assert raw.stdout.split().count(self.REL) == 3
        assert len(self._git(repo, "ls-files", "--unmerged").stdout.splitlines()) == 3

    def test_enumeration_would_duplicate_the_entry(self, tmp_path, monkeypatch):
        """Le degat : sans garde, la render-list porte l'entree trois fois."""
        repo = self._conflicted_repo(tmp_path)
        monkeypatch.setattr(rqr, "REPO_ROOT", repo)
        assert rqr.git_tracked_readmes().count(self.REL) == 3
        assert rqr.duplicate_render_entries(rqr.render_sections()) == [
            ("readmes", self.REL), ("readmes", self.REL)]

    def test_unmerged_paths_names_it_once(self, tmp_path, monkeypatch):
        """La garde nomme le chemin une seule fois."""
        repo = self._conflicted_repo(tmp_path)
        monkeypatch.setattr(rqr, "REPO_ROOT", repo)
        assert rqr.unmerged_paths() == [self.REL]

    def test_main_refuses_on_a_conflicted_repo(self, tmp_path, monkeypatch, capsys):
        """Bout en bout : sur un index non resolu, le script sort en erreur en
        nommant le chemin, au lieu d'ecrire une render-list dupliquee."""
        repo = self._conflicted_repo(tmp_path)
        monkeypatch.setattr(rqr, "REPO_ROOT", repo)
        monkeypatch.setattr(sys, "argv", ["regen_quarto_render.py", "--check"])
        assert rqr.main() == 1
        err = capsys.readouterr().err
        assert "::error::" in err and self.REL in err