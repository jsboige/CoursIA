"""Tests for scripts/notebook_tools/demote_md_asides.py — multi-family HINT-AS-HEADING demoter.

Consolidated tests covering the byte-surgical pattern reused from
fix_sudoku_hierarchy.py (c.925, PR #8654) and fix_tweety_hierarchy.py
(c.922, PR #8647). Three families of tests:

  - Source format detection / preservation (3 nbformat formats per L925-A/L983).
  - Heading detection (6 patterns: Indices, Étapes, Étapes a suivre,
    Étapes de la modélisation..., Pistes d'amélioration/amelioration,
    Notes techniques).
  - Idempotence (re-running on already-demoted cells is a no-op).
  - Multi-heading per cell (Sudoku-6-AIMA-CSP-Python has both Étapes
    and Indices in the same cell — both must be demoted).
  - File-level fix (write-back semantics, LF-only CR=0, dry-run).
"""

import json
import pathlib
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from demote_md_asides import (
    _detect_source_format,
    _demote_all_headings,
    _matches_target,
    _re_emit_in_format,
    _resolve_dir,
    fix_notebook,
)


# ---------------------------------------------------------------------------
# _matches_target
# ---------------------------------------------------------------------------


class TestMatchesTarget:
    """Detection of bare asides (Sudoku + Tweety patterns)."""

    @pytest.mark.parametrize('text', [
        'Indices',
        'Étapes',
        'Étapes a suivre',
        'Étapes de la modélisation avec OR-Tools',
        'Étapes de la modélisation avec Google OR-Tools',
        "Pistes d'amélioration",
        "Pistes d'amelioration",  # legacy no-accent
        'Notes techniques',
        'Notes techniques (Tweety 1.30)',
    ])
    def test_target_matches(self, text):
        assert _matches_target(text) is True

    @pytest.mark.parametrize('text', [
        '1. Introduction',
        'Concepts clés',
        'Méthodologie',
        'Exercice 3',
        'Objectif',
        'Step 1: Load Data',  # titled step — not bare aside
        'Note pédagogique',  # bare aside but NOT in our scope
        'Aide-mémoire des commandes',  # compound — not bare aside
        'Remarques finales',  # bare aside but NOT in our scope
        'Important à retenir',  # bare aside but NOT in our scope
    ])
    def test_non_targets_no_match(self, text):
        assert _matches_target(text) is False


# ---------------------------------------------------------------------------
# _detect_source_format
# ---------------------------------------------------------------------------


class TestDetectSourceFormat:
    """L925-A ★★ / L983 ★★ — three nbformat source formats."""

    def test_string(self):
        assert _detect_source_format("line1\nline2\nline3") == 'string'

    def test_line_list(self):
        assert _detect_source_format(["line1\n", "line2\n", "line3"]) == 'line-list'

    def test_char_split(self):
        # Each element is a single char; no '\n' anywhere.
        assert _detect_source_format(list("hello world")) == 'char-split'

    def test_empty_list(self):
        # Empty list: treat as line-list for safety (avoid format confusion).
        assert _detect_source_format([]) == 'line-list'

    def test_empty_string(self):
        # Empty string is technically a 'string' (single joined element).
        assert _detect_source_format("") == 'string'

    def test_single_line_list(self):
        # Single-element list with '\n' is still line-list (one of the lines).
        assert _detect_source_format(["only\n"]) == 'line-list'


# ---------------------------------------------------------------------------
# _demote_all_headings
# ---------------------------------------------------------------------------


class TestDemoteAllHeadings:
    """Heading demotion logic — multi-heading per cell honored."""

    def test_indices_only(self):
        """Single `### Indices` heading -> blockquote, body preserved."""
        src = ["### Indices\n", "\n", "Voici les indices.\n"]
        new, count = _demote_all_headings(src)
        assert count == 1
        assert new == ["> **Indices :**\n", "\n", "Voici les indices.\n"]

    def test_etapes_with_modern_accent(self):
        src = ["### Étapes\n", "\n", "Étape 1...\n"]
        new, count = _demote_all_headings(src)
        assert count == 1
        assert new[0] == "> **Étapes :**\n"
        assert new[1:] == ["\n", "Étape 1...\n"]

    def test_etapes_legacy_no_accent(self):
        src = ["### Étapes a suivre\n", "\n", "Étape 1...\n"]
        new, count = _demote_all_headings(src)
        assert count == 1
        assert new[0] == "> **Étapes a suivre :**\n"

    def test_etapes_modelling_with_engine(self):
        src = ["### Étapes de la modélisation avec OR-Tools\n", "\n", "Étape 1...\n"]
        new, count = _demote_all_headings(src)
        assert count == 1
        assert new[0] == "> **Étapes de la modélisation avec OR-Tools :**\n"

    def test_pistes_amelioration_curly(self):
        src = ["### Pistes d'amélioration\n", "\n", "Amélioration future.\n"]
        new, count = _demote_all_headings(src)
        assert count == 1
        assert new[0] == "> **Pistes d'amélioration :**\n"

    def test_pistes_amelioration_legacy_no_accent(self):
        src = ["### Pistes d'amelioration\n", "\n", "Amélioration future.\n"]
        new, count = _demote_all_headings(src)
        assert count == 1
        assert new[0] == "> **Pistes d'amelioration :**\n"

    def test_notes_techniques(self):
        src = ["## Notes techniques\n", "\n", "Détails.\n"]
        new, count = _demote_all_headings(src)
        assert count == 1
        assert new[0] == "> **Notes techniques :**\n"

    def test_notes_techniques_with_parenthetical(self):
        """Parenthetical-strip allows canonical match."""
        src = ["## Notes techniques (Tweety 1.30)\n", "\n", "Détails.\n"]
        new, count = _demote_all_headings(src)
        assert count == 1
        # The demoted text preserves the original (with parenthetical).
        assert new[0] == "> **Notes techniques (Tweety 1.30) :**\n"

    def test_multi_headings_same_cell(self):
        """Sudoku-6-AIMA-CSP-Python has BOTH Étapes AND Indices in one cell."""
        src = [
            "### Étapes\n",
            "\n",
            "Étape 1...\n",
            "\n",
            "### Indices\n",
            "\n",
            "Voici les indices.\n",
        ]
        new, count = _demote_all_headings(src)
        assert count == 2
        assert new[0] == "> **Étapes :**\n"
        assert new[4] == "> **Indices :**\n"

    def test_no_match_no_change(self):
        """No matching heading -> empty demote, no count change."""
        src = ["## Concepts\n", "\n", "Some body.\n"]
        new, count = _demote_all_headings(src)
        assert count == 0
        assert new == src

    def test_h1_or_h2_heading_ignored(self):
        """Heading levels (#..######) all scanned, but non-target text ignored."""
        src = ["# 1. Introduction\n", "## Concepts\n", "### Étapes\n"]
        new, count = _demote_all_headings(src)
        assert count == 1
        assert new[0] == "# 1. Introduction\n"
        assert new[1] == "## Concepts\n"
        assert new[2] == "> **Étapes :**\n"

    def test_empty_source(self):
        new, count = _demote_all_headings([])
        assert count == 0
        assert new == []

    def test_string_source_split_to_lines(self):
        """Caller-side invariant: _demote_all_headings expects a list.
        A 'string' source cell would normally be split into lines BEFORE
        calling (via splitlines(keepends=True)). Verify the algorithm
        works on the already-split form.
        """
        joined = "### Étapes\n\nÉtape 1...\n"
        src = joined.splitlines(keepends=True)
        new, count = _demote_all_headings(src)
        assert count == 1
        assert new[0] == "> **Étapes :**\n"


# ---------------------------------------------------------------------------
# _re_emit_in_format
# ---------------------------------------------------------------------------


class TestReEmitInFormat:
    """Format preservation on re-serialization."""

    def test_string_format(self):
        new_lines = ["> **Indices :**\n", "\n", "Body.\n"]
        out = _re_emit_in_format('string', new_lines)
        assert isinstance(out, str)
        assert out == "> **Indices :**\n\nBody.\n"

    def test_line_list_format(self):
        new_lines = ["> **Indices :**\n", "\n", "Body.\n"]
        out = _re_emit_in_format('line-list', new_lines)
        assert out == new_lines

    def test_char_split_format(self):
        new_lines = ["> **Indices :**\n"]
        out = _re_emit_in_format('char-split', new_lines)
        assert isinstance(out, list)
        assert out == list("> **Indices :**\n")

    def test_unknown_format_passthrough(self):
        new_lines = ["> **Indices :**\n"]
        out = _re_emit_in_format('unknown', new_lines)
        assert out is new_lines


# ---------------------------------------------------------------------------
# fix_notebook
# ---------------------------------------------------------------------------


class TestFixNotebook:
    """File-level fix with write-back semantics."""

    def _write_nb(self, path: Path, cells: list[dict]) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        path.write_text(json.dumps(nb), encoding="utf-8")
        return path

    def test_demotes_indices(self, tmp_path):
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "markdown",
             "source": ["### Indices\n", "\n", "Voici les indices.\n"],
             "metadata": {}},
        ])
        n, err = fix_notebook(nb_path)
        assert err is None
        assert n == 1

        with open(nb_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        assert data["cells"][0]["source"] == [
            "> **Indices :**\n", "\n", "Voici les indices.\n",
        ]

    def test_demotes_string_format_cell(self, tmp_path):
        """String-format source cell -> preserved as string after demotion.
        Body MUST NOT be lost (incident c.925 #8654: 941 -> 16 chars).
        """
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "markdown",
             "source": "### Indices\n\nVoici les indices.\n",
             "metadata": {}},
        ])
        n, err = fix_notebook(nb_path)
        assert err is None
        assert n == 1

        with open(nb_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        # Format preserved as string (not collapsed to single-line list).
        assert isinstance(data["cells"][0]["source"], str)
        assert "> **Indices :**" in data["cells"][0]["source"]
        assert "Voici les indices." in data["cells"][0]["source"]
        # Body intact: cell content should be > 30 chars (not collapsed to
        # the demoted heading alone, ~16 chars).
        assert len(data["cells"][0]["source"]) > 30

    def test_demotes_char_split_format_cell(self, tmp_path):
        """Char-split source cell -> preserved as char-list after demotion."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "markdown",
             "source": list("### Indices\n\nBody.\n"),
             "metadata": {}},
        ])
        n, err = fix_notebook(nb_path)
        assert err is None
        assert n == 1

        with open(nb_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        # Format preserved as char-list.
        assert isinstance(data["cells"][0]["source"], list)
        joined = ''.join(data["cells"][0]["source"])
        assert "> **Indices :**" in joined
        assert "Body." in joined

    def test_idempotent_on_already_demoted(self, tmp_path):
        """Re-running on already-demoted cell -> no change, no write."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "markdown",
             "source": ["> **Indices :**\n", "\n", "Body.\n"],
             "metadata": {}},
        ])
        original = nb_path.read_text(encoding="utf-8")
        n, err = fix_notebook(nb_path)
        assert err is None
        assert n == 0
        # File unchanged (no demotion, no write).
        assert nb_path.read_text(encoding="utf-8") == original

    def test_skips_code_cells(self, tmp_path):
        """Code cells are not modified even if source contains target text."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code",
             "source": "### Indices\nprint('not a heading')",
             "outputs": [], "execution_count": 1},
        ])
        n, err = fix_notebook(nb_path)
        assert err is None
        assert n == 0

    def test_dry_run_no_write(self, tmp_path):
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "markdown",
             "source": ["### Étapes\n", "\n", "Body.\n"],
             "metadata": {}},
        ])
        original = nb_path.read_text(encoding="utf-8")
        n, err = fix_notebook(nb_path, dry_run=True)
        assert err is None
        assert n == 1
        assert nb_path.read_text(encoding="utf-8") == original

    def test_trailing_newline_preserved(self, tmp_path):
        # Write the notebook WITH a trailing newline (mimicking repo
        # convention); the fix must preserve it.
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "markdown",
             "source": ["### Étapes\n", "\n", "Body.\n"],
             "metadata": {}},
        ])
        # Add trailing newline (some test infra strips it).
        with open(nb_path, "ab") as f:
            f.write(b"\n")
        fix_notebook(nb_path)
        content = nb_path.read_bytes()
        assert content.endswith(b"\n")

    def test_no_modification_no_write(self, tmp_path):
        """Notebook with no demotable headings -> no write (preserves
        byte-identity even on files where the cell format might differ).
        """
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "markdown",
             "source": ["# 1. Introduction\n", "\n", "Body.\n"],
             "metadata": {}},
        ])
        original_bytes = nb_path.read_bytes()
        n, err = fix_notebook(nb_path)
        assert err is None
        assert n == 0
        assert nb_path.read_bytes() == original_bytes

    def test_multi_headings_same_cell(self, tmp_path):
        """Sudoku-6-AIMA-CSP-Python: BOTH Étapes AND Indices in one cell."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "markdown",
             "source": [
                 "### Étapes\n", "\n",
                 "Étape 1...\n", "\n",
                 "### Indices\n", "\n",
                 "Voici les indices.\n",
             ],
             "metadata": {}},
        ])
        n, err = fix_notebook(nb_path)
        assert err is None
        assert n == 2

        with open(nb_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        src = data["cells"][0]["source"]
        assert "> **Étapes :**\n" in src
        assert "> **Indices :**\n" in src

    def test_parse_error_returns_error_string(self, tmp_path):
        """A non-JSON file yields (0, 'parse: ...') instead of crashing."""
        bad = tmp_path / "bad.ipynb"
        bad.write_text("not json", encoding="utf-8")
        n, err = fix_notebook(bad)
        assert n == 0
        assert err is not None
        assert "parse" in err

    def test_empty_cells(self, tmp_path):
        """Notebook with no cells -> (0, None), no crash."""
        nb_path = self._write_nb(tmp_path / "empty.ipynb", [])
        n, err = fix_notebook(nb_path)
        assert err is None
        assert n == 0


# ---------------------------------------------------------------------------
# _resolve_dir
# ---------------------------------------------------------------------------


class TestResolveDir:
    """CLI path resolution."""

    def test_absolute_path(self):
        out = _resolve_dir("D:/abs/path")
        assert out.is_absolute()

    def test_relative_path(self, tmp_path):
        """Relative path is resolved against the worktree root."""
        # Create the family dir under the worktree.
        nb_root = pathlib.Path(__file__).resolve().parent.parent.parent.parent
        target_dir = nb_root / "MyIA.AI.Notebooks" / "Sudoku"
        if not target_dir.is_dir():
            pytest.skip(f"family dir does not exist: {target_dir}")
        out = _resolve_dir("MyIA.AI.Notebooks/Sudoku")
        assert out.is_absolute()
        assert out.is_dir()
        assert out == target_dir.resolve()

    def test_relative_path_uses_arg_dir(self):
        """_resolve_dir handles non-existent relative paths by returning
        the resolved (but not yet existing) absolute path."""
        # Use a deliberately bogus path; _resolve_dir is a path resolver,
        # not a validator.
        out = _resolve_dir("MyIA.AI.Notebooks/NotARealFamily")
        assert out.is_absolute()
