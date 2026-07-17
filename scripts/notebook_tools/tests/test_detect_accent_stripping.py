"""Tests for scripts/notebook_tools/detect_accent_stripping.py — accent-stripping detector.

Tests focus on pure functions: scan_notebook, _STRIP_RE, _build_regex, _src_lines,
and the main() exit codes. Uses synthetic notebook dicts and tmp_path for
filesystem isolation.

Why this test file exists
--------------------------
`detect_accent_stripping.py` (registre #2876) is the canonical DETECTOR for FR
accent loss in pedagogical notebooks. The detection half is formally tested here;
the restoration half remains manual by design (po-2025 explicitly skipped
ambiguous cases on #6799, see detector docstring). Five clusters:

  1. TestSrcLines — nbformat source-as-list vs source-as-str split semantics
  2. TestStripRegex — boundary semantics, case-insensitivity, dictionary hygiene
  3. TestScanNotebook — happy-path / TN / TP / cross-cell / mixed md+code / error
  4. TestMainExitCodes — exit 0/1/2 contract (--check, missing file, family)
  5. TestAccentPairs — dictionary self-consistency (canonicalization, no FP risks)

Test data design: every stripped form used in tests is a member of the
conservative dictionary (probleme, caracteres, methode, etc.), so the regex
*will* hit. Tests for FP-prone pairs (e.g. "ou", "complete") are explicitly
NOT in the dictionary — see detector docstring line 17-26 (G.1 finding c.539).
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_accent_stripping import (  # noqa: E402
    ACCENT_PAIRS,
    _STRIP_RE,
    _build_regex,
    _src_lines,
    main,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _md(source: str) -> dict:
    """A markdown cell with given source (str)."""
    return {"cell_type": "markdown", "source": source}


def _code(source: str) -> dict:
    """A code cell with given source (str)."""
    return {"cell_type": "code", "source": source}


def _md_list(lines: list[str]) -> dict:
    """A markdown cell with source as nbformat list-of-strings (each may carry \\n)."""
    return {"cell_type": "markdown", "source": [ln if ln.endswith("\n") else ln + "\n" for ln in lines]}


def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# _src_lines — split semantics for source-as-str vs source-as-list
# ---------------------------------------------------------------------------

class TestSrcLines:
    def test_str_with_multiple_newlines(self):
        # Single string source: splitlines() splits on every \n.
        cell = {"source": "line 1\nline 2\nline 3"}
        assert _src_lines(cell) == ["line 1", "line 2", "line 3"]

    def test_str_no_trailing_newline(self):
        cell = {"source": "a\nb"}
        assert _src_lines(cell) == ["a", "b"]

    def test_str_empty(self):
        cell = {"source": ""}
        assert _src_lines(cell) == []

    def test_list_with_trailing_newlines(self):
        # nbformat typical: list of chunks, each with trailing \n.
        cell = {"source": ["alpha\n", "beta\n", "gamma\n"]}
        assert _src_lines(cell) == ["alpha", "beta", "gamma"]

    def test_list_mixed_trailing_newlines(self):
        # Some chunks without trailing \n (last chunk).
        cell = {"source": ["first\n", "second"]}
        assert _src_lines(cell) == ["first", "second"]

    def test_list_empty(self):
        cell = {"source": []}
        assert _src_lines(cell) == []

    def test_list_empty_strings(self):
        # nbformat can pad with empty strings; should yield no lines.
        cell = {"source": [""]}
        assert _src_lines(cell) == []


# ---------------------------------------------------------------------------
# _STRIP_RE / _build_regex — dictionary-driven detection contract
# ---------------------------------------------------------------------------

class TestStripRegex:
    def test_matches_known_stripped_form(self):
        # Dictionary has "probleme" -> "problème"; case-insensitive match.
        assert _STRIP_RE.search("un probleme de parsing") is not None

    def test_matches_at_word_boundary(self):
        # "caractere" alone should match; embedded in identifier should NOT.
        assert _STRIP_RE.search("caractere") is not None
        # "caracteres" (with s) is in dict; "caracteresspec" is not a word boundary.
        assert _STRIP_RE.search("caracteres_spec") is None

    def test_matches_case_insensitive(self):
        # ACCENT_PAIRS keys are lowercase; regex is case-insensitive.
        assert _STRIP_RE.search("PROBLEME") is not None
        assert _STRIP_RE.search("Probleme") is not None

    def test_plural_matches_before_singular(self):
        # Sorted by length descending: "caracteres" before "caractere".
        # "caracteres" should hit as a single match, not as "caractere" + "s".
        text = "les caracteres sont importants"
        m = _STRIP_RE.search(text)
        assert m is not None
        assert m.group(0) == "caracteres"

    def test_does_not_match_fp_words(self):
        # G.1 finding: dictionary excludes FR-valid-without-accent words.
        # Note: "modele" is intentionally IN the dictionary (author comment L72:
        # "modele(wait inclus car non-mot)" — the detector author explicitly
        # judged "modele" alone is not a valid FR word, so it stays as a hit).
        # The list below is the verified exclusion set from detector docstring L72.
        for fp_word in ["complete", "ou", "a", "niveau", "valeur", "exemple",
                        "fonction", "variable", "analyse", "finale", "suite",
                        "mais", "donc", "car", "or", "ni", "puis", "alors", "ici",
                        "chaque", "code", "option", "branche"]:
            assert _STRIP_RE.search(f"un {fp_word} de plus") is None, (
                f"FP regression: {fp_word!r} should NOT match (it's a valid FR word)"
            )

    def test_does_not_match_english_words(self):
        # Pure English text: no hit.
        assert _STRIP_RE.search("The system has a problem with parameters") is None

    def test_matches_accented_form_is_idempotent(self):
        # The accented form MUST NOT match (otherwise restoration would loop).
        assert _STRIP_RE.search("un problème de parsing") is None
        assert _STRIP_RE.search("les caractères spéciaux") is None

    def test_build_regex_repeatable(self):
        # Two calls should yield equivalent regexes (no shared mutable state).
        r1 = _build_regex()
        r2 = _build_regex()
        assert r1.pattern == r2.pattern
        assert r1.search("probleme") is not None
        assert r2.search("probleme") is not None


# ---------------------------------------------------------------------------
# scan_notebook — end-to-end detection contract
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def test_clean_notebook_no_hits(self, tmp_path):
        # All cells use accented forms correctly — no stripped tokens.
        cells = [
            _md("# Introduction\n\nCe problème est traité en plusieurs étapes."),
            _code("# Calcul de la moyenne\nresult = sum(values) / len(values)"),
        ]
        p = _write_nb(tmp_path / "clean.ipynb", cells)
        result = scan_notebook(p)
        assert isinstance(result, list)
        assert result == []

    def test_markdown_stripped_form_detected(self, tmp_path):
        # Mirror of #6799 finding (Sudoku-11-Choco-Python, 169 lignes stripped).
        cells = [_md("# Méthode\n\nLe probleme est le suivant: ...")]
        p = _write_nb(tmp_path / "stripped.ipynb", cells)
        result = scan_notebook(p)
        assert isinstance(result, list)
        assert len(result) == 1
        h = result[0]
        assert h["cell_idx"] == 0
        assert h["cell_type"] == "markdown"
        assert h["stripped"] == "probleme"
        assert h["suggestion"] == "problème"
        assert "Le probleme" in h["line"]

    def test_code_cell_stripped_detected(self, tmp_path):
        # Stripped token in a code comment.
        cells = [_code("# Cette methode calcule la moyenne")]
        p = _write_nb(tmp_path / "code.ipynb", cells)
        result = scan_notebook(p)
        assert isinstance(result, list)
        assert len(result) == 1
        assert result[0]["cell_type"] == "code"
        assert result[0]["stripped"].lower() == "methode"
        assert result[0]["suggestion"] == "méthode"

    def test_multiple_hits_in_single_cell(self, tmp_path):
        cells = [_md("Le probleme et la methode sont distincts, ainsi que l'etape")]
        p = _write_nb(tmp_path / "multi.ipynb", cells)
        result = scan_notebook(p)
        assert isinstance(result, list)
        # 3 distinct stripped tokens on the same line.
        stripped = {h["stripped"].lower() for h in result}
        assert "probleme" in stripped
        assert "methode" in stripped
        assert "etape" in stripped

    def test_multi_line_hits_line_numbers(self, tmp_path):
        cells = [_md("Ligne 1 sans accent\nLigne 2 avec probleme\nLigne 3 propre")]
        p = _write_nb(tmp_path / "lines.ipynb", cells)
        result = scan_notebook(p)
        assert isinstance(result, list)
        assert len(result) == 1
        assert result[0]["line_no"] == 2

    def test_multi_cell_hits_correct_indices(self, tmp_path):
        cells = [
            _md("Premier probleme en cellule 0"),
            _code("# Methode en cellule 1"),
            _md("Troisieme etape en cellule 2"),
        ]
        p = _write_nb(tmp_path / "cells.ipynb", cells)
        result = scan_notebook(p)
        assert isinstance(result, list)
        assert len(result) == 3
        assert {h["cell_idx"] for h in result} == {0, 1, 2}

    def test_nbformat_list_source_stripped(self, tmp_path):
        # nbformat can have source as list-of-strings.
        cells = [_md_list(["# Titre\n", "Le probleme est connu"])]
        p = _write_nb(tmp_path / "nbformat.ipynb", cells)
        result = scan_notebook(p)
        assert isinstance(result, list)
        assert len(result) == 1
        assert result[0]["stripped"].lower() == "probleme"

    def test_unreadable_notebook_returns_error_dict(self, tmp_path):
        # scan_notebook returns {"error": str} on parse failure (mixed return type).
        # Python 3.12+ JSONDecodeError messages don't always contain "json"/"decode"
        # substrings — just verify that *some* error message is captured.
        bad = tmp_path / "bad.ipynb"
        bad.write_text("{ not json", encoding="utf-8")
        result = scan_notebook(bad)
        assert isinstance(result, dict)
        assert "error" in result
        assert isinstance(result["error"], str)
        assert len(result["error"]) > 0


# ---------------------------------------------------------------------------
# ACCENT_PAIRS — dictionary self-consistency
# ---------------------------------------------------------------------------

class TestAccentPairs:
    def test_dictionary_non_empty(self):
        assert len(ACCENT_PAIRS) > 50  # conservative threshold

    def test_stripped_keys_are_lowercase(self):
        # Detector lowercases for canonicalization; keys should already be lowercase.
        for k in ACCENT_PAIRS:
            assert k == k.lower(), f"Key {k!r} should be lowercase"

    def test_stripped_keys_unique(self):
        # No duplicate keys.
        assert len(ACCENT_PAIRS) == len(set(ACCENT_PAIRS))

    def test_suggestions_differ_from_keys(self):
        # A dictionary mapping stripped -> accented must differ (otherwise no-op).
        for k, v in ACCENT_PAIRS.items():
            assert k != v, f"Pair {k!r}->{v!r} is identity (no-op)"

    def test_suggestions_contain_accents(self):
        # Sanity: suggestions should actually carry accents (or other diacritics).
        # Count at least 50% of suggestions containing non-ASCII chars.
        with_accents = sum(1 for v in ACCENT_PAIRS.values()
                           if any(ord(c) > 127 for c in v))
        assert with_accents >= len(ACCENT_PAIRS) // 2

    def test_excludes_known_fp_words(self):
        # G.1 c.539: these words are FP risks. None should be in the dict.
        # Same exclusion set as test_does_not_match_fp_words above.
        # Note: "modele" is intentionally IN dict per author comment L72.
        forbidden = {"complete", "ou", "a", "la", "valeur", "niveau", "exemple",
                     "fonction", "variable", "analyse", "finale", "suite",
                     "mais", "donc", "car", "or", "ni", "puis", "alors", "ici",
                     "chaque", "code", "option", "branche"}
        leaks = forbidden & set(ACCENT_PAIRS.keys())
        assert not leaks, f"FP-prone words in dictionary: {leaks}"

    def test_extension_c589_pairs_present(self):
        # PR accent-dict-extension (#2876): 55 conservative pairs added whose
        # stripped form is neither a valid FR word nor a common EN word.
        added = {
            "strategie": "stratégie", "controle": "contrôle",
            "definir": "définir", "mecanisme": "mécanisme",
            "criteres": "critères", "operateur": "opérateur",
            "theorique": "théorique", "caracteristique": "caractéristique",
            "numerique": "numérique", "systematique": "systématique",
            "metaheuristique": "métaheuristique", "genetique": "génétique",
            "hierarchie": "hiérarchie", "semantique": "sémantique",
            "specifique": "spécifique", "interet": "intérêt",
            "precis": "précis", "egalement": "également",
            "sequentiel": "séquentiel", "deterministe": "déterministe",
            "regle": "règle",
        }
        for k, v in added.items():
            assert k in ACCENT_PAIRS, f"missing extension pair {k!r}"
            assert ACCENT_PAIRS[k] == v, f"wrong mapping for {k!r}"

    def test_accented_forms_are_idempotent(self):
        # CRITICAL anti-loop invariant: the accented suggestion MUST NOT itself
        # match _STRIP_RE (otherwise restoration would re-trigger on the cured
        # text, looping forever / flagging already-correct prose). Verified
        # across the WHOLE dictionary, not just the extension.
        violations = [(k, v) for k, v in ACCENT_PAIRS.items() if _STRIP_RE.search(v)]
        assert not violations, (
            f"Accented forms match the strip regex (restoration loop risk): {violations[:5]}"
        )

    def test_excludes_en_valid_words(self):
        # PR accent-dict-extension: the -tion/-ence anglicisms whose stripped
        # form is a common ENGLISH word are deliberately EXCLUDED (FP risk in
        # EN prose or code identifiers — the silent-corruption class flagged
        # by po-2025 c.591). They must NOT be in the dictionary.
        en_valid_risky = {
            "generation", "evolution", "resolution", "evaluation",
            "implementation", "reference", "sequence", "definition",
            "integration", "prediction", "regression", "representation",
            "optimization", "decomposition", "detection",
        }
        leaks = en_valid_risky & set(ACCENT_PAIRS.keys())
        assert not leaks, (
            f"EN-valid words leaked into dict (FP risk in bilingual/code context): {leaks}"
        )


# ---------------------------------------------------------------------------
# main() exit codes
# ---------------------------------------------------------------------------

class TestMainExitCodes:
    def test_check_clean_exit_0(self, tmp_path):
        p = _write_nb(tmp_path / "clean.ipynb",
                      [_md("# Tout est accentué correctement ici")])
        assert main([str(p), "--check"]) == 0

    def test_check_stripped_exit_1(self, tmp_path):
        p = _write_nb(tmp_path / "stripped.ipynb",
                      [_md("Le probleme est evident")])
        assert main([str(p), "--check"]) == 1

    def test_missing_notebook_exit_2(self, tmp_path):
        # Notebook arg points to a non-existent file -> exit 2.
        assert main([str(tmp_path / "nope.ipynb")]) == 2

    def test_non_check_mode_exits_0_even_with_hits(self, tmp_path):
        # Without --check, hits do NOT trigger non-zero exit (informational mode).
        p = _write_nb(tmp_path / "stripped.ipynb",
                      [_md("Le probleme est evident")])
        assert main([str(p)]) == 0  # no --check => exit 0

    def test_json_mode_emits_valid_json(self, tmp_path, capsys):
        p = _write_nb(tmp_path / "stripped.ipynb",
                      [_md("Le probleme est evident")])
        rc = main([str(p), "--json"])
        out = capsys.readouterr().out
        payload = json.loads(out)
        assert "total_hits" in payload
        assert "notebooks" in payload
        assert payload["total_hits"] == 1
        # JSON must NOT include non-ASCII-friendly escapes for accents.
        # The detector uses ensure_ascii=False (per source line 302).
        assert "problème" in out
        assert rc == 0  # no --check => exit 0