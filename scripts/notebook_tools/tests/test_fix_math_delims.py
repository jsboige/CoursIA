"""Tests for scripts/notebook_tools/fix_math_delims.py (#17380).

Couvre :
  - les DEUX formes du delimiteur inline : simple `\\( ... \\)` et ECHAPPEE
    `\\\\( ... \\\\)` (mesuree sur IIT-01 cellules 14/26/37) -- le backslash de
    tete appartient au delimiteur, donc `\\\\(\\Phi\\\\)` se repare en `$\\Phi$`
    et JAMAIS en `\\$\\Phi\\$` (dollar echappe = toujours du texte brut)
  - le faux-fix fondateur (mesure 2026-09-22, twin-parity de cette PR) :
    « les separateurs (/ ou \\) selon l'OS » n'est PAS un span math
  - l'exclusion des code spans et des fences, comme le detector
  - l'invariant de round-trip, a parite tokens/$
  - le bout-en-bout : `--apply` sur un notebook temporaire convertit le
    markdown et laisse les cellules code byte-identiques
"""

import json
import sys
from pathlib import Path

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

from fix_math_delims import (  # noqa: E402
    _MATH_SPAN_RE,
    _check_invariant,
    _convert_outside_code,
    _looks_like_math,
    _skeleton,
    process,
)


def _make_nb(markdown_sources, code_sources=()):
    cells = [
        {"cell_type": "markdown", "metadata": {}, "source": [s]}
        for s in markdown_sources
    ]
    cells += [
        {"cell_type": "code", "metadata": {}, "execution_count": 1,
         "outputs": [], "source": [s]}
        for s in code_sources
    ]
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


# ---------------------------------------------------------------------------
# Forme simple
# ---------------------------------------------------------------------------

def test_plain_pair_is_converted():
    out, n = _convert_outside_code(r"Soit \(S = \mathbb{F}_p^n\) l'ensemble.")
    assert out == r"Soit $S = \mathbb{F}_p^n$ l'ensemble."
    assert n == 2


def test_two_pairs_on_one_line():
    out, n = _convert_outside_code(r"\(a\) et \(b\) valent.")
    assert out == "$a$ et $b$ valent."
    assert n == 4


# ---------------------------------------------------------------------------
# Forme ECHAPPEE -- le defaut que la premiere version du fixer a produit
# ---------------------------------------------------------------------------

def test_escaped_pair_is_converted_to_plain_dollars():
    out, n = _convert_outside_code(r"On peut egalement calculer \\(\Phi\\) ici.")
    assert out == r"On peut egalement calculer $\Phi$ ici."
    assert n == 2


def test_escaped_pair_introduces_no_escaped_dollar():
    """Le faux-fix d'origine : laisser le backslash de tete produisait
    `\\$\\Phi\\$`, un dollar ECHAPPE -- donc toujours du texte, jamais du math."""
    out, _ = _convert_outside_code(r"calculer \\(\Phi\\) ici")
    assert "\\$" not in out


def test_escaped_and_plain_forms_coexist_on_one_line():
    out, n = _convert_outside_code(r"\(\Phi\) puis \\(\Psi\\) ici")
    assert out == r"$\Phi$ puis $\Psi$ ici"
    assert n == 4


def test_escaped_orphan_without_opener_is_intact():
    """Forme echappee SANS `\\(` ouvrant apparie : prose Windows, pas un span."""
    src = "les separateurs (/ ou \\\\) selon l'OS."
    out, n = _convert_outside_code(src)
    assert out == src and n == 0


# ---------------------------------------------------------------------------
# Faux-fix fondateur et exclusions (parite avec le detector)
# ---------------------------------------------------------------------------

def test_founding_false_fix_is_intact():
    src = "les separateurs (/ ou \\\\) selon l'OS."
    out, n = _convert_outside_code(src)
    assert out == src and n == 0


def test_code_span_is_intact():
    src = r"La syntaxe `\(x\)` n'est pas rendue."
    out, n = _convert_outside_code(src)
    assert out == src and n == 0


def test_unclosed_backtick_makes_the_rest_literal():
    src = r"`code ouvert \(x\) reste literal"
    out, n = _convert_outside_code(src)
    assert out == src and n == 0


def test_math_guard_contract_and_its_reachability():
    """Contrat de la garde, et mesure de sa portee reelle.

    Le contrat isole : un body portant un backslash litteral suivi d'une
    parenthese fermante est refuse. Mais le motif de PAIRES rend ce cas
    inatteignable -- le groupe non-greedy s'arrete au premier `\\)`, donc aucun
    body extrait d'un texte reel ne peut le contenir. On verifie les deux : le
    contrat, et la non-atteignabilite (qui est ce qui fait de la borne le motif,
    pas l'heuristique).
    """
    assert _looks_like_math("/ ou \\)") is False
    assert _looks_like_math("\\Phi") is True

    # non-atteignabilite : sur tout body REELLEMENT extrait, la garde est vraie
    for text in (
        r"\(a \) b\)",
        r"\(\Phi\)",
        r"\\(\Phi\\)",
        r"\(S = \mathbb{F}_p^n\)",
        r"\(/ ou \\)",
    ):
        for m in _MATH_SPAN_RE.finditer(text):
            assert _looks_like_math(m.group("body")) is True, text


# ---------------------------------------------------------------------------
# Invariant de round-trip
# ---------------------------------------------------------------------------

def test_skeleton_removes_both_delimiter_forms():
    assert _skeleton(r"\\(\Phi\\)") == _skeleton("$\\Phi$")
    assert _skeleton(r"\(x\)") == _skeleton("$x$")


def test_invariant_accepts_a_correct_escaped_conversion():
    _check_invariant(r"\\(\Phi\\)", r"$\Phi$", 2)


def test_invariant_rejects_a_leftover_backslash():
    """Convertir `\\(` en `$` sans consommer le backslash de tete laisse un
    caractere de plus : l'invariant doit refuser d'ecrire."""
    try:
        _check_invariant(r"\\(\Phi\\)", r"\$\Phi\$", 2)
    except SystemExit as exc:
        assert "INVARIANT VIOLE" in str(exc)
    else:
        raise AssertionError("l'invariant aurait du refuser la conversion")


# ---------------------------------------------------------------------------
# Bout-en-bout (process / --apply)
# ---------------------------------------------------------------------------

def test_process_converts_markdown_and_preserves_code_bytes(tmp_path):
    nb = _make_nb(
        [r"On calcule \\(\Phi\\) ici." + "\n", r"Et \(x\) la." + "\n"],
        [r"print('\(\Phi\)')" + "\n"],
    )
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, ensure_ascii=False, indent=1), encoding="utf-8")

    total, _report = process(p, apply=True)
    assert total == 4

    after = json.loads(p.read_text(encoding="utf-8"))
    md = ["".join(c["source"]) for c in after["cells"] if c["cell_type"] == "markdown"]
    code = ["".join(c["source"]) for c in after["cells"] if c["cell_type"] == "code"]
    assert md[0] == r"On calcule $\Phi$ ici." + "\n"
    assert md[1] == r"Et $x$ la." + "\n"
    # la cellule code garde son `\(` litteral (ce n'est pas du markdown)
    assert code == [r"print('\(\Phi\)')" + "\n"]


def test_process_scan_mode_does_not_write(tmp_path):
    nb = _make_nb([r"On calcule \(x\) ici." + "\n"])
    p = tmp_path / "nb.ipynb"
    original = json.dumps(nb, ensure_ascii=False, indent=1)
    p.write_text(original, encoding="utf-8")

    total, _report = process(p, apply=False)
    assert total == 2
    assert p.read_text(encoding="utf-8") == original


def test_process_is_idempotent(tmp_path):
    nb = _make_nb([r"On calcule \\(\Phi\\) ici." + "\n"])
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, ensure_ascii=False, indent=1), encoding="utf-8")

    first, _ = process(p, apply=True)
    second, _ = process(p, apply=True)
    assert first == 2
    assert second == 0, "un second passage ne doit rien trouver"
