"""Tests du mode PR de scan_lake_notebook_visibility (acceptance 3, #11703).

L'extraction des declarations ajoutees par un diff unifie est une fonction
PURE (names_from_unified_diff) : testable sans git, sur un diff embarque.
Les fixtures vivent ICI, pas sur le disque (lecon fixture-embarquee : un
test lisant un fichier muté in-place par un run vivant race ce run).
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

SPEC = importlib.util.spec_from_file_location(
    "scan_lake_visibility",
    Path(__file__).resolve().parents[1] / "lean" / "scan_lake_notebook_visibility.py",
)
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)

DIFF = """\
diff --git a/MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/Mimo/Core.lean b/MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/Mimo/Core.lean
index 1111111..2222222 100644
--- a/MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/Mimo/Core.lean
+++ b/MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/Mimo/Core.lean
@@ -12,0 +13,2 @@
+theorem mimoThm_new : True := trivial
+def flipAux2 (n : Nat) := n + 1
@@ -40,1 +43,0 @@
-theorem mimoThm_old : True := trivial
diff --git a/MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/Mimo/Core_en.lean b/MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/Mimo/Core_en.lean
index 3333333..4444444 100644
--- a/MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/Mimo/Core_en.lean
+++ b/MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/Mimo/Core_en.lean
@@ -12,0 +13,1 @@
+theorem englishOnlyThm : True := trivial
diff --git a/src/PlainCode.lean b/src/PlainCode.lean
index 5555555..6666666 100644
--- a/src/PlainCode.lean
+++ b/src/PlainCode.lean
@@ -1,0 +2,1 @@
+theorem notALakeThm : True := trivial
diff --git a/.lake/packages/mathlib/Mathlib/Order/Basic.lean b/.lake/packages/mathlib/Mathlib/Order/Basic.lean
index 7777777..8888888 100644
--- a/.lake/packages/mathlib/Mathlib/Order/Basic.lean
+++ b/.lake/packages/mathlib/Mathlib/Order/Basic.lean
@@ -1,0 +2,1 @@
+theorem vendoredThm : True := trivial
"""


def test_added_names_extracted_per_file():
    added = MOD.names_from_unified_diff(DIFF)
    core = "MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/Mimo/Core.lean"
    assert added == {core: {"mimoThm_new", "flipAux2"}}


def test_en_sibling_ignored():
    added = MOD.names_from_unified_diff(DIFF)
    assert not any(p.endswith("_en.lean") for p in added)


def test_non_lake_path_ignored():
    added = MOD.names_from_unified_diff(DIFF)
    assert "src/PlainCode.lean" not in added


def test_vendored_excluded():
    added = MOD.names_from_unified_diff(DIFF)
    assert not any(".lake/packages" in p for p in added)


def test_removed_lines_do_not_count():
    added = MOD.names_from_unified_diff(DIFF)
    core = "MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/Mimo/Core.lean"
    assert "mimoThm_old" not in added[core]


def test_modifiers_and_annotations_still_match():
    local_diff = (
        "--- a/MyIA.AI.Notebooks/GameTheory/game_theory_lean/G.lean\n"
        "+++ b/MyIA.AI.Notebooks/GameTheory/game_theory_lean/G.lean\n"
        "@@ -1,0 +2,2 @@\n"
        "+@[simp] theorem annotatedThm : True := trivial\n"
        "+private def hiddenDef2 := 5\n"
    )
    added = MOD.names_from_unified_diff(local_diff)
    assert added == {
        "MyIA.AI.Notebooks/GameTheory/game_theory_lean/G.lean":
            {"annotatedThm", "hiddenDef2"}
    }


# --- neutralisation des commentaires (issue #21768) --------------------------
#
# Un mot-cle Lean en tete d'une ligne de PROSE (docstring francaise) etait
# lu comme une declaration : `structure existe` dans une docstring, c'est
# une phrase, pas une declaration.

LEAN_DOCSTRING = """\
/-
structure existe, aucune instance n'est fournie : #18611 a mesure qu'une
-/
theorem vrai : True := trivial
"""


def test_prose_line_in_docstring_is_not_a_declaration():
    stripped = MOD.strip_lean_comments(LEAN_DOCSTRING)
    names = [m.group(2) for m in (MOD.DECL_RE.match(l) for l in stripped.splitlines()) if m]
    assert names == ["vrai"]


def test_prose_line_is_matched_without_neutralisation():
    """Controle : sans la neutralisation, la prose EST lue comme une
    declaration -- c'est le defaut que la correction ferme."""
    names = [m.group(2) for m in (MOD.DECL_RE.match(l) for l in LEAN_DOCSTRING.splitlines()) if m]
    assert "existe" in names


def test_nested_block_comment_is_neutralized():
    text = "/- outer /- inner -/ encore -/\ntheorem vrai : True := trivial\n"
    stripped = MOD.strip_lean_comments(text)
    assert "encore" not in stripped
    assert "theorem vrai" in stripped


def test_line_comment_is_neutralized_declaration_survives():
    text = "theorem vrai : True := trivial  -- une note\n"
    stripped = MOD.strip_lean_comments(text)
    assert "une note" not in stripped
    assert MOD.DECL_RE.match(stripped)


def test_double_dash_inside_string_is_not_a_comment():
    text = 'def greeting : String := "-- structure existe"\n'
    stripped = MOD.strip_lean_comments(text)
    assert '"-- structure existe"' in stripped
    assert MOD.DECL_RE.match(stripped)


def test_declaration_on_docstring_closing_line_is_extracted():
    """`-/def foo` : la declaration est sur la ligne qui ferme la
    docstring. Elle etait invisible a l'extracteur (il exigeait le mot-cle
    en debut de ligne) et devient visible -- une declaration REELLE, pas une
    perte."""
    text = "/--\nLa doc.\n-/def fourierSupport : Nat := 0\n"
    stripped = MOD.strip_lean_comments(text)
    names = [m.group(2) for m in (MOD.DECL_RE.match(l) for l in stripped.splitlines()) if m]
    assert names == ["fourierSupport"]


def test_diff_added_prose_line_is_masked_by_head_reader():
    """Le diff est produit avec `--unified=0` : il ne porte aucun contexte,
    la position seule ne dit pas si la ligne est dans une docstring. Le
    lecteur de tete (lignes neutralisees) tranche."""
    path = "MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/Knots/Inv.lean"
    diff = (
        "--- a/%s\n" % path
        + "+++ b/%s\n" % path
        + "@@ -1,0 +2,1 @@\n"
        + "+structure existe, aucune instance n'est fournie\n"
    )

    def reader(p):
        # Contrat du lecteur : les lignes du fichier a la tete, commentaires
        # DEJA neutralises (le lecteur canonique applique strip_lean_comments).
        # La ligne 2 est une docstring -> neutralisee -> plus de declaration.
        assert p == path
        return ["", " " * 55]

    assert MOD.names_from_unified_diff(diff, head_reader=reader) == {}


def test_diff_added_real_declaration_survives_the_head_reader():
    path = "MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/Knots/Inv.lean"
    diff = (
        "--- a/%s\n" % path
        + "+++ b/%s\n" % path
        + "@@ -1,0 +2,1 @@\n"
        + "+theorem nouveauThm : True := trivial\n"
    )

    def reader(p):
        return ["", "theorem nouveauThm : True := trivial"]

    added = MOD.names_from_unified_diff(diff, head_reader=reader)
    assert added == {path: {"nouveauThm"}}


def test_diff_without_head_reader_keeps_previous_behaviour():
    path = "MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/Knots/Inv.lean"
    diff = (
        "--- a/%s\n" % path
        + "+++ b/%s\n" % path
        + "@@ -1,0 +2,1 @@\n"
        + "+structure existe, aucune instance n'est fournie\n"
    )
    added = MOD.names_from_unified_diff(diff)
    assert added == {path: {"existe"}}

