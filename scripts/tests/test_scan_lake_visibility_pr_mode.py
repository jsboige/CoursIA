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
