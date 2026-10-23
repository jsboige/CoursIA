#!/usr/bin/env python3
"""Tests hermetiques du detecteur de duplication d'organe (#16776, fille #13564).

Controles d'acceptance encodes :
- Positif retroactif Greffe2 : la forme du patch reel de #13802 (fichier IIT
  ajoutant les 5 symboles STRIPS de Planners) produit 5 COLLISION sans body
  (exit 1 en --check) et 5 EXEMPTED avec le body declaratif (« copie fidele »).
- Negatif : un consommateur pur (ICT-12e, 0 def/class ; PR reelle #13664 =
  CLEAN verifie firsthand) n'importe pas de collision.

Executable deux fois facons :
    py scripts/tests/test_detect_organ_duplication.py
    npx pytest scripts/tests/test_detect_organ_duplication.py
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
DETECTOR = REPO / "scripts" / "audit" / "detect_organ_duplication.py"
INDEX = REPO / "scripts" / "audit" / "organ_api_index.yaml"


def _load_detector():
    spec = importlib.util.spec_from_file_location("detect_organ_duplication", DETECTOR)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _write(tmp_path: Path, name: str, text: str) -> Path:
    p = tmp_path / name
    p.write_text(text, encoding="utf-8", newline="\n")
    return p


GREFFE2_PATCH = """diff --git a/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Greffe2-EspaceAtteignable.ipynb b/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Greffe2-EspaceAtteignable.ipynb
new file mode 100644
--- /dev/null
+++ b/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Greffe2-EspaceAtteignable.ipynb
@@ -0,0 +1,9 @@
+{
+ "cells": [
+  {
+   "cell_type": "code",
+   "source": [
+    "class Operateur:\\n",
+    "def ops_de_base():\\n",
+    "def ops_avec_radeau():\\n",
+    "def prop(etat):\\n",
+    "def successeurs(etat, ops):\\n"
+   ]
+  }
+ ]
+}
"""

BODY_DECLARED_CANONIQUE = (
    "## Copie\n\nCopie pédagogique déclarée, motif : montrer comment marche "
    "le moteur STRIPS de Planners-5c en 30 lignes lisibles."
)
BODY_DECLARED_FIDELE = (
    "Interdit respecté : le moteur STRIPS est la **copie fidèle** de "
    "l'instrument de mesure de Planners-5c."
)
BODY_UNRELATED = "Ajout d'un notebook ICT sur l'atteignabilité. See #13568."


def test_index_loads_measured_series():
    mod = _load_detector()
    owners, symbol_owners = mod.load_index(INDEX)
    assert len(owners) >= 6, "acceptance: >= 6 series mesurees"
    for sym in ("Operateur", "ops_de_base", "ops_avec_radeau", "prop", "successeurs"):
        assert symbol_owners[sym] == "Planners"


def test_greffe2_flagged_without_body(tmp_path, capsys):
    """Controle positif retroactif : sans declaration, les 5 symboles STRIPS collisionnent."""
    mod = _load_detector()
    patch = _write(tmp_path, "greffe2.diff", GREFFE2_PATCH)
    rc = mod.main(["--patch", str(patch), "--index", str(INDEX), "--check"])
    out = capsys.readouterr().out
    assert rc == 1
    assert out.count("COLLISION") == 5
    for sym in ("Operateur", "ops_de_base", "ops_avec_radeau", "prop", "successeurs"):
        assert f"({sym})" in out
    assert "-> Planners" in out
    assert "~IIT" in out, "label de serie demandeuse hors index"
    assert "BLOCKED" in out


def test_greffe2_whitened_by_canonical_declaration(tmp_path, capsys):
    mod = _load_detector()
    patch = _write(tmp_path, "greffe2.diff", GREFFE2_PATCH)
    body = _write(tmp_path, "body.md", BODY_DECLARED_CANONIQUE)
    rc = mod.main(["--patch", str(patch), "--body-file", str(body),
                   "--index", str(INDEX), "--check"])
    out = capsys.readouterr().out
    assert rc == 0
    assert out.count("EXEMPTED") == 6  # 5 lignes + le resume
    assert "non declaree(s), 0" in out or "0 non declaree" in out


def test_greffe2_whitened_by_retroactive_fidele(tmp_path, capsys):
    """Le body reel de #13802 (« copie fidèle ») blanchit aussi."""
    mod = _load_detector()
    patch = _write(tmp_path, "greffe2.diff", GREFFE2_PATCH)
    body = _write(tmp_path, "body.md", BODY_DECLARED_FIDELE)
    rc = mod.main(["--patch", str(patch), "--body-file", str(body),
                   "--index", str(INDEX), "--check"])
    assert rc == 0
    assert "EXEMPTED" in capsys.readouterr().out


def test_unrelated_body_still_blocks(tmp_path, capsys):
    mod = _load_detector()
    patch = _write(tmp_path, "greffe2.diff", GREFFE2_PATCH)
    body = _write(tmp_path, "body.md", BODY_UNRELATED)
    rc = mod.main(["--patch", str(patch), "--body-file", str(body),
                   "--index", str(INDEX), "--check"])
    assert rc == 1


def test_negative_consumer_no_collision(tmp_path, capsys):
    """Controle negatif : un consommateur (ICT-12e, PR #13664) ajoute des
    definitions qui ne collisionnent avec aucun organe de l'index."""
    mod = _load_detector()
    patch = _write(tmp_path, "consumer.diff", """diff --git a/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12e-Value-of-Information-Animat-Python.ipynb b/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12e-Value-of-Information-Animat-Python.ipynb
--- a/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12e-Value-of-Information-Animat-Python.ipynb
+++ b/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12e-Value-of-Information-Animat-Python.ipynb
@@ -1,3 +1,5 @@
+import pymc as pm
+import numpy as np
+def animat_policy(evpi, evsi):
+    return evsi / evpi
""")
    rc = mod.main(["--patch", str(patch), "--index", str(INDEX), "--check"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "CLEAN" in out and "0 collision" in out


def test_owner_series_does_not_collide_with_itself(tmp_path, capsys):
    """La serie proprietaire qui enrichit son propre organe ne collisionne pas."""
    mod = _load_detector()
    patch = _write(tmp_path, "owner.diff", """diff --git a/MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/planners_core.py b/MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/planners_core.py
--- a/MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/planners_core.py
+++ b/MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/planners_core.py
@@ -1,2 +1,4 @@
+def successeurs(etat, ops):
+    pass
+class Operateur:
+    pass
""")
    rc = mod.main(["--patch", str(patch), "--index", str(INDEX), "--check"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "CLEAN" in out and "0 collision" in out


def test_generic_symbol_outside_index_is_ignored(tmp_path, capsys):
    """Un nom generique absent de l'index (curation) ne compte pas."""
    mod = _load_detector()
    patch = _write(tmp_path, "generic.diff", """diff --git a/MyIA.AI.Notebooks/GenAI/Texte/essai.py b/MyIA.AI.Notebooks/GenAI/Texte/essai.py
--- a/MyIA.AI.Notebooks/GenAI/Texte/essai.py
+++ b/MyIA.AI.Notebooks/GenAI/Texte/essai.py
@@ -1,1 +1,2 @@
+def solve(problem):
+    pass
""")
    rc = mod.main(["--patch", str(patch), "--index", str(INDEX), "--check"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "CLEAN" in out


def test_py_file_and_notebook_json_both_scanned(tmp_path, capsys):
    """Une reimplementation .py (pas notebook) est aussi attrapee."""
    mod = _load_detector()
    patch = _write(tmp_path, "py.diff", """diff --git a/MyIA.AI.Notebooks/GameTheory/local_strips.py b/MyIA.AI.Notebooks/GameTheory/local_strips.py
--- a/MyIA.AI.Notebooks/GameTheory/local_strips.py
+++ b/MyIA.AI.Notebooks/GameTheory/local_strips.py
@@ -0,0 +1,2 @@
+def h_max(etat, buts):
+    pass
""")
    rc = mod.main(["--patch", str(patch), "--index", str(INDEX), "--check"])
    out = capsys.readouterr().out
    assert rc == 1
    assert "COLLISION ~GameTheory" in out and "(h_max)" in out


def test_accent_tolerant_declaration_forms():
    mod = _load_detector()
    assert mod.is_declared("copie pédagogique déclarée, motif : X")
    assert mod.is_declared("copie pedagogique declaree")
    assert mod.is_declared("la copie fidèle de Planners-5c")
    assert mod.is_declared("copie fidele")
    assert not mod.is_declared("on a copié le style")
    assert not mod.is_declared("")


# --- Lean (#20210) : index derive d'un faux arbre, citations, jumeaux _en ---

HECKE_PROBE = "MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean/Hecke/Probe.lean"
MATH_FR = "MyIA.AI.Notebooks/ML/learning_theory_lean/MathUniverse.lean"
MATH_EN = "MyIA.AI.Notebooks/ML/learning_theory_lean/MathUniverse_en.lean"
TEGMARK_AUT = "MyIA.AI.Notebooks/SymbolicAI/Lean/tegmark_muh_lean/MUH/Aut.lean"
TEGMARK_LAKE = "MyIA.AI.Notebooks/SymbolicAI/Lean/tegmark_muh_lean/lakefile.lean"
SEARCH_LAKE = "MyIA.AI.Notebooks/Search/search_lean/lakefile.lean"
PROBE = "MyIA.AI.Notebooks/Search/search_lean/Probe.lean"

# Faux arbre de lakes : meme forme que le depot (tegmark_muh_lean cite R16 Annexe A,
# learning_theory_lean aussi, hecke_lean est un consommateur sans rapport).
LEAN_TREE = {
    TEGMARK_LAKE: "-- lake tegmark (fixture)\n",
    TEGMARK_AUT: (
        "/-! # Aut(S) est un groupe (Tegmark R16 Annexe A §1 in fine)\n-/\n"
        "structure IsAutomorphism (S : Nat) where\n  ok : True\n\n"
        "def sheffer (x : Nat) : Nat := x\n"
    ),
    "MyIA.AI.Notebooks/ML/learning_theory_lean/lakefile.lean": "-- lake learning (fixture)\n",
    MATH_FR: (
        "/-!\n# MathUniverse (Annexe A, R16 Tegmark)\n\n"
        "Formalisation Lean de l'**Annexe A** de R16 (fixture).\n-/\n"
        "structure FinRelStruct (α : Type) where\n  rel : Nat\n\n"
        "def EquivStruct (S : FinRelStruct) : Prop := True\n"
    ),
    MATH_EN: (
        "/-!\n# MathUniverse (Appendix A, R16 Tegmark)\n\n"
        "Lean formalization of **Appendix A** of R16 (fixture).\n-/\n"
        "structure FinRelStruct (α : Type) where\n  rel : Nat\n\n"
        "def EquivStruct (S : FinRelStruct) : Prop := True\n"
    ),
    "MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean/lakefile.lean": "-- lake hecke (fixture)\n",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean/Hecke/Base.lean": "def heckeBaseUnique := 1\n",
}

# Extrait fidele du fichier MathUniverse.lean ajoute par #20111 : en-tete de
# citation (lignes 1-8 du head) et declarations Preserves/aut (lignes 66-86).
MATHUNIVERSE_20111_EXCERPT = [
    "import Mathlib",
    "",
    "/-!",
    "# MathUniverse — structures mathématiques finies (Annexe A, R16 Tegmark)",
    "",
    "Formalisation Lean de l'**Annexe A** de R16 — *The Mathematical Universe*",
    "(Tegmark, [arXiv:0704.0646](https://arxiv.org/abs/0704.0646), §A.1-A.2) —",
    "-/",
    "namespace MathUniverse",
    "",
    "structure FinRelStruct (α : Type*) [Fintype α] {n : ℕ} (σ : Fin n → ℕ) where",
    "def Preserves (S : FinRelStruct α σ) (f : α → α) : Prop :=",
    "  ∀ i (t : Fin (σ i) → α), S.rel i t ↔ S.rel i (f ∘ t)",
    "def aut (S : FinRelStruct α σ) : Subgroup (Equiv.Perm α) where",
    "  carrier := {f | Preserves S f}",
]


def _write_lean_tree(base: Path) -> Path:
    for rel, text in LEAN_TREE.items():
        p = base / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8", newline="\n")
    return base


def _lean_tree(tmp_path: Path) -> Path:
    return _write_lean_tree(tmp_path / "lean_tree")


def _lean_new_file_patch(path: str, lines) -> str:
    return (
        f"diff --git a/{path} b/{path}\nnew file mode 100644\n--- /dev/null\n"
        f"+++ b/{path}\n@@ -0,0 +1,{len(lines)} @@\n"
        + "".join(f"+{line}\n" for line in lines)
    )


def _run(mod, tmp_path, name, patch_text, capsys):
    patch = _write(tmp_path, name, patch_text)
    rc = mod.main(["--patch", str(patch), "--index", str(INDEX), "--check",
                   "--lean-root", str(_lean_tree(tmp_path))])
    return rc, capsys.readouterr().out


def test_lean_index_derived_from_fixture_tree(tmp_path):
    mod = _load_detector()
    lakes = mod.build_lean_index(mod.lean_files_from_tree(_lean_tree(tmp_path)))
    owners, symbol_owners, source_owners = mod.lean_maps(lakes)
    assert owners["tegmark_muh_lean"] == "MyIA.AI.Notebooks/SymbolicAI/Lean/tegmark_muh_lean"
    assert symbol_owners["IsAutomorphism"] == "tegmark_muh_lean"
    assert symbol_owners["sheffer"] == "tegmark_muh_lean"
    assert symbol_owners["FinRelStruct"] == "learning_theory_lean"
    assert set(source_owners["R16 Annexe A"]) == {"tegmark_muh_lean", "learning_theory_lean"}


def test_lean_positive_control_20111_source_citation(tmp_path, capsys):
    """Controle positif #20111 : MathUniverse cite « R16 Annexe A » que
    tegmark_muh_lean cite deja. Sans declaration : bloque, une seule ligne
    (la citation est repetee dans l'en-tete, la collision est dedoublonnee)."""
    mod = _load_detector()
    rc, out = _run(mod, tmp_path, "m.diff",
                   _lean_new_file_patch(MATH_FR, MATHUNIVERSE_20111_EXCERPT), capsys)
    assert rc == 1
    assert out.count("COLLISION") == 1
    assert f"COLLISION learning_theory_lean ({MATH_FR}) -> tegmark_muh_lean (source R16 Annexe A)" in out
    assert "BLOCKED" in out

    body = _write(tmp_path, "body.md", BODY_DECLARED_CANONIQUE)
    rc = mod.main(["--patch", str(tmp_path / "m.diff"), "--body-file", str(body),
                   "--index", str(INDEX), "--check", "--lean-root", str(_lean_tree(tmp_path))])
    assert rc == 0
    assert "EXEMPTED" in capsys.readouterr().out


def test_lean_positive_control_20111_real_tree(tmp_path, capsys):
    """Meme controle contre l'arbre reel de ce depot, sans fixture : tegmark_muh_lean
    est sur origin/main. Lent (~3 s) : l'index est derive de tout l'arbre."""
    mod = _load_detector()
    patch = _write(tmp_path, "real.diff", _lean_new_file_patch(MATH_FR, MATHUNIVERSE_20111_EXCERPT))
    rc = mod.main(["--patch", str(patch), "--index", str(INDEX), "--check"])
    out = capsys.readouterr().out
    assert rc == 1
    assert "-> tegmark_muh_lean (source R16 Annexe A)" in out


def test_lean_name_collision_on_organ_symbol(tmp_path, capsys):
    mod = _load_detector()
    rc, out = _run(mod, tmp_path, "n.diff",
                   _lean_new_file_patch(HECKE_PROBE, ["def IsAutomorphism (x : Nat) : Nat := x"]),
                   capsys)
    assert rc == 1
    assert f"COLLISION hecke_lean ({HECKE_PROBE}) -> tegmark_muh_lean (IsAutomorphism)" in out


def test_lean_negative_no_homonym_is_clean(tmp_path, capsys):
    mod = _load_detector()
    rc, out = _run(mod, tmp_path, "c.diff",
                   _lean_new_file_patch(HECKE_PROBE, ["def zetaProbeUniqueName (n : Nat) : Nat := n"]),
                   capsys)
    assert rc == 0
    assert "CLEAN" in out and "0 collision" in out


def test_lean_negative_comments_are_not_declarations(tmp_path, capsys):
    """Commentaire `--`, docstring et bloc `/- -/` contenant un nom de l'index : rien."""
    mod = _load_detector()
    lines = [
        "-- structure IsAutomorphism (rappel de lecture)",
        "/-- Rappel : structure IsAutomorphism et sheffer, en prose. -/",
        "/-",
        "theorem sheffer : bloc de commentaire",
        "-/",
        "def probeOkUnique := 1",
    ]
    rc, out = _run(mod, tmp_path, "k.diff", _lean_new_file_patch(HECKE_PROBE, lines), capsys)
    assert rc == 0
    assert "CLEAN" in out


def test_lean_negative_twin_en_same_lake_not_flagged(tmp_path, capsys):
    """Jumeau _en du meme lake : meme serie proprietaire, aucune collision."""
    mod = _load_detector()
    lines = [
        "structure FinRelStruct (α : Type) where",
        "def EquivStruct (S : FinRelStruct) : Prop := True",
    ]
    rc, out = _run(mod, tmp_path, "t.diff", _lean_new_file_patch(MATH_EN, lines), capsys)
    assert rc == 0
    assert "CLEAN" in out and "0 collision" in out


def test_lean_theorem_and_instance_are_scanned(tmp_path, capsys):
    """Le scan couvre theorem/lemma/instance (non indexes) : un theorem au nom d'un organe collisionne."""
    mod = _load_detector()
    rc, out = _run(mod, tmp_path, "th.diff",
                   _lean_new_file_patch(HECKE_PROBE, ["theorem sheffer (x : Nat) : x = x := rfl"]),
                   capsys)
    assert rc == 1
    assert "-> tegmark_muh_lean (sheffer)" in out


def test_lean_citation_alias_appendix_multi_owner(tmp_path, capsys):
    """« Appendix A of R16 » (jumeau anglais) = meme cle ; deux lakes la citent."""
    mod = _load_detector()
    lines = ["/-- Appendix A of R16 : probe. -/", "def probeAppendixUnique := 1"]
    rc, out = _run(mod, tmp_path, "ap.diff", _lean_new_file_patch(HECKE_PROBE, lines), capsys)
    assert rc == 1
    assert out.count("COLLISION") == 2
    assert "-> tegmark_muh_lean (source R16 Annexe A)" in out
    assert "-> learning_theory_lean (source R16 Annexe A)" in out


def test_lean_citation_needs_article_and_annex_on_same_line(tmp_path, capsys):
    mod = _load_detector()
    lines = ["Source PDF : R16 `85712871`", "-- voir Annexe A de la note ci-dessous"]
    rc, out = _run(mod, tmp_path, "cit.diff", _lean_new_file_patch(HECKE_PROBE, lines), capsys)
    assert rc == 0
    assert "CLEAN" in out


def test_lean_symbols_do_not_leak_into_python(tmp_path, capsys):
    """Le verdict Python est inchange : un symbole Lean n'est pas un symbole Python."""
    mod = _load_detector()
    patch = """diff --git a/MyIA.AI.Notebooks/GameTheory/local_probe.py b/MyIA.AI.Notebooks/GameTheory/local_probe.py
--- a/MyIA.AI.Notebooks/GameTheory/local_probe.py
+++ b/MyIA.AI.Notebooks/GameTheory/local_probe.py
@@ -0,0 +1,2 @@
+def IsAutomorphism(x):
+    return x
"""
    rc, out = _run(mod, tmp_path, "py2.diff", patch, capsys)
    assert rc == 0
    assert "CLEAN" in out


def test_python_only_diff_does_not_build_lean_index(tmp_path, capsys):
    """Pas de fichier .lean dans le diff : l'index Lean n'est pas construit (0 lake)."""
    mod = _load_detector()
    patch = _write(tmp_path, "py3.diff", """diff --git a/MyIA.AI.Notebooks/GenAI/Texte/essai.py b/MyIA.AI.Notebooks/GenAI/Texte/essai.py
--- a/MyIA.AI.Notebooks/GenAI/Texte/essai.py
+++ b/MyIA.AI.Notebooks/GenAI/Texte/essai.py
@@ -0,0 +1,1 @@
+def solve(problem):
""")
    rc = mod.main(["--patch", str(patch), "--index", str(INDEX), "--check",
                   "--lean-root", str(tmp_path / "absent")])
    out = capsys.readouterr().out
    assert rc == 0
    assert "0 lakes Lean" in out


def test_lean_git_mode_masks_whole_file(tmp_path, capsys):
    """En mode git, un ajout dans une docstring deja ouverte plus haut reste un
    commentaire : seule la vraie declaration (ligne suivante) collisionne. L'index
    est derive de la base (HEAD~1), ou tegmark definit sheffer et IsAutomorphism."""
    mod = _load_detector()
    repo = tmp_path / "repo"
    repo.mkdir()
    git = ["git", "-C", str(repo), "-c", "user.email=t@example.invalid",
           "-c", "user.name=test", "-c", "commit.gpgsign=false"]
    subprocess.run(["git", "init", "-q", str(repo)], check=True)
    base = {
        TEGMARK_LAKE: LEAN_TREE[TEGMARK_LAKE],
        TEGMARK_AUT: LEAN_TREE[TEGMARK_AUT],
        SEARCH_LAKE: "-- lake search (fixture)\n",
        PROBE: "/-!\n# Sonde\nligne initiale\n-/\ndef probeBase := 1\n",
    }
    for rel, text in base.items():
        (repo / rel).parent.mkdir(parents=True, exist_ok=True)
        (repo / rel).write_text(text, encoding="utf-8", newline="\n")
    subprocess.run([*git, "add", "MyIA.AI.Notebooks"], check=True)
    subprocess.run([*git, "commit", "-q", "-m", "base"], check=True)
    # Prose ajoutee DANS la docstring (nom de l'index) + vraie declaration apres.
    # newline="\n" est obligatoire : sans lui, Path.write_text traduit en CRLF sur
    # Windows, le fichier de tete differe alors de la base sur TOUTES ses lignes,
    # et le diff devient un remplacement fichier entier dont les hunks portent
    # l'ouverture de docstring -- la limite du mode --patch n'est plus exercee.
    (repo / PROBE).write_text(
        "/-!\n# Sonde\nligne initiale\nstructure IsAutomorphism en prose\n-/\n"
        "def probeBase := 1\ndef sheffer (x : Nat) : Nat := x\n",
        encoding="utf-8", newline="\n")
    subprocess.run([*git, "add", PROBE], check=True)
    subprocess.run([*git, "commit", "-q", "-m", "head"], check=True)
    rc = mod.main(["--base", "HEAD~1", "--head", "HEAD", "--cwd", str(repo),
                   "--index", str(INDEX), "--check"])
    out = capsys.readouterr().out
    assert rc == 1
    assert out.count("COLLISION") == 1
    assert "-> tegmark_muh_lean (sheffer)" in out
    assert "(IsAutomorphism)" not in out, "la prose de la docstring ne doit pas collisionner"

    # Limite documentee du mode --patch : le hunk n'a pas l'ouverture de la
    # docstring, la prose est lue comme du code (faux positif connu).
    diff = subprocess.run(["git", "-C", str(repo), "diff", "HEAD~1", "HEAD", "--unified=0"],
                          capture_output=True, text=True,
                          encoding="utf-8", errors="replace", check=True).stdout
    # Garde : le diff doit rester minimal (2 hunks, 2 lignes ajoutees). Un hunk
    # unique couvrant tout le fichier signifie que les deux ecritures different
    # par leurs fins de ligne (CRLF vs LF) et que le mode --patch voit alors la
    # docstring ouverte : l'assertion suivante ne testerait plus sa limite.
    hunk_headers = [line for line in diff.splitlines() if line.startswith("@@")]
    added = [line for line in diff.splitlines() if line.startswith("+")
             and not line.startswith("+++")]
    assert len(hunk_headers) == 2, f"diff non minimal (hunks) :\n{diff}"
    assert len(added) == 2, f"diff non minimal (lignes ajoutees) :\n{diff}"
    patch = _write(tmp_path, "hunk.diff", diff)
    mod.main(["--patch", str(patch), "--index", str(INDEX), "--lean-root", str(_lean_tree(tmp_path))])
    assert "(IsAutomorphism)" in capsys.readouterr().out


def test_lean_source_git_equals_tree(tmp_path):
    """La source git (git archive) et la source fichier donnent le meme index."""
    mod = _load_detector()
    repo = tmp_path / "repo"
    _write_lean_tree(repo)
    git = ["git", "-C", str(repo), "-c", "user.email=t@example.invalid",
           "-c", "user.name=test", "-c", "commit.gpgsign=false"]
    subprocess.run(["git", "init", "-q", str(repo)], check=True)
    subprocess.run([*git, "add", "MyIA.AI.Notebooks"], check=True)
    subprocess.run([*git, "commit", "-q", "-m", "tree"], check=True)
    from_git = mod.build_lean_index(mod.lean_files_from_git("HEAD", repo))
    from_tree = mod.build_lean_index(mod.lean_files_from_tree(repo))
    assert from_git == from_tree
    assert from_git["tegmark_muh_lean"]["symbols"], "l'index git n'est pas vide"


def test_lean_twin_pair_reports_once(tmp_path, capsys):
    """FR + jumeau _en citant la meme source : une seule collision (l'unite X/X_en)."""
    mod = _load_detector()
    cite = "-- Formalisation Lean de l'**Annexe A** de R16 — probe."
    patch = _lean_new_file_patch(MATH_FR, [cite]) + _lean_new_file_patch(MATH_EN, [cite])
    rc, out = _run(mod, tmp_path, "pair.diff", patch, capsys)
    assert rc == 1
    assert out.count("COLLISION") == 1
    assert f"COLLISION learning_theory_lean ({MATH_FR})" in out


def test_lean_lakefile_prose_is_not_scanned(tmp_path, capsys):
    """Le lakefile decrit les modules (configuration), il ne porte pas de semantique."""
    mod = _load_detector()
    cfg = "MyIA.AI.Notebooks/ML/learning_theory_lean/lakefile.lean"
    rc, out = _run(mod, tmp_path, "cfg.diff",
                   _lean_new_file_patch(cfg, ["/-- Annexe A de R16 — module registry. -/"]), capsys)
    assert rc == 0
    assert "CLEAN" in out


def test_lean_index_skips_external_and_ignores_lakefile_prose(tmp_path):
    """Lakes *_peters et .lake exclus de l'arbre ; lakefile.* jamais scanne comme source."""
    mod = _load_detector()
    root = _lean_tree(tmp_path)
    ext = root / "MyIA.AI.Notebooks" / "GameTheory" / "social_choice_lean_peters"
    ext.mkdir(parents=True)
    (ext / "lakefile.lean").write_text("-- externe\n", encoding="utf-8")
    (ext / "P.lean").write_text("def Hidden1 := 1\n", encoding="utf-8")
    rels = [rel for rel, _ in mod.lean_files_from_tree(root)]
    assert not any("peters" in rel for rel in rels)
    lakes = mod.build_lean_index(mod.lean_files_from_tree(root))
    assert not any("peters" in name for name in lakes)


def test_lean_generator_pure_fixture(tmp_path):
    """Derivation pure : ambigu exclu, court exclu, citations unies (sans E/S)."""
    mod = _load_detector()
    files = [
        ("MyIA.AI.Notebooks/Lake_a/lakefile.lean", "-- lake\n"),
        ("MyIA.AI.Notebooks/Lake_a/A.lean",
         "/-! R7 Annexe B -/\nstructure Gadget where\n  x : Nat\ndef abc := 1\n"),
        ("MyIA.AI.Notebooks/Lake_b/lakefile.lean", "-- lake\n"),
        ("MyIA.AI.Notebooks/Lake_b/B.lean",
         "-- R7 Annexe B\ndef Gadget := 2\ndef uniqueWidget := 3\n"),
    ]
    index = mod.build_lean_index(files)
    assert set(index) == {"Lake_a", "Lake_b"}
    assert index["Lake_a"]["symbols"] == [], "Gadget ambigu (2 lakes), abc trop court"
    assert index["Lake_b"]["symbols"] == ["uniqueWidget"]
    assert index["Lake_a"]["sources"] == index["Lake_b"]["sources"] == ["R7 Annexe B"]
    assert index["Lake_a"]["owner_path"] == "MyIA.AI.Notebooks/Lake_a"


def test_emit_lean_index_roundtrip(tmp_path, capsys):
    """--emit-lean-index (inspection, stdout) : le rendu YAML se relit a l'identique."""
    mod = _load_detector()
    import yaml
    root = _lean_tree(tmp_path)
    assert mod.main(["--emit-lean-index", "--lean-root", str(root)]) == 0
    out = capsys.readouterr().out
    assert yaml.safe_load(out) == {"lean_series": mod.build_lean_index(mod.lean_files_from_tree(root))}


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
