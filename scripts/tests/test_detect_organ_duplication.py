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
    patch = _write(tmp_path, "consumer.diff", """diff --git a/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12e-Value-of-Information-Animat.ipynb b/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12e-Value-of-Information-Animat.ipynb
--- a/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12e-Value-of-Information-Animat.ipynb
+++ b/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12e-Value-of-Information-Animat.ipynb
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


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
