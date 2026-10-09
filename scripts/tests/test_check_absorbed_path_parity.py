"""Tests de l'organe de parite de couverture (check_absorbed_path_parity).

Les deux controles d'acceptance (mesures c.361, branche #20166) :
  - POSITIF : registre post-fix -> PARITY_OK ;
  - NEGATIF : registre simule pre-fix -> PARITY_BROKEN avec exactement les
    3 motifs perdus de `pip-leak-guard`.
Ces deux la exigent `git` et un depot, ils vivent dans le rapport de PR. Les
tests ci-dessous couvrent les pieces pures qui fondent le verdict.
"""

from __future__ import annotations

import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

from check_absorbed_path_parity import (  # noqa: E402
    _event_block,
    _normalize,
    _residual_paths,
    _trigger_paths,
    covered_by,
)


def test_normalize_unifie_le_dialecte_double_etoile():
    """`**.ipynb` et `**/*.ipynb` sont le meme motif (cf `fast_lane.py`)."""
    assert _normalize("**.ipynb") == "*.ipynb"
    assert _normalize("**/*.ipynb") == "*.ipynb"
    assert _normalize("Serie/**/*.ipynb") == "Serie/*.ipynb"


def test_covered_by_dialecte():
    """Un declencheur `**.ipynb` est couvert par un registre `**/*.ipynb`."""
    assert covered_by("**.ipynb", ["**/*.ipynb"]) == "**/*.ipynb"


def test_covered_by_sous_arbre():
    """Un glob repo-wide couvre un glob de sous-arbre plus etroit."""
    assert covered_by("MyIA.AI.Notebooks/**/*.ipynb", ["**/*.ipynb"])


def test_covered_by_litteral_absent():
    """Un chemin litteral absent du registre n'est pas couvert.

    C'est la classe mesuree le 2026-10-09 : les detecteurs et outils perdus
    (`audit_pip_install_cells.py`, `pip_leak_delta.py`).
    """
    assert covered_by("scripts/notebook_tools/pip_leak_delta.py",
                      ["**/*.ipynb"]) is None
    assert covered_by("scripts/x.py", []) is None


def test_covered_by_litteral_dans_sous_arbre():
    """Un sous-arbre du registre couvre un fichier litteral qu'il contient."""
    assert covered_by("a/b/c.py", ["a/**"])
    assert covered_by("a/b.py", ["a/**"])


def test_trigger_paths():
    """`paths:` lu d'un bloc ; None = declencheur sans filtre."""
    assert _trigger_paths({"paths": ["x", "y"]}) == ["x", "y"]
    assert _trigger_paths({"paths": "z"}) == ["z"]
    assert _trigger_paths({}) is None
    assert _trigger_paths("pas-un-dict") is None


def test_event_block_lit_on_nu_comme_booleen():
    """PyYAML lit `on:` nu comme True ; les deux formes doivent marcher."""
    data = {True: {"push": {"paths": ["p"]}}}
    assert _event_block(data, "push") == {"paths": ["p"]}
    data2 = {"on": ["push", "pull_request"]}
    assert _event_block(data2, "pull_request") == {}
    assert _event_block(data2, "schedule") is None


def test_residual_paths():
    """Chemins des declencheurs residuels ; None = l'un d'eux est non filtre."""
    assert _residual_paths({"on": {"push": {"paths": ["z"]}}}) == ["z"]
    assert _residual_paths({"on": {"push": {}}}) is None
    assert _residual_paths({"on": {"pull_request": {"paths": ["x"]}}}) == []
