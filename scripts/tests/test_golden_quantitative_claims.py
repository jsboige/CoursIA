"""Golden set — validation du scanner check_prose_quantitative_claims.py (#9434).

Le golden set (``golden_quantitative_claims.json``) est un ensemble de snippets de
prose annotes a la main avec la ground-truth humaine (classe + expect match/nomatch).
Ce test compare la ground truth au **comportement reel du scanner** en appelant la
**meme fonction** (``_findings_in_text``) que le scanner utilise en production.

Les cas ou le scanner actuel diverge de la ground truth (angles-mort connus) sont
marques ``xfail`` avec un rationale documente. Un ``xfail`` n'est PAS un bug du test :
c'est un angle-mort inventorie. Si le scanner est ameliore et matche enfin le cas,
l'``xfail`` devient un echec (signaling) -> il faut alors le retirer.

La logique seed (un carnet seme = reproductible = legitime) est validee separement
via des fixtures mini-notebooks (on ne peut pas la tester au niveau texte seul).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# --- Import du scanner (meme fonction que la production) ------------------- #
HERE = Path(__file__).resolve().parent
NOTEBOOK_TOOLS = HERE.parent / "notebook_tools"
sys.path.insert(0, str(NOTEBOOK_TOOLS))
from check_prose_quantitative_claims import _findings_in_text, _notebook_is_seeded  # noqa: E402

GOLDEN = HERE / "golden_quantitative_claims.json"


# --- Angles-mort connus (scanner diverge de la ground truth) --------------- #
# Ces cas DOIVENT matcher humainement mais le scanner actuel les rate.
# Documentes pour prevenir qu'on les oublie ; xfail -> xpass signaling si fixe.
XFAIL_KNOWN_GAPS: dict[str, str] = {
    "m7": "ANGLE-MORT machine: '30s' sans \\ss (espace avant 's') n'est pas matche",
    "s6": "ANGLE-MORT stochastic: 42.5 a 1 decimale, STOCHASTIC_NUM exige >=2",
    "s8": "ANGLE-MORT stochastic: 'tentatives' hors KW + 1 decimale (App-7-Wordle)",
    # "t1" (2.78e24x notation scientifique + x) retire : FIXE par #9564
    # (STRUCTURAL_RE etendu a e\d+x?) — les deux PRs #9560/#9564 etaient
    # in-flight simultanement, chacune verte isolement, rouges combinees.
}


def _load_cases() -> list[dict]:
    data = json.loads(GOLDEN.read_text(encoding="utf-8"))
    return data["cases"]


CASES = _load_cases()


# =========================================================================== #
#  1. Cohherence du golden set lui-meme                                       #
# =========================================================================== #


def test_golden_set_has_expected_size():
    """Le golden set cible >= 30 cas (mandat issue #9434 option alpha)."""
    assert len(CASES) >= 30, f"Golden set trop petit: {len(CASES)} cas (< 30)"


def test_golden_set_ids_unique():
    ids = [c["id"] for c in CASES]
    assert len(ids) == len(set(ids)), "IDs dupliques dans le golden set"


def test_golden_set_covers_all_four_classes():
    classes = {c["cls"] for c in CASES}
    assert classes == {"machine", "env", "stochastic", "structural"}, (
        f"Classes couvertes: {classes}"
    )


def test_golden_set_has_tp_and_tn_per_class():
    """Chaque classe doit avoir au moins un cas qui matche (TP) et un TN."""
    for cls in ("machine", "env", "stochastic", "structural"):
        has_match = any(c["cls"] == cls and c["expect"] == "match" for c in CASES)
        has_nomatch = any(c["cls"] == cls and c["expect"] == "nomatch" for c in CASES)
        assert has_match, f"Classe {cls}: aucun cas expect=match (TP manquant)"
        assert has_nomatch, f"Classe {cls}: aucun cas expect=nomatch (TN manquant)"


def test_xfail_known_gaps_reference_real_cases():
    """Chaque xfail declare pointe vers un cas reel du golden set."""
    ids = {c["id"] for c in CASES}
    for xfail_id in XFAIL_KNOWN_GAPS:
        assert xfail_id in ids, f"XFAIL_KNOWN_GAPS reference un id absent: {xfail_id}"


# =========================================================================== #
#  2. Validation cas par cas (le coeur du golden set)                         #
# =========================================================================== #


def _scanner_matches(text: str, cls: str) -> bool:
    """Le scanner reel trouve-t-il un finding de `cls` dans `text`?"""
    findings = _findings_in_text(text, "golden-test", {cls})
    return len(findings) > 0


@pytest.mark.parametrize(
    "case",
    CASES,
    ids=[c["id"] for c in CASES],
)
def test_scanner_matches_ground_truth(case):
    """Pour chaque cas du golden set, le scanner doit respecter la ground truth.

    Les angles-mort connus (XFAIL_KNOWN_GAPS) sont marques xfail : le scanner
    actuel diverge, c'est inventorie. Si le scanner est ameliore, l'xfail echoue
    (xpass strict) -> il faut retirer l'entree de XFAIL_KNOWN_GAPS.
    """
    case_id = case["id"]
    expected_match = case["expect"] == "match"
    actual_match = _scanner_matches(case["text"], case["cls"])

    if case_id in XFAIL_KNOWN_GAPS:
        # Angle-mort documente : on s'attend a ce que le scanner rate le cas.
        pytest.xfail(XFAIL_KNOWN_GAPS[case_id])

    assert actual_match == expected_match, (
        f"[{case_id}] cls={case['cls']} expect={case['expect']} "
        f"actual_match={actual_match} | text={case['text']!r} | note={case['note']}"
    )


# =========================================================================== #
#  3. Logique seed (fixtures mini-notebooks)                                  #
#  On ne peut pas tester au niveau texte: il faut un carnet.                  #
# =========================================================================== #


def _write_mini_notebook(path: Path, code_source: str) -> None:
    """Cree un mini-notebook (1 cellule code) pour tester _notebook_is_seeded."""
    nb = {
        "cells": [
            {"cell_type": "code", "execution_count": None,
             "metadata": {}, "outputs": [],
             "source": code_source},
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")


def test_seeded_numpy_notebook_is_legitimate(tmp_path):
    """Un carnet avec np.random.seed(...) est seme -> reproductible -> legitime."""
    nb = tmp_path / "seeded_numpy.ipynb"
    _write_mini_notebook(nb, "import numpy as np\nnp.random.seed(42)\nx = np.random.rand(5)")
    assert _notebook_is_seeded(nb) is True


def test_seeded_torch_notebook_is_legitimate(tmp_path):
    """torch.manual_seed(...) rend aussi le carnet reproductible."""
    nb = tmp_path / "seeded_torch.ipynb"
    _write_mini_notebook(nb, "import torch\ntorch.manual_seed(0)\n_ = torch.rand(3)")
    assert _notebook_is_seeded(nb) is True


def test_seeded_random_state_sklearn_is_legitimate(tmp_path):
    """random_state=42 (sklearn) est un seed -> legitime."""
    nb = tmp_path / "seeded_sklearn.ipynb"
    _write_mini_notebook(nb, "from sklearn.cluster import KMeans\nm = KMeans(random_state=42)")
    assert _notebook_is_seeded(nb) is True


def test_unseeded_notebook_is_not_legitimate(tmp_path):
    """Un carnet sans seed -> stochastic non-reproductible -> a signaler."""
    nb = tmp_path / "unseeded.ipynb"
    _write_mini_notebook(nb, "import numpy as np\nx = np.random.rand(5)  # pas de seed")
    assert _notebook_is_seeded(nb) is False


def test_seeded_logic_independence_from_text_level():
    """La logique seed est ORTHOGONALE a la detection texte: un carnet non-seede
    avec 'fitness 41.71' en prose DOIT etre flagge, un carnet seede ne l'est pas.
    Ce test documente la separation des deux niveaux (cf _meta.note_stochastic)."""
    # Au niveau texte, 'fitness 41.71' est detecte (cooccurrence KW+NUM)
    assert _scanner_matches("fitness moyen de 41.71", "stochastic") is True
    # Mais c'est la logique seed du CARNET qui decide si c'est legitime —
    # ce n'est pas testable au niveau texte (cf fixtures ci-dessus).


# =========================================================================== #
#  4. Metriques agregees (precision/recall par classe)                        #
# =========================================================================== #


def _confusion_for_class(cls: str) -> dict:
    """Matrice de confusion du scanner sur les cas non-xfail d'une classe."""
    tp = tn = fp = fn = 0
    for c in CASES:
        if c["cls"] != cls or c["id"] in XFAIL_KNOWN_GAPS:
            continue
        actual = _scanner_matches(c["text"], cls)
        expected = c["expect"] == "match"
        if expected and actual:
            tp += 1
        elif expected and not actual:
            fn += 1
        elif not expected and actual:
            fp += 1
        else:
            tn += 1
    return {"tp": tp, "tn": tn, "fp": fp, "fn": fn}


def test_scanner_precision_recall_per_class():
    """Sur les cas non-xfail, le scanner doit etre parfait (precision=recall=1).

    C'est le contrat du golden set: les cas non-xfail sont des frontieres ou le
    scanner est cense etre exact. Toute deviation ici = regression a investiguer.
    Les angles-mort isoles dans XFAIL_KNOWN_GAPS ne penalisent pas cette metrique.
    """
    failures = []
    for cls in ("machine", "env", "stochastic", "structural"):
        cm = _confusion_for_class(cls)
        precision = cm["tp"] / (cm["tp"] + cm["fp"]) if (cm["tp"] + cm["fp"]) else 1.0
        recall = cm["tp"] / (cm["tp"] + cm["fn"]) if (cm["tp"] + cm["fn"]) else 1.0
        if precision < 1.0 or recall < 1.0:
            failures.append(
                f"{cls}: precision={precision:.2f} recall={recall:.2f} cm={cm}"
            )
    assert not failures, (
        "Le scanner n'est pas exact sur les frontieres non-xfail (regression):\n  "
        + "\n  ".join(failures)
    )


def test_known_gap_count_is_documented():
    """Anti-oubli: le nombre d'angles-mort doit correspondre au dict XFAIL.

    Si on ajoute un cas xfail au golden set sans l'inventorier dans
    XFAIL_KNOWN_GAPS (ou inversement), ce test echoue -> oblige a tenir le
    registre a jour. C'est l'audit trail des angles-mort.
    """
    # Recalcule les divergences reelles (sans xfail precoce)
    divergences = []
    for c in CASES:
        actual = _scanner_matches(c["text"], c["cls"])
        expected = c["expect"] == "match"
        if actual != expected:
            divergences.append(c["id"])
    assert set(divergences) == set(XFAIL_KNOWN_GAPS), (
        f"Registre des angles-mort desynchronise.\n"
        f"  Divergences reelles:    {sorted(divergences)}\n"
        f"  XFAIL_KNOWN_GAPS declare: {sorted(XFAIL_KNOWN_GAPS)}\n"
        f"  -> si un cas a commence a matcher (regression ou fixe), le retirer "
        f"de XFAIL_KNOWN_GAPS ; si un nouvel angle-mort est trouve, l'inventorier."
    )
