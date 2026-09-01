"""Test anti-derive : la sortie du notebook Quasi-Experimental.ipynb = sortie de causal_organs.

Issue #14051 tranche 2/2 acceptance 4 :
> Un test anti-derive : si le module canonique change sa sortie, le pont rougit.
> C'est ce qui manque aujourd'hui et qui donne son sens au mot « cross-engine ».

Strategie : on execute reellement les estimateurs du notebook (cellules 5 et 40)
apres les modifications d'acceptance #14051 (import depuis ``causal_organs``),
et on verifie que la sortie observee par le notebook **est byte-identique**
a la sortie du module canonique appele directement.

L'execution reelle (H.1 — pas de mock) capture le bug qui se serait manifeste
si quelqu'un revertait l'import ou modifiait le module sans toucher le notebook :
le pont continuerait de passer au vert sur un test qui ne regarde que la valeur
de l'organe canonique, sans voir le notebook. Ce test **rattache les deux**.

Note byte-identique (cf. docstring de causal_organs.py) : le notebook cellule 5
positionne ``np.random.seed(42)`` AVANT l'appel ``make_panel_did(0.0)``, ce qui
aligne le seed global sur la valeur 42. Le module utilise un ``RandomState(seed)``
LOCAL avec ``seed=42``. Ces deux conventions produisent des DataFrames **byte-
identiques** (la deviation documentee du module ne se manifeste que si d'autres
cellules ont consomme le RNG global entre le seed et l'appel, ce qui n'est pas
le cas de la cellule 5 ni de la cellule 40).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

# Permettre l'import direct sans packaging : on ajoute le dossier parent au sys.path
_PARENT_DIR = Path(__file__).resolve().parent.parent
if str(_PARENT_DIR) not in sys.path:
    sys.path.insert(0, str(_PARENT_DIR))

import causal_organs as co  # noqa: E402

# Chemin du notebook source (relatif a ce test)
NB_PATH = _PARENT_DIR / "Quasi-Experimental.ipynb"


def _extract_cell_source(nb_path: Path, cell_index: int) -> str:
    """Lit la cellule ``cell_index`` du notebook et retourne son source concatene."""
    nb = json.load(open(nb_path, encoding="utf-8"))
    return "".join(nb["cells"][cell_index]["source"])


def _exec_cell_in_fresh_globals(nb_path: Path, cell_index: int, init: dict | None = None) -> dict:
    """Execute la cellule ``cell_index`` dans un namespace frais.

    Retourne le namespace apres execution (les variables locales que la cellule
    a definies sont accessibles). Le namespace est pre-popule avec les imports
    que les cellules amont du notebook realisent (cf. cellule 3 : numpy, pandas,
    scipy, statsmodels, statsmodels.formula.api, matplotlib).
    """
    src = _extract_cell_source(nb_path, cell_index)
    g: dict = dict(init) if init else {}
    # Pre-charger les imports que la cellule 3 (et les suivantes) realisent.
    # Sans ce pre-chargement, ``np``, ``pd``, ``smf``, ``plt``, ``stats`` ne
    # seraient pas definis et le cellule 5 ferait NameError.
    g["np"] = np
    g["pd"] = pd
    try:
        import scipy.stats as stats  # noqa: F401
        g["stats"] = stats
        import scipy  # noqa: F401
        g["scipy"] = scipy
    except ImportError:
        pass
    try:
        import statsmodels  # noqa: F401
        g["statsmodels"] = statsmodels
        import statsmodels.api as sm  # noqa: F401
        g["sm"] = sm
        import statsmodels.formula.api as smf  # noqa: F401
        g["smf"] = smf
    except ImportError:
        pass
    try:
        import matplotlib  # noqa: F401
        matplotlib.use("Agg")
        g["matplotlib"] = matplotlib
        import matplotlib.pyplot as plt  # noqa: F401
        g["plt"] = plt
    except ImportError:
        pass
    exec(compile(src, f"<cell-{cell_index}>", "exec"), g)
    return g


# ---------------------------------------------------------------------------
# Acceptance 4 — anti-derive : make_panel_did (cellule 5)
# ---------------------------------------------------------------------------
def test_cellule5_make_panel_did_byte_identique_module():
    """La cellule 5 du notebook produit la meme DataFrame que causal_organs.make_panel_did().

    Avant l'acceptance #14051, la cellule 5 DEFINISSAIT ``make_panel_did`` en local ;
    apres l'acceptance, elle IMPORTE depuis ``causal_organs``. Ce test verifie que
    l'import preserve la byte-identite (puisque le notebook seed le RNG global avant
    l'appel, ce qui aligne le RandomState LOCAL du module sur seed=42).

    Note : la cellule 5 ajoute 3 colonnes derivees (``treated``, ``post``,
    ``treated_post``) au panel. On compare sur les 4 colonnes de base du
    module, qui seules sont sous le controle de ``causal_organs``.
    """
    g = _exec_cell_in_fresh_globals(NB_PATH, 5)
    df_nb = g["df_did"]
    df_co = co.make_panel_did(seed=42)  # seed=42 explicite

    pd.testing.assert_frame_equal(
        df_nb[["group", "unit", "period", "y"]],
        df_co[["group", "unit", "period", "y"]],
    )


def test_cellule5_tau_did_hand_egal_module_tau_recovered():
    """Le tau_DiD 2x2 calcule a la main dans la cellule 5 vaut ~3.0 (cible TAU_TRUE_DID).

    Anti-derive : si le module canonique change sa constante TAU_TRUE_DID, la valeur
    affichee par le notebook change aussi (via l'import). Ce test detecte ce cas
    par la valeur de la cellule 5 qui doit suivre la cible.
    """
    g = _exec_cell_in_fresh_globals(NB_PATH, 5)
    tau_did_nb = (g["mT_post"] - g["mT_pre"]) - (g["mC_post"] - g["mC_pre"])
    # On accepte la tolerance large (PR #13921 B1, ecart Monte-Carlo seed=42 unique)
    assert abs(tau_did_nb - co.TAU_TRUE_DID) < 0.5, (
        f"tau_DiD cellule 5 = {tau_did_nb:.6f}, cible {co.TAU_TRUE_DID} "
        f"(tolerance 0.5 — Monte-Carlo seed=42)"
    )


# ---------------------------------------------------------------------------
# Acceptance 4 — anti-derive : make_panel_did violation (cellule 13)
# ---------------------------------------------------------------------------
def test_cellule13_violation_augmente_le_biais():
    """La cellule 13 (panel avec derive differentielle) montre un biais positif.

    Anti-derive : si le module canonique ne repond plus a la violation SUTA
    (par exemple si quelqu'un retire la ligne ``y += differential_pretrend * t``),
    la difference ``tau_bad - tau_clean`` chute. Ce test detecte ce cas.
    """
    g_cell5 = _exec_cell_in_fresh_globals(NB_PATH, 5)
    g = _exec_cell_in_fresh_globals(NB_PATH, 13, init=g_cell5)
    tau_bad = g["tau_bad"]
    tau_clean = (g_cell5["mT_post"] - g_cell5["mT_pre"]) - (g_cell5["mC_post"] - g_cell5["mC_pre"])
    assert tau_bad > tau_clean, (
        f"violation SUTA doit augmenter tau : clean={tau_clean:.3f}, bad={tau_bad:.3f}"
    )


# ---------------------------------------------------------------------------
# Acceptance 4 — anti-derive : iv_replay (cellule 40)
# ---------------------------------------------------------------------------
def test_cellule40_iv_replay_byte_identique_module():
    """La cellule 40 du notebook produit la meme distribution que causal_organs.iv_replay().

    Avant l'acceptance #14051, la cellule 40 DEFINISSAIT ``iv_replay`` en local ;
    apres, elle IMPORTE depuis ``causal_organs``. Ce test verifie que le notebook
    (apres seed global ``np.random.seed(123)``) et le module (RandomState LOCAL
    seed0=0 par defaut) produisent la meme distribution sur instrument FORT.

    Note : la cellule 40 depend de la cellule 34 qui definit ``TAU_TRUE_IV`` (avant
    l'acceptance localement, apres par import). On execute donc c34 d'abord dans le
    meme namespace.
    """
    g34 = _exec_cell_in_fresh_globals(NB_PATH, 34)
    g = _exec_cell_in_fresh_globals(NB_PATH, 40, init=g34)
    tau_fort_nb = g["tau_fort_dist"]
    tau_fort_co = co.iv_replay(coef_z=1.00)
    np.testing.assert_array_equal(tau_fort_nb, tau_fort_co)


def test_cellule40_iv_replay_instrument_fort_centered():
    """Instrument FORT (coef_z=1.0) dans la cellule 40 : moyenne ~ 2.0, std borne.

    Anti-derive : si le module change la valeur cible TAU_TRUE_IV, le notebook
    suit (via l'import). La tolerance reste large (PR #13921 B1).
    """
    g34 = _exec_cell_in_fresh_globals(NB_PATH, 34)
    g = _exec_cell_in_fresh_globals(NB_PATH, 40, init=g34)
    tau_fort = g["tau_fort_dist"]
    assert abs(tau_fort.mean() - co.TAU_TRUE_IV) < 0.5, (
        f"tau_2SLS moyen cellule 40 = {tau_fort.mean():.6f}, "
        f"cible {co.TAU_TRUE_IV} (tolerance 0.5)"
    )
    assert tau_fort.std() < 0.5, (
        f"instrument FORT doit avoir variance bornee, std={tau_fort.std():.6f}"
    )


def test_cellule40_iv_replay_instrument_faible_variance_explose():
    """Instrument FAIBLE (coef_z=0.05) : variance explosee vs cas FORT.

    Anti-derive : le verdict NON_IDENTIFIABLE de la cellule 40 (PR #13921 B2)
    tient via l'import du module. Si le module perdait la dependance en coef_z,
    le std FAIBLE pourrait chuter ; ce test detecte ce cas.
    """
    g34 = _exec_cell_in_fresh_globals(NB_PATH, 34)
    g = _exec_cell_in_fresh_globals(NB_PATH, 40, init=g34)
    tau_fort = g["tau_fort_dist"]
    tau_weak = g["tau_weak_dist"]
    assert tau_weak.std() > tau_fort.std(), (
        f"SD instrument faible ({tau_weak.std():.3f}) doit etre > SD fort ({tau_fort.std():.3f})"
    )


# ---------------------------------------------------------------------------
# Acceptance 4 — anti-derive : TAU_TRUE_IV est importe depuis le module
# ---------------------------------------------------------------------------
def test_cellule34_tau_true_iv_vaut_module():
    """La cellule 34 du notebook importe TAU_TRUE_IV depuis causal_organs.

    Avant l'acceptance, cellule 34 DEFINISSAIT TAU_TRUE_IV = 2.0 localement ;
    apres, elle IMPORTE depuis le module. Si quelqu'un revertait l'import et
    redefinissait localement une valeur differente, ce test rougirait.
    """
    g = _exec_cell_in_fresh_globals(NB_PATH, 34)
    # Si la cellule importe correctement, la variable dans le namespace designe
    # l'objet de causal_organs (meme reference memoire).
    assert g["TAU_TRUE_IV"] is co.TAU_TRUE_IV, (
        f"cellule 34 TAU_TRUE_IV ({g['TAU_TRUE_IV']}) n'est pas la meme reference "
        f"que causal_organs.TAU_TRUE_IV ({co.TAU_TRUE_IV})"
    )


def test_cellule5_tau_true_did_vaut_module():
    """La cellule 5 du notebook importe TAU_TRUE_DID depuis causal_organs."""
    g = _exec_cell_in_fresh_globals(NB_PATH, 5)
    assert g["TAU_TRUE_DID"] is co.TAU_TRUE_DID, (
        f"cellule 5 TAU_TRUE_DID ({g['TAU_TRUE_DID']}) n'est pas la meme reference "
        f"que causal_organs.TAU_TRUE_DID ({co.TAU_TRUE_DID})"
    )