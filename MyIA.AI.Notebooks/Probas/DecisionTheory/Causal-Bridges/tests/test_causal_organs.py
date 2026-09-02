"""Tests pytest pour causal_organs.py — tranche 1/2 #14051.

Issue #14051 §1 acceptance : « Les deux modules existent, sont importables,
et sont testes (le test compare la sortie du module a la valeur attendue
du notebook) ».

Strategie de test : on **execute reellement** les estimateurs (pas de mock,
H.1) et on verifie que :

(a) la forme du DataFrame / ndarray retournes correspond aux dimensions
    natives du notebook ;
(b) les grandeurs agregees (moyenne, ecart-type) des estimateurs collent
    au comportement attendu par le notebook : tau_DiD ~ TAU_TRUE_DID pour
    SUTA satisfaite ; tau_2SLS moyen ~ TAU_TRUE_IV pour instrument fort,
    variance bornee ; variance explosee pour instrument faible.
(c) reproductibilite via seed LOCAL (RandomState) -- deux appels
    successifs retournent la meme sortie.

Note : byte-identique strict aux cellules 5/40 du notebook n'est PAS
atteignable, parce que les cellules du notebook utilisent un seed global
``np.random.seed(42)`` suivi d'autres cellules qui consomment le RNG. Les
tests verifient donc la distribution agregee, documentee comme deviation
explicite dans la docstring de ``causal_organs.py``.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

# Permettre l'import direct sans packaging : on ajoute le dossier parent
# (Probas/DecisionTheory/Causal-Bridges/) au sys.path.
_PARENT_DIR = Path(__file__).resolve().parent.parent
if str(_PARENT_DIR) not in sys.path:
    sys.path.insert(0, str(_PARENT_DIR))

import causal_organs as co


# ---------------------------------------------------------------------------
# Tests make_panel_did
# ---------------------------------------------------------------------------
def test_make_panel_did_default_shape():
    """Dimensions du panel par defaut : n_units=60 x 2 groupes x 8 periodes = 960 lignes."""
    df = co.make_panel_did()
    assert isinstance(df, pd.DataFrame)
    assert df.shape == (960, 4)
    assert list(df.columns) == ["group", "unit", "period", "y"]
    assert df["group"].nunique() == 2
    assert df["period"].nunique() == 8
    assert df["unit"].nunique() == 60


def test_make_panel_did_seed_reproductible():
    """RandomState LOCAL -> deux appels avec meme seed retournent la meme DataFrame."""
    df_a = co.make_panel_did(seed=42)
    df_b = co.make_panel_did(seed=42)
    pd.testing.assert_frame_equal(df_a, df_b)


def test_make_panel_did_tau_recovered():
    """tau_DiD par les 4 cellules 2x2 doit etre proche de TAU_TRUE_DID = 3.0 pour SUTA.

    Tolerance large (0.5) car l'estimation est Monte-Carlo avec un seed
    unique ; le test pertinent est « l'ordre de grandeur est correct, le
    signe est correct, le diagnostic de violation fonctionne » -- voir PR
    #13921 B1 (accord tolerance 1.0 entre DiD et backdoor).
    """
    df = co.make_panel_did()  # SUTA satisfaite, differential_pretrend=0
    mT_pre = df.query("group == 1 and period < 5").y.mean()
    mT_post = df.query("group == 1 and period >= 5").y.mean()
    mC_pre = df.query("group == 0 and period < 5").y.mean()
    mC_post = df.query("group == 0 and period >= 5").y.mean()
    tau_did = (mT_post - mT_pre) - (mC_post - mC_pre)
    assert abs(tau_did - co.TAU_TRUE_DID) < 0.5, (
        f"tau_DiD {tau_did:.3f} eloigne de {co.TAU_TRUE_DID} (tolerance 0.5)"
    )


def test_make_panel_did_violation_increases_bias():
    """Une violation de SUTA (differential_pretrend=0.5) doit faire deriver le tau.

    Le test verifie que la violation INJECTEE engendre un biais observe non
    nul. La tolerance est large pour absorber la variance Monte-Carlo.
    """
    df_clean = co.make_panel_did(seed=42)
    df_bad = co.make_panel_did(differential_pretrend=0.5, seed=42)

    def tau_2x2(d):
        mT_pre = d.query("group == 1 and period < 5").y.mean()
        mT_post = d.query("group == 1 and period >= 5").y.mean()
        mC_pre = d.query("group == 0 and period < 5").y.mean()
        mC_post = d.query("group == 0 and period >= 5").y.mean()
        return (mT_post - mT_pre) - (mC_post - mC_pre)

    tau_clean = tau_2x2(df_clean)
    tau_bad = tau_2x2(df_bad)
    assert tau_bad > tau_clean, (
        f"violation SUTA doit augmenter tau mesure : clean={tau_clean:.3f}, bad={tau_bad:.3f}"
    )


# ---------------------------------------------------------------------------
# Tests iv_replay
# ---------------------------------------------------------------------------
def test_iv_replay_shape():
    """iv_replay retourne un ndarray de forme (n_rep,)."""
    d = co.iv_replay(coef_z=1.0)
    assert isinstance(d, np.ndarray)
    assert d.shape == (60,)  # n_rep=60 par defaut


def test_iv_replay_seed_reproductible():
    """Meme seed0 -> meme distribution."""
    d1 = co.iv_replay(coef_z=1.0)
    d2 = co.iv_replay(coef_z=1.0)
    np.testing.assert_array_equal(d1, d2)


def test_iv_replay_fort_centered_and_bounded():
    """Instrument FORT (coef_z=1.0) -> tau_2SLS moyen ~ 2.0, ecart-type borne.

    Tolerance analog a PR #13921 test B1 (instrument fort : moyenne 1.996
    contre vraie 2.0, ecart implicite < 0.5).
    """
    d = co.iv_replay(coef_z=1.0)
    mean = d.mean()
    std = d.std()
    assert abs(mean - co.TAU_TRUE_IV) < 0.5, (
        f"tau_2SLS moyen {mean:.3f} eloigne de {co.TAU_TRUE_IV}"
    )
    assert std < 0.5, f"instrument FORT doit avoir variance bornee, std={std:.3f}"


def test_iv_replay_faible_variance_exploses():
    """Instrument FAIBLE (coef_z=0.05) -> variance explosee par rapport au cas FORT.

    Le notebook observe « tau part dans le decor » ; on accepte le verdict
    INON_IDENTIFIABLE du test B2 (PR #13921) -- ce qui compte pour ce
    module, c'est que la SD du cas FAIBLE soit >> SD du cas FORT.
    """
    d_fort = co.iv_replay(coef_z=1.0)
    d_faible = co.iv_replay(coef_z=0.05)
    sd_fort = d_fort.std()
    sd_faible = d_faible.std()
    assert sd_faible > sd_fort, (
        f"SD instrument faible ({sd_faible:.3f}) doit etre > SD instrument fort ({sd_fort:.3f})"
    )
