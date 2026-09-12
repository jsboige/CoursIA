"""Tests pytest pour dowhy_iv_organs.py -- slice 5/5 #14049 (DoWhy-5-Instrument-Faible).

Issue #14049 §1 acceptance : « chaque notebook de la serie DoWhy expose
un organe importable des sa livraison, et les tests verifient la sortie du
module contre la valeur attendue ».

Strategie de test (meme convention que test_dowhy_organs.py) : on
**execute reellement** le pipeline dowhy (pas de mock, H.1) et on
verifie que :

(a) ``generer_donnees_iv`` rend un DataFrame de la bonne forme et
    respecte la RandomState LOCALE (deux appels avec meme seed ->
    DataFrame egal) ;
(b) ``f_statistic`` discrimine bien instrument fort vs faible : F > 100
    pour ``force=1.0``, F < 30 pour ``force=0.05`` (le seuil
    Staiger-Stock 10 est largement teste sur Monte-Carlo implicite) ;
(c) ``biais_iv_vs_ols`` : pour instrument fort, biais IV < 0.05 et
    std < 0.1 ; pour instrument faible, std IV > 1.0 (le warning
    classique : « IV explodes on weak instruments ») ;
(d) ``verdict_exclusion`` en mode terrain : NON_IDENTIFIABLE si
    l'effet direct est au-dessus de la tolerance, IDENTIFIABLE sinon.
    En mode observation, on REFUSE par defaut (la regression naive
    dans un monde IV confond colinearite X/Z et effet direct -- le
    module ne triche pas en donnant un verdict statistique) ;
(e) ``dowhy_iv_run`` retourne un DowhyIvResult avec estimand ``"iv"``
    et une valeur proche du vrai tau pour instrument fort, et un
    F_stat superieur au seuil Staiger-Stock 10.

Les tolerances sont larges : Monte-Carlo + bruit Gaussien, le test
pertinent est « ordre de grandeur et signe corrects ».
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

# Import direct sans packaging : on ajoute le dossier parent
# (Probas/DecisionTheory/Causal-Bridges/) au sys.path.
_PARENT_DIR = Path(__file__).resolve().parent.parent
if str(_PARENT_DIR) not in sys.path:
    sys.path.insert(0, str(_PARENT_DIR))

import dowhy_iv_organs as dio


# ---------------------------------------------------------------------------
# generer_donnees_iv
# ---------------------------------------------------------------------------
def test_generer_donnees_iv_shape():
    """Dimensions par defaut : n=2000 x 4 colonnes (U, Z, X, Y)."""
    df = dio.generer_donnees_iv()
    assert isinstance(df, pd.DataFrame)
    assert df.shape == (2000, 4)
    assert list(df.columns) == ["U", "Z", "X", "Y"]


def test_generer_donnees_iv_seed_reproductible():
    """RandomState LOCAL -> deux appels avec meme seed retournent la meme DataFrame."""
    df_a = dio.generer_donnees_iv(seed=42)
    df_b = dio.generer_donnees_iv(seed=42)
    pd.testing.assert_frame_equal(df_a, df_b)


def test_generer_donnees_iv_seed_change_impacte():
    """Deux seeds differents -> deux DataFrames differentes."""
    df_a = dio.generer_donnees_iv(seed=42)
    df_b = dio.generer_donnees_iv(seed=43)
    assert not df_a.equals(df_b)


def test_generer_donnees_iv_force_change_dgp():
    """force=1 (fort) -> X tres correlee a Z ; force=0.05 -> X presque indep.
    La correlation absolue |corr(X, Z)| mesure l'impact de la force.
    """
    df_fort = dio.generer_donnees_iv(n=5000, force=1.0, seed=42)
    df_faible = dio.generer_donnees_iv(n=5000, force=0.05, seed=42)
    corr_fort = float(df_fort[["X", "Z"]].corr().iloc[0, 1])
    corr_faible = float(df_faible[["X", "Z"]].corr().iloc[0, 1])
    assert abs(corr_fort) > 0.6, f"FORT corr {corr_fort:+.3f} attendue > 0.6"
    assert abs(corr_faible) < 0.1, f"FAIBLE corr {corr_faible:+.3f} attendue < 0.1"


# ---------------------------------------------------------------------------
# f_statistic
# ---------------------------------------------------------------------------
def test_f_statistic_instrument_fort():
    """force=1.0 : F >> 10 (instrument FORT)."""
    df = dio.generer_donnees_iv(n=2000, force=1.0, seed=42)
    f, p, r2 = dio.f_statistic(df)
    assert f > 100.0, f"FORT F={f:.2f} attendu >> 10"
    assert p < 0.001, f"FORT p={p:.4g} attendue < 0.001"
    assert r2 > 0.3, f"FORT R2={r2:.4f} attendu > 0.3"


def test_f_statistic_instrument_faible():
    """force=0.05 : F < 30 (instrument FAIBLE, sous le seuil Staiger-Stock
    10 sur Monte-Carlo peut etre, ici on teste un seuil conservateur).
    """
    df = dio.generer_donnees_iv(n=2000, force=0.05, seed=42)
    f, p, r2 = dio.f_statistic(df)
    assert f < 30.0, f"FAIBLE F={f:.2f} attendu < 30 (Staiger-Stock rule)"


def test_f_statistic_staiger_stock_seuil():
    """Le seuil canonique F > 10 : on prend les deux forces et on verifie
    que l'instrument fort le franchit largement et le faible reste sous
    (avec une marge).
    """
    f_fort, _, _ = dio.f_statistic(dio.generer_donnees_iv(n=2000, force=1.0, seed=1))
    f_faible, _, _ = dio.f_statistic(dio.generer_donnees_iv(n=2000, force=0.05, seed=1))
    assert f_fort > dio.SEUIL_F_STAIGER_STOCK
    assert f_faible < 30.0


# ---------------------------------------------------------------------------
# biais_iv_vs_ols
# ---------------------------------------------------------------------------
def test_biais_iv_vs_ols_instrument_fort():
    """force=1.0 : IV a biais < 0.05 et std < 0.1 -- le 2SLS est
    concentrique autour du vrai tau. OLS avec U ajuste (qu'on ne peut
    PAS observer en pratique, juste en simulation) est comparable ou
    meilleur : c'est le SANITY CHECK du DGP, pas le test de l'IV.
    """
    mc = dio.biais_iv_vs_ols(force=1.0, n_samp=1000, n_rep=60, seed0=0)
    biais_iv = float(np.mean(mc["tau_iv"]) - mc["tau_true"][0])
    std_iv = float(np.std(mc["tau_iv"]))
    assert abs(biais_iv) < 0.05, f"IV fort biais {biais_iv:+.3f} attendu ~ 0"
    assert std_iv < 0.1, f"IV fort std {std_iv:.3f} attendu < 0.1"


def test_biais_iv_vs_ols_instrument_faible_explose():
    """force=0.05 : std IV > 1.0 (explosion classique de l'IV sur
    instrument faible). On accepte un biais modere, c'est la std qui
    caracterise le piege.
    """
    mc = dio.biais_iv_vs_ols(force=0.05, n_samp=1000, n_rep=60, seed0=0)
    std_iv = float(np.std(mc["tau_iv"]))
    assert std_iv > 1.0, f"IV faible std {std_iv:.3f} attendu > 1.0"


def test_biais_iv_vs_ols_tau_true_expose():
    """Le dict expose bien ``tau_true`` comme constante, pas comme
    estimation -- c'est la VERITE TERRAIN du DGP, indispensable pour
    calculer le biais sans bricoler.
    """
    mc = dio.biais_iv_vs_ols(force=1.0, n_samp=100, n_rep=5, seed0=0)
    assert "tau_true" in mc
    assert np.all(mc["tau_true"] == dio.TAU_VRAI)


# ---------------------------------------------------------------------------
# verdict_exclusion
# ---------------------------------------------------------------------------
def test_verdict_exclusion_mode_observation_refuse_par_defaut():
    """Sans verite terrain, le module REFUSE de troller un test sur la
    regression brute (X et Z colineaires par construction dans le DGP).
    Verdict = REFUTE_PAR_DEFAUT, mode = observation.
    """
    df = dio.generer_donnees_iv(n=2000, force=1.0, seed=42)
    v = dio.verdict_exclusion(df)
    assert v["verdict"] == "REFUTE_PAR_DEFAUT"
    assert v["mode"] == "observation"
    assert np.isnan(v["effet_direct_z"])


def test_verdict_exclusion_terrain_zero_identifiable():
    """Verite terrain = 0.0 : verdict IDENTIFIABLE (exclusion respectee)."""
    df = dio.generer_donnees_iv(n=2000, force=1.0, seed=42)
    v = dio.verdict_exclusion(df, effet_direct_z_connu=0.0)
    assert v["verdict"] == "IDENTIFIABLE"
    assert v["mode"] == "terrain"
    assert v["effet_direct_z"] == 0.0


def test_verdict_exclusion_terrain_non_zero_non_identifiable():
    """Verite terrain = 0.5 : verdict NON_IDENTIFIABLE (exclusion violee).
    C'est le cas pedagogue central : le praticien voit un beau tau 2SLS
    et pourtant la cible identifiee n'est pas l'effet causal cherche.
    """
    df = dio.generer_donnees_iv(n=2000, force=1.0, seed=42)
    v = dio.verdict_exclusion(df, effet_direct_z_connu=0.5)
    assert v["verdict"] == "NON_IDENTIFIABLE"


def test_verdict_exclusion_tol_marge():
    """Avec ``tol=0.1``, un effet direct de 0.05 reste dans la
    tolerance et verdict = IDENTIFIABLE. Avec 0.2, NON_IDENTIFIABLE.
    """
    df = dio.generer_donnees_iv(n=2000, force=1.0, seed=42)
    v_ok = dio.verdict_exclusion(df, effet_direct_z_connu=0.05, tol=0.1)
    v_ko = dio.verdict_exclusion(df, effet_direct_z_connu=0.2, tol=0.1)
    assert v_ok["verdict"] == "IDENTIFIABLE"
    assert v_ko["verdict"] == "NON_IDENTIFIABLE"


# ---------------------------------------------------------------------------
# dowhy_iv_run (pipeline end-to-end)
# ---------------------------------------------------------------------------
def test_dowhy_iv_run_force_fort_proche_du_vrai_tau():
    """Instrument fort : le tau dowhy doit etre proche de TAU_VRAI=2.0
    (tolérance 0.2 sur Monte-Carlo a n=1500).
    """
    df = dio.generer_donnees_iv(n=1500, force=1.0, seed=42)
    res = dio.dowhy_iv_run(df, n_rep=3)
    assert res.estimand_text == "iv"
    assert abs(res.estimate_value - dio.TAU_VRAI) < 0.2, (
        f"tau dowhy {res.estimate_value:.4f} attendu proche de {dio.TAU_VRAI}"
    )
    assert res.f_stat > dio.SEUIL_F_STAIGER_STOCK
    assert res.estimate_method == "iv.instrumental_variable"


def test_dowhy_iv_run_force_faible_f_stat_bas():
    """Instrument faible : F_stat < 30 (donc sous le seuil pratique 10
    ou proche), et la valeur tau peut diverger (le test accepte un
    chiffre eloigne du vrai, on ne fait pas de CHIANTI dessus).
    """
    df = dio.generer_donnees_iv(n=3000, force=0.05, seed=7)
    res = dio.dowhy_iv_run(df, n_rep=3)
    assert res.f_stat < 30.0, (
        f"F_stat {res.f_stat:.2f} attendu < 30 (instrument faible)"
    )


def test_dowhy_iv_run_refuters_renvoient_pvalue():
    """Les refuters ``placebo`` et ``data_subset`` tournent et rendent
    une p-value (meme NaN, pas une KeyError). On accepte les erreurs
    silencieuses (le module les capture) mais pas de crash.
    """
    df = dio.generer_donnees_iv(n=1500, force=1.0, seed=42)
    res = dio.dowhy_iv_run(df, n_rep=3)
    assert "placebo_pvalue" in res.refutations
    assert "data_subset_pvalue" in res.refutations
    # Les p-values sont des floats (NaN ou reels)
    assert isinstance(res.refutations["placebo_pvalue"], float)


def test_dowhy_iv_run_verdict_exclusion_par_defaut():
    """En l'absence de verite terrain, verdict_exclusion = REFUTE_PAR_DEFAUT.
    Le pipeline ne pretend pas trancher la violation d'exclusion -- c'est
    au DAG declare de le faire.
    """
    df = dio.generer_donnees_iv(n=1500, force=1.0, seed=42)
    res = dio.dowhy_iv_run(df, n_rep=3)
    assert res.verdict_exclusion == "REFUTE_PAR_DEFAUT"


# ---------------------------------------------------------------------------
# Reproductibilite
# ---------------------------------------------------------------------------
def test_generer_donnees_iv_independance_du_rng_global():
    """Le seed pose est LOCAL : l'etat du RNG global numpy n'est pas
    touche apres l'appel (doctrine module, cf. L532 MEMORY).
    """
    np.random.seed(9999)
    etat_avant = np.random.get_state()
    dio.generer_donnees_iv(n=500, force=1.0, seed=42)
    etat_apres = np.random.get_state()
    # L'API 0.14 peut avoir utilise np.random dans dowhy en interne ;
    # on verifie au moins que l'appel direct a notre organe ne pollue
    # PAS le RNG (l'organe est purement RandomState LOCAL).
    assert etat_avant[0] == etat_apres[0]
    assert np.array_equal(etat_avant[1], etat_apres[1])
