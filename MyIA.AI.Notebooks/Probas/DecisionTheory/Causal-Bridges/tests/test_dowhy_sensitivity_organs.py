"""Tests pytest pour dowhy_sensitivity_organs.py -- grain DoWhy-4 de l'issue #14049.

Issue #14049, acceptance 4 : « chaque notebook de la serie DoWhy expose
un organe importable des sa livraison, et les tests verifient la sortie
du module contre la valeur attendue ». Ce fichier EST le consommateur
externe de l'organe (avec le notebook).

Strategie de test (meme convention que test_dowhy_discovery_organs.py) :
on **execute reellement** les refuters de sensibilite de dowhy 0.14 (pas
de mock, H.1) et on verifie que :

(a) ``generer_donnees_continues`` / ``generer_donnees_binaires``
    respectent la RandomState LOCALE, la vue analyste vs oracle
    (cacher_u), et les proprietes du monde binaire (issue rare) ;
(b) l'estime naif du monde A (~1.16 pour un effet vrai de 0.5) est
    biaise vers le haut par le confondeur cache U -- et l'oracle
    dowhy ajuste {C, U} restaure ~0.53 ;
(c) la robustness value de Cinelli-Hazlett vaut ~0.68 sur le monde par
    defaut, avec ses benchmarks ;
(d) le R2 partiel REEL de U (~0.49 / ~0.43) se mesure sur la vue oracle
    et reste sous le RV : verdict SURVIT -- mais le monde affaibli
    (tau=0.2, bruit_y=3.0) bascule en ANNULABLE ;
(e) la courbe de bascule du confondeur simule est reproductible
    (re-seed du RNG global) et croise zero vers kappa ~1.5 (kappa_t=0.7)
    et ~1.1 (diagonale) ;
(f) le RR binaire se lit sur le COEFFICIENT GLM (~1.79), pas sur le
    contraste marginal .value (~1.04) -- le piege API encapsule ;
(g) l'E-value dowhy natif vaut ~2.98, exactement RR + sqrt(RR(RR-1)),
    avec le benchmark McGowan-Greevy de C a ~1.16 : verdict ROBUSTE
    RELATIVEMENT AUX OBSERVES ;
(h) les bornes de Rosenbaum sont exactes : p_bas == p_haut a Gamma=1,
    la borne haute croit avec Gamma, Gamma* ~1.33 rend non significatif ;
(i) anti-derive : les cellules cles du notebook consomment l'organe et
    produisent les memes donnees que l'appel canonique.

Les tolerances sont celles de la serie : mondes DGP-connus, coefficients
forts, n=2000/3000 -- les valeurs ci-dessus sont stables sur 10 seeds
(mesurees avant l'ecriture de ces tests), les tests fixent seed=42.
"""

from __future__ import annotations

import json
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

import dowhy_sensitivity_organs as dso

NB_PATH = _PARENT_DIR / "DoWhy-4-Sensibilite-Confounder-Cache.ipynb"


# ---------------------------------------------------------------------------
# (a) Generateurs
# ---------------------------------------------------------------------------
def test_generer_continues_formes_et_vues():
    """Vue analyste (X, Y, C) vs oracle (avec U) ; meme graine = meme monde."""
    df = dso.generer_donnees_continues(n=2000, seed=42)
    df_o = dso.generer_donnees_continues(n=2000, seed=42, cacher_u=False)
    assert df.shape == (2000, 3)
    assert list(df.columns) == ["X", "Y", "C"]
    assert list(df_o.columns) == ["X", "Y", "C", "U"]
    # la vue analyste est la projection de la vue oracle
    pd.testing.assert_frame_equal(df, df_o[["X", "Y", "C"]])


def test_generer_continues_seed_reproductible():
    pd.testing.assert_frame_equal(
        dso.generer_donnees_continues(seed=7),
        dso.generer_donnees_continues(seed=7),
    )
    assert not dso.generer_donnees_continues(seed=7).equals(
        dso.generer_donnees_continues(seed=8)
    )


def test_generer_binaires_issue_rare_et_binaires():
    """Monde B : X et Y binaires, issue rare (< 15 %), C binaire."""
    df = dso.generer_donnees_binaires(n=3000, seed=42)
    assert df.shape == (3000, 3)
    assert set(df["X"].unique()) <= {0, 1}
    assert set(df["Y"].unique()) <= {0, 1}
    assert set(df["C"].unique()) <= {0, 1}
    assert df["Y"].mean() < 0.15, "l'issue doit etre rare (~7 %)"


def test_generer_binaires_param_b_x_change_le_rr():
    """b_x est le log-RR vrai : l'affaiblir rapproche le RR brut de 1."""
    df_fort = dso.generer_donnees_binaires(n=8000, seed=42, b_x=0.8)
    rr_fort = df_fort.groupby("X")["Y"].mean()[1] / df_fort.groupby("X")["Y"].mean()[0]
    df_faible = dso.generer_donnees_binaires(n=8000, seed=42, b_x=0.1)
    rr_faible = df_faible.groupby("X")["Y"].mean()[1] / df_faible.groupby("X")["Y"].mean()[0]
    assert rr_fort > rr_faible


# ---------------------------------------------------------------------------
# (b) Monde A : estime naif biaise, oracle qui restaure
# ---------------------------------------------------------------------------
def test_estime_naif_est_biaise_par_u():
    """L'estime naif (~1.16) depasse l'effet vrai 0.5 : le travail de U."""
    df = dso.generer_donnees_continues(seed=42)
    res = dso.estimer_effet_continu(df)
    assert abs(res.value - 1.159) < 0.02
    assert res.ic[0] < res.value < res.ic[1]
    assert res.value > dso.TAU_VRAI + 0.3, "le biais de U doit etre substantiel"


def test_oracle_dowhy_restaure_effet_vrai():
    """Ajuster {C, U} (vue oracle) ramene l'estime a ~0.53 (vrai 0.5)."""
    from dowhy import CausalModel

    df_o = dso.generer_donnees_continues(seed=42, cacher_u=False)
    modele = CausalModel(data=df_o, treatment="X", outcome="Y", common_causes=["C", "U"])
    estimand = modele.identify_effect(proceed_when_unidentifiable=True)
    oracle = modele.estimate_effect(estimand, method_name="backdoor.linear_regression")
    assert abs(float(oracle.value) - dso.TAU_VRAI) < 0.1


# ---------------------------------------------------------------------------
# (c) Robustness value (Cinelli-Hazlett via dowhy)
# ---------------------------------------------------------------------------
def test_robustesse_partielle_r2_valeurs_mesurees():
    """RV ~0.677 (annuler), RV_alpha ~0.665 (non significatif), r2yt_w ~0.587."""
    df = dso.generer_donnees_continues(seed=42)
    res = dso.estimer_effet_continu(df)
    rob = dso.robustesse_partielle_r2(res.model, res.estimand, res.estimate)
    assert abs(rob.robustness_value - 0.677) < 0.01
    assert abs(rob.robustness_value_alpha - 0.665) < 0.01
    assert 0 < rob.robustness_value_alpha < rob.robustness_value < 1
    assert len(rob.benchmarking) == 1, "une ligne de benchmark par covariable (C)"


# ---------------------------------------------------------------------------
# (d) R2 partiel reel de U + verdicts
# ---------------------------------------------------------------------------
def test_r2_partiel_valeurs_et_identite():
    """R2 reel de U (~0.493/~0.427) ; proprietes formelles du R2 partiel."""
    df_o = dso.generer_donnees_continues(seed=42, cacher_u=False)
    assert abs(dso.r2_partiel(df_o, "X", "U", ["C"]) - 0.493) < 0.01
    assert abs(dso.r2_partiel(df_o, "Y", "U", ["X", "C"]) - 0.427) < 0.01
    # une variable explique elle-meme completement sa propre regression
    assert abs(dso.r2_partiel(df_o, "U", "U", []) - 1.0) < 1e-9


def test_verdict_survit_sur_le_monde_defaut():
    """max(R2 U) ~0.49 < RV ~0.68 : l'association SURVIT a ce confondeur."""
    df = dso.generer_donnees_continues(seed=42)
    df_o = dso.generer_donnees_continues(seed=42, cacher_u=False)
    res = dso.estimer_effet_continu(df)
    rob = dso.robustesse_partielle_r2(res.model, res.estimand, res.estimate)
    v = dso.verdict_sensibilite(
        dso.r2_partiel(df_o, "X", "U", ["C"]),
        dso.r2_partiel(df_o, "Y", "U", ["X", "C"]),
        rob,
    )
    assert v["verdict"] == "SURVIT_A_CE_CONFOUNDEUR"
    assert "RESULTAT" in v["message"]
    assert "ATTENTION" in v["message"], "survivre n'est pas etre juste"


def test_verdict_survit_meme_a_u_renforce():
    """Piege pedagogique : renforcer U fait MONTER le RV -- ca survit encore."""
    df_o = dso.generer_donnees_continues(seed=42, cacher_u=False, coef_u_x=1.8, coef_u_y=1.8)
    res = dso.estimer_effet_continu(df_o[["X", "Y", "C"]])
    rob = dso.robustesse_partielle_r2(res.model, res.estimand, res.estimate)
    v = dso.verdict_sensibilite(
        dso.r2_partiel(df_o, "X", "U", ["C"]),
        dso.r2_partiel(df_o, "Y", "U", ["X", "C"]),
        rob,
    )
    assert rob.robustness_value > 0.8, "le RV doit grimper avec U"
    assert v["verdict"] == "SURVIT_A_CE_CONFOUNDEUR"


def test_verdict_annulable_monde_affaibli():
    """Signal affaibli (tau=0.2, bruit_y=3.0) : RV ~0.25 passe sous R2 U."""
    df_o = dso.generer_donnees_continues(seed=42, cacher_u=False, tau=0.2, bruit_y=3.0)
    res = dso.estimer_effet_continu(df_o[["X", "Y", "C"]])
    rob = dso.robustesse_partielle_r2(res.model, res.estimand, res.estimate)
    v = dso.verdict_sensibilite(
        dso.r2_partiel(df_o, "X", "U", ["C"]),
        dso.r2_partiel(df_o, "Y", "U", ["X", "C"]),
        rob,
    )
    assert res.value > 0, "l'association reste observable"
    assert v["verdict"] == "ANNULABLE_PAR_CE_CONFOUNDEUR"
    assert "RESULTAT" in v["message"]


def test_verdict_annulable_cas_unitaire():
    """Branche ANNULABLE sur entrees synthetiques (fonction pure)."""
    rob = dso.ResultatRobustesse(
        robustness_value=0.3, robustness_value_alpha=0.25, r2yt_w=0.5,
        stats={}, benchmarking=pd.DataFrame(), analyzer=None,
    )
    v = dso.verdict_sensibilite(0.5, 0.4, rob)
    assert v["verdict"] == "ANNULABLE_PAR_CE_CONFOUNDEUR"
    assert "RESULTAT" in v["message"]


# ---------------------------------------------------------------------------
# (e) Confondeur simule : courbe de bascule reproductible
# ---------------------------------------------------------------------------
def test_courbe_bascule_reproductible_et_croise_zero():
    """La courbe (re-seed global) est identique d'un appel a l'autre."""
    df = dso.generer_donnees_continues(seed=42)
    res = dso.estimer_effet_continu(df)
    t1 = dso.confondeur_simule(res.model, res.estimand, res.estimate,
                               k_fixe=0.7, k_max=1.8, pas=0.2)
    t2 = dso.confondeur_simule(res.model, res.estimand, res.estimate,
                               k_fixe=0.7, k_max=1.8, pas=0.2)
    pd.testing.assert_frame_equal(t1, t2)
    assert abs(float(t1.iloc[-1]["estime_ajuste"]) - (-0.043)) < 0.03
    kappa = dso.kappa_bascule(t1)
    assert kappa is not None and 1.3 < kappa < 1.8


def test_courbe_bascule_diagonale():
    """A force egale des deux cotes, la bascule tombe vers kappa ~1.06."""
    df = dso.generer_donnees_continues(seed=42)
    res = dso.estimer_effet_continu(df)
    t = dso.confondeur_simule(res.model, res.estimand, res.estimate,
                              k_max=1.4, pas=0.1, diagonale=True)
    assert (t["kappa_t"] == t["k"]).all(), "diagonale : meme force des deux cotes"
    assert float(t.iloc[0]["estime_ajuste"]) == pytest.approx(res.value, abs=1e-6), (
        "k=0 sans confondeur simule doit rendre l'estime initial"
    )
    kappa = dso.kappa_bascule(t)
    assert kappa is not None and 0.9 < kappa < 1.3


def test_kappa_bascule_sans_croisement():
    tab = pd.DataFrame({"k": [0.0, 0.5, 1.0], "estime_ajuste": [1.0, 0.5, 0.1]})
    assert dso.kappa_bascule(tab) is None


# ---------------------------------------------------------------------------
# (f) Monde B : RR sur le coefficient, pas le contraste marginal
# ---------------------------------------------------------------------------
def test_rr_binaire_sur_le_coefficient():
    """RR ~1.79 (biais de U au-dessus du vrai 1.49) ; le piege .value ~1.04."""
    df = dso.generer_donnees_binaires(seed=42)
    rr = dso.estimer_rr_binaire(df)
    assert abs(rr.rr - 1.790) < 0.01
    assert rr.rr_inf < rr.rr < rr.rr_sup
    assert abs(rr.rr_inf - 1.352) < 0.02 and abs(rr.rr_sup - 2.371) < 0.02
    # le piege encapsule : le contraste marginal n'est PAS le RR
    assert abs(float(rr.estimate.value) - rr.rr) > 0.3


# ---------------------------------------------------------------------------
# (g) E-value dowhy natif + benchmark McGowan-Greevy
# ---------------------------------------------------------------------------
def test_e_value_valeurs_et_formule():
    """E-value ~2.98, exactement RR + sqrt(RR(RR-1)) ; benchmark C ~1.16."""
    df = dso.generer_donnees_binaires(seed=42)
    rr = dso.estimer_rr_binaire(df)
    ev = dso.sensibilite_e_value(rr.model, rr.estimand, rr.estimate)
    assert abs(ev.rr_converti - 1.790) < 0.01
    assert abs(ev.evalue_estime - 2.9796) < 0.01
    assert ev.evalue_ic_limite is not None
    assert abs(ev.evalue_ic_limite - 2.0409) < 0.01
    assert ev.evalue_ic_limite < ev.evalue_estime, "l'IC est plus fragile que l'estime"
    # controle independant : formule fermee de VanderWeele-Ding
    formule = ev.rr_converti + np.sqrt(ev.rr_converti * (ev.rr_converti - 1))
    assert abs(formule - ev.evalue_estime) < 1e-9
    bench = float(ev.benchmarking["observed_covariate_e_value"].iloc[0])
    assert abs(bench - 1.160) < 0.01


def test_verdict_e_value_robuste_relativement_aux_observes():
    df = dso.generer_donnees_binaires(seed=42)
    rr = dso.estimer_rr_binaire(df)
    ev = dso.sensibilite_e_value(rr.model, rr.estimand, rr.estimate)
    v = dso.verdict_e_value(ev)
    assert v["verdict"] == "ROBUSTE_RELATIVEMENT_AUX_OBSERVES"
    assert abs(v["rapport"] - 2.57) < 0.15
    assert "RESULTAT" in v["message"]


# ---------------------------------------------------------------------------
# (h) Bornes de Rosenbaum exactes
# ---------------------------------------------------------------------------
def test_paires_appariees_reproductibles():
    df = dso.generer_donnees_binaires(seed=42)
    d1 = dso.paires_appariees(df, seed=0)
    d2 = dso.paires_appariees(df, seed=0)
    assert (m := len(d1)) == 193
    assert int(d1.sum()) == 122
    np.testing.assert_array_equal(d1, d2)


def test_bornes_rosenbaum_proprietes():
    """Gamma=1 : bornes egales a la p-valeur observee ; la borne haute croit."""
    s, m = 122, 193
    p_bas, p_haut = dso.bornes_rosenbaum(s, m, 1.0)
    assert p_bas == pytest.approx(p_haut)
    assert p_haut == pytest.approx(1.48e-04, rel=0.05)
    precedente = p_haut
    for g in (1.2, 1.5, 2.0, 3.0):
        lo, hi = dso.bornes_rosenbaum(s, m, g)
        assert lo < p_bas, "la borne basse descend avec Gamma"
        assert hi > precedente, "la borne haute monte avec Gamma"
        precedente = hi
    assert dso.bornes_rosenbaum(s, m, 1.0)[0] == pytest.approx(
        dso.bornes_rosenbaum(s, m, 1.0)[1]
    )


def test_gamma_critique_rend_non_significatif():
    s, m = 122, 193
    g = dso.gamma_critique(s, m)
    assert abs(g - 1.332) < 0.01
    # a Gamma*, la borne haute atteint exactement le seuil
    _, p_haut = dso.bornes_rosenbaum(s, m, g)
    assert p_haut == pytest.approx(0.05, abs=1e-6)
    # juste en dessous, l'effet reste significatif dans le pire des mondes
    _, p_haut_avant = dso.bornes_rosenbaum(s, m, g - 0.05)
    assert p_haut_avant < 0.05


def test_bornes_rosenbaum_gamma_invalide():
    with pytest.raises(ValueError):
        dso.bornes_rosenbaum(10, 20, 0.5)


# ---------------------------------------------------------------------------
# (i) Anti-derive : le notebook consomme l'organe
# ---------------------------------------------------------------------------
def _lire_cellule(nb_path: Path, cell_index: int) -> str:
    nb = json.load(open(nb_path, encoding="utf-8"))
    return "".join(nb["cells"][cell_index]["source"])


def test_notebook_cellule_dgp_byte_identique_module():
    """La cellule DGP (index 3) consomme l'organe, sans redefinition locale."""
    src = _lire_cellule(NB_PATH, 3)
    assert "dso.generer_donnees_continues" in src
    g: dict = {"dso": dso}
    exec(compile(src, "<cellule-dgp>", "exec"), g)
    pd.testing.assert_frame_equal(
        g["df_monde"], dso.generer_donnees_continues(n=2000, seed=42)
    )


def test_notebook_cellule_robustesse_consomme_lorgane():
    src = _lire_cellule(NB_PATH, 9)
    assert "dso.robustesse_partielle_r2" in src


def test_notebook_cellule_evalue_consomme_lorgane():
    src = _lire_cellule(NB_PATH, 23)
    assert "dso.sensibilite_e_value" in src
    verdict_src = _lire_cellule(NB_PATH, 25)
    assert "dso.verdict_e_value" in verdict_src


def test_notebook_sans_erreur_volontaire_et_trois_exercices():
    """C.1 : aucun raise/assert/1-0 volontaire ; 3 stubs TODO etudiant."""
    nb = json.load(open(NB_PATH, encoding="utf-8"))
    tout = "\n".join("".join(c["source"]) for c in nb["cells"] if c["cell_type"] == "code")
    assert "raise NotImplementedError" not in tout
    assert "assert False" not in tout
    assert "1/0" not in tout
    assert tout.count("TODO etudiant") >= 3
    # et le notebook execute : toutes les cellules code ont un execution_count
    assert all(
        c.get("execution_count") is not None
        for c in nb["cells"]
        if c["cell_type"] == "code"
    )
