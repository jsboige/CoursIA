"""Tests pytest pour dowhy_organs.py -- slice 1/4 #14049 (DoWhy-2-Contrefactuel-Individuel).

Issue #14049 §1 acceptance : « ...chaque notebook de la serie DoWhy expose
un organe importable des sa livraison, et les tests verifient la sortie du
module contre la valeur attendue ».

Strategie de test (meme convention que test_causal_organs.py) : on
**execute reellement** le SCM dowhy-gcm (pas de mock, H.1) et on verifie
que :

(a) les formes DataFrame / Series retournees correspondent aux dimensions
    consommees par le notebook ;
(b) le monde generatif repond aux trois nombres du notebook : pente naive
    confondue > 2, specification bien posee (interaction) ~ 3.0, ATE vrai 0
    cache dans une CATE(v) = 3v ;
(c) la boucle row-wise redonne l'effet individuel : ecart positif pour
    V > 0, negatif pour V < 0, |ecart| moyen net > 0 ; le mecanisme
    LINEAIRE ecrase le contrefactuel (fragilite du notebook) ;
(d) reproductibilite par seed LOCAL -- deux appels retournent la meme
    sortie (doctrine RandomState, cf. docstring du module).

Les tolérances sont larges : l'estimation est Monte-Carlo avec un seed
unique, le test pertinent est « ordre de grandeur et signe corrects ».
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

import dowhy_organs as do


def _pente_naive(df):
    """Pente OLS de Y ~ T (estimateur confondu du notebook)."""
    return float(np.polyfit(df["T"], df["Y"], 1)[0])


def _individus_extremes(df):
    """Les deux individus traites aux V extremes (les deux etoiles du notebook)."""
    traites = df[df["T"] > 0.6]
    idx_hi = int(traites["V"].idxmax())
    idx_lo = int(traites["V"].idxmin())
    return idx_hi, idx_lo


# ---------------------------------------------------------------------------
# generer_donnees
# ---------------------------------------------------------------------------
def test_generer_donnees_shape():
    """Dimensions par defaut : n=600 x 3 colonnes (V, T, Y)."""
    df = do.generer_donnees()
    assert isinstance(df, pd.DataFrame)
    assert df.shape == (600, 3)
    assert list(df.columns) == ["V", "T", "Y"]


def test_generer_donnees_seed_reproductible():
    """RandomState LOCAL -> deux appels avec meme seed retournent la meme DataFrame."""
    df_a = do.generer_donnees(seed=42)
    df_b = do.generer_donnees(seed=42)
    pd.testing.assert_frame_equal(df_a, df_b)


def test_generer_donnees_naive_confoundee():
    """La pente naive Y ~ T est confondue : > 2, alors que l'ATE vrai est 0.

    C'est le premier nombre du notebook : le confondant V -> {T, Y} gonfle
    la regression simple (0.3 * 3 = +0.9 de covariance + borne).
    """
    df = do.generer_donnees()
    pente = _pente_naive(df)
    assert pente > 2.0, f"pente naive {pente:.3f} attendue confondue (trap du notebook)"


def test_generer_donnees_specification_bien_posee():
    """Y ~ 1 + T + V + T:V avec interaction : coefficient T:V ~ 3.0, T ~ 0.

    Le notebook montre qu'une specification qui CONNAIT la forme (rung 1)
    recupere la mecanique ; c'est la verification de coherence du DGP.
    """
    df = do.generer_donnees()
    X = np.column_stack([np.ones(len(df)), df["T"], df["V"], df["T"] * df["V"]])
    beta = np.linalg.lstsq(X, df["Y"].values, rcond=None)[0]
    _, b_t, b_v, b_tv = beta
    assert abs(b_tv - do.BETA_INTERACTION) < 0.5, f"T:V {b_tv:.3f} ~ 3.0 attendu"
    assert abs(b_t) < 0.5, f"T direct {b_t:.3f} ~ 0 attendu"
    assert abs(b_v - do.COEF_V_Y) < 0.5, f"V direct {b_v:.3f} ~ 0.5 attendu"


# ---------------------------------------------------------------------------
# construire_scm + contrefactuel_individuel
# ---------------------------------------------------------------------------
def test_construire_scm_fit_sans_erreur():
    """Le SCM inversible se fitte sur le monde generatif (reellement, H.1)."""
    df = do.generer_donnees()
    scm = do.construire_scm(df, degre_y=2)
    assert scm is not None


def test_contrefactuel_individuel_shape():
    """Un contrefactuel pour UNE ligne retourne un DataFrame (1, 3)."""
    df = do.generer_donnees()
    scm = do.construire_scm(df, degre_y=2)
    idx_hi, _ = _individus_extremes(df)
    cf = do.contrefactuel_individuel(scm, df.loc[idx_hi])
    assert isinstance(cf, pd.DataFrame)
    assert cf.shape == (1, 3)
    assert list(cf.columns) == ["V", "T", "Y"]
    # l'intervention T:=0 est bien visible DANS la sortie
    assert abs(float(cf["T"].iloc[0])) < 1e-9


def test_contrefactuel_individuel_recupere_la_cate():
    """V > 0 : Y_0 < Y_obs (le traitement a aide) ; V < 0 : Y_0 > Y_obs (il a nui).

    C'est le deuxieme nombre du notebook : les deux etoiles +3.35 / -1.61.
    Seuil conservateur (2.0) pour le V positif, signe seul pour le negatif.
    """
    df = do.generer_donnees()
    scm = do.construire_scm(df, degre_y=2)
    idx_hi, idx_lo = _individus_extremes(df)
    cf_hi = do.contrefactuel_individuel(scm, df.loc[idx_hi])
    ecart_hi = float(df.loc[idx_hi, "Y"]) - float(cf_hi["Y"].iloc[0])
    assert ecart_hi > 2.0, f"V>0 : ecart {ecart_hi:+.3f} attendu > +2.0"
    cf_lo = do.contrefactuel_individuel(scm, df.loc[idx_lo])
    ecart_lo = float(df.loc[idx_lo, "Y"]) - float(cf_lo["Y"].iloc[0])
    assert ecart_lo < -1.0, f"V<0 : ecart {ecart_lo:+.3f} attendu < -1.0"


def test_ecarts_contrefactuels_boucle_row_wise():
    """La decomposition boucle par individu : |ecart| moyen net > 0.5 et
    variance reelle (std > 0.5) sur un sous-echantillon de 60 lignes.
    """
    df = do.generer_donnees()
    scm = do.construire_scm(df, degre_y=2)
    ec = do.ecarts_contrefactuels(scm, df.iloc[:60])
    assert isinstance(ec, pd.Series)
    assert len(ec) == 60
    assert ec.abs().mean() > 0.5, f"|ecart| moyen {ec.abs().mean():.3f} attendu net"
    assert ec.std() > 0.5, f"dispersion {ec.std():.3f} attendue reelle"


def test_mecanisme_lineaire_ecrase_le_contrefactuel():
    """degre_y=1 (lineaire) ne capte pas l'interaction : l'ecart du V positif
    s'effondre par rapport au poly2 -- la demonstration de fragilite.
    """
    df = do.generer_donnees()
    scm_poly = do.construire_scm(df, degre_y=2)
    scm_lin = do.construire_scm(df, degre_y=1)
    idx_hi, _ = _individus_extremes(df)
    ecart_poly = float(df.loc[idx_hi, "Y"]) - float(
        do.contrefactuel_individuel(scm_poly, df.loc[idx_hi])["Y"].iloc[0]
    )
    ecart_lin = float(df.loc[idx_hi, "Y"]) - float(
        do.contrefactuel_individuel(scm_lin, df.loc[idx_hi])["Y"].iloc[0]
    )
    assert abs(ecart_lin) < abs(ecart_poly) / 2, (
        f"lineaire {ecart_lin:+.3f} doit ecraser poly2 {ecart_poly:+.3f}"
    )