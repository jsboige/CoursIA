"""Organes canoniques de la ligne causal-fairness (Causal-Fairness).

Ce module expose l'API importable du notebook Causal-Fairness : le monde
génératif (SCM d'embauche à attribut protégé), la batterie de mesures
d'équité de la famille TV (Plecko-Bareinboim, FnT R-90, ch. 3-4) et la
règle des 80 % (EEOC four-fifths rule) pour le disparate impact concret.
Même convention que ``dowhy_organs.py`` : le notebook consomme l'organe,
un tiers peut l'appeler sans recopier (leçon #13921).

Fonctions exposées
------------------

- ``generer_monde(n, seed)`` -- SCM embauche linéaire-gaussien :
  Z (SES, exogène) -> A (attribut protégé, binaire via sigmoïde),
  Z -> W, Z -> Y, A -> W, A -> Y, W -> Y. Retourne le DataFrame **avec
  les bruits** (``epsW``, ``epsY``) : le SCM étant connu, l'abduction
  est triviale et les contrefactuels imbriqués (Y_{x1,W_x0}) se
  calculent en réutilisant les mêmes bruits.
- ``contrefactuel(df, a, w_valeur)`` -- Y sous A := a et W figé à
  ``w_valeur`` (si ``None``, W suit le SCM sous do(A=a)).
- ``mesures_equite(df)`` -- dict des six mesures (TV, TE, NDE, NIE,
  Exp-SE_1, Exp-SE_0) + les résidus des deux identités (Lem 4.1 et
  Thm 4.2), exacts à la précision machine sur données simulées.
- ``regle_80(df, colonne_groupe, colonne_decision, defavorise, ...)`` --
  ratio du taux favorable du groupe défavorisé sur celui du groupe de
  référence et verdict EEOC (seuil 0.8).

Théorie du monde (identités linéaires vérifiées à ~1e-16 en N grand) :
TE = BETA_AY + BETA_WY * BETA_AW = 0.5 ; NDE = BETA_AY = 0.3 ;
NIE (Eq. 4.8 de R-90, orientation P(y_{x1,W_x0}) - P(y_{x1})) = -0.2 ;
TV = TE + (Exp-SE_1 - Exp-SE_0) (Lem 4.1) = NDE - NIE + (Exp-SE_1 -
Exp-SE_0) (Thm 4.2).

Doctrine de paramétrisation (cf. ``causal_organs.py``) : RandomState
local par fonction, jamais de dépendance au seed global ; les constantes
du monde vivent en constantes de module documentées.

Références
----------
Plecko & Bareinboim, *Causal Fairness Analysis*, Foundations and Trends
in Machine Learning R-90, 2024 -- ch. 3 (critères structurels), ch. 4
(famille TV, Lem 4.1, Thm 4.2, déf. 4.7-4.8).
"""

from __future__ import annotations

import numpy as np
import pandas as pd

# --- Constantes du monde générateur (théorie : cf. docstring module) ---
PENTE_ZA = 0.9   # Z -> A (logistique) : la ségrégation résidentielle sélectionne A
BETA_AW = 0.5    # A -> W : l'attribut influence le score de formation
BETA_ZW = 0.6    # Z -> W
BETA_AY = 0.3    # A -> Y : discrimination DIRECTE du score d'embauche
BETA_WY = 0.4    # W -> Y : le score de formation est récompensé
BETA_ZY = 0.2    # Z -> Y

TE_THEORIQUE = BETA_AY + BETA_WY * BETA_AW     # 0.50
NDE_THEORIQUE = BETA_AY                        # 0.30
NIE_THEORIQUE = -(BETA_WY * BETA_AW)           # -0.20 (Eq. 4.8)


def generer_monde(n: int, seed: int = 42) -> pd.DataFrame:
    """Simule le SCM d'embauche et retourne Z, A, W, Y + les bruits.

    A ~ Bern(sigmoïde(PENTE_ZA * Z)) : l'attribut protégé n'est pas
    assigné au hasard -- Z (SES) le sélectionne. C'est ce chemin
    Z -> A qui rend le naïf observationnel (TV) biaisé.
    """
    rng = np.random.default_rng(seed)
    Z = rng.normal(0.0, 1.0, n)
    p_A = 1.0 / (1.0 + np.exp(-PENTE_ZA * Z))
    A = (rng.uniform(0.0, 1.0, n) < p_A).astype(float)
    epsW = rng.normal(0.0, 1.0, n)
    epsY = rng.normal(0.0, 1.0, n)
    W = BETA_AW * A + BETA_ZW * Z + epsW
    Y = BETA_AY * A + BETA_WY * W + BETA_ZY * Z + epsY
    return pd.DataFrame({"Z": Z, "A": A, "W": W, "Y": Y,
                         "epsW": epsW, "epsY": epsY})


def w_sous_intervention(df: pd.DataFrame, a: float) -> np.ndarray:
    """W_x : le médiateur sous do(A=a), mêmes Z et bruits."""
    return BETA_AW * a + BETA_ZW * df["Z"].to_numpy() + df["epsW"].to_numpy()


def y_sous_intervention(df: pd.DataFrame, a: float, w: np.ndarray | None = None) -> np.ndarray:
    """Y_{x,W} : le score sous A := a et W figé à ``w`` (si None : W naturel sous do(A=a))."""
    if w is None:
        w = w_sous_intervention(df, a)
    Z = df["Z"].to_numpy()
    return BETA_AY * a + BETA_WY * w + BETA_ZY * Z + df["epsY"].to_numpy()


def mesures_equite(df: pd.DataFrame) -> dict[str, float]:
    """Les six mesures de la famille TV + les résidus des deux identités.

    TV (observationnel) : E[Y|A=1] - E[Y|A=0] sur le monde factuel.
    TE, NDE, NIE, Exp-SE_x : contrefactuels à bruits partagés
    (abduction triviale -- le générateur est connu).
    """
    A = df["A"].to_numpy()
    # Y factuel : A tel qu'observé, W tel qu'observé
    Y_fact = BETA_AY * A + BETA_WY * df["W"].to_numpy() + BETA_ZY * df["Z"].to_numpy() + df["epsY"].to_numpy()

    Y0 = y_sous_intervention(df, 0.0)               # Y_{x0}
    Y1 = y_sous_intervention(df, 1.0)               # Y_{x1}
    W0 = w_sous_intervention(df, 0.0)               # W_{x0}
    Y1_W0 = y_sous_intervention(df, 1.0, W0)        # Y_{x1, W_x0} (imbriqué)

    tv = float(Y_fact[A == 1].mean() - Y_fact[A == 0].mean())
    te = float(Y1.mean() - Y0.mean())
    exp_se1 = float(Y1[A == 1].mean() - Y1.mean())
    exp_se0 = float(Y0[A == 0].mean() - Y0.mean())
    nde = float(Y1_W0.mean() - Y0.mean())           # Eq. 4.7
    nie = float(Y1_W0.mean() - Y1.mean())           # Eq. 4.8

    return {
        "TV": tv,
        "TE": te,
        "ExpSE1": exp_se1,
        "ExpSE0": exp_se0,
        "NDE": nde,
        "NIE": nie,
        "residu_lemme_4_1": abs(tv - (te + exp_se1 - exp_se0)),
        "residu_thm_4_2": abs(tv - (nde - nie + exp_se1 - exp_se0)),
    }


def regle_80(df: pd.DataFrame, colonne_groupe: str, colonne_decision: str,
             defavorise, reference=None, seuil: float = 0.8) -> dict:
    """Règle des 80 % (EEOC four-fifths rule) sur un tableau croisé.

    Compare le taux de décision favorable du groupe ``defavorise`` à
    celui du groupe ``reference`` (si None : l'autre modalité). Le
    rapport < 0.8 signale un disparate impact selon le guide EEOC --
    un signal statistique de dépistage, PAS un verdict juridique.
    """
    modalites = df[colonne_groupe].astype(str)
    if reference is None:
        autres = [m for m in modalites.unique() if m != str(defavorise)]
        reference = autres[0] if len(autres) == 1 else "/".join(sorted(autres))
        masque_ref = modalites != str(defavorise)
    else:
        masque_ref = modalites == str(reference)
    taux_def = float(df.loc[modalites == str(defavorise), colonne_decision].mean())
    taux_ref = float(df.loc[masque_ref, colonne_decision].mean())
    ratio = taux_def / taux_ref if taux_ref > 0 else float("inf")
    return {
        "taux_defavorise": taux_def,
        "taux_reference": taux_ref,
        "ratio": ratio,
        "seuil": seuil,
        "disparate_impact": ratio < seuil,
    }
