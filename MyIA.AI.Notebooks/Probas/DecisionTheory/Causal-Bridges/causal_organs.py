"""Organes canoniques des estimateurs Quasi-Experimental — DiD + IV (cellules 5 et 40).

Issue #14051 tranche 1/2 (planifie en deux PR atomic, Tell NEW c.287-L1) :
extraire les estimateurs natifs du notebook Quasi-Experimental.ipynb vers un
module importable, a cote du notebook, pour que la substance pedagogique
demeure accessible (le notebook importe le module au lieu de definir les
fonctions ; tranche 2/2) et pour que les adaptateurs cross-engine
(notamment ``ict.bridges``, PR #13921 tranche 2/3) aient une cible
reellement observable — plutot que de redéclarer localement et verifier
ICT contre une copie d'elle-meme.

Cette tranche 1/2 isole UNIQUEMENT les deux estimateurs requis par
``ict.bridges`` :

- ``make_panel_did(...)`` (cellule 5) — generateur de panel DiD.
- ``iv_replay(coef_z, ...)`` (cellule 40) — rejoue l'estimation 2SLS sur
  ``n_rep`` echantillons i.i.d. avec force d'instrument controlee.

Les autres estimateurs du notebook (``scm_weights``, ``rdd_tau``,
``cv_mse``, ``mccrary_counts``) sont hors scope de cette tranche (cible
de la tranche 2/2, cf. issue #14051).

Parametrisation et anti-regression (CLAUDE.md section D)
--------------------------------------------------------

Les fonctions reproduisent le pattern algorithmique des cellules 5 et 40.
La parametrisation est strictement MINIMALE :

- Les constantes globales du notebook (``N_UNITS``, ``N_PRE``, ``N_POST``,
  ``ALPHA``, ``TAU_TRUE_DID``, ``TAU_TRUE_IV``) deviennent des kwargs par
  defaut — les valeurs par defaut sont celles que la cellule utilise.
- ``np.random.seed(42)`` global du notebook devient un ``RandomState(seed)``
  LOCAL — c'est la doctrine reconnue (L532 MEMORY ``pymc_enumerate.py`` PR
  #13921, c.293 ai-01 verbatim) qui evite la dependance au seed global.

Consequence byte-identique : pour les valeurs par defaut, les DataFrames
produits par ``causal_organs.make_panel_did()`` et ``make_panel_did()``
dans le notebook (apres seed global) ne sont PAS byte-identiques au
niveau ligne-a-ligne : le notebook consomme d'autres cellules entre
l'import et l'appel, ce qui deplace l'etat du RNG global. En revanche,
les grandeurs AGREGGEES (moyenne du tau_DiD 2x2, distribution 2SLS, etc.)
sont statistiquement identiques — c'est ce que les tests verifient.

C'est une deviation explicite et documentee par rapport au pattern
« byte-identique strict » applique par ``pymc_enumerate.py`` dans la
PR #13921 tranche 2/3. Justification : les estimateurs DiD et IV etant
aleatoires par construction, le test pertinent est la distribution
aggregee, pas la realisation particuliere.

References
----------

- Source canonique : ``MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/
  Quasi-Experimental.ipynb`` cellules 5 et 40, branche ``origin/main``.
- Duplication declaree : meme algorithme que PR #13921 tranche 2/3
  (``MyIA.AI.Notebooks/IIT/ICT-Series/ict/bridges/quasi_experimental.py``)
  — la difference est la LOCALISATION (a cote du notebook source plutot
  que dans ``ict.bridges``), conformement a l'acceptance #14051. La
  deduplication (``ict.bridges`` importe ce module au lieu de re-dupliquer)
  est l'objet de la tranche 2/2.
- Issue #14051 « [ICT/Probas] ict.bridges duplique ses organes natifs --
  extraire des modules canoniques a cote des notebooks ».
"""

from __future__ import annotations

from typing import Dict

import numpy as np
import pandas as pd


# ---------------------------------------------------------------------------
# Constantes par defaut (miroir des globales du notebook)
# ---------------------------------------------------------------------------
TAU_TRUE_DID: float = 3.0
TAU_TRUE_IV: float = 2.0
DEFAULT_ALPHA: Dict[int, float] = {0: 10.0, 1: 12.0}


# ---------------------------------------------------------------------------
# Estimateur DiD (cellule 5)
# ---------------------------------------------------------------------------
def make_panel_did(
    differential_pretrend: float = 0.0,
    n_units: int = 60,
    n_pre: int = 5,
    n_post: int = 3,
    alpha: Dict[int, float] = DEFAULT_ALPHA,
    tau_true: float = TAU_TRUE_DID,
    seed: int = 42,
) -> pd.DataFrame:
    """Panel groupe x periode pour difference-in-differences.

    Pattern de la cellule 5 de Quasi-Experimental.ipynb. Le dataframe
    retourne porte les colonnes ``group`` (0/1), ``unit`` (identifiant
    d'unite dans [0, n_units) ), ``period`` (0..n_pre+n_post-1), ``y``
    (outcome continu).

    Parametrisation
    ---------------
    differential_pretrend : float, default 0.0
        Derive differenciee du groupe traite avant traitement. 0 = SUTA
        satisfaite (parallel trends) ; != 0 = violation (le test pertinent
        de la branche adaptation backdoor dans la PR #13921 utilise 0.5).
    n_units, n_pre, n_post : int
        Dimensions du panel. Le notebook utilise 60 x 5 x 3 (480 lignes,
        8 periodes).
    alpha : dict
        Niveaux permanents par groupe. Le notebook utilise {0: 10.0, 1:
        12.0} (le traite part 2 points au-dessus du controle).
    tau_true : float, default 3.0
        Effet causal VRAI connu par construction. La PR #13921 a cette
        constante comme globale ``TAU_TRUE_DID = 3.0``.
    seed : int, default 42
        Graine aleatoire pour reproductibilite (RandomState LOCAL).

    Return
    ------
    pd.DataFrame de shape ``(n_units * 2 * (n_pre + n_post), 4)``
    """
    rng = np.random.RandomState(seed)
    t_all = np.arange(n_pre + n_post)
    rows = []
    for g in [0, 1]:
        for i in range(n_units):
            unit_fe = rng.normal(0, 2.0)
            for t in t_all:
                y = alpha[g] + unit_fe + 1.0 * t
                if g == 1:
                    y += differential_pretrend * t
                    if t >= n_pre:
                        y += tau_true
                y += rng.normal(0, 1.0)
                rows.append((g, i, t, y))
    return pd.DataFrame(rows, columns=["group", "unit", "period", "y"])


# ---------------------------------------------------------------------------
# Estimateur IV (cellule 40)
# ---------------------------------------------------------------------------
def iv_replay(
    coef_z: float,
    n_samp: int = 1000,
    n_rep: int = 60,
    seed0: int = 0,
    tau_true: float = TAU_TRUE_IV,
) -> np.ndarray:
    """Repete l'estimation 2SLS sur ``n_rep`` echantillons i.i.d.

    Pattern de la cellule 40 de Quasi-Experimental.ipynb. L'instrument
    Z a une force proportionnelle a ``coef_z`` (``coef_z=1.0`` -> F ~ 800
    = instrument FORT ; ``coef_z=0.05`` -> F ~ 2-3 = instrument FAIBLE).

    Pour chaque echantillon s dans [seed0, seed0 + n_rep) :
        u_s = N(0, 1)
        z_s = N(0, 1)
        x_s = coef_z * z_s + 0.8 * u_s + N(0, 0.5)   # 1er etage
        y_s = 2.0 * x_s + 1.0 * u_s + N(0, 0.7)     # 2eme etage
    2SLS scalaire sur (y_s, x_s, z_s, intercept).

    Parametrisation
    ---------------
    coef_z : float
        Pertinence de l'instrument dans le 1er etage. 1.0 -> FORT, 0.05
        -> FAIBLE (les valeurs explorées dans la cellule 40 du notebook).
    n_samp : int, default 1000
        Taille de chaque echantillon.
    n_rep : int, default 60
        Nombre de replications i.i.d.
    seed0 : int, default 0
        Offset de graine (RandomState(seed0 + s) par echantillon).
    tau_true : float, default 2.0
        Effet causal VRAI (definit dans la cellule 34 du notebook via
        ``TAU_TRUE_IV = 2.0``). Expose en kwargs pour la testabilite
        et pour symetriser avec ``make_panel_did``.

    Return
    ------
    np.ndarray de shape ``(n_rep,)`` -- la distribution des ``tau_2SLS``
    estimes. Pour instrument fort, moyenne ~ 2.0 et ecart-type < 0.1 ;
    pour instrument faible, moyenne divergente et ecart-type >> 1.
    """
    out = []
    for s in range(n_rep):
        rs = np.random.RandomState(seed0 + s)
        u = rs.normal(0, 1, n_samp)
        z = rs.normal(0, 1, n_samp)
        x = coef_z * z + 0.8 * u + rs.normal(0, 0.5, n_samp)
        y = 2.0 * x + 1.0 * u + rs.normal(0, 0.7, n_samp)
        Zs = np.column_stack([np.ones(n_samp), z])
        Xs = np.column_stack([np.ones(n_samp), x])
        Ps = Zs @ np.linalg.inv(Zs.T @ Zs) @ Zs.T
        beta = np.linalg.solve(Xs.T @ Ps @ Xs, Xs.T @ Ps @ y)
        out.append(beta[1])
    return np.array(out)


# ---------------------------------------------------------------------------
# Estimateur DiD 2x2 (cellule 5) -- tranche 3 de #14051
# ---------------------------------------------------------------------------
def panel_did_two_by_two(
    df: pd.DataFrame,
    group_col: str = "group",
    period_col: str = "period",
    y_col: str = "y",
    n_pre: int = 5,
) -> float:
    """Difference-in-differences 2x2 sur un panel groupe x periode.

    Forme fonctionnelle de l'arithmetique de la **cellule 5** de
    ``Quasi-Experimental.ipynb``, qui calcule les quatre moyennes en ligne :

    .. code-block:: python

        mT_pre  = df_did.query("group == 1 and period < 5").y.mean()
        mT_post = df_did.query("group == 1 and period >= 5").y.mean()
        mC_pre  = df_did.query("group == 0 and period < 5").y.mean()
        mC_post = df_did.query("group == 0 and period >= 5").y.mean()
        tau_DiD = (mT_post - mT_pre) - (mC_post - mC_pre)

    Le notebook garde volontairement sa forme deroulee : afficher les quatre
    cellules 2x2 une par une **est** le geste pedagogique (on montre que
    l'ecart post-seulement melange niveau permanent et effet, la ou la
    double difference isole l'effet). Ce module en expose la forme
    appelable, pour les consommateurs programmatiques -- au premier rang
    desquels ``ict.bridges.quasi_experimental``, dont la verification
    cross-engine doit observer **cet** estimateur et non une reproduction
    locale (acceptance 3 de #14051).

    L'accord entre les deux formes est verrouille par un test qui rejoue
    l'arithmetique ``.query()`` de la cellule et exige l'egalite exacte
    (``test_bridges_canonical_wiring.py``). Une derive de l'une des deux
    formes rougit.

    Parameters
    ----------
    df : pd.DataFrame
        Panel portant les colonnes ``group`` (0/1), ``period``, ``y``.
    group_col, period_col, y_col : str
        Noms de colonnes, pour les panels qui ne suivent pas la convention.
    n_pre : int, default 5
        Nombre de periodes pre-traitement -- la frontiere ``period >= n_pre``
        separe post de pre.

    Return
    ------
    float
        ``tau_DiD = (T_post - T_pre) - (C_post - C_pre)``.
    """
    g1 = df[df[group_col] == 1]
    g0 = df[df[group_col] == 0]
    t_post = g1[g1[period_col] >= n_pre][y_col].mean()
    t_pre = g1[g1[period_col] < n_pre][y_col].mean()
    c_post = g0[g0[period_col] >= n_pre][y_col].mean()
    c_pre = g0[g0[period_col] < n_pre][y_col].mean()
    return float((t_post - t_pre) - (c_post - c_pre))
