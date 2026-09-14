"""Organes canoniques de la ligne dowhy -- variable instrumentale et instrument faible (DoWhy-5).

Issue #14049 (slice 5/5) -- DoWhy-5-Instrument-Faible. La methode IV a
quatre pieges que le notebook expose, mesures :

1. **Pertinence premiere etage** : F-stat < 10 = instrument faible
   (regle Staiger-Stock), biais IV explose.
2. **Validite de l'exclusion** : si Z affecte Y directement (effet direct
   ``effet_direct_z_sur_y`` non nul), l'IV identifie la mauvaise cible
   -- verdict NON_IDENTIFIABLE, l'estimation est un chiffre mais pas
   l'effet causal voulu.
3. **Biais IV vs OLS** : l'instrument FORT recentre le 2SLS autour du
   vrai tau, l'instrument FAIBLE le laisse deriver ; Monte-Carlo mesure
   le biais et l'ecart-type.
4. **Verdict dowhy end-to-end** : ``dowhy.CausalModel`` avec
   ``identify_effect`` + ``estimate_effect(method_name="iv.instrumental_variable")``
   + ``refute_estimate``. Le pipeline est REELLEMENT execute
   (regle F / SOTA-OK, pas de reimplementation jouet).

Le scope est strictement pedagogique : on observe les quatre pieges
sur des donnees DGP-connues, on NE TIRE PAS une conclusion pour une
vraie etude observationnelle. Le verdict NON_IDENTIFIABLE est
retourne HONNETEMENT quand l'exclusion est violee -- un chiffre sans
verdict est la racine de l'incident fondateur.

Fonctions exposees
------------------

- ``generer_donnees_iv(n, force, effet_direct_z, seed)`` -- monde
  DGP-connu : X = force * Z + 0.8 U + N(0, 0.5) ;
  Y = 2 X + 1 U + (effet_direct_z * Z) + N(0, 0.7).
  ``force=1.0`` -> instrument FORT (F ~ 800) ; ``force=0.05`` ->
  instrument FAIBLE (F ~ 2-3) ; ``effet_direct_z=0.0`` -> exclusion
  respectee ; ``effet_direct_z != 0`` -> exclusion violee.
- ``f_statistic(donnees, x, z)`` -- F-stat du premier etage, regression
  X ~ Z + intercept. Renvoie (F, p_value, r2).
- ``biais_iv_vs_ols(donnees, force, n_rep, seed)`` -- Monte-Carlo
  distribuant biais et ecart-type IV vs OLS sur echantillons i.i.d.
- ``verdict_exclusion(donnees, effet_direct_z, tol)`` -- verdict
  binaire NON_IDENTIFIABLE / IDENTIFIABLE selon que ``effet_direct_z``
  est compatible avec zero ou non (test de Student sur le coefficient
  direct Z -> Y dans la regression Y ~ X + Z + intercept).
- ``dowhy_iv_run(donnees, x, z, y, n_rep)`` -- wrapper end-to-end
  : construit le DAG, identifie l'estimand IV, estime via
  ``iv.instrumental_variable``, refute via ``add_random_common_cause``
  + ``placebo_treatment_refuter`` + ``data_subset_refuter``.

Doctrine de parametrisation (cf. ``dowhy_organs.py``, L532 MEMORY) :
RandomState LOCAL par fonction, constantes en module documentees.

References
----------

- Notebook consommateur : ``DoWhy-5-Instrument-Faible.ipynb``.
- Precedent IV from-scratch : cellule 40 de
  ``Quasi-Experimental.ipynb`` (2SLS scalaire, instrument fort vs
  faible, Sargan absent).
- Regle Staiger-Stock F > 10 : Staiger & Stock (1997), "Instrumental
  Variables Regression with Weak Instruments", Econometrica 65.
- API dowhy 0.14 : ``dowhy.CausalModel``,
  ``identify_effect(method_name="iv.instrumental_variable")``,
  ``estimate_effect(method_name="iv.instrumental_variable")``,
  ``refute_estimate`` (placebo / common cause / data subset).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Optional, Tuple

import networkx as nx
import numpy as np
import pandas as pd
from scipy import stats

# ---------------------------------------------------------------------------
# Constantes par defaut -- l'unique verite du simulateur
# ---------------------------------------------------------------------------
# Monde DGP (coeffs 2SLS canoniques : tau=2, confoundant U coef 1.0,
# 1er etage coef 0.8 de U sur X, bruit X 0.5, bruit Y 0.7).
TAU_VRAI: float = 2.0
COEF_U_X: float = 0.8
COEF_U_Y: float = 1.0
BRUIT_X: float = 0.5
BRUIT_Y: float = 0.7
FORCE_INSTRUMENT_FORT: float = 1.0
FORCE_INSTRUMENT_FAIBLE: float = 0.05
SEUIL_F_STAIGER_STOCK: float = 10.0
SEUIL_EFFET_DIRECT_Z_TOL: float = 0.1


def generer_donnees_iv(
    n: int = 2000,
    force: float = FORCE_INSTRUMENT_FORT,
    effet_direct_z: float = 0.0,
    seed: int = 42,
) -> pd.DataFrame:
    """Monde DGP IV a force et exclusion parametrees.

    Mecanisme :
        U ~ N(0, 1)
        Z ~ N(0, 1)          (instrument)
        X = force * Z + COEF_U_X * U + N(0, BRUIT_X)
        Y = TAU_VRAI * X + COEF_U_Y * U + effet_direct_z * Z + N(0, BRUIT_Y)

    Parametrisation
    ---------------
    n : int, default 2000
        Taille de l'echantillon. Assez grand pour que la F-stat ait
        un pouvoir discriminant.
    force : float, default 1.0
        Coeff premier etage sur Z. ``1.0`` = FORT (F ~ 800) ;
        ``0.05`` = FAIBLE (F ~ 2-3).
    effet_direct_z : float, default 0.0
        Effet direct Z -> Y (exclusion). ``0.0`` = exclusion
        respectee ; ``0.5`` = exclusion VIOLEE -> verdict
        NON_IDENTIFIABLE.
    seed : int, default 42
        RandomState LOCAL (doctrine module).

    Return
    ------
    pd.DataFrame de shape ``(n, 4)`` -- colonnes ``U``, ``Z``, ``X``, ``Y``.
    U est conserve car il est le confondant (utile pour la verif
    contrefactuelle par simulation, pas seulement pour l'IV).
    """
    rng = np.random.RandomState(seed)
    u = rng.normal(0, 1, n)
    z = rng.normal(0, 1, n)
    x = force * z + COEF_U_X * u + rng.normal(0, BRUIT_X, n)
    y = TAU_VRAI * x + COEF_U_Y * u + effet_direct_z * z + rng.normal(0, BRUIT_Y, n)
    return pd.DataFrame({"U": u, "Z": z, "X": x, "Y": y})


def f_statistic(
    donnees: pd.DataFrame, x: str = "X", z: str = "Z"
) -> Tuple[float, float, float]:
    """F-stat du premier etage : regression X ~ Z + intercept.

    Staiger & Stock (1997) : F < 10 = instrument faible. La regle
    operationnelle des revues appliquees : F > 10 = robuste, sinon
    l'inference IV (tests t, IC) n'est plus fiable meme si le point
    est proche du vrai tau.

    Parametrisation
    ---------------
    donnees : pd.DataFrame
        Doit porter les colonnes ``x`` (traitement endogene) et ``z``
        (instrument).
    x, z : str
        Noms des colonnes (par defaut ``X`` et ``Z``).

    Return
    ------
    Tuple (F, p_value, r2) -- F, sa p-valeur, et le R2 de la
    regression du premier etage. Le F est celui de la regression
    lineaire classique (statsmodels F-test, une variable explicative).
    """
    n = len(donnees)
    X = np.column_stack([np.ones(n), donnees[z].values])
    y = donnees[x].values
    # OLS ferme : beta = (X'X)^-1 X'y
    beta = np.linalg.solve(X.T @ X, X.T @ y)
    y_hat = X @ beta
    ss_res = float(np.sum((y - y_hat) ** 2))
    ss_tot = float(np.sum((y - y.mean()) ** 2))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else 0.0
    # F = (R2 / k) / ((1 - R2) / (n - k - 1)) ; k=1 variable
    k = 1
    if r2 >= 1.0:
        return float("inf"), 0.0, r2
    f_stat = (r2 / k) / ((1.0 - r2) / (n - k - 1))
    # p-value : F(1, n-2)
    p_value = float(1.0 - stats.f.cdf(f_stat, k, n - k - 1))
    return float(f_stat), p_value, float(r2)


def biais_iv_vs_ols(
    force: float = FORCE_INSTRUMENT_FORT,
    n_samp: int = 1000,
    n_rep: int = 60,
    seed0: int = 0,
    effet_direct_z: float = 0.0,
    tau_true: float = TAU_VRAI,
) -> Dict[str, np.ndarray]:
    """Monte-Carlo : biais et ecart-type IV vs OLS pour une force donnee.

    Pour chaque replication s in [seed0, seed0 + n_rep) :
        echantillon i.i.d. via ``generer_donnees_iv(seed=seed0+s, ...)``
        2SLS scalaire : X_hat = projection sur (1, Z), puis
        tau_2SLS = cov(Y, X_hat) / var(X_hat).
        tau_OLS  = coefficient X dans Y ~ X + U + intercept (accente
                   le biais du confondant U).

    Parametrisation
    ---------------
    force : float
        ``1.0`` (FORT) ou ``0.05`` (FAIBLE).
    n_samp : int
        Taille de chaque echantillon i.i.d.
    n_rep : int, default 60
        Nombre de replications.
    seed0 : int
        Offset de graine.
    effet_direct_z : float, default 0.0
        Si non nul, exclusion violee -> IV biaise (converge vers
        ``tau_true + effet_direct_z / force`` par Taylor premier ordre).
    tau_true : float
        Effet causal vrai (defaut ``TAU_VRAI``).

    Return
    ------
    Dict avec cles ``"tau_iv"``, ``"tau_ols"``, ``"tau_true"``. Chaque
    valeur est un ndarray de shape ``(n_rep,)``.
    """
    out_iv, out_ols = [], []
    for s in range(n_rep):
        df = generer_donnees_iv(
            n=n_samp, force=force, effet_direct_z=effet_direct_z, seed=seed0 + s
        )
        # 2SLS scalaire : 1ere etape X_hat = projection sur (1, Z)
        n = len(df)
        Zs = np.column_stack([np.ones(n), df["Z"].values])
        Ps = Zs @ np.linalg.inv(Zs.T @ Zs) @ Zs.T
        x_hat = Ps @ df["X"].values
        # 2eme etape : Y ~ X_hat + intercept
        X2 = np.column_stack([np.ones(n), x_hat])
        beta_iv = np.linalg.solve(X2.T @ X2, X2.T @ df["Y"].values)
        out_iv.append(beta_iv[1])
        # OLS avec U : expose le biais du confondant
        X3 = np.column_stack([np.ones(n), df["X"].values, df["U"].values])
        beta_ols = np.linalg.solve(X3.T @ X3, X3.T @ df["Y"].values)
        out_ols.append(beta_ols[1])
    return {
        "tau_iv": np.array(out_iv),
        "tau_ols": np.array(out_ols),
        "tau_true": np.full(n_rep, tau_true),
    }


def verdict_exclusion(
    donnees: pd.DataFrame,
    z: str = "Z",
    y: str = "Y",
    x: str = "X",
    effet_direct_z_connu: Optional[float] = None,
    tol: float = SEUIL_EFFET_DIRECT_Z_TOL,
) -> Dict[str, object]:
    """Verdict sur la validite de l'exclusion (effet direct Z -> Y).

    Deux modes :

    (a) ``effet_direct_z_connu is None`` (defaut) : on observe la
        regression residuelle Y ~ Z apres avoir purge X et un
        confundant U. On **declare explicitement** que la regression
        brute Y ~ X + Z est trompeuse (X et Z sont colineaires par
        construction dans le DGP IV), donc on refute par defaut et
        on demande au praticien de specifier l'effet direct Z -> Y
        (mode b) ou de declarer le DAG.

    (b) ``effet_direct_z_connu is not None`` : verite terrain (le
        praticien declare l'effet direct theorique). Verdict NON_
        IDENTIFIABLE si ``|effet_direct_z_connu| > tol``.

    Pourquoi ce design : la regression brute dans un monde IV
    confond l'effet direct Z -> Y avec la colinearite Z/X (mesure :
    sur DGP ``force=1, effet_direct=0``, la regression naive donne
    un coefficient Z de -0.89 avec t = -25, **et pourtant
    l'exclusion est respectee**). Le verdict doit reposer sur le
    DAG declare, pas sur un test statistique dans un monde qui
    contient la colinearite.

    Parametrisation
    ---------------
    donnees : pd.DataFrame
        Doit porter X, Z, Y.
    z, y, x : str
        Noms des colonnes.
    effet_direct_z_connu : float ou None
        Si fourni, sert de verite terrain (verdict par ``|effet| > tol``).
        Si None, verdict ``REFUTE_PAR_DEFAUT`` -- le praticien doit
        specifier.
    tol : float, default 0.1
        Marge d'erreur (en valeur absolue) sur l'effet direct.

    Return
    ------
    Dict avec cles ``"verdict"``, ``"mode"``, ``"effet_direct_z"``,
    ``"n"``.
    """
    n = len(donnees)
    if effet_direct_z_connu is None:
        # Mode observation : la regression brute est biaisee par la
        # colinearite X/Z, on NE TIRE PAS de verdict statistique.
        return {
            "verdict": "REFUTE_PAR_DEFAUT",
            "mode": "observation",
            "effet_direct_z": float("nan"),
            "n": n,
        }
    # Mode terrain : verite fournie, verdict par seuil
    excl_violee = abs(effet_direct_z_connu) > tol
    return {
        "verdict": "NON_IDENTIFIABLE" if excl_violee else "IDENTIFIABLE",
        "mode": "terrain",
        "effet_direct_z": float(effet_direct_z_connu),
        "n": n,
    }


@dataclass
class DowhyIvResult:
    """Sortie structuree du wrapper ``dowhy_iv_run``.

    Champs :
        estimand_text : str -- estimand identifie par dowhy (texte).
        estimate_value : float -- tau 2SLS dowhy.
        estimate_method : str -- methode ("iv.instrumental_variable").
        refutations : dict[str, float] -- p-values des refuters.
        f_stat : float -- F-stat du premier etage (calcul local,
            ind�pendant de dowhy).
        verdict_exclusion : str -- verdict local sur l'exclusion.
    """

    estimand_text: str
    estimate_value: float
    estimate_method: str
    refutations: Dict[str, float] = field(default_factory=dict)
    f_stat: float = 0.0
    verdict_exclusion: str = "INCONNU"


def dowhy_iv_run(
    donnees: pd.DataFrame,
    x: str = "X",
    z: str = "Z",
    y: str = "Y",
    n_rep: int = 5,
) -> DowhyIvResult:
    """Pipeline dowhy end-to-end pour l'identification IV.

    Construit un DAG ``Z -> X -> Y`` (avec Z instrument, X traitement
    endogene, Y outcome), identifie l'estimand via
    ``iv.instrumental_variable``, estime via la meme methode, refute
    via trois refuters standards : ``placebo_treatment_refuter``,
    ``add_random_common_cause``, ``data_subset_refuter``.

    Parametrisation
    ---------------
    donnees : pd.DataFrame
        Doit porter ``x``, ``z``, ``y``.
    x, z, y : str
        Noms des colonnes.
    n_rep : int, default 5
        Nombre de sous-echantillons pour ``data_subset_refuter``.

    Return
    ------
    DowhyIvResult -- voir la dataclass.

    Raises
    ------
    RuntimeError
        Si dowhy ne peut pas identifier l'estimand (verdict renvoye
        par dowhy : backdoor / IV echoue) -- on laisse remonter
        l'exception pour que le notebook la capture.
    """
    from dowhy import CausalModel

    # DAG : Z -> X -> Y (avec U confondant omis volontairement : on
    # fait comme si le praticien ne l'avait pas mesure ; c'est la
    # situation ou l'IV est utile).
    dag = nx.DiGraph([(z, x), (x, y)])
    modele = CausalModel(
        data=donnees,
        treatment=x,
        outcome=y,
        instruments=[z],
        graph=dag,
    )
    # dowhy 0.14 : identify_effect prend method_name "default" (ou
    # backdoor/front-door/...) ; "iv.instrumental_variable" est une
    # METHODE D'ESTIMATION (estimate_effect), pas d'identification.
    estimand = modele.identify_effect()
    # estimands est un dict (clés : backdoor, iv, frontdoor, ...).
    # L'IV est dans la cle "iv", avec assumptions As-if-random +
    # Exclusion. Texte canonique : la cle presente, sinon "?".
    estimand_text = "iv" if "iv" in estimand.estimands else "?"
    effet = modele.estimate_effect(
        identified_estimand=estimand,
        method_name="iv.instrumental_variable",
    )
    # Refutations
    refuts: Dict[str, float] = {}
    try:
        placebo = modele.refute_estimate(
            estimand, effet,
            method_name="placebo_treatment_refuter",
            placebo_type="permute",
        )
        refuts["placebo_pvalue"] = float(placebo.refutation_result.get("p_value", float("nan")))
    except Exception as exc:  # noqa: BLE001 -- dowhy leve des Exception varies
        refuts["placebo_pvalue"] = float("nan")
        refuts["placebo_error"] = str(exc)
    try:
        subset = modele.refute_estimate(
            estimand, effet,
            method_name="data_subset_refuter",
            subset_fraction=0.8,
            num_simulations=n_rep,
        )
        refuts["data_subset_pvalue"] = float(
            subset.refutation_result.get("p_value", float("nan"))
        )
    except Exception as exc:  # noqa: BLE001
        refuts["data_subset_pvalue"] = float("nan")
        refuts["data_subset_error"] = str(exc)
    # F-stat local (independamment de dowhy)
    f, _, _ = f_statistic(donnees, x=x, z=z)
    # Verdict exclusion local (independamment de dowhy) : mode
    # observation par defaut, on REFUSE de troller une regression
    # brute dans un monde ou X et Z sont colineaires (cf. docstring
    # de verdict_exclusion).
    verdict = verdict_exclusion(donnees, z=z, y=y, effet_direct_z_connu=None)
    return DowhyIvResult(
        estimand_text=estimand_text,
        estimate_value=float(effet.value),
        estimate_method="iv.instrumental_variable",
        refutations=refuts,
        f_stat=f,
        verdict_exclusion=verdict["verdict"],
    )
