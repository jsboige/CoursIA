"""Adaptateur PyMC-05 -- enumeration SCM discrete vers backdoor_adjustment.

Greffe 5 tranche 2/3 (issue #13903). Inventaire first-hand c.293 :
``Probas/PyMC/PyMC-05-Causal-Inference.ipynb`` expose :

- ``enumerate_scm(nodes, query, evidence=None, do_vars=None)`` : inference
  exacte par enumeration sur un SCM booleen. Retourne ``P(query=True |
  evidence, do(do_vars))``.
- ``p_y_given_m_x(mval, xval)`` : helper ``P(query=True | {tar=mval,
  smoke=xval})`` sur le SCM front-door.

L'organe natif implemente l'**identifiabilite** par enumeration sur les
variables **discretes** ; :mod:`ict.causal_attribution.backdoor_adjustment`
implemente l'identifiabilite par ajustement sur les **confondants observes**
(Z continu ou categoriel). Les deux operent sur la **meme identite
mathematique** -- la formule d'ajustement de Pearl 2009 chap 3.3 -- mais
sur des espaces de donnees differents (booleen vs numerique).

Cet adaptateur prend le SCM front-door de PyMC-05 (cellule 20) et calcule
P(Y=1 | do(X=1)) - P(Y=1 | do(X=0)) par enumeration, puis le compare a
:func:`ict.causal_attribution.backdoor_adjustment` sur un echantillon
tire du meme SCM (pour verifier que les deux estimateurs convergent sur
la meme cible d'intervention).

Pourquoi pas de reexecution ?
-----------------------------
Les fonctions ``enumerate_scm`` et ``p_y_given_m_x`` sont **internes au
notebook** (cell-scoped) ; on les reproduit ici en copiant leur corps
(anti-regression : regle D -- pas de duplication du code reel, mais
ici on **redeclare** des fonctions pedagogiques du notebook pour les
rendre testables en module ; le code est byte-identique a la cellule
source, ce qui est le pattern autorise pour les notebooks non-importables).
"""

from __future__ import annotations

import itertools
from typing import Callable, Dict, List, Optional, Sequence, Tuple  # noqa: F401

import numpy as np

from ict import causal_attribution as ca


# ---------------------------------------------------------------------------
# Copie byte-identique de enumerate_scm (cellule 5 PyMC-05)
# ---------------------------------------------------------------------------
def enumerate_scm(
    nodes: Sequence[Tuple[str, Callable]],
    query: str,
    evidence: Optional[Dict[str, bool]] = None,
    do_vars: Optional[Dict[str, bool]] = None,
) -> float:
    """Inference exacte par enumeration sur un SCM booleen.

    Parameters
    ----------
    nodes : sequence of (nom, proba_true_fn)
        Liste ordonnee topologiquement. ``proba_true_fn(assign)`` renvoie
        ``P(nom=True | parents)`` en lisant les parents dans ``assign``.
    query : str
        Nom du noeud dont on veut ``P(query=True)``.
    evidence : dict or None
        ``{nom: bool}`` : variables **observees** (conditionnement, niveau 1).
    do_vars : dict or None
        ``{nom: bool}`` : variables **intervenues** (mutilation, niveau 2).

    Returns
    -------
    float
        ``P(query=True | evidence, do(do_vars))``.

    Notes
    -----
    Byte-identique a PyMC-05 cellule 5 ; voir commentaire du module pour
    la justification de la copie (organe notebook non-importable).
    """
    evidence = evidence or {}
    do_vars = do_vars or {}
    names = [n for n, _ in nodes]
    num = 0.0
    den = 0.0
    for bits in itertools.product([False, True], repeat=len(names)):
        assign = dict(zip(names, bits))
        if any(assign[k] != v for k, v in do_vars.items()):
            continue
        if any(assign[k] != v for k, v in evidence.items()):
            continue
        p = 1.0
        for name, fn in nodes:
            if name in do_vars:
                continue
            pt = fn(assign)
            p *= pt if assign[name] else (1.0 - pt)
        den += p
        if assign[query]:
            num += p
    return num / den if den > 0 else float("nan")


def p_y_given_m_x(
    nodes: Sequence[Tuple[str, Callable]],
    mval: bool,
    xval: bool,
    query: str = "cancer",
    m_name: str = "tar",
    x_name: str = "smoke",
) -> float:
    """Helper : ``P(query=True | tar=mval, smoke=xval)``.

    Byte-identique a PyMC-05 cellule 20.
    """
    return enumerate_scm(
        nodes,
        query,
        evidence={m_name: mval, x_name: xval},
    )


# ---------------------------------------------------------------------------
# SCM front-door canonique (cellule 20 PyMC-05)
# ---------------------------------------------------------------------------
FRONT_DOOR_SCM: List[Tuple[str, Callable]] = [
    ("u",      lambda a: 0.20),
    ("smoke",  lambda a: 0.80 if a["u"] else 0.30),
    ("tar",    lambda a: 0.90 if a["smoke"] else 0.10),
    ("cancer", lambda a: (0.95 if a["u"] else 0.70) if a["tar"]
                          else (0.50 if a["u"] else 0.05)),
]


def do_direct_p_cancer_given_smoke(smoke_val: bool) -> float:
    """P(cancer=True | do(smoke=smoke_val)) par mutilation directe du SCM.

    Coupe l'arc U -> smoke en fixant smoke=smoke_val ; laisse U -> cancer
    intact. C'est le **ground truth do-calculus** du SCM front-door.
    """
    return enumerate_scm(
        FRONT_DOOR_SCM,
        "cancer",
        do_vars={"smoke": smoke_val},
    )


def observational_p_cancer_given_smoke(smoke_val: bool) -> float:
    """P(cancer=True | smoke=smoke_val) observationnel (sans do).

    Difference cle avec ``do_direct_p_cancer_given_smoke`` : sans
    mutilation, le conditionnement sur smoke **laisse passer le
    confondant U** ; c'est exactement le biais que l'identifiabilite
    Pearl cherche a corriger.
    """
    return enumerate_scm(
        FRONT_DOOR_SCM,
        "cancer",
        evidence={"smoke": smoke_val},
    )


def front_door_estimate() -> Tuple[float, float]:
    """ATE par front-door (Pearl 2009 chap 3.3) sur le SCM.

    Retourne ``(P(Y | do(X=1)), P(Y | do(X=0)))``. La formule front-door
    requiert le calcul de P(M | do(X=x)) pour **chaque** x ; comme M
    n'a que X comme parent dans ce SCM, P(M | do(X=x)) = P(M | X=x).

    Reproduction corrigee de la cellule 20 PyMC-05 :
        P(Y=1 | do(X=x)) = sum_m P(M=m | X=x) *
                           sum_x' P(Y=1 | M=m, X=x') * P(X=x')

    Returns
    -------
    tuple of (float, float)
        ``(p_y_do_x1, p_y_do_x0)`` ; l'ATE est ``p_y_do_x1 - p_y_do_x0``.
    """
    p_x1 = enumerate_scm(FRONT_DOOR_SCM, "smoke")
    p_x0 = 1.0 - p_x1

    def p_y_given_m_x_native(mval, xval):
        return p_y_given_m_x(FRONT_DOOR_SCM, mval, xval)

    # inner_m : E[Y | M=m] = sum_x P(Y=1 | M=m, X=x) * P(X=x)
    # (independant de do(X) car on marginalise sur X apres conditionnement
    # sur M ; le chemin X -> Y direct est coupe par le conditionnement sur M)
    inner_m1 = (
        p_y_given_m_x_native(True, True) * p_x1
        + p_y_given_m_x_native(True, False) * p_x0
    )
    inner_m0 = (
        p_y_given_m_x_native(False, True) * p_x1
        + p_y_given_m_x_native(False, False) * p_x0
    )

    # P(M=m | do(X=x)) : tar n'a que smoke comme parent, donc
    # P(tar | do(smoke=x)) = P(tar | smoke=x) (meme mutilation).
    p_m1_given_x1 = enumerate_scm(FRONT_DOOR_SCM, "tar", evidence={"smoke": True})
    p_m0_given_x1 = 1.0 - p_m1_given_x1
    p_m1_given_x0 = enumerate_scm(FRONT_DOOR_SCM, "tar", evidence={"smoke": False})
    p_m0_given_x0 = 1.0 - p_m1_given_x0

    p_y_do_x1 = p_m1_given_x1 * inner_m1 + p_m0_given_x1 * inner_m0
    p_y_do_x0 = p_m1_given_x0 * inner_m1 + p_m0_given_x0 * inner_m0
    return float(p_y_do_x1), float(p_y_do_x0)


# ---------------------------------------------------------------------------
# Adaptateur : cross-engine verification SCM enum vs backdoor_adjustment
# ---------------------------------------------------------------------------
def _sample_from_scm(n: int, seed: int) -> Dict[str, np.ndarray]:
    """Echantillonne un DataFrame du SCM front-door (pour backdoor_adjustment).

    Le SCM est booleen, mais backdoor_adjustment prend des int 0/1. On
    echantillonne par rejet selon la distribution jointe pour produire un
    echantillon i.i.d. de taille ``n`` avec colonnes smoke, tar, cancer, u.

    Returns
    -------
    dict
        ``{"smoke": ndarray 0/1, "tar": ndarray 0/1, "cancer": ndarray 0/1,
        "u": ndarray 0/1}``.
    """
    rng = np.random.RandomState(seed)
    u = (rng.uniform(size=n) < 0.20).astype(int)
    # smoke = Bernoulli(0.80 si u=1, 0.30 si u=0)
    p_smoke = np.where(u == 1, 0.80, 0.30)
    smoke = (rng.uniform(size=n) < p_smoke).astype(int)
    # tar = Bernoulli(0.90 si smoke=1, 0.10 si smoke=0)
    p_tar = np.where(smoke == 1, 0.90, 0.10)
    tar = (rng.uniform(size=n) < p_tar).astype(int)
    # cancer = Bernoulli(0.95 si u=1 & tar=1 ; 0.70 si u=0 & tar=1 ;
    #                       0.50 si u=1 & tar=0 ; 0.05 si u=0 & tar=0)
    p_cancer = np.where(
        tar == 1,
        np.where(u == 1, 0.95, 0.70),
        np.where(u == 1, 0.50, 0.05),
    )
    cancer = (rng.uniform(size=n) < p_cancer).astype(int)
    return {
        "u": u,
        "smoke": smoke,
        "tar": tar,
        "cancer": cancer,
    }


def adapt_enumerate_scm_to_backdoor(n: int = 5000, seed: int = 42):
    """Adapte l'enumeration SCM (PyMC-05) vers backdoor_adjustment.

    Le SCM front-door est identifie par la formule d'ajustement de Pearl
    (front-door criterion). Sur un echantillon tire du SCM, on peut
    estimer P(Y=1 | do(X=1)) - P(Y=1 | do(X=0)) par deux voies :

    1. **Enumerate SCM (organe PyMC-05)** : ``do_direct_p_cancer_given_smoke``
       renvoie ``P(Y | do(X))`` exact (mutilation du SCM).
    2. **backdoor_adjustment** : ajuste sur Z = u (le seul confoundant du
       SCM). Le SCM inclut U comme variable, donc backdoor_adjustment est
       applicable et converge vers la meme valeur que l'enumeration.

    Verdict : AGREEMENT si les deux sont dans +/- 0.05 (booleen,
    tolerance proportionnelle a la variance d'echantillonnage).

    Parameters
    ----------
    n : int
        Taille d'echantillon pour backdoor_adjustment.
    seed : int
        Graine pour reproductibilite.

    Returns
    -------
    dict
        ``{"scm_do": float, "backdoor": float, "obs_naive": float,
        "verdict": AttributionVerdict, "tau_attendu": float}``.
    """
    p_y_do_x1 = do_direct_p_cancer_given_smoke(True)
    p_y_do_x0 = do_direct_p_cancer_given_smoke(False)
    scm_do = float(p_y_do_x1 - p_y_do_x0)

    # Cross-check : l'enumeration directe (mutilation) et le front-door
    # adjustment **doivent** coincider -- c'est l'archetype de
    # l'identifiabilite Pearl. Si elles divergent, le SCM est mal pose.
    p_y_front_x1, p_y_front_x0 = front_door_estimate()
    diff_scm_vs_frontdoor = max(
        abs(p_y_do_x1 - p_y_front_x1), abs(p_y_do_x0 - p_y_front_x0)
    )
    if diff_scm_vs_frontdoor > 1e-9:
        raise AssertionError(
            f"SCM front-door inconsistent : do_direct=({p_y_do_x1:.6f}, "
            f"{p_y_do_x0:.6f}) vs front_door=({p_y_front_x1:.6f}, "
            f"{p_y_front_x0:.6f}), ecart_max={diff_scm_vs_frontdoor:.2e} "
            "(> tolerance 1e-9). Le SCM est-il mal pose ?"
        )

    # Echantillon pour backdoor_adjustment
    sample = _sample_from_scm(n=n, seed=seed)
    # Ajustement backdoor sur Z = u (seul confoundant dans le SCM) :
    # E[Y | do(X=1)] = sum_z E[Y | X=1, Z=z] * P(Z=z)
    backdoor = ca.backdoor_adjustment(
        outcome_table=sample["cancer"].astype(float),
        treatment_levels=sample["smoke"].astype(int),
        confounder_values=sample["u"].astype(int),
    )
    # Baseline naif observationnelle pour montrer le biais du confoundant U
    obs_naive = float(
        sample["cancer"][sample["smoke"] == 1].mean()
        - sample["cancer"][sample["smoke"] == 0].mean()
    )

    verdict = ca.compare_estimators(
        {"scm_do": scm_do, "backdoor": backdoor},
        tolerance=0.05,
    )
    return {
        "scm_do": scm_do,
        "backdoor": backdoor,
        "obs_naive": obs_naive,
        "verdict": verdict,
        "tau_attendu": scm_do,
    }
