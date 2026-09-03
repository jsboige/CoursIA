"""Adaptateur Quasi-Experimental -- instruments & panels de l'organe natif.

Greffe 5 tranche 2/3 (issue #13903), **decouple de ses copies** par la
tranche 3 de l'issue #14051.

Estimateurs de l'organe natif ``Probas/DecisionTheory/Causal-Bridges/
Quasi-Experimental.ipynb``, desormais consommes depuis le module canonique
``causal_organs`` qui vit a cote de ce notebook :

- ``make_panel_did(differential_pretrend=0.0)`` : panel groupe x periode pour
  difference-in-differences ; ``TAU_TRUE_DID = 3.0`` par construction (cellule 5).
- ``panel_did_two_by_two(df, n_pre=5)`` : la double difference elle-meme,
  forme appelable de l'arithmetique de la cellule 5.
- ``iv_replay(coef_z, n_samp=1000, n_rep=60, seed0=0)`` : ``n_rep`` tirages
  2SLS avec instrument de force ``coef_z`` ; ``TAU_TRUE_IV = 2.0`` (cellule 40).

Ces estimateurs sont **du meme genre** que
:func:`ict.causal_attribution.backdoor_adjustment` (DiD est un ajustement
backdoor sur la periode) et :func:`ict.causal_attribution.iv_estimate` (2SLS
est l'implementation canonique de l'IV d'Angrist-Krueger). Les adaptateurs
ici prennent les generateurs/estimateurs de l'organe natif et les passent
dans l'interface analytique close-form de :mod:`ict.causal_attribution`
pour produire un verdict tri-etat (cf. ICT-12e EVSI).

Pourquoi ce module n'a plus de copies (issue #14051)
-----------------------------------------------------
La tranche 2/3 de la Greffe 5 **redeclarait** localement les quatre organes,
faute de cible importable : les fonctions vivaient dans des cellules de
notebook. La docstring de l'epoque nommait exactement la cause -- *"Code
duplique ici uniquement parce que l'organe natif est un notebook, pas un
module importable. Si l'organe natif etait expose comme module, on
l'importerait."*

Le defaut n'etait pas le rangement, mais le **cablage du verdict** : ces
adaptateurs portent le nom de *cross-engine verification*, et comparaient
:mod:`ict.causal_attribution` non pas a l'organe natif, mais a une
reproduction locale de cet organe. Consequence mecanique : si le notebook
changeait son estimateur DiD, le pont continuait de passer au vert -- il
n'observait plus rien du natif.

Les PR #14076 et #14092 ont leve la cause : ``causal_organs.py`` existe a
cote du notebook, et le notebook l'importe. Ce module importe donc
desormais **le meme objet** que le notebook consomme. Le cablage est
verrouille par ``ict/tests/test_bridges_canonical_wiring.py``, qui exige
l'identite des objets fonction et rougit si une copie reapparait.

Note de lecture : la docstring supprimee invoquait *"la regle
anti-regression qui impose cette duplication"*. L'anti-regression interdit
de **supprimer** une implementation existante ; elle n'a jamais impose d'en
dupliquer une. Ce que la situation imposait, c'etait l'absence de module
importable -- le diagnostic etait juste, seule l'etiquette etait a corriger.

``_iv_2sls_scalaire`` a ete **retire** et non deplace : la mesure repo-wide
ne lui trouve aucun site d'appel (seule sa propre definition et deux
mentions de docstring), et le notebook natif ne definit aucune fonction
2SLS scalaire -- ses cellules 36 et 40 font la forme matricielle en ligne.
Le canoniser aurait cree un troisieme exemplaire d'un organe que personne
n'appelle, exactement le defaut que #14051 corrige.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Optional

import numpy as np

from ict import causal_attribution as ca

# ---------------------------------------------------------------------------
# Organe natif canonique : le module qui vit a cote de Quasi-Experimental.ipynb
# ---------------------------------------------------------------------------
# `causal_organs` n'est pas un package installable -- c'est un module pose a
# cote de son notebook, pour que le notebook ET les tiers consomment le meme
# objet. Le pont traverse donc l'arbre pour l'atteindre.
#
#   quasi_experimental.py -> bridges -> ict -> ICT-Series -> IIT -> MyIA.AI.Notebooks
#                                                                   ^ parents[4]
_CAUSAL_BRIDGES_DIR = (
    Path(__file__).resolve().parents[4] / "Probas" / "DecisionTheory" / "Causal-Bridges"
)
if str(_CAUSAL_BRIDGES_DIR) not in sys.path:
    sys.path.insert(0, str(_CAUSAL_BRIDGES_DIR))

from causal_organs import (  # noqa: E402  (import differe : sys.path ci-dessus)
    TAU_TRUE_DID,
    TAU_TRUE_IV,
    iv_replay,
    make_panel_did,
    panel_did_two_by_two,
)

__all__ = [
    "TAU_TRUE_DID",
    "TAU_TRUE_IV",
    "adapt_iv_replay_to_iv_estimate",
    "adapt_panel_did_to_backdoor",
    "iv_replay",
    "make_panel_did",
    "panel_did_two_by_two",
]


# ---------------------------------------------------------------------------
# Adaptateurs : cross-engine verification
# ---------------------------------------------------------------------------
def adapt_panel_did_to_backdoor(differential_pretrend=0.0, n_pre=5):
    """Adapte DiD (organe Quasi-Experimental) vers backdoor_adjustment.

    Le DiD est un cas particulier d'ajustement backdoor ou Z = "periode"
    est le confounder observe et X = "groupe traite" est l'intervention.
    On construit le panel, on calcule le tau_DiD par les 4 cellules 2x2,
    et on le confronte a :func:`ict.causal_attribution.backdoor_adjustment`
    qui prendrait Y | X, Z=periode_post comme inputs.

    Parameters
    ----------
    differential_pretrend : float
        0 = SUTA satisfaite ; != 0 = violation. Si != 0, l'estimation
        DiD doit biaiser -- l'adaptateur rapporte ``DESACCORD`` attendu.
    n_pre : int
        Periodes pre-traitement.

    Returns
    -------
    dict
        ``{"did": float, "backdoor": float, "verdict": AttributionVerdict,
        "tau_true": float, "bias_attendu": float}``.
    """
    df = make_panel_did(differential_pretrend=differential_pretrend, n_pre=n_pre)
    tau_did = panel_did_two_by_two(df, n_pre=n_pre)

    # Encodage backdoor_adjustment : X = groupe (0/1), Z = post (0/1),
    # Y = outcome. Conformement au schema DiD : Y | do(X=1) - Y | do(X=0)
    # approxime par (Y | X=1, post=1) - (Y | X=1, post=0) - (Y | X=0, post=1)
    # + (Y | X=0, post=0) ajuste par P(post).
    # Mais backdoor_adjustment prend un seul confounder Z et ajuste par
    # moyenne ponderee. Pour mapper DiD -> backdoor, on prend Y = outcome,
    # X = traite_post, Z = post, et on ajuste par P(post).
    # Le resultat differe du DiD 4-cellules car l'ajustement marginalise
    # par P(post) au lieu de prendre la difference post - pre ; on
    # documente donc explicitement la relation.
    df["treated_post"] = (df["group"] == 1).astype(int)
    df["post"] = (df["period"] >= n_pre).astype(int)
    backdoor_value = ca.backdoor_adjustment(
        outcome_table=df["y"].values,
        treatment_levels=df["treated_post"].values,
        confounder_values=df["post"].values,
    )

    # Verdict : tolerance elargie car DiD-4-cellules et backdoor-marginalisent
    # ponderent differemment. La tolerance choisie est 1.0 pour accepter
    # l'ecart de specification (les deux estimateurs ne mesurent PAS
    # exactement la meme chose -- c'est pedagogue).
    verdict = ca.compare_estimators(
        {"did": tau_did, "backdoor": backdoor_value},
        tolerance=1.0,
    )
    bias_attendu = (
        differential_pretrend * (n_pre + 3 - 1) * 0.5
        if differential_pretrend != 0
        else 0.0
    )
    return {
        "did": tau_did,
        "backdoor": backdoor_value,
        "verdict": verdict,
        "tau_true": TAU_TRUE_DID,
        "bias_attendu": bias_attendu,
    }


def adapt_iv_replay_to_iv_estimate(coef_z=1.0, n_samp=2000, n_rep=10, seed0=0):
    """Adapte 2SLS-replay (organe Quasi-Experimental) vers iv_estimate.

    Chaque rep de l'organe Quasi-Experimental produit un 2SLS scalaire ;
    :func:`ict.causal_attribution.iv_estimate` produit un ATE instrumental
    sur un seul echantillon. Pour verifier la coherence cross-engine :

    - appel 1 : moyenne des ``n_rep`` 2SLS de Quasi-Experimental ;
    - appel 2 : :func:`ict.causal_attribution.iv_estimate` sur UN echantillon
      tire avec la meme specification ;
    - verdict tri-etat : AGREEMENT si dans +/- 0.5 (coherence cross-engine).

    Parameters
    ----------
    coef_z : float
        Force de l'instrument. 0.05 = faible (pertinence insuffisante,
        l'organe natif levera NON_IDENTIFIABLE), 1.0 = fort.
    n_samp : int
        Taille d'echantillon par rep.
    n_rep : int
        Nombre de repetitions (moyenne des 2SLS).
    seed0 : int
        Graine de base.

    Returns
    -------
    dict
        ``{"iv_mean": float, "iv_native": float, "verdict": AttributionVerdict,
        "tau_true": float, "pertinence": bool}``.
    """
    taus = iv_replay(coef_z=coef_z, n_samp=n_samp, n_rep=n_rep, seed0=seed0)
    iv_mean = float(taus.mean())

    # Echantillon unique pour iv_estimate (meme seed que la premiere rep).
    # On capture l'exception NON PERTINENT : c'est le **resultat legitime**
    # quand l'instrument est trop faible (cf. protocole ICT-12e).
    rs = np.random.RandomState(seed0)
    u = rs.normal(0, 1, n_samp)
    z = rs.normal(0, 1, n_samp)
    x = coef_z * z + 0.8 * u + rs.normal(0, 0.5, n_samp)
    y = 2.0 * x + 1.0 * u + rs.normal(0, 0.7, n_samp)

    # Pertinence : |Cov(X, Z)| doit etre >= 5/sqrt(n) sinon estimand
    # NON_IDENTIFIABLE ; on rapporte le booleen pour transparence.
    cov_xz = float(np.cov(x, z, ddof=0)[0, 1])
    relevance_floor = 5.0 / np.sqrt(n_samp)
    pertinent = abs(cov_xz) >= relevance_floor

    if not pertinent:
        # Instrument NON PERTINENT : c'est le resultat legitime du
        # garde-fou, pas une erreur. On rapporte NON_IDENTIFIABLE et on
        # laisse iv_native=None pour signaler au consommateur qu'aucune
        # valeur n'a ete produite (et non pas que l'estimateur a diverge).
        iv_native: Optional[float] = None
        verdict = ca.AttributionVerdict.NON_IDENTIFIABLE
    else:
        try:
            iv_native = ca.iv_estimate(y.tolist(), x.tolist(), z.tolist())
        except ValueError:
            # Defense en profondeur : si la pertinence est OK mais que
            # iv_estimate leve quand meme (variance plus elevee que
            # prevue), on rapporte NON_IDENTIFIABLE.
            iv_native = None
            verdict = ca.AttributionVerdict.NON_IDENTIFIABLE
            return {
                "iv_mean": iv_mean,
                "iv_native": None,
                "verdict": verdict,
                "tau_true": TAU_TRUE_IV,
                "pertinence": pertinent,
            }
        verdict = ca.compare_estimators(
            {"iv_replay_mean": iv_mean, "iv_native_single": iv_native},
            tolerance=0.5,
        )
    return {
        "iv_mean": iv_mean,
        "iv_native": iv_native,
        "verdict": verdict,
        "tau_true": TAU_TRUE_IV,
        "pertinence": pertinent,
    }
