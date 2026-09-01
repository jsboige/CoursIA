"""Attribution causale d'une intervention : estimands contrefactuels vs naifs.

Greffe 5 de la serie ICT (issue #13903, Epic #4588) -- **controle de falsifiabilite**
que reclament les greffes 4/sandbox :

- **#13570** fait passer un vote verifiable ;
- **#13571** ouvre un bac a sable ou une action institutionnelle s'execute pour de vrai ;
- **#13572** y met des agents heterogenes.

Chacune produit un ``S_t -> S_{t+1}``. Aucune ne peut dire que l'intervention en est
la cause. Cette greffe fournit la jambe manquante : etant donne un changement observe
apres une intervention, peut-on l'**attribuer** a l'intervention plutot qu'a la derive,
au confondant, ou au choix de l'ordre d'ablation.

.. warning::

   **Ne pas confondre avec l'emergence causale** (``ict.causal_emergence``).
   L'emergence causale mesure *combien* de pouvoir causal une echelle grossiere gagne
   sur sa micro-dynamique, sur une TPM connue et fermee (Hoel ; Jansma & Hoel 2025).
   L'attribution causale mesure *si* une intervention observee est cause du changement
   observe, sur des donnees observationnelles ou experimentales brutes (Pearl ;
   Imbens & Rubin 2015).

Trois estimateurs implementes, du plus naif au plus correct :

1. **naive_difference** : ``E[Y | X=1] - E[Y | X=0]``. Biaise par confondants et
   effet selection. Sert uniquement de baseline pour montrer la limite.
2. **backdoor_adjustment** : ajuste sur un set de confondants ``Z`` observes, en
   sommant ``sum_z P(Y=y | X=x, Z=z) * P(Z=z)``. Correct si le set ``Z`` satisfait
   le critere backdoor (Pearl).
3. **iv_estimate** : estimation par variable instrumentale (2SLS simplifie, 1 variable
   instrumentale scalaire). Correct si l'instrument respecte les trois conditions
   (relevance, exclusion, exogeneite).

Verdict tri-etat (analogue au protocole d'ICT-12e pour l'EVSI) :

- **AGREEMENT** : les deux estimateurs donnent la meme valeur a tolerance pres.
- **DESACCORD** : ecart superieur a la tolerance declaree ; rapporte les deux
  valeurs, **ne prend pas la moyenne** (le protocole d'ICT-12e sur l'EVSI
  253 000 vs 252 794 EUR, ecart 206 EUR sous tolerance, est l'archetype).
- **NON_IDENTIFIABLE** : l'estimand n'est pas identifiable sous le graphe causal
  pose (backdoor non bloque, instrument non valide, etc.). C'est un **resultat
  legitime**, pas un echec (le notebook Greffe 5 doit le rapporter comme tel,
  cf. le modele SAE-Catastrophes cite dans l'issue #13903).

Controle negatif obligatoire : une intervention dont on **sait** qu'elle ne cause
pas le changement observe doit retourner un ATE proche de zero dans la ground
truth et lever ``ValueError`` (ou retourner ``NON_IDENTIFIABLE``) si le graphe
pose ne bloque pas le bon backdoor. Voir ``tests/test_causal_attribution.py``.

Dependances : bibliotheque standard + numpy. Les moteurs natifs du depot
(DoWhy-1, PyMC-05, Infer-5, Tweety-11, ``DecisionTheory/Causal-Bridges``)
sont les organes de calcul canoniques ; cette **tranche 1/3** fournit
l'interface analytique close-form qui sert de specification executable et de
cible de test commune aux moteurs. La **tranche 2/3** branchera cette
interface sur les notebooks natifs et montrera que les estimateurs donnent
la meme valeur a tolerance pres sur les memes cas canoniques.

References
----------
- Judea Pearl, *Causality*, Cambridge UP, 2009 (chap. 3 : do-calculus,
  chap. 3.3 : backdoor criterion).
- Guido Imbens & Donald Rubin, *Causal Inference for Statistics, Social,
  and Biomedical Sciences*, Cambridge UP, 2015.
- Joshua Angrist & Alan Krueger, 2001 (variables instrumentales).
- Place dans la serie : ICT-0 (cadrage), Epic #4588.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Mapping, Optional, Sequence

import numpy as np


# ---------------------------------------------------------------------------
# Verdict tri-etat
# ---------------------------------------------------------------------------
class AttributionVerdict(str, Enum):
    """Resultat d'une comparaison entre estimateurs ou d'une evaluation d'identifiabilite.

    * ``AGREEMENT`` : estimateurs d'accord a tolerance pres.
    * ``DESACCORD`` : ecart > tolerance ; rapporte brut, sans moyenne.
    * ``NON_IDENTIFIABLE`` : estimand non identifiable sous le graphe pose.
    """

    AGREEMENT = "AGREEMENT"
    DESACCORD = "DESACCORD"
    NON_IDENTIFIABLE = "NON_IDENTIFIABLE"


# ---------------------------------------------------------------------------
# CausalGraph : squelette structurel minimal
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class CausalGraph:
    """Graphe causal structurel minimal : variable de traitement, de reponse, confondants.

    Attributes
    ----------
    treatment : str
        Nom de la variable de traitement X (l'intervention).
    outcome : str
        Nom de la variable de reponse Y (ce qu'on observe apres l'intervention).
    confounders : tuple of str
        Variables Z dont on **suppose** qu'elles confondent X -> Y (covariables
        observees utilisees par le backdoor adjustment).
    instrument : str or None
        Variable instrumentale Z, si dispo. Doit influencer X mais pas Y
        conditionnellement a X et Z (3 conditions d'Angrist-Krueger).
    """

    treatment: str
    outcome: str
    confounders: tuple = ()
    instrument: Optional[str] = None

    def __post_init__(self):
        if not self.treatment or not self.outcome:
            raise ValueError("treatment et outcome sont requis")
        if self.treatment == self.outcome:
            raise ValueError(
                f"treatment == outcome ({self.treatment!r}) : intervention ne peut "
                "pas etre sa propre reponse"
            )
        for c in self.confounders:
            if c in (self.treatment, self.outcome):
                raise ValueError(
                    f"confounder {c!r} ne peut pas etre treatment ou outcome"
                )
        if self.instrument is not None:
            if self.instrument in (self.treatment, self.outcome):
                raise ValueError(
                    f"instrument {self.instrument!r} ne peut pas etre treatment "
                    "ou outcome"
                )
            if self.instrument in self.confounders:
                raise ValueError(
                    f"instrument {self.instrument!r} ne peut pas etre confounder"
                )


# ---------------------------------------------------------------------------
# Estimateur naif : baseline pour montrer la limite
# ---------------------------------------------------------------------------
def naive_difference(
    outcome_by_treatment: Mapping[int, Sequence[float]],
    tol_zero: float = 1e-9,
) -> float:
    """Difference d'esperances brutes : ``E[Y | X=1] - E[Y | X=0]``.

    **Biaise** par confondants et effet selection (cf. Pearl 2009 chap. 1).
    Sert uniquement de baseline pour montrer la limite des estimateurs
    causaux ; a ne JAMAIS rapporter comme ATE.

    Parameters
    ----------
    outcome_by_treatment : mapping
        ``{1: [y_1_1, ...], 0: [y_0_1, ...]}`` : valeurs de Y observees
        sous chaque modalite de X.
    tol_zero : float
        Tolerance pour signaler un set vide.

    Returns
    -------
    float
        Difference ``E[Y | X=1] - E[Y | X=0]``.

    Raises
    ------
    ValueError
        Si l'un des deux ensembles est vide ou si la cle 0 ou 1 manque.
    """
    if 1 not in outcome_by_treatment or 0 not in outcome_by_treatment:
        raise ValueError(
            f"naive_difference exige les deux modalites 0 et 1, recu "
            f"{sorted(outcome_by_treatment.keys())}"
        )
    y1 = np.asarray(outcome_by_treatment[1], dtype=float)
    y0 = np.asarray(outcome_by_treatment[0], dtype=float)
    if y1.size < 1 or y0.size < 1:
        raise ValueError(
            f"naive_difference : set vide (|X=1|={y1.size}, |X=0|={y0.size})"
        )
    return float(np.mean(y1) - np.mean(y0))


# ---------------------------------------------------------------------------
# Estimateur backdoor adjustment
# ---------------------------------------------------------------------------
def backdoor_adjustment(
    outcome_table: np.ndarray,
    treatment_levels: Sequence[int],
    confounder_values: Sequence,
    *,
    tol_zero: float = 1e-9,
) -> float:
    """ATE par ajustement backdoor (Pearl 2009 chap. 3.3).

    Calcule ``ATE = E[Y | do(X=1)] - E[Y | do(X=0)]`` via la formule
    d'ajustement : ``sum_z E[Y | X=x, Z=z] * P(Z=z)``.

    Parameters
    ----------
    outcome_table : np.ndarray, shape (n_obs,)
        Valeurs de Y observees.
    treatment_levels : sequence of int
        Modalite de X pour chaque observation, longueur ``n_obs``.
    confounder_values : sequence
        Valeur de Z pour chaque observation, longueur ``n_obs``. Doit etre
        discret ou convertible en categories (on groupe par modalite unique).
    tol_zero : float
        Tolerance pour signaler un groupement vide.

    Returns
    -------
    float
        ATE = ``E[Y | do(X=1)] - E[Y | do(X=0)]``.

    Raises
    ------
    ValueError
        Si ``outcome_table`` et ``treatment_levels`` n'ont pas la meme longueur,
        ou si une modalite de X manque pour au moins une modalite de Z
        (estimand non identifiable).
    """
    y = np.asarray(outcome_table, dtype=float)
    x = np.asarray(treatment_levels, dtype=int)
    if y.size != x.size:
        raise ValueError(
            f"backdoor_adjustment : tailles incompatibles y={y.size}, x={x.size}"
        )
    if y.size < 1:
        raise ValueError("backdoor_adjustment : set vide")
    if x.size > 1:
        unique_x = np.unique(x)
        if not np.array_equal(unique_x, np.array([0, 1])):
            raise ValueError(
                f"backdoor_adjustment : X doit etre binaire (0/1), recu {unique_x.tolist()}"
            )

    # Indexation par (X, Z) : moyenne de Y par couple.
    z_arr = np.asarray(
        [str(c) for c in confounder_values],
        dtype=object,
    )
    unique_z = np.unique(z_arr)
    ate = 0.0
    for z in unique_z:
        mask_z = z_arr == z
        p_z = mask_z.sum() / y.size
        if p_z <= tol_zero:
            continue
        # E[Y | do(X=x), Z=z] approximee par E[Y | X=x, Z=z] (ignoring positivity)
        mask_x1_z = (x == 1) & mask_z
        mask_x0_z = (x == 0) & mask_z
        e1 = y[mask_x1_z].mean() if mask_x1_z.any() else None
        e0 = y[mask_x0_z].mean() if mask_x0_z.any() else None
        if e1 is None or e0 is None:
            raise ValueError(
                f"backdoor_adjustment : modalite X manquante pour Z={z} "
                "(estimand NON_IDENTIFIABLE -- backdoor non bloque)"
            )
        ate += p_z * (e1 - e0)
    return float(ate)


# ---------------------------------------------------------------------------
# Estimateur par variable instrumentale (2SLS simplifie, scalaire)
# ---------------------------------------------------------------------------
def iv_estimate(
    outcome: Sequence[float],
    treatment: Sequence[float],
    instrument: Sequence[float],
) -> float:
    """ATE par variable instrumentale : 2SLS scalaire simplifie.

    Estimateur : ``ATE_IV = Cov(Y, Z) / Cov(X, Z)`` (Angrist-Krueger 2001).

    Conditions requises pour la validite :

    1. **Relevance** : ``Cov(X, Z) != 0``.
    2. **Exclusion** : Z n'influence Y que via X (conditionnellement a X).
    3. **Exogeneite** : Z est independant des confondants non observes.

    Si la condition 1 echoue, lever ``ValueError`` (instrument non pertinent,
    estimand NON_IDENTIFIABLE).

    Parameters
    ----------
    outcome : sequence of float
        Valeurs de Y, longueur ``n_obs``.
    treatment : sequence of float
        Valeurs de X, longueur ``n_obs``.
    instrument : sequence of float
        Valeurs de Z, longueur ``n_obs``.

    Returns
    -------
    float
        ATE instrumental.

    Raises
    ------
    ValueError
        Si tailles incompatibles ou instrument non pertinent (relevance fail).
    """
    y = np.asarray(outcome, dtype=float)
    x = np.asarray(treatment, dtype=float)
    z = np.asarray(instrument, dtype=float)
    n = y.size
    if x.size != n or z.size != n:
        raise ValueError(
            f"iv_estimate : tailles incompatibles y={n}, x={x.size}, z={z.size}"
        )
    if n < 2:
        raise ValueError("iv_estimate : n >= 2 requis pour calculer une covariance")
    cov_yz = float(np.cov(y, z, ddof=0)[0, 1])
    cov_xz = float(np.cov(x, z, ddof=0)[0, 1])
    # Pertinence : on compare |Cov(X, Z)| au bruit d'echantillonnage attendu.
    # Pour X et Z i.i.d. N(0,1) independants, Cov echantillonnale ~ 1/sqrt(n).
    # Tolerance 5/sqrt(n) = seuil ~5 sigma (pertinence clairement insuffisante).
    relevance_floor = 5.0 / np.sqrt(n)
    if abs(cov_xz) < relevance_floor:
        raise ValueError(
            f"iv_estimate : instrument NON PERTINENT "
            f"(|Cov(X, Z)|={abs(cov_xz):.6f} < 5/sqrt(n)={relevance_floor:.6f}) -- "
            "estimand NON_IDENTIFIABLE"
        )
    return cov_yz / cov_xz


# ---------------------------------------------------------------------------
# Comparaison tri-etat entre estimateurs (protocole ICT-12e)
# ---------------------------------------------------------------------------
def compare_estimators(
    estimates: Mapping[str, float],
    tolerance: float,
) -> AttributionVerdict:
    """Compare deux estimateurs (ou plus) avec tolerance.

    Protocole analogue a ICT-12e (EVSI 253 000 vs 252 796, ecart 204 EUR sous
    tolerance) : on ne moyenne **jamais** des estimateurs qui divergent, on
    rapporte les deux valeurs et le verdict tri-etat.

    Parameters
    ----------
    estimates : mapping
        ``{label_estimateur: valeur}``. Au moins deux estimateurs requis.
    tolerance : float
        Tolerance absolue pour declarer AGREEMENT.

    Returns
    -------
    AttributionVerdict
        ``AGREEMENT`` si toutes les valeurs sont dans une fenetre de
        ``+/- tolerance`` autour de la mediane, ``DESACCORD`` sinon.

    Raises
    ------
    ValueError
        Si moins de deux estimateurs ou si tolerance < 0.
    """
    if tolerance < 0:
        raise ValueError(f"tolerance doit etre >= 0, recu {tolerance}")
    if len(estimates) < 2:
        raise ValueError(
            f"compare_estimators exige >= 2 estimateurs, recu {len(estimates)}"
        )
    values = np.asarray(list(estimates.values()), dtype=float)
    median = float(np.median(values))
    spread = float(np.max(np.abs(values - median)))
    if spread <= tolerance:
        return AttributionVerdict.AGREEMENT
    return AttributionVerdict.DESACCORD
