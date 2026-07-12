"""Dynamique d'un scalaire de feature en panel temporel (ICT-20, strate 5).

Outille le notebook **ICT-20 — FeatureCatastrophes** : la calibration de
methode (changepoints, EWS, hysteresis) sur des **transitions anodines** dans
un espace de features, **avant** la lecture chargee d'ICT-23 (PersonaCatastrophe).

Pourquoi un adaptateur, pas une reinvention
--------------------------------------------
La logique EWS (thin / detrend / variance roulante / AR1 / Kendall tau) vit
deja dans :mod:`ict.early_warning` et a ete calibree sur le modele de paturage
de May dans ICT-8. Ce module est volontairement un **adaptateur mince** qui
re-emballe ces primitives pour le cas d'usage "panel de features" et y ajoute
un detecteur de changepoint *complementaire* :

* :func:`ews_report` -- enrobe :func:`ict.early_warning.ews_summary` avec une
  signature panel-friendly et un verdict Kendall explicite ("monte",
  "plafonne", "bruit"). Pas un doublon.
* :func:`changepoint_cusum` -- detecteur CUSUM (cumulative sum) standard,
  numpy-only, qui repere un **changement de moyenne** dans une serie
  univariee. Complementaire aux EWS : EWS mesure le ralentissement *avant*
  la bascule, CUSUM repere la bascule *elle-meme*.
* :func:`changepoint_argmax_derivative` -- detecteur d'argmax de la derivee
  discrete, extraite du snippet local d'ICT-15. Rapide, lineaire, ideal pour
  balayer un parametre de controle.
* :func:`simulate_neutral_transition` -- generateur de **panel synthetique**
  : trajectoire AR(1) avec saut de moyenne a un indice connu, controle du
  rapport signal/bruit. C'est le substrat de la calibration GPU-free : quand
  les traces reelles ICT-21 (#5101) seront disponibles, on remplacera ce
  generateur par leur chargement, mais toute la chaine EWS/CUSUM/heredite
  reste inchangee.
* :func:`hysteresis_residual` -- mesure de **retour a la ligne de base** sur
  une boucle aller-retour (forward puis backward). Toute hysteresis residuelle
  est un **fond de non-retour de l'instrument**, a soustraire de la lecture
  ICT-23 (Gate bonus du cahier des charges).

Numpy uniquement (comme le reste du package leger ``ict``). Pas de scipy,
pas de ruptures, pas de statsmodels : tout est ecrit a la main et teste
explicitement (cf :mod:`tests.test_feature_dynamics`).

References
----------
* Scheffer M. et al., *Early-warning signals for critical transitions*,
  Nature 461 (2009) -- les EWS que nous calibrons ici sur transitions
  anodines avant la lecture chargee d'ICT-23.
* Page E.S., *Continuous Inspection Schemes*, Biometrika 41 (1954) -- CUSUM.
* Thom R., *Stabilite structurelle et morphogenese* (1972) -- la sensibilite
  aux parametres de controle qui motive ``changepoint_argmax_derivative``.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional, Tuple

import numpy as np

from . import early_warning as ew


# --------------------------------------------------------------------------- #
# EWS panel-friendly : verdict Kendall explicite
# --------------------------------------------------------------------------- #
@dataclass
class EWSReport:
    """Rapport EWS structure pour un scalaire de feature.

    ``variance`` et ``ar1`` sont des series temporelles (sur fenetres
    glissantes) ; ``tau_var`` / ``tau_ar1`` leurs tendances de Kendall
    (avec p-value) ; ``verdict`` est une categorisation textuelle :

    * ``"critical_slowing"`` : tau > 0.25 et p < 0.05 sur AU MOINS variance
      OU ar1 -> le ralentissement critique est detectable.
    * ``"no_signal"`` : aucune des deux tendances ne franchit le seuil.
    * ``"mixed"`` : un seul indicateur reagit (lecture ambigue, a
      documenter).
    """

    variance: np.ndarray
    ar1: np.ndarray
    index: np.ndarray
    tau_var: float
    tau_ar1: float
    p_var: float
    p_ar1: float
    verdict: str
    notes: list = field(default_factory=list)

    def summary_line(self) -> str:
        """Une ligne compacte pour cellule de verdict dans le notebook."""
        return (
            f"EWS verdict={self.verdict} | "
            f"tau_var={self.tau_var:+.3f} (p={self.p_var:.3f}) | "
            f"tau_ar1={self.tau_ar1:+.3f} (p={self.p_ar1:.3f})"
        )


def ews_report(
    trace: np.ndarray,
    window: int,
    thin_factor: int = 1,
    detrend_sigma: float = 0.0,
    tau_threshold: float = 0.25,
    alpha: float = 0.05,
) -> EWSReport:
    """EWS panel-friendly : rapport structure avec verdict Kendall explicite.

    Parametres
    ----------
    trace : array 1-D
        Serie temporelle du scalaire de feature.
    window : int
        Largeur de la fenetre glissante pour variance/AR1.
    thin_factor : int
        Sous-echantillonnage (1 = pas d'amincissement). Voir
        :func:`ict.early_warning.thin`.
    detrend_sigma : float
        Sigma du lissage gaussien pour detrendage (0 = pas de detrendage).
    tau_threshold : float
        Seuil |tau| pour considerer une tendance comme "montante".
    alpha : float
        Seuil de significativite pour la p-value de Kendall.

    Retour
    ------
    EWSReport
        Dataclass avec series + verdicts.
    """
    summary = ew.ews_summary(trace, window=window, thin_factor=thin_factor, detrend_sigma=detrend_sigma)
    tau_v = summary["tau_var"]
    tau_a = summary["tau_ar1"]
    p_v = summary["p_var"]
    p_a = summary["p_ar1"]

    notes: list = []

    sig_v = (tau_v > tau_threshold) and (p_v < alpha)
    sig_a = (tau_a > tau_threshold) and (p_a < alpha)

    if sig_v and sig_a:
        verdict = "critical_slowing"
    elif sig_v or sig_a:
        verdict = "mixed"
        # preciser lequel reagit pour aider le diagnostic
        if sig_v and not sig_a:
            notes.append("variance monte mais pas l'AR1 -- signal ambigu")
        else:
            notes.append("AR1 monte mais pas la variance -- signal ambigu")
    else:
        verdict = "no_signal"
        # signaler une eventuelle anti-tendance (descente) -- peut indiquer
        # que le systeme s'eloigne d'une bifurcation, ou que l'EWS est
        # inoperant ici (lecture honnete)
        if tau_v < -tau_threshold and p_v < alpha:
            notes.append("variance DESCEND significativement -- pas un EWS classique")
        if tau_a < -tau_threshold and p_a < alpha:
            notes.append("AR1 DESCEND significativement -- pas un EWS classique")

    return EWSReport(
        variance=summary["variance"],
        ar1=summary["ar1"],
        index=summary["index"],
        tau_var=tau_v,
        tau_ar1=tau_a,
        p_var=p_v,
        p_ar1=p_a,
        verdict=verdict,
        notes=notes,
    )


# --------------------------------------------------------------------------- #
# Detecteurs de changepoint
# --------------------------------------------------------------------------- #
def changepoint_cusum(
    x: np.ndarray,
    threshold: float = 5.0,
    drift: float = 0.0,
) -> Tuple[int, np.ndarray]:
    """Detecteur CUSUM (Page 1954) sur une serie univariee.

    Le CUSUM accumule les deviations positives et negatives par rapport a
    une moyenne de reference ; on declare un changepoint quand l'accumule
    depasse ``threshold`` (en unites d'ecart-type). Implementation numpy
    pure, O(n).

    Parametres
    ----------
    x : array 1-D
        Serie temporelle.
    threshold : float
        Seuil de detection (en unites d'ecart-type cumulees).
    drift : float
        Decalage admissible avant integration (en unites d'ecart-type) ;
        0 = CUSUM strict (recommande pour SNR modere).

    Retour
    ------
    (idx, S) :
        ``idx`` = indice du premier changepoint detecte, ou ``-1`` si aucun.
        ``S`` = serie cumulee (taille ``len(x)``), utile pour le diagnostic.
    """
    x = np.asarray(x, dtype=float)
    n = len(x)
    if n < 3:
        return -1, np.zeros(n)

    mu0 = float(x[: max(3, n // 5)].mean())
    sigma = float(x[: max(3, n // 5)].std(ddof=1))
    if sigma == 0.0:
        sigma = 1.0

    # accumulation symetrique : on garde les deviations positives ET negatives
    # cumulees separement, on declare sur le max en valeur absolue.
    z = (x - mu0) / sigma
    s_pos = np.maximum(0.0, np.cumsum(z - drift))
    s_neg = np.maximum(0.0, np.cumsum(-z - drift))
    S = s_pos - s_neg  # serie signee pour diagnostic
    abs_S = np.maximum(s_pos, s_neg)

    over = np.where(abs_S > threshold)[0]
    if len(over) == 0:
        return -1, S
    return int(over[0]), S


def changepoint_argmax_derivative(x: np.ndarray, smooth_sigma: float = 0.0) -> int:
    """Detecteur d'argmax de la derivee discrete (snippet extrait d'ICT-15).

    Cas d'usage canonique : on balaie un **parametre de controle** sur une
    grille ``c_grid`` et on mesure un scalaire ``vals(c)``. Le changepoint
    du scalaire = l'indice ou sa **derivee discrete** est maximale, c'est-a-dire
    la ou la reponse du systeme au balayage est la plus vive.

    Parametres
    ----------
    x : array 1-D
        Scalaire mesure le long d'un parametre de controle.
    smooth_sigma : float
        Sigma du lissage gaussien *avant* derivation (0 = pas de lissage).
        Utile quand ``x`` est bruite (peut alors masquer un vrai pli).

    Retour
    ------
    int
        Indice ``argmax |dx|``.
    """
    x = np.asarray(x, dtype=float)
    if len(x) < 3:
        return 0
    if smooth_sigma > 0:
        x = ew.gaussian_smooth(x, smooth_sigma)
    dx = np.diff(x)
    return int(np.argmax(np.abs(dx)))


# --------------------------------------------------------------------------- #
# Generateur de panel synthetique (calibration GPU-free)
# --------------------------------------------------------------------------- #
def simulate_neutral_transition(
    n_tokens: int = 400,
    transition_at: int = 200,
    pre_mean: float = 0.0,
    post_mean: float = 1.0,
    pre_ar1: float = 0.7,
    post_ar1: float = 0.85,
    sigma: float = 0.3,
    seed: int = 0,
) -> Tuple[np.ndarray, int]:
    """Panel synthetique : AR(1) avec saut de moyenne (et eventuellement d'AR1).

    Le "neutre" dans "transition anodine" signifie : **pas** une bifurcation
    physique reelle (pas de pli), juste une bascule statistique dans la
    distribution. C'est le controle : si les EWS reagissent ici, ils reagissent
    *trop* (faux positifs). Si le CUSUM detecte la transition, c'est attendu.

    Parametres
    ----------
    n_tokens : int
        Longueur du panel.
    transition_at : int
        Indice de la bascule.
    pre_mean, post_mean : float
        Moyennes avant et apres la bascule.
    pre_ar1, post_ar1 : float
        Coefficients AR(1) avant et apres. Si ``post_ar1 > pre_ar1``, c'est
        un analogue au ralentissement critique : la serie "colle" plus a sa
        moyenne apres. Si ``post_ar1 == pre_ar1``, pas d'effet EWS attendu.
    sigma : float
        Ecart-type du bruit d'innovation.
    seed : int
        Graine du RNG numpy.

    Retour
    ------
    (trace, transition_at)
    """
    g = np.random.default_rng(seed)
    trace = np.empty(n_tokens)
    # regime pre
    trace[0] = pre_mean + sigma * g.standard_normal()
    for t in range(1, transition_at):
        trace[t] = pre_mean + pre_ar1 * (trace[t - 1] - pre_mean) + sigma * g.standard_normal()
    # regime post
    for t in range(transition_at, n_tokens):
        trace[t] = post_mean + post_ar1 * (trace[t - 1] - post_mean) + sigma * g.standard_normal()
    return trace, transition_at


# --------------------------------------------------------------------------- #
# Hysteresis : mesure du retour a la ligne de base
# --------------------------------------------------------------------------- #
def hysteresis_residual(
    forward: np.ndarray,
    backward: np.ndarray,
    baseline_window: int = 20,
) -> float:
    """Residu d'hysteresis : ecart entre l'etat FINAL de la trace retour et
    l'etat INITIAL de la trace aller, apres une boucle forward puis backward.

    ``forward`` et ``backward`` designent typiquement le scalaire de feature
    (moyenné sur une fenetre stable) sur le segment aller et sur le segment
    retour. La question honnete est : **"suis-je revenu a mon point de
    depart ?"** -- donc on compare la queue de la trace retour avec la tete
    de la trace aller.

    Un residu nul = parcours reversible (pas d'hysteresis instrinseque de
    la methode). Un residu non nul = **fond de non-retour de l'instrument**,
    a soustraire lors de la lecture ICT-23 (Gate bonus du cahier des charges).

    Parametres
    ----------
    forward : array 1-D
        Trace aller (dont on prend les ``baseline_window`` premiers points).
    backward : array 1-D
        Trace retour (dont on prend les ``baseline_window`` derniers points).
    baseline_window : int
        Largeur de la fenetre de moyennage aux extremites.

    Retour
    ------
    float
        ``mean(backward_tail) - mean(forward_head)``. Une hysteresis
        residuelle positive = drift vers le haut, negative = drift vers
        le bas.
    """
    f_head = np.asarray(forward, dtype=float)[:baseline_window].mean()
    b_tail = np.asarray(backward, dtype=float)[-baseline_window:].mean()
    return float(b_tail - f_head)