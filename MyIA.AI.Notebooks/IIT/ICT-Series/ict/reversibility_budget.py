"""Budget de reversibilite (ICT-18b, strate 5 Epic #4588).

La **reversibilisation** (ICT-18) mesurait le *moyen* -- la production
d'entropie ``sigma`` comme fleche du temps -- et ICT-19 l'*enjeu* (la batterie
``I_stake`` d'auto-maintien). Il manquait la troisieme jambe de la triade
**moyen / fin / enjeu** : la *fin* de la reversibilisation, c'est-a-dire la
**reversibilite comportementale** lue comme une **ressource** -- un budget
``B(t)`` qui se constitue, se depense et s'epuise. Ce module fournit
l'instrument de mesure.

Un budget de reversibilite = mesure de la capacite du systeme a *regagner* sa
**region de consigne** apres perturbation. Deux definitions candidats,
comparees honnetement (aucune privilegiee a priori) :

1. **Version espace d'etats** : fraction des perturbations (dans une boule de
   rayon ``r`` autour de l'etat courant) depuis lesquelles le systeme revient
   dans la region de consigne (voisine de l'ancre) en moins de ``tau`` pas.
   Mesure de Monte-Carlo directement sur la dynamique. **Robuste** : elle
   n'exige pas de discretiser l'etat (le piege qui annulait ``sigma`` sur les
   substrats continus dans ICT-18), et se mesure sur tous les substrats.

2. **Version travail** : distance a la projection reversible ``P_rev`` deja
   construite dans :mod:`ict.time_arrow`. C'est la quantite de dynamique
   irreversible porte par la chaine -- la part *non recuperable* ; le budget
   est son complement. Plus fine mais sensibles aux artefacts de
   discretisation (cf. ICT-18 gates KO/AMBIGU sur S2/S3).

Lecture-ressource des *early-warning signals* (Scheffer 2009, ICT-8) : un
signal precurseur (variance ↑, AR1 ↑ a l'approche d'un pli) EST un
epuisement de budget -- le bassin se retracte, la probabilite de retour
s'effondre avant la bifurcation. Si ``B_state`` ne co-varie pas avec les EWS,
le cadre ressource est affaibli (a dire).

Numpy uniquement, comme le reste du package leger ``ict``. Aucun GPU requis.
"""

from __future__ import annotations

from typing import Callable, Optional, Sequence, Tuple

import numpy as np

from . import time_arrow


# --------------------------------------------------------------------------- #
#  Utilitaire : echantillonnage uniforme dans la boule de rayon r              #
# --------------------------------------------------------------------------- #


def sample_ball(
    radius: float,
    n_dims: int,
    n_samples: int,
    rng: np.random.Generator,
) -> np.ndarray:
    """Echantillonnage **uniforme dans le volume** de la boule de rayon ``radius``.

    Loi : direction uniforme sur la sphere (Gaussienne normalisee) x rayon
    ``radius * u**(1/n_dims)`` ou ``u`` est uniforme sur ``[0, 1]``. Cela donne
    une densite volumique constante dans la boule (et non une concentration
    sur la surface qu'on obtiendrait en tirant le rayon uniformement).

    Retourne un tableau ``(n_samples, n_dims)``.

    Cas ``n_dims == 1`` : uniforme sur ``[-radius, radius]`` (la sphere de
    dimension 1 est le paire ``{-1, +1}`` ; la formule ci-dessus se reduit a
    ``signe * radius * u``).
    """
    if n_dims <= 0:
        raise ValueError(f"sample_ball : n_dims>0 requis, recu {n_dims}")
    if radius <= 0:
        raise ValueError(f"sample_ball : radius>0 requis, recu {radius}")
    directions = rng.standard_normal((n_samples, n_dims))
    norms = np.linalg.norm(directions, axis=1, keepdims=True)
    norms = np.where(norms > 0, norms, 1.0)
    directions = directions / norms
    u = rng.random((n_samples, 1))
    radii = radius * (u ** (1.0 / n_dims))
    return directions * radii


# --------------------------------------------------------------------------- #
#  Version espace d'etats : budget B_state(r, tau)                            #
# --------------------------------------------------------------------------- #


StepFn = Callable[[np.ndarray], np.ndarray]


def state_space_budget(
    step_fn: StepFn,
    anchor: np.ndarray,
    radius: float,
    tau: int,
    n_samples: int = 200,
    rng: Optional[np.random.Generator] = None,
    consigne_radius: Optional[float] = None,
    bounds: Optional[Tuple[float, float]] = None,
) -> float:
    """Budget espace d'etats ``B_state(r, tau)`` (definition primaire).

    Fraction des perturbations de magnitude ``<= radius`` (uniformes dans la
    boule) depuis lesquelles le systeme revient dans la **region de consigne**
    (boule de rayon ``consigne_radius`` centree sur ``anchor``) en ``<= tau``
    pas de dynamique.

    Pour chaque perturbation ``delta_i`` :

      - ``x0_i = anchor + delta_i`` (reprojete dans ``bounds`` si fourni) ;
      - on applique ``step_fn`` iterativement ``tau`` fois ;
      - succes si ``||x_tau_i - anchor|| <= consigne_radius``.

    La fraction de succes est le budget. ``1.0`` = retour systematique
    (consigne robustement defendue), ``0.0`` = aucun retour (consigne
    perdue / etat absorbant ailleurs).

    Parametres :
      - ``step_fn`` : fonction ``etat -> etat_suivant`` (un pas de dynamique).
        ``etat`` est un ``np.ndarray`` 1-D ; la meme fonction est appliquee
        element par element sur le batch via une boucle Python (clarte).
      - ``anchor`` : etat de consigne (1-D).
      - ``radius`` : rayon de la boule de perturbation.
      - ``tau`` : horizon de retour (nombre de pas).
      - ``n_samples`` : taille de l'echantillon Monte-Carlo.
      - ``rng`` : generateur numpy (defaut : nouveau ``default_rng()``).
      - ``consigne_radius`` : rayon de la region de consigne ; si ``None``,
        pris egal a ``radius / 2`` (la consigne couvre la moitie interieure de
        la perturbation -- convention neutre ; l'appelant peut la choisir).
      - ``bounds`` : couple ``(lo, hi)`` optionnel pour clipper l'etat a un
        domaine valide (ex. concentration >= 0).

    Retourne un scalaire dans ``[0, 1]``.
    """
    if rng is None:
        rng = np.random.default_rng()
    anchor = np.asarray(anchor, dtype=float).ravel()
    n_dims = anchor.size
    if consigne_radius is None:
        consigne_radius = radius / 2.0
    if consigne_radius <= 0:
        raise ValueError("consigne_radius doit etre > 0")

    deltas = sample_ball(radius, n_dims, n_samples, rng)
    states0 = anchor[None, :] + deltas
    if bounds is not None:
        lo, hi = bounds
        states0 = np.clip(states0, lo, hi)

    n_success = 0
    for i in range(n_samples):
        x = states0[i]
        for _ in range(int(tau)):
            x = step_fn(x)
            x = np.asarray(x, dtype=float).ravel()
            if bounds is not None:
                lo, hi = bounds
                x = np.clip(x, lo, hi)
        if np.linalg.norm(x - anchor) <= consigne_radius:
            n_success += 1
    return n_success / n_samples


def budget_curve(
    step_fn: StepFn,
    anchor: np.ndarray,
    radii: Sequence[float],
    tau: int,
    n_samples: int = 200,
    rng: Optional[np.random.Generator] = None,
    consigne_radius: Optional[float] = None,
    bounds: Optional[Tuple[float, float]] = None,
) -> np.ndarray:
    """Budget ``B_state(r, tau)`` sur une grille de rayons de perturbation.

    Courbe de degradation : comment le budget s'epuise quand la perturbation
    grandit. Une courbe qui reste plate a 1.0 = consigne infiniment robuste
    (irrealiste) ; une courbe qui chute vite = consigne vulnerable.

    Retourne un ``np.ndarray`` 1-D de meme longueur que ``radii``.
    """
    return np.array(
        [
            state_space_budget(
                step_fn,
                anchor,
                radius=float(r),
                tau=tau,
                n_samples=n_samples,
                rng=rng,
                consigne_radius=consigne_radius,
                bounds=bounds,
            )
            for r in radii
        ]
    )


# --------------------------------------------------------------------------- #
#  Version travail : budget B_work(P, pi) = distance a la reversible          #
# --------------------------------------------------------------------------- #


def work_budget(P: np.ndarray, pi: np.ndarray) -> float:
    """Budget travail ``B_work`` (definition secondaire, basee sur ``P_rev``).

    Definition : c'est la **distance L1/2** entre la chaine reelle ``P`` et sa
    projection reversible ``P_rev`` (construite par :func:`ict.time_arrow.reversibilize`).
    Interpretation : la quantite de dynamique irreversible (ce que la chaine
    porte de fleche du temps) = ce qui **n'est pas recuperable** sans casser
    la stationnarite. Le complement ``1 - B_work_normalise`` mesure le budget.

    On renvoie la distance brute (``>= 0``, sans borne superieure canonique).
    Une distance nulle = chaine deja reversible (budget epuise au sens
    thermodynamique : rien a recuperer, la dynamique est symetrique). Une
    distance elevee = dynamique fortement irreversible (beaucoup de
    structure "defaisable" en theorie).

    NB : cette definition souffre des memes artefacts de discretisation que
    ``entropy_production`` (cf. ICT-18 gates KO/AMBIGU sur S2/S3 ou les
    matrices estimees etaient trop creuses). Elle sert de **temoin
    secondaire** ; la definition primaire est :func:`state_space_budget`.

    Parametres :
      - ``P`` : matrice de transition (lignes somment a 1).
      - ``pi`` : distribution stationnaire de ``P``.

    Retourne un scalaire ``>= 0``.
    """
    P = np.asarray(P, dtype=float)
    pi = np.asarray(pi, dtype=float)
    P_rev = time_arrow.reversibilize(P, pi)
    return 0.5 * float(np.sum(np.abs(P - P_rev)))


def work_budget_normalized(P: np.ndarray, pi: np.ndarray) -> float:
    """Budget travail normalise dans ``[0, 1]``.

    On normalise la distance a ``P_rev`` par la distance maximale atteignable
    entre deux matrices stochastiques (``k``, taille du vocabulaire) de facon
    grossiere : ``L1/2(P, P_rev) / k``. C'est une normalisation de
    *convenience* (pas une borne exacte) pour permettre la comparaison entre
    chaines de tailles differentes dans un meme graphique.

    Retourne un scalaire dans ``[0, 1]`` approche.
    """
    P = np.asarray(P, dtype=float)
    k = P.shape[0]
    if k == 0:
        raise ValueError("work_budget_normalized : matrice vide")
    raw = work_budget(P, pi)
    return min(raw / k, 1.0)


# --------------------------------------------------------------------------- #
#  Diagnostic : co-variation budget <-> EWS (lecture-ressource)               #
# --------------------------------------------------------------------------- #


def covariation_with_ews(
    parameter_sweep: Sequence[float],
    budgets: Sequence[float],
    ews_values: Sequence[float],
) -> dict:
    """Diagnostique la co-variation budget ``B_state`` <-> early-warning signals.

    Prediction P1 (ICT-18b) : le budget decroit a l'approche du pli, de facon
    co-variante avec les EWS classiques (variance, AR1). Cette fonction teste
    les deux cotes du contrat :

      - ``tau_budget`` : tau de Kendall entre le parametre de bifurcation et le
        budget (on attend une decroissance monotone, donc ``tau <= -0.5``) ;
      - ``tau_ews`` : tau de Kendall entre le parametre et l'EWS (on attend
        ``tau >= +0.5``, hausse du signal precurseur) ;
      - ``tau_budget_vs_ews`` : tau de Kendall entre budget et EWS (on attend
        une anti-correlation forte, ``tau <= -0.5`` : le signal precurseur
        EST un epuisement de budget).

    Le contrat lecture-ressource est **valide** si ``tau_budget_vs_ews <= -0.5``
    (avec p < 0.05). Sinon le cadre ressource est affaibli -- le dire.

    Parametres :
      - ``parameter_sweep`` : valeurs du parametre de bifurcation (ex. ``c``
        du modele de May).
      - ``budgets`` : ``B_state`` mesure a chaque valeur.
      - ``ews_values`` : EWS (variance ou AR1 roulante) mesure a chaque valeur.

    Retourne un dict ``{tau_budget, p_budget, tau_ews, p_ews,
    tau_budget_vs_ews, p_budget_vs_ews, contract_valid}``.
    """
    from . import early_warning

    parameter_sweep = np.asarray(list(parameter_sweep), dtype=float)
    budgets = np.asarray(list(budgets), dtype=float)
    ews_values = np.asarray(list(ews_values), dtype=float)
    if not (len(parameter_sweep) == len(budgets) == len(ews_values)):
        raise ValueError("covariation_with_ews : longueurs incoherentes")

    tau_b, p_b = early_warning.kendall_tau(parameter_sweep, budgets)
    tau_e, p_e = early_warning.kendall_tau(parameter_sweep, ews_values)
    tau_be, p_be = early_warning.kendall_tau(budgets, ews_values)
    return {
        "tau_budget": tau_b,
        "p_budget": p_b,
        "tau_ews": tau_e,
        "p_ews": p_e,
        "tau_budget_vs_ews": tau_be,
        "p_budget_vs_ews": p_be,
        "contract_valid": bool(tau_be <= -0.5 and p_be < 0.05),
    }
