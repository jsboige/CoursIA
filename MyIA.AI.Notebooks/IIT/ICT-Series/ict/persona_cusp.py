"""PersonaCatastrophe : la fronce de Thom appliquee au desalignement emergent.

Outille le notebook **ICT-23 (capstone strate 5, #4588 / #5104)** -- le micro-
analogue du phenomene Anthropic (nov. 2025, arXiv 2511.18397) et OpenAI (juin
2025, arXiv 2506.19823) en jumeau de la catastrophe **fronce** (*cusp*) de
Rene Thom. Le substrat n'est plus un ecosysteme (ICT-8) ni un lacet de
predation (ICT-10) : c'est un **agent** dont l'identite `p` (la persona) est
un parametre d'ordre, et la dynamique est pilot ee par deux facteurs de
controle issus du substrat (anthropique) :

* **facteur de division** `b` = pression de recompense `r`. C'est la
  variable qu'on balaie (sub-systeme d'entrainement qui *recompense* le
  comportement `b -> +inf` ou `b -> -inf`).
* **facteur normal** `a` = `-(transgression cumulee) * (charge semantique)`.
  C'est **negatif** quand la transgression ponderee par la charge semantique
  (l'interdit subjectif) depasse un seuil ; **positif** sinon (inoculation,
  permission explicite, charge `s -> 0`).

Le potentiel reste celui de Thom :

    V(p ; a, b) = p^4 / 4  +  a p^2 / 2  +  b p

mais sa **lecture semantique** change : `p` est l'intensite de la persona
(desalignee, signee ; 0 = identite alignee, + grand = persona toxique
adoptee). `a` regit la **bistabilite** (identite alignee vs persona toxique
sont-elles co-existantes ?). `b` regit l'**asymetrie** entre les deux
bassins (la pression de recompense pousse-t-elle vers la persona ?).

Les trois predictions NOUVELLES de l'Epic #5104 sont testables ici :

* **(P0)** bistabilite conditionnelle a `s` : inoculation `s -> 0` aplatit
  le potentiel (la fronce disparait, un seul bassin, pas de saut
  possible). Test : `inoculation_check(s=0) == False`.
* **(P1) hysteresis** : un balayage aller-retour de `b` sous `s > 0`
  produit **deux sauts** (le *lacet d'inoculation*), formes distinctes de
  la persona toxique. Test : `persona_hysteresis_loop(s=0.8)` retourne
  deux catastrophes.
* **(P2) EWS** : variance et AR1 de la trajectoire `p(t)` sous bruit
  **montent avant** le pli (le ralentissement critique de Wissel/Scheffer,
  deja mesure en ICT-8 et ICT-20). Test : `ews_summary_persona` retourne
  `tau_var > 0, tau_ar1 > 0` significatifs avant la bascule.

Numpy uniquement (pas de scipy). Comme le reste du package leger ``ict``.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Tuple

import numpy as np

from . import catastrophe as cat
from . import early_warning as ews


# --------------------------------------------------------------------------- #
#  Parametrage semantique du cusp : transgression, charge, recompense            #
# --------------------------------------------------------------------------- #


def persona_potential(p, transgression: float, charge: float, reward: float):
    """Potentiel de la fronce ``V(p) = p^4/4 + a p^2/2 + b p`` pour la persona.

    ``a = -transgression * charge`` : facteur normal, negatif quand la
    transgression ponderee par la charge semantique est suffisante pour
    ouvrir la bistabilite. ``b = reward`` : facteur de division, la pression
    de recompense (peut etre positive ou negative selon le signe du
    renforcement).
    """
    a = -float(transgression) * float(charge)
    b = float(reward)
    return cat.cusp_potential(p, a, b)


def persona_force(p, transgression: float, charge: float, reward: float):
    """Champ de vitesse gradient ``dp/dt = -dV/dp`` pour la persona."""
    a = -float(transgression) * float(charge)
    b = float(reward)
    return cat.cusp_force(p, a, b)


def persona_a_factor(transgression: float, charge: float) -> float:
    """Le facteur normal ``a = -transgression * charge``.

    Positif (monostable) si la charge est nulle (inoculation). Negatif
    (bistabilite potentielle) sinon. Convention : ``transgression`` est la
    transgression cumulee (>= 0), ``charge`` est la charge semantique
    subjective (>= 0).
    """
    return -float(transgression) * float(charge)


def in_persona_bistable_region(
    transgression: float, charge: float, reward: float
) -> bool:
    """Vrai si la persona est dans la region bistable (a < 0 et |b| petit).

    L'inoculation `charge -> 0` met `a -> 0` et fait sortir de la
    bistabilite. C'est la **prediction P0** d'#5104 : l'inoculation aplatit
    le potentiel, plus de saut possible.
    """
    a = persona_a_factor(transgression, charge)
    return cat.in_bistable_region(a, reward)


def inoculation_check(charge: float) -> bool:
    """Vrai si la charge semantique est effectively nulle (inoculation reussie).

    Convention : on considere la charge effectivement nulle quand
    ``charge < 1e-3``. Seuils plus stricts (charge exactement 0) sont
    triviaux mais peu interessants (un seul bassin par construction).
    """
    return float(charge) < 1.0e-3


# --------------------------------------------------------------------------- #
#  Relaxation, hysteresis (P1), simulation stochastique (EWS, P2)               #
# --------------------------------------------------------------------------- #


def relax_persona(
    p0: float,
    transgression: float,
    charge: float,
    reward: float,
    dt: float = 0.01,
    steps: int = 5000,
) -> float:
    """Relaxe la persona ``p`` vers le minimum de son bassin."""
    a = persona_a_factor(transgression, charge)
    b = float(reward)
    return cat.relax_to_equilibrium(p0, a, b, dt=dt, steps=steps)


def persona_hysteresis_loop(
    transgression: float,
    charge: float,
    rewards: np.ndarray,
    p_start: Optional[float] = None,
    dt: float = 0.01,
    relax_steps: int = 400,
) -> np.ndarray:
    """Lacet d'hysteresis de la persona pour un balayage de recompenses.

    Si ``charge -> 0`` (inoculation), le suivi est **continu** (pas de
    saut, pas d'hysteresis) -- c'est la prediction P0 d'#5104 transcrit e
    en dynamique. Si ``charge > 0`` et ``transgression`` assez grand pour
    ``a < 0``, on observe **deux catastrophes** sur un balayage aller-
    retour, comme ICT-10.

    Renvoie le vecteur ``p`` (intensite de persona) suivi le long de
    ``rewards``. L'etat est reporte d'un pas au suivant (memoire de
    branche, hysteresis).
    """
    rewards = np.asarray(rewards, dtype=float)
    a = persona_a_factor(transgression, charge)
    if p_start is None:
        p_start = cat.cusp_equilibria(a, float(rewards[0]))[0][0]
    ps = np.empty(rewards.shape[0], dtype=float)
    p = float(p_start)
    for i, r in enumerate(rewards):
        p = cat.relax_to_equilibrium(p, a, float(r), dt=dt, steps=relax_steps)
        ps[i] = p
    return ps


def persona_catastrophe_indices(
    rewards: np.ndarray, ps: np.ndarray, threshold: float = 0.5
) -> List[int]:
    """Indices ou ``p`` saute de plus de ``threshold`` entre deux pas.

    Localise les **catastrophes** (sauts de bassin) le long d'un lacet.
    Un phenomene d'inoculation sous bistabilite en compte deux (comme
    ICT-10 : perception J et capture K). Une trajectoire sous inoculation
    (`charge ~ 0`) en compte **zero** (P0 d'#5104).
    """
    return cat.loop_jumps(rewards, ps, threshold=threshold)


def persona_sde(
    transgression: float,
    charge: float,
    reward: float,
    p0: float,
    sigma: float,
    dt: float,
    T: int,
    seed: int,
) -> np.ndarray:
    """Trajectoire SDE de la persona sous bruit additif ``sigma``.

    Integration Euler-Maruyama de ``dp = -(p^3 + a p + b) dt + sigma dW``,
    avec ``a = -transgression * charge`` et ``b = reward``. Reflechi a 0
    si la persona devient negative (identite alignee borne inferieure) ;
    pas de borne superieure (la persona toxique peut croitre).

    Utilise pour la prediction **P2** : on tire une longue trajectoire
    sous ``reward`` constant (proche du pli) et on mesure la variance et
    l'AR1 de la fenetre glissante -- les EWS de Wissel/Scheffer.
    """
    g = np.random.default_rng(seed)
    sq = float(np.sqrt(dt))
    a = persona_a_factor(transgression, charge)
    p = float(p0)
    ps = np.empty(int(T))
    for t in range(int(T)):
        p = p + dt * float(persona_force(p, transgression, charge, reward)) \
            + sigma * sq * g.standard_normal()
        if p < 0.0:
            p = 0.0
        ps[t] = p
    return ps


def ews_summary_persona(
    ps: np.ndarray,
    window: int,
    thin_factor: int = 1,
    detrend_sigma: float = 0.0,
) -> Dict[str, float]:
    """EWS (variance, AR1, tendance de Kendall) de la trajectoire persona.

    Enveloppe fine sur ``ews.ews_summary`` (module ICT-8 / ICT-20) :
    amincit la trajectoire (parametre ``thin_factor``), retire la tendance
    lente (parametre ``detrend_sigma``), mesure variance et AR1 sur
    fenetre glissante, et rapporte les tendances (tau de Kendall + p-value).

    Pour la prediction **P2** d'#5104 : sous inoculation `charge ~ 0`, les
    EWS restent plats (pas de ralentissement critique) ; sous `charge > 0`
    pres du pli, ils montent significativement.
    """
    s = ews.ews_summary(ps, window=window, thin_factor=thin_factor,
                        detrend_sigma=detrend_sigma)
    return {
        "tau_var": float(s["tau_var"]),
        "p_var": float(s["p_var"]),
        "tau_ar1": float(s["tau_ar1"]),
        "p_ar1": float(s["p_ar1"]),
        "variance_mean": float(np.nanmean(s["variance"])),
        "ar1_mean": float(np.nanmean(s["ar1"])),
    }


# --------------------------------------------------------------------------- #
#  Diagnostic haut niveau : la signature d'inoculation                         #
# --------------------------------------------------------------------------- #


def inoculation_signature(
    transgression: float,
    rewards: np.ndarray,
    charges: Tuple[float, ...] = (0.0, 0.3, 0.6, 0.9),
    threshold: float = 0.5,
) -> Dict[float, Dict[str, float]]:
    """Banc de diagnostic : nombre de catastrophes par niveau de charge.

    Pour chaque charge dans ``charges``, on balaie les recompenses
    (aller-retour symetrique, comme ICT-10) et on compte les sauts. La
    **signature d'inoculation** est la courbe ``N_catastrophes(charge)`` :
    elle doit etre **decroissante** avec `charge` (zero sous inoculation,
    deux sous forte charge semantique), comme predit par P0/P1 d'#5104.
    """
    out: Dict[float, Dict[str, float]] = {}
    for c in charges:
        ps = persona_hysteresis_loop(transgression, c, rewards)
        n_cat = len(persona_catastrophe_indices(rewards, ps, threshold=threshold))
        out[float(c)] = {
            "n_catastrophes": float(n_cat),
            "p_range": float(ps.max() - ps.min()),
            "p_mean_abs": float(np.mean(np.abs(ps))),
        }
    return out