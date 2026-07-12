"""La batterie de l'ENJEU : auto-maintien discret apres intervention ``do(.)``
(strate 5, ICT-19 ; Epic #4588, reframe #5352).

ICT-18 (``ict.time_arrow``) outille le **MOYEN** de la triade teleonomique
*moyen / fin / enjeu* : lafleche du temps thermodynamique, ``I_thermo`` =
distance de la chaine reelle a sa projection reversibilisee. L'instrument est
**necessaire mais pas suffisant** (ICT-18 section 2.bis, substrat S5 controle
faux-positif) : un pur dissipateur (marche aleatoire biaisee, oscillateur
pilote) allume ``I_thermo`` au meme ordre qu'un agent, parce qu'il dissipe --
sans pour autant defendre un soi. Manque le *stake* : l'auto-maintien, la
cloture de contraintes, la resistance active a l'equilibration (Friston ;
Mossio & Moreno 2015).

Ce module comble exactement ce manque : il construit le complement **ENJEU**
``I_stake`` = return-to-basin apres perturbation ``do(.)`` (intervention causale
de Pearl, fil rouge ICT-5). Un substrat qui a un enjeu revient activement vers
son bassin apres un kick ; un pur dissipateur n'a pas de bassin a defendre et
derive. La **PAIRE** ``(I_thermo, I_stake)`` separe l'agent (Gray-Scott S4 :
dissipe ET regenere son motif apres ablation) du pur dissipateur (S5 : dissipe
SANS enjeu) -- la decoupe qu'ICT-18 seul ne sait pas faire.

Portee honnete (ICT-18 spec squelette, Epic #4588) : ``I_stake`` mesure
l'auto-maintien seul (return-to-basin), pas la triade complete. La *FIN*
(accessibilite cinematique, Levin *competency for free*) est mesuree par
ICT-2/3/9 ; l'ajouter ici serait re-mesurer ce qu'ils mesurent deja.

Le module est volontairement **discret et generique** : il operere sur des
etats scalaires (entiers ou flottants) munis d'une fonction de pas ``step_fn``.
Les substrats 2D (Gray-Scott S4) reutilisent ``ict.agency`` (qui est specifique
aux champs ``U``/``V``) ; le present module couvre les substrats discrets S1
(tri), S3 (Axelrod / automate), S5a (marche biaisee) et continus S2 (bistable).
Aucune dependance hors numpy.
"""

from __future__ import annotations

from typing import Callable, Optional, Sequence, Tuple, Union

import numpy as np

Number = Union[int, float]
StepFn = Callable[[np.ndarray], np.ndarray]


def basin_anchor(states: Sequence) -> float:
    """Le point de consigne que le substrat defend (le *soi* a maintenir).

    Pour une trajectoire discrete ou continue, l'ancre du bassin = la moyenne
    temporelle (l'etat autours duquel le systeme passe le plus de temps a
    l'equilibre libre). On l'estime par la moyenne empirique de la trajectoire
    libre (avant perturbation).

    Choix documente : on prend la moyenne, pas le mode, pour rester coherent
    entre substrats discrets (S1/S3) et continus (S2 bistable). Pour un
    substrat strictement multimodal (plusieurs attracteurs), l'ancre est le
    barycentre des modes -- l'instrument mesure alors le retour vers ce
    barycentre, ce qui sous-estime l'enjeu reel (un retour vers N'IMPORTE LEQUEL
    des modes compte). Le notebook ICT-19 documentera cette limite et
    travaillera sur des substrats a attracteur principal unique.
    """
    arr = np.asarray(states, dtype=float)
    if arr.size == 0:
        raise ValueError("basin_anchor: trajectoire vide")
    return float(arr.mean())


def do_kick(
    state: np.ndarray,
    delta: float,
    lo: Optional[float] = None,
    hi: Optional[float] = None,
) -> np.ndarray:
    """Intervention causale ``do(x <- x + delta)`` (Pearl, fil rouge ICT-5).

    Ajoute ``delta`` a l'etat, puis clip aux bornes ``[lo, hi]`` si fournies
    (les substrats discrets ont un alphabet fini ; les implicites bornes).

    NB : c'est une *intervention* (do-calculus), pas une observation. On ne
    conditionne pas par un evenement -- on force l'etat hors du bassin, puis on
    relache la dynamique libre et on mesure le retour. C'est exactement la
    structure d'ICT-9 (``ict.agency.ablate``) generalisee aux etats discrets.
    """
    kicked = np.asarray(state, dtype=float) + float(delta)
    if lo is not None or hi is not None:
        kicked = np.clip(kicked, lo if lo is not None else -np.inf,
                         hi if hi is not None else np.inf)
    return kicked


def distance_to_anchor(traj: np.ndarray, anchor: float) -> np.ndarray:
    """Distance absolue ``|traj[t] - anchor|`` a chaque pas de temps.

    Vecteur de la distance au bassin sur la trajectoire. Sous `I_stake`, on
    regarde si cette distance **decroit** apres le kick (retour = agent) ou
    **reste elevee / croit** (pas de soi = pur dissipateur).
    """
    return np.abs(np.asarray(traj, dtype=float) - float(anchor))


def recovery_curve(
    kicked_state: np.ndarray,
    step_fn: StepFn,
    steps: int,
    anchor: float,
) -> np.ndarray:
    """Distance au bassin au cours du temps apres un kick ``do(.)``.

    Part de ``kicked_state``, integre ``step_fn`` pendant ``steps`` pas, et
    renvoie ``|state_t - anchor|`` pour ``t = 0..steps`` (``t=0`` = distance
    immediatement apres le kick, avant toute relaxation).

    Un substrat avec enjeu produit une courbe **decroissante** (retour vers
    l'ancre) ; un pur dissipateur produit une courbe **plate ou croissante**
    (derive sans cible).
    """
    if steps < 0:
        raise ValueError("recovery_curve: steps doit etre >= 0")
    distances = np.empty(steps + 1, dtype=float)
    state = np.asarray(kicked_state, dtype=float).copy()
    distances[0] = float(np.abs(state - anchor).sum())
    for t in range(1, steps + 1):
        state = step_fn(state)
        distances[t] = float(np.abs(state - anchor).sum())
    return distances


def stake_index(
    kicked_state: np.ndarray,
    step_fn: StepFn,
    steps: int,
    anchor: float,
    free_step_fn: Optional[StepFn] = None,
    free_init: Optional[np.ndarray] = None,
) -> float:
    """Indice d'ENJEU ``I_stake`` : gain de retour au bassin apres ``do(.)``.

    Mesure combien un substrat revient activement vers son ancre apres un kick,
    **au-dela de la derive spontanee**. Renvoie un scalaire dans ``[-1, 1]`` :

    * ``I_stake > 0`` : le substrat revient vers son bassin (auto-maintien =
      enjeu). Un agent (Gray-Scott S4 sur substrat 2D, ou chaine restauratrice
      sur substrat discret) donne ``I_stake`` strictement positif.
    * ``I_stake ~= 0`` : pas de retour signicatif au-dela de la derive. Un pur
      dissipateur (S5 : marche biaisee, oscillateur pilote) donne ``I_stake``
      proche de zero -- c'est le controle faux-positif d'ICT-18.
    * ``I_stake < 0`` : le substrat s'eloigne du bassin apres le kick (instabilite).

    Parametres :
      - ``kicked_state`` : etat immediatement apres ``do(.)`` (sortie de
        ``do_kick``).
      - ``step_fn`` : un pas de la dynamique libre du substrat (``state ->
        state``).
      - ``steps`` : horizon de relaxation (assez long pour que le retour se
        manifeste, assez court pour rester pedagogique).
      - ``anchor`` : ancre du bassin (``basin_anchor``).
      - ``free_step_fn`` / ``free_init`` (optionnel) : dynamique et etat initial
        d'un **controle libre** (meme substrat sans kick). Si fourni, la derive
        spontanee est soustraite -- un substrat dont le bassin deriverait tout
        seul ne fait pas passer ``I_stake`` artificiellement. Si omis, on
        soustrait la distance initiale (hypothese : libre = stationnaire).

    Formule :
      ``I_stake = (d0 - d_final) / d0 - (d0_free - d_final_free) / d0_free``
      ``= fraction de distance regagnee (kick) - fraction regagnee (libre)``

    La normalisation par la distance initiale ``d0`` rend l'indice invariant
    a l'amplitude du kick (un kick plus fort donne plus de retour absolu mais
    la meme fraction regagnee si le substrat a un vrai enjeu).
    """
    d_kick = recovery_curve(kicked_state, step_fn, steps, anchor)
    d0 = d_kick[0]
    if d0 < 1e-12:
        return 0.0  # kick nul : pas d'enjeu mesurable
    frac_kick = (d0 - d_kick[-1]) / d0

    if free_step_fn is not None and free_init is not None:
        d_free = recovery_curve(free_init, free_step_fn, steps, anchor)
        d0_free = d_free[0]
        if d0_free < 1e-12:
            frac_free = 0.0
        else:
            frac_free = (d0_free - d_free[-1]) / d0_free
    else:
        frac_free = 0.0  # hypothese : libre = stationnaire (derive nulle)

    return float(np.clip(frac_kick - frac_free, -1.0, 1.0))


# ---------------------------------------------------------------------------
# Substrats de demonstration (le contraste falsifiable)
# ---------------------------------------------------------------------------

def restoring_step(state: np.ndarray, strength: float = 0.3,
                   rng: Optional[np.random.Generator] = None) -> np.ndarray:
    """Pas d'une chaine **restauratrice** : tire vers 0 (l'ancre) avec bruit.

    Modele minimal d'un substrat qui defend un point de consigne : chaque pas,
    l'etat se rapproche de 0 d'un facteur ``strength`` + petit bruit. C'est
    l'analogue discret d'un ressort amorti -- un vrai soi. Apres un kick, la
    trajectoire revient vers 0 : ``I_stake > 0``.
    """
    if rng is None:
        rng = np.random.default_rng()
    return state * (1.0 - strength) + rng.normal(0.0, 0.05, size=np.shape(state))


def drift_step(state: np.ndarray, bias: float = 0.4,
               rng: Optional[np.random.Generator] = None) -> np.ndarray:
    """Pas d'une **marche aleatoire biaisee** : derive sans cible (S5a).

    Aucune force de rappel -- l'etat derive a chaque pas d'un terme ``bias``
    constant + bruit. C'est le **controle faux-positif** d'ICT-18 (substrat S5a)
    : dissipe (fleche du temps non-nulle, ``I_thermo > 0``) MAIS n'a aucun bassin
    a defender. Apres un kick, la trajectoire ne revient pas : ``I_stake ~= 0``.
    """
    if rng is None:
        rng = np.random.default_rng()
    return state + bias + rng.normal(0.0, 0.1, size=np.shape(state))


def demo_contrast(steps: int = 50, seed: int = 42) -> Tuple[float, float]:
    """Contraste falsifiable : restauratrice (agent) vs derive (pur dissipateur).

    Renvoie ``(I_stake_restoring, I_stake_drift)``. La prediction falsifiable
    (gate ENJEU-1 du notebook ICT-19) : ``I_stake_restoring > I_stake_drift``
    avec une marge claire, bien que les deux substrats dissipe (a bruit pres).
    Si faux, la batterie ne discrimine pas -- resultat nul honnete, pas un
    succes maquille.
    """
    rng_r = np.random.default_rng(seed)
    rng_d = np.random.default_rng(seed + 1)
    anchor = 0.0
    kick = 5.0
    i_r = stake_index(
        kicked_state=do_kick(np.array([0.0]), kick),
        step_fn=lambda s: restoring_step(s, 0.3, rng_r),
        steps=steps, anchor=anchor,
    )
    i_d = stake_index(
        kicked_state=do_kick(np.array([0.0]), kick),
        step_fn=lambda s: drift_step(s, 0.4, rng_d),
        steps=steps, anchor=anchor,
    )
    return i_r, i_d
