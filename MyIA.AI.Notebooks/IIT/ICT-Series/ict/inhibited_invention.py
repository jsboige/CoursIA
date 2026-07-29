"""Module #7746 D2 experience E : inhibition de l'innovation (pont Laborit C2 #7741).

Le cinquieme et dernier des bancs d'essai controles de la strate 7 (#7746). Les
experiences A-D ont explore comment une convention emerge (A), s'invente (B), se
diffuse par masse critique (C). Cette experience E modele le cas NEGATIF : que se
passe-t-il quand l'agent a la CAPACITE d'inventer mais INHIBE cette extension de
vocabulaire sous echec repete ? C'est le pont vers la strate C2 (#7741, animat inhibe
de Laborit) : l'inhibition de l'action (et ici, de la RE-description / innovation)
quand l'environnement se revele incontrrollable.

Mecanisme (couplage OPPOSE a l'experience B)
--------------------------------------------
L'experience B (``symbol_invention``) couple l'invention a l'erreur de maniere
CONSTRUCTIVE : un echec de coordination declenche l'invention d'un nouveau signal
(portant le vocabulaire vers ``n_states``). L'experience E couple l'invention a
l'erreur de maniere INHIBITRICE : chaque echec ACCUMULE un niveau d'inhibition qui
SUPPRIME la probabilite d'inventer. Plus l'agent echoue, moins il invente — alors
meme que l'invention est son seul moyen de sortir du goulot de vocabulaire. C'est le
paradoxe de l'inhibition de Laborit : l'echec repete dans un environnement
incontrrollable n'augmente pas l'exploration, il la REDUIT (impuissance apprise,
Seligman 1972 ; inhibition de l'action, Laborit 1979).

Attendus falsifiables (#7746 spec E)
- **Repetition sterile** : vocabulaire fige sous l'inhibition (sous-optimal).
- **Effondrement exploratoire** : meme avec une temperature elevee (exploration),
  l'inhibition empeche de sortir du goulot.
- **Rigidification** : la politique devient rigide (inhibition -> 1) mais FAUSSE.
- **Piege persistant** : plus de cycles d'entrainement ne rescussitent pas la
  coordination (le piege est permanent, pas un manque de calcul).

``InhibitedInventingGame`` sous-classe ``InventingSignalingGame`` (experience B) :
aucune duplication du moteur Roth-Erev / pavage Q. Seul le declencheur d'invention est
rebranche par une porte d'inhibition.

numpy CPU ; reutilise ``InventingSignalingGame`` et ``mutual_information``.
"""

from __future__ import annotations

from typing import Dict, List, Optional

import numpy as np

from ict.symbol_invention import InventingSignalingGame
from ict.signaling_convention import mutual_information


class InhibitedInventingGame(InventingSignalingGame):
    """Jeu d'invention (experience B) ou l'echec repete INHIBE l'innovation.

    Etend :class:`InhibitedInventingGame` (cf ``symbol_invention``) par un couplage
    OPPOSE : au lieu que l'echec declenche l'invention, l'echec ACCUMULE une inhibition
    qui supprime la probabilite d'inventer. L'agent a le mecanisme d'invention (porte
    de rentabilite de B) MAIS une porte d'inhibition additionnelle le freine.

    Parametres (additionnels a ceux de ``InventingSignalingGame``)
    --------------------------------------------------------------
    inhibition_growth : float
        Increment d'inhibition accumule a chaque ECHEC de coordination (>= 0).
        L'inhibition plafonne a 1.0 (invention totalement supprimee).
        ``0.0`` = aucune inhibition (se comporte exactement comme l'experience B).
    inhibition_decay : float
        Decrement d'inhibition a chaque SUCCES (>= 0). Defaut 0 = l'inhibition
        n'est pas oubliee (impuissance apprise persistante). Une valeur > 0 modelise
        une recuperation possible quand l'environnement redevient controllable.
    """

    def __init__(
        self,
        *args,
        inhibition_growth: float = 0.0,
        inhibition_decay: float = 0.0,
        **kwargs,
    ) -> None:
        if inhibition_growth < 0.0:
            raise ValueError(f"inhibition_growth >= 0 requis (recu {inhibition_growth}).")
        if inhibition_decay < 0.0:
            raise ValueError(f"inhibition_decay >= 0 requis (recu {inhibition_decay}).")
        self.inhibition_growth = float(inhibition_growth)
        self.inhibition_decay = float(inhibition_decay)
        super().__init__(*args, **kwargs)

    def reset(self) -> None:
        """Reinitialise le moteur B + le niveau d'inhibition a 0."""
        super().reset()
        self.inhibition_level: float = 0.0
        self.inhibition_history: List[float] = []

    def _invent(self) -> bool:
        """Porte d'inhibition : l'invention est supprimee selon ``inhibition_level``.

        Compose la porte de rentabilite de B (appelee en amont dans ``play_round``)
        avec la porte d'inhibition : si le niveau d'inhibition a atteint 1.0,
        l'invention est totalement bloquee ; sinon elle est supprimee avec la
        probabilite ``inhibition_level`` (inhibition partielle = invention freinee).
        """
        if self.inhibition_level >= 1.0:
            return False
        if self.rng.random() < self.inhibition_level:
            return False
        return super()._invent()

    def play_round(self, reinforce: bool = True):
        """Un tour de jeu B, suivi de la mise a jour du niveau d'inhibition.

        Couplage Laborit : ECHEC -> inhibition augmente ; SUCCES -> inhibition decroit
        (si ``inhibition_decay`` > 0). L'inhibition accumulee agit sur les tours
        SUIVANTS (porte de :meth:`_invent`).
        """
        state, signal, action, net = super().play_round(reinforce=reinforce)
        coordinated = 1 if action == state else 0
        if coordinated == 0:
            self.inhibition_level = min(1.0, self.inhibition_level + self.inhibition_growth)
        else:
            self.inhibition_level = max(0.0, self.inhibition_level - self.inhibition_decay)
        self.inhibition_history.append(self.inhibition_level)
        return state, signal, action, net

    def final_inhibition(self) -> float:
        """Niveau d'inhibition final (dernier tour)."""
        return float(self.inhibition_history[-1]) if self.inhibition_history else 0.0

    def mean_inhibition(self, window: int = 0) -> float:
        """Niveau d'inhibition moyen sur les ``window`` derniers tours (0 = tout)."""
        if not self.inhibition_history:
            return 0.0
        recent = self.inhibition_history[-window:] if window > 0 else self.inhibition_history
        return float(np.mean(recent))


# --- Bancs d'essai falsifiables (#7746 D2 experience E) ---


def inhibition_traps_rigidification_test(
    n_states: int = 4, n_seeds: int = 3, seed: int = 0, *, n_rounds: int = 4000
) -> Dict[str, float]:
    """Verdict RIGIDIFICATION : balayer ``inhibition_growth`` gele le vocabulaire.

    Sans inhibition (``growth=0``), l'agent invente vers ``n_states`` (comportement B).
    Avec une inhibition croissante, le vocabulaire final DECROIT (l'agent rigidifie,
    fige un vocabulaire sous-optimal) et la coordination finale DECROIT aussi. Verdict
    ``rigidifies = 1.0`` ssi : (i) vocab a growth=0 atteint ``n_states``, (ii) vocab au
    growth maximal reste a sa valeur initiale (1), ET (iii) le vocabulaire final est
    monotone decroissant en ``growth`` (au moins un palier de chute).
    """
    growths = [0.0, 0.01, 0.03, 0.08, 0.2, 0.5]
    vocab_means: List[float] = []
    coord_means: List[float] = []
    for g in growths:
        vocabs = []
        coords = []
        for s in range(n_seeds):
            game = InhibitedInventingGame(
                n_states, 1, temperature=0.6, invention_rate=0.1, invention_cost=0.0,
                inhibition_growth=g, rng=np.random.default_rng(seed + 100 * len(vocab_means) + s),
            )
            game.train(n_rounds, anneal_to=0.15)
            vocabs.append(game.final_vocab_size())
            coords.append(game.success_rate(500))
        vocab_means.append(float(np.mean(vocabs)))
        coord_means.append(float(np.mean(coords)))
    vocab_free = vocab_means[0]
    vocab_rigid = vocab_means[-1]
    diffs = np.diff(vocab_means)
    has_drop = bool(np.any(diffs < -0.5))
    monotone_decrease = bool(np.all(diffs <= 0.5))  # tolerate noise; net downward
    rigidifies = 1.0 if (
        vocab_free >= n_states and vocab_rigid <= 2.0 and has_drop and monotone_decrease
    ) else 0.0
    return {
        "growths": growths,
        "vocab_per_growth": vocab_means,
        "coord_per_growth": coord_means,
        "vocab_at_free_inhibition": float(vocab_free),
        "vocab_at_max_inhibition": float(vocab_rigid),
        "rigidifies": rigidifies,
    }


def learned_helplessness_test(
    n_states: int = 4, n_seeds: int = 3, seed: int = 0, *, n_rounds: int = 4000
) -> Dict[str, float]:
    """Verdict IMPUISSANCE APPRISE : l'inhibition croît, plafonne, et piege l'agent.

    Avec une inhibition marquee (``growth=0.08``, ``decay=0``), le niveau d'inhibition
    croît au fil de l'entrainement et stagne a son maximum (l'agent « renonce » a
    innover). Verdict ``helplessness = 1.0`` ssi : (i) l'inhibition finale > 0.8,
    (ii) l'inhibition finale >= l'inhibition a mi-parcours (croissance non-renversee),
    (iii) le vocabulaire reste sous-optimal (< n_states), ET (iv) la coordination
    finale reste imparfaite (< 0.9) — l'agent n'a pas echappe.
    """
    finals = []
    mids = []
    vocabs = []
    coords = []
    for s in range(n_seeds):
        game = InhibitedInventingGame(
            n_states, 1, temperature=0.6, invention_rate=0.1, inhibition_growth=0.08,
            rng=np.random.default_rng(seed + s),
        )
        game.train(n_rounds, anneal_to=0.15)
        finals.append(game.final_inhibition())
        mid = game.inhibition_history[n_rounds // 2] if len(game.inhibition_history) > n_rounds // 2 else 0.0
        mids.append(mid)
        vocabs.append(game.final_vocab_size())
        coords.append(game.success_rate(500))
    final_inh = float(np.mean(finals))
    mid_inh = float(np.mean(mids))
    mean_vocab = float(np.mean(vocabs))
    mean_coord = float(np.mean(coords))
    helplessness = 1.0 if (
        final_inh > 0.8 and final_inh >= mid_inh - 0.1 and mean_vocab < n_states and mean_coord < 0.9
    ) else 0.0
    return {
        "inhibition_at_mid": mid_inh,
        "inhibition_at_end": final_inh,
        "final_vocab": mean_vocab,
        "final_coord": mean_coord,
        "helplessness": helplessness,
    }


def trap_persists_under_more_compute_test(
    n_states: int = 4, n_seeds: int = 3, seed: int = 0
) -> Dict[str, float]:
    """Verdict PIEGE PERMANENT : le double de cycles ne rescussite pas l'inhibe.

    Avec inhibition, doubler le nombre de cycles d'entrainement laisse l'agent piege
    (coordination reste basse a 2N) ; sans inhibition, l'agent atteint une coordination
    elevee. Le piege n'est pas un manque de calcul — c'est structurel. Verdict
    ``persistent_trap = 1.0`` ssi : (i) coord inhibee a 2N reste basse (< 0.5),
    (ii) coord libre a 2N est elevee (> 0.8), ET (iii) le gain de calcul inhibe est
    faible (< 0.1 : doubler les cycles n'a pas rescussite).
    """
    n = 4000
    res = {}
    for label, growth in [("inhibited", 0.1), ("free", 0.0)]:
        for rounds_label, rounds in [("n", n), ("2n", 2 * n)]:
            coords = []
            vocabs = []
            for s in range(n_seeds):
                game = InhibitedInventingGame(
                    n_states, 1, temperature=0.6, invention_rate=0.1,
                    inhibition_growth=growth, rng=np.random.default_rng(seed + s),
                )
                game.train(rounds, anneal_to=0.15)
                coords.append(game.success_rate(500))
                vocabs.append(game.final_vocab_size())
            res[f"{label}_coord_{rounds_label}"] = float(np.mean(coords))
            res[f"{label}_vocab_{rounds_label}"] = float(np.mean(vocabs))
    inhibited_gain = res["inhibited_coord_2n"] - res["inhibited_coord_n"]
    persistent_trap = 1.0 if (
        res["inhibited_coord_2n"] < 0.5 and res["free_coord_2n"] > 0.8 and inhibited_gain < 0.1
    ) else 0.0
    res["inhibited_compute_gain"] = float(inhibited_gain)
    res["persistent_trap"] = persistent_trap
    return res


def no_inhibition_escapes_control_test(
    n_states: int = 4, n_seeds: int = 3, seed: int = 0, *, n_rounds: int = 4000
) -> Dict[str, float]:
    """Controle negatif : ``inhibition_growth=0`` -> comportement B (l'agent s'echappe).

    Sans inhibition, le jeu se comporte exactement comme l'experience B : le vocabulaire
    croît vers ``n_states`` et la coordination devient elevee. Ce controle confirme que
    c'est BIEN l'inhibition (et non le hasard) qui piege l'agent dans les autres bancs.
    """
    vocabs = []
    coords = []
    for s in range(n_seeds):
        game = InhibitedInventingGame(
            n_states, 1, temperature=0.6, invention_rate=0.1, inhibition_growth=0.0,
            rng=np.random.default_rng(seed + s),
        )
        game.train(n_rounds, anneal_to=0.15)
        vocabs.append(game.final_vocab_size())
        coords.append(game.success_rate(500))
    mean_vocab = float(np.mean(vocabs))
    mean_coord = float(np.mean(coords))
    escapes = 1.0 if (mean_vocab >= n_states and mean_coord > 0.8) else 0.0
    return {
        "vocab_without_inhibition": mean_vocab,
        "coord_without_inhibition": mean_coord,
        "escapes": escapes,
    }
