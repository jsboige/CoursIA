"""Free coordinates / freebits de second ordre — banc executable strate 7 (#18052, D1 #7745).

Contexte
--------
Aaronson (*The Ghost in the Quantum Turing Machine*, 2013) definit le **freebit** :
une incertitude *de Knight* sur la **valeur** d'une variable dans un espace **fixe** —
un point ``x in L`` que l'agent ne peut pas connaitre avant la mesure, et que la
physique (no-cloning, retrocausalite bornee) empeche de réduire a une distribution.
Le cadrage D1 de la strate 7 (#7745, ``strate7-cadres-libres.md``) pose l'objet
strictement plus fort : le **freebit de second ordre**, ou l'incertitude porte sur
**l'espace ``L`` lui-meme** — le choix, non canonique, d'une extension
``xi_t dans AdmExt(L_t)``.

Ce module est le banc qui rend ce contraste **executable** :

1. un **jeu evolutif** ``G_t = (N, L_t, A_t, U_t)`` en dataclasses gelees ;
2. des **coups internes** ``a in A_t`` (le jeu ne bouge pas) et des **coups
   ontologiques** ``eta : G_t -> G_{t+1}`` (le jeu change d'espace) ;
3. un **mecanisme M** a quorum qui decide quelles extensions deviennent publiques ;
4. les **six proxys mesurables** du cadrage : ``O_t`` (expansion ontologique),
   ``Delta A_t`` (ouverture politique), ``C_t = |AdmExt|`` (non-canonicite),
   ``P(R)`` (pouvoir performatif, KL interventionnelle sur trajectoires simulees),
   l'**institutionnalisation** (persistance apres retrait de l'instigateur) et
   ``I(R)`` (dette d'irreversibilite) ;
5. le **pont Aaronson executable** : un predicteur bayesien d'espace fixe, dont la
   log-perte sur un support connu est bornee par l'entropie, subit une surprise
   **structurelle** (pas probabiliste) la premiere fois qu'une action hors de son
   espace apparait — la difference exacte entre ignorer une valeur dans ``L`` et
   ignorer ``L``.

Le module est deterministe : toute stochasticite passe par un ``numpy.random.Generator``
fourni par l'appelant. Aucune dependance hors numpy.
"""
from __future__ import annotations

from dataclasses import dataclass, field, replace

import numpy as np

__all__ = [
    "EvolutiveGame",
    "OntologicalMove",
    "internal_move",
    "apply_ontology",
    "quorum_mechanism",
    "expansion_ontology",
    "political_opening",
    "non_canonicity",
    "simulate_trajectory",
    "performative_power",
    "institutionalization",
    "irreversibility_debt",
    "FixedSpacePredictor",
]


@dataclass(frozen=True)
class EvolutiveGame:
    """Etat ``G_t`` de la strate 7 : agents, langage, actions, utilites.

    ``lexicon`` est l'espace des representations partagees ``L_t`` ; ``actions``
    est ``A_t``, genere par le langage ; ``payoffs`` mappe ``(agent, action)``
    vers l'utilite immediate. La prediction ``P_t`` du cadrage vit dans le
    predicteur (cf. ``FixedSpacePredictor``), pas dans l'etat.
    """

    agents: tuple[str, ...]
    lexicon: frozenset[str]
    actions: frozenset[str]
    payoffs: dict[tuple[str, str], float] = field(default_factory=dict)

    def payoff(self, agent: str, action: str) -> float:
        return self.payoffs.get((agent, action), 0.0)


@dataclass(frozen=True)
class OntologicalMove:
    """Un coup ontologique ``eta : G_t -> G_{t+1}``.

    ``new_concepts`` etendent ``L_t`` ; ``opened_actions`` mappe chaque concept
    nouveau vers les actions qu'il rend jouables (c'est le lien ``O_t`` ->
    ``Delta A_t`` : un concept ornemental n'ouvre rien). ``pose_cost`` et
    ``undo_cost`` portent la dette d'irreversibilite ``I(R)``.
    """

    proposer: str
    new_concepts: tuple[str, ...]
    opened_actions: dict[str, tuple[str, ...]]
    pose_cost: float = 1.0
    undo_cost: float = 10.0


def internal_move(game: EvolutiveGame, agent: str, action: str) -> float:
    """Coup interne ``a in A_t`` : retourne le paiement, le jeu est inchange."""
    if action not in game.actions:
        raise ValueError(f"action {action!r} hors de A_t — coup interne seulement")
    return game.payoff(agent, action)


def apply_ontology(game: EvolutiveGame, eta: OntologicalMove) -> EvolutiveGame:
    """Applique ``eta`` : ``L_{t+1} = L_t + concepts``, ``A_{t+1} = A_t + ouvertes``.

    Les utilites des nouvelles actions derivent du concept qui les ouvre :
    un concept ``c`` confere ``opened_payoff`` (defaut 1.0) a chaque action
    qu'il ouvre — surchargeable en pre-etendant ``payoffs`` avant l'appel.
    """
    opened = tuple(a for acts in eta.opened_actions.values() for a in acts)
    payoffs = dict(game.payoffs)
    for concept, acts in eta.opened_actions.items():
        for a in acts:
            payoffs.setdefault((eta.proposer, a), 1.0)
            for agent in game.agents:
                payoffs.setdefault((agent, a), 0.5 if agent != eta.proposer else 1.0)
    return replace(
        game,
        lexicon=game.lexicon | frozenset(eta.new_concepts),
        actions=game.actions | frozenset(opened),
        payoffs=payoffs,
    )


def quorum_mechanism(
    game: EvolutiveGame,
    proposals: tuple[OntologicalMove, ...],
    votes: dict[str, set[str]],
    quorum: int,
) -> tuple[EvolutiveGame, tuple[OntologicalMove, ...]]:
    """Le mecanisme ``M`` : ne rend publics que les ``eta`` atteignant le quorum.

    ``votes[candidate]`` est l'ensemble des agents soutenant la candidature ``c``
    (identifiee par ses concepts). Retourne ``(G_{t+1}, etas_acceptes)`` — les
    candidats rejetes sont silencieux : rien n'entre dans le jeu public.
    """
    accepted: list[OntologicalMove] = []
    for eta in proposals:
        key = ",".join(sorted(eta.new_concepts))
        if len(votes.get(key, ())) >= quorum:
            accepted.append(eta)
    result = game
    for eta in accepted:
        result = apply_ontology(result, eta)
    return result, tuple(accepted)


def expansion_ontology(g0: EvolutiveGame, g1: EvolutiveGame) -> int:
    """Proxy ``O_t = |L_{t+1} \\ L_t|`` — ouverture linguistique."""
    return len(g1.lexicon - g0.lexicon)


def political_opening(g0: EvolutiveGame, g1: EvolutiveGame) -> int:
    """Proxy ``Delta A_t = |A_{t+1} \\ A_t|`` — garde-fou contre le verbiage."""
    return len(g1.actions - g0.actions)


def non_canonicity(
    game: EvolutiveGame,
    candidate_extensions: tuple[OntologicalMove, ...],
) -> int:
    """Proxy ``C_t = |AdmExt(G_t)|`` — nombre d'extensions non equivalentes.

    Deux extensions sont equivalentes si elles ouvrent les **memes actions**
    (a renommage de concept pres) : c'est la forme observable de l'equivalence
    pour ce banc. Une famille dont toutes les paires ouvrent le meme jeu rend
    ``C_t = 1`` : le prolongement est canonique, il n'y a rien a choisir.
    """
    action_sets = set()
    for eta in candidate_extensions:
        extended = apply_ontology(game, eta)
        action_sets.add(frozenset(extended.actions))
    return len(action_sets)


def simulate_trajectory(
    game: EvolutiveGame,
    horizon: int,
    rng: np.random.Generator,
    temperature: float = 0.5,
) -> dict[str, int]:
    """Simule ``horizon`` coups internes : agents myopes en softmax sur ``U_t``.

    Retourne l'histogramme des actions jouees — l'observable sur lequel les
    proxys interventionnels se mesurent.
    """
    actions = sorted(game.actions)
    if not actions:
        return {}
    counts = {a: 0 for a in actions}
    agents = list(game.agents)
    for _ in range(horizon):
        for agent in agents:
            logits = np.array(
                [game.payoff(agent, a) / max(temperature, 1e-9) for a in actions]
            )
            probs = np.exp(logits - logits.max())
            probs /= probs.sum()
            chosen = actions[int(rng.choice(len(actions), p=probs))]
            counts[chosen] += 1
    return counts


def performative_power(
    game_do: EvolutiveGame,
    game_skip: EvolutiveGame,
    horizon: int,
    n_sim: int,
    rng: np.random.Generator,
) -> float:
    """Proxy ``P(R)`` — KL empirique entre trajectoires sous ``do(eta)`` et ``do(-eta)``.

    ``D(Pr(traj | do(R)) || Pr(traj | do(not R)))`` est estimee par divergence KL
    a lissage de Laplace sur les histograms d'actions des deux bras. Un coup
    decoratif rend ``P(R) ~ 0``.
    """
    def _dist(game: EvolutiveGame) -> dict[str, float]:
        agg: dict[str, int] = {}
        for _ in range(n_sim):
            for a, c in simulate_trajectory(game, horizon, rng).items():
                agg[a] = agg.get(a, 0) + c
        total = sum(agg.values()) + len(agg)
        return {a: (c + 1) / total for a, c in agg.items()}

    p, q = _dist(game_do), _dist(game_skip)
    support = set(p) | set(q)
    kl = 0.0
    for a in support:
        pa = p.get(a, 1e-12)
        qa = q.get(a, 1e-12)
        kl += pa * np.log(pa / qa)
    return float(kl)


def institutionalization(
    extended_game: EvolutiveGame,
    eta: OntologicalMove,
    horizon: int,
    rng: np.random.Generator,
) -> float:
    """Persistance du coup ``eta`` apres retrait de son instigateur.

    ``extended_game`` est le jeu APRES application de ``eta`` (l'appelant
    controle donc les paiements des actions ouvertes — c'est eux, pas le coup,
    qui decident de la survie). Retourne la **fraction des coups** (sur
    ``horizon`` pas, joueurs reduits aux agents non-instigateurs) qui
    utilisent encore les actions ouvertes par ``eta`` : proche de 0.0 = le
    concept meurt avec son inventeur, > 0 = institutionnalise.
    """
    survivors = tuple(a for a in extended_game.agents if a != eta.proposer)
    if not survivors:
        return 0.0
    reduced = replace(extended_game, agents=survivors)
    opened = {a for acts in eta.opened_actions.values() for a in acts}
    counts = simulate_trajectory(reduced, horizon, rng)
    played = sum(counts.values())
    if played == 0:
        return 0.0
    return float(sum(c for a, c in counts.items() if a in opened) / played)


def irreversibility_debt(eta: OntologicalMove) -> float:
    """Proxy ``I(R) = cout(defaire) / cout(poser)`` — asymetrie creation/dissolution."""
    if eta.pose_cost <= 0:
        raise ValueError("pose_cost doit etre positif")
    return eta.undo_cost / eta.pose_cost


class FixedSpacePredictor:
    """Le predicteur d'espace fixe — la jambe Aaronson du banc.

    Apprend ``p(a)`` par comptage sur ``A`` fixe. Sa log-perte sur un support
    connu est bornee par l'entropie empirique : c'est le regime du freebit
    d'Aaronson (ignorer une **valeur** dans un espace donne). La premiere action
    hors de ``A`` ne lui coute pas une grande perte : elle lui revele que son
    espace etait le mauvais objet — ``surprise_structurelle`` la quantifie en
    bits de coordination manquante (``log2(|A| + 1)``, le +1 etant la porte
    que l'espace n'avait pas).
    """

    def __init__(self, actions: tuple[str, ...]) -> None:
        if not actions:
            raise ValueError("espace d'actions vide")
        self.actions = tuple(actions)
        self._counts: dict[str, int] = {a: 0 for a in self.actions}

    def update(self, action: str) -> None:
        if action not in self._counts:
            raise KeyError(
                f"action {action!r} hors de l'espace fixe — le predicteur ne peut "
                "pas la representez (c'est le fait experimental, pas un bug)"
            )
        self._counts[action] += 1

    def log_loss(self, action: str, epsilon: float = 0.0) -> float:
        """Log-perte naturelle en bits ; ``epsilon`` lisse le zero-count."""
        if action not in self._counts:
            return self.surprise_structurelle()
        total = sum(self._counts.values()) + epsilon * len(self.actions)
        p = (self._counts[action] + epsilon) / total
        return float(-np.log2(max(p, 1e-12)))

    def surprise_structurelle(self) -> float:
        """Perte d'un point hors support, en bits : ``log2(|A| + 1)``."""
        return float(np.log2(len(self.actions) + 1))
