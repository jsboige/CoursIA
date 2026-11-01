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
    "candidate_key",
    "quorum_mechanism",
    "authority_mechanism",
    "competing_mechanisms",
    "compose_ontology",
    "composition_report",
    "expansion_ontology",
    "political_opening",
    "non_canonicity",
    "simulate_trajectory",
    "performative_power",
    "institutionalization",
    "irreversibility_debt",
    "FixedSpacePredictor",
    "BenchVerdict",
    "classer_proxys",
    "temoin_decoratif",
    "bancher_mecanisme",
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
        if len(votes.get(candidate_key(eta), ())) >= quorum:
            accepted.append(eta)
    result = game
    for eta in accepted:
        result = apply_ontology(result, eta)
    return result, tuple(accepted)


def candidate_key(eta: OntologicalMove) -> str:
    """Cle canonique d'une candidature : ses concepts tries (identite des candidats)."""
    return ",".join(sorted(eta.new_concepts))


def authority_mechanism(
    game: EvolutiveGame,
    proposals: tuple[OntologicalMove, ...],
    votes: dict[str, set[str]],
    authority: str,
) -> tuple[OntologicalMove, ...]:
    """Regle d'anciennete : seul le soutien de ``authority`` decide.

    Deuxieme regle d'admission du banc, volontairement disjointe du quorum :
    elle lit les **memes** votes mais n'en retient qu'un electeur. Avec le
    quorum seul, le choix entre extensions concurrentes est tranche par
    construction (une seule regle) ; avec les deux, il devient observable.
    """
    accepted = [
        eta for eta in proposals if authority in votes.get(candidate_key(eta), ())
    ]
    return tuple(accepted)


def competing_mechanisms(
    game: EvolutiveGame,
    proposals: tuple[OntologicalMove, ...],
    votes: dict[str, set[str]],
    mechanisms: dict[str, "object"],
    policy: str = "and",
) -> tuple[EvolutiveGame, tuple[OntologicalMove, ...], tuple[str, ...]]:
    """Deux regles d'admission se disputent les memes candidatures (#20773).

    ``mechanisms`` mappe un nom vers un appelable
    ``(game, proposals, votes) -> tuple[OntologicalMove, ...]`` (le profil de
    ``quorum_mechanism`` partiellement applique et d'``authority_mechanism``).
    ``policy`` compose les verdicts : ``"and"`` (conjonction — les deux regles
    doivent admettre) ou ``"or"`` (disjonction — une suffit).

    Retourne ``(G_{t+1}, etas_acceptes, litiges)`` ou ``litiges`` sont les
    cles des candidatures sur lesquelles les regles **divergent** (l'une
    admet, l'autre refuse) : c'est la que le choix de politique change le jeu
    public, donc l'observable propre de la concurrence.
    """
    if policy not in ("and", "or"):
        raise ValueError("policy doit valoir 'and' ou 'or'")
    if not mechanisms:
        raise ValueError("au moins une regle d'admission")
    decisions = {
        name: frozenset(
            candidate_key(eta) for eta in mech(game, proposals, votes)
        )
        for name, mech in mechanisms.items()
    }
    litiges: list[str] = []
    accepted: list[OntologicalMove] = []
    for eta in proposals:
        key = candidate_key(eta)
        admits = [key in decided for decided in decisions.values()]
        if len(set(admits)) > 1:
            litiges.append(key)
        admit = all(admits) if policy == "and" else any(admits)
        if admit:
            accepted.append(eta)
    result = game
    for eta in accepted:
        result = apply_ontology(result, eta)
    return result, tuple(accepted), tuple(litiges)


def expansion_ontology(
    g0: EvolutiveGame,
    g1: EvolutiveGame,
    equivalence: dict[str, str] | None = None,
) -> int:
    """Proxy ``O_t = |L_{t+1} \\ L_t|`` — ouverture linguistique.

    Mesure dans le **quotient** par ``equivalence`` quand celle-ci est fournie :
    on compte les **classes** de concepts nouveaux, pas les symboles. Un
    renommage ``a' ≡ a`` n'ajoute aucune classe, donc ``O_t = 0`` **par
    mesure** (et non par l'identité ``g1 = g0``). Sans ``equivalence`` : l'identité.
    """
    equiv = equivalence or {}
    classes0 = {equiv.get(x, x) for x in g0.lexicon}
    classes1 = {equiv.get(x, x) for x in g1.lexicon}
    return len(classes1 - classes0)


def political_opening(
    g0: EvolutiveGame,
    g1: EvolutiveGame,
    equivalence: dict[str, str] | None = None,
) -> int:
    """Proxy ``Delta A_t = |A_{t+1} \\ A_t|`` — garde-fou contre le verbiage.

    Mesure dans le **quotient** par ``equivalence`` : on compte les **classes**
    d'actions nouvelles, pas les symboles. Un renommage d'action
    ``a' ≡ a`` n'ouvre aucune classe, ``Delta A_t = 0`` **par mesure**.
    Sans ``equivalence`` : l'identité.
    """
    equiv = equivalence or {}
    classes0 = {equiv.get(x, x) for x in g0.actions}
    classes1 = {equiv.get(x, x) for x in g1.actions}
    return len(classes1 - classes0)


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


def compose_ontology(game: EvolutiveGame, etas: tuple[OntologicalMove, ...]) -> EvolutiveGame:
    """Compose des coups ontologiques **dans l'ordre donne** (fold d'``apply_ontology``).

    L'ordre est le parametre experimental : ``compose(G, (e1, e2))`` vs
    ``compose(G, (e2, e1))`` alimente ``composition_report``.
    """
    for eta in etas:
        game = apply_ontology(game, eta)
    return game


def composition_report(
    game: EvolutiveGame,
    eta1: OntologicalMove,
    eta2: OntologicalMove,
) -> dict:
    """Communativite de la composition de deux coups ontologiques (#20773).

    Deux ordres d'application, quatre observables :

    - ``same_lexicon`` / ``same_actions`` : le langage et l'espace de coups
      sont des unions — ils commutent *structurellement* par construction de
      l'organe ;
    - ``structural_commutativity`` : les deux precedents conjoints ;
    - ``payoff_commutativity`` :
      les paiements des actions ouvertes sont poses par ``setdefault`` au
      nom du **proposeur** — quand deux coups ouvrent la **meme action**,
      le premier poseur capture la coordonnee (paiement de proposeur 1.0)
      et le second devient simple tiers (0.5). ``payoff_conflicts`` liste
      les cles ``(agent, action)`` dont le paiement depend de l'ordre.

    Le temoin negatif du banc : deux coups ouvrant des actions **disjointes**
    doivent commuter sur les QUATRE axes — une non-commutativite mesuree sur
    ce cas serait un defaut de l'organe, pas un resultat.
    """
    g12 = compose_ontology(game, (eta1, eta2))
    g21 = compose_ontology(game, (eta2, eta1))
    conflicts = {
        k
        for k in set(g12.payoffs) | set(g21.payoffs)
        if g12.payoffs.get(k) != g21.payoffs.get(k)
    }
    return {
        "same_lexicon": g12.lexicon == g21.lexicon,
        "same_actions": g12.actions == g21.actions,
        "structural_commutativity": g12.lexicon == g21.lexicon
        and g12.actions == g21.actions,
        "payoff_commutativity": not conflicts,
        "payoff_conflicts": frozenset(conflicts),
    }


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
    equivalence: dict[str, str] | None = None,
) -> float:
    """Proxy ``P(R)`` — KL empirique (en bits) entre trajectoires ``do(eta)`` / ``do(-eta)``.

    ``D(Pr(traj | do(R)) || Pr(traj | do(not R)))`` est estimee par divergence KL
    sur les histogrammes d'actions des deux bras, a lissage de Laplace
    SYMETRIQUE sur l'union des supports (une action absente d'un bras pese
    ``log2(n_total)``, pas un plancher arbitraire : les deux bras recoivent le
    meme +1 sur le meme support).

    ``equivalence`` mappe chaque action vers sa classe d'equivalence (par
    defaut, l'identite) ; les histograms sont fusionnes par classe AVANT la KL.

    Semantique du contraste decoratif — deux lectures, pas une :

    - BRUT : une copie d'action (meme profil de paiements) reste une option
      DISTINGUEE — le softmax lui consacre du temps de jeu, et ``P(R) > 0`` ;
    - MARGINALISEE : passee sous ``equivalence`` (copie -> original),
      ``P(R) ~ 0`` — la copie ne change pas la dynamique de fond, seulement
      son habillage. C'est la meme equivalence action/classe que le quotient
      d'extensions du ``C_t`` (``non_canonicity``).

    Un coup ouvrant de vraies nouvelles actions garde un ``P(R)`` eleve dans
    les deux lectures : ses classes n'existent pas dans le bras de reference.
    """
    equiv = equivalence or {}

    def _cls(a: str) -> str:
        return equiv.get(a, a)

    def _counts(game: EvolutiveGame) -> dict[str, int]:
        agg: dict[str, int] = {}
        for _ in range(n_sim):
            for a, c in simulate_trajectory(game, horizon, rng).items():
                k = _cls(a)
                agg[k] = agg.get(k, 0) + c
        return agg

    cd, cs = _counts(game_do), _counts(game_skip)
    support = set(cd) | set(cs) | {_cls(a) for a in game_do.actions} | {_cls(a) for a in game_skip.actions}

    def _dist(counts: dict[str, int]) -> dict[str, float]:
        total = sum(counts.values()) + len(support)
        return {k: (counts.get(k, 0) + 1) / total for k in support}

    p, q = _dist(cd), _dist(cs)
    return float(sum(p[k] * np.log2(p[k] / q[k]) for k in support))


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


# ---------------------------------------------------------------------------
# Banc unique (tete de la strate 7) — unification transversale du depot
# ---------------------------------------------------------------------------
#
# ICT-46 (premier barreau) tourne les six proxys sur ses propres mecanismes
# jouets. Le banc unique (tete du palier, #23778) emploie les MEMES six proxys
# comme lentille sur des mecanismes qui changent l'espace des actions PARTOUT
# dans le depot, chacun transcrit depuis son organe natif de serie (volet A) ou
# sa copie pedagogique declaree (volet B). Le banc ne reimplimente rien : il
# mesure les proxys sur la transcription et CLASSE le coup (latent / nouveau /
# decoratif). Les trois controles et le temoin negatif vivent ici, dans l'organe.

@dataclass(frozen=True)
class BenchVerdict:
    """Resultat du banc unique pour un mecanisme : les six proxys + la classe.

    ``P_R`` est la lecture BRUTE de ``performative_power`` ; ``P_R_marg`` la
    lecture MARGINALISEE (copie -> original, via ``equivalence``). ``temoin``
    liste les violations du temoin negatif du 'decoratif' : vide = le verdict
    'decoratif' est tenu, non vide = le temoin a ROUGI (ce n'est pas decoratif).
    """

    mecanisme: str
    O_t: int
    dA_t: int
    C_t: int
    P_R: float
    P_R_marg: float
    institutionnalisation: float
    I_R: float
    classe: str
    temoin: tuple[str, ...] = ()


def classer_proxys(
    o_t: int,
    d_a_t: int,
    c_t: int,
    p_r_marg: float,
    institutionalisation: float,
    eps: float = 1e-2,
) -> str:
    """Les trois controles du banc, decides par les proxys MESURES.

    - ``nouveau``   : l'espace change reellement (``O_t > 0`` et ``dA_t > 0``)
      ET le coup survit au retrait de son instigateur (``institutionnalisation > 0``) ;
    - ``latent``    : l'espace ne change pas (``O_t = 0`` et ``dA_t = 0``) mais la
      coordonnee preexistante est activee (``P(R) marginalisee > eps``) ;
    - ``decoratif`` : l'espace ne change pas ET, sous marginalisation par
      equivalence, ``P(R) -> 0`` (<= ``eps``) et la famille d'extensions est
      canonique (``C_t = 1`` — il n'y a rien a choisir).
    """
    if o_t > 0 and d_a_t > 0:
        return "nouveau" if institutionalisation > 0 else "nouveau (non institutionnalise)"
    if o_t == 0 and d_a_t == 0:
        if p_r_marg > eps:
            return "latent"
        if c_t == 1:
            return "decoratif"
        return "decoratif? (C_t > 1)"
    return "?"


def temoin_decoratif(
    o_t: int,
    d_a_t: int,
    c_t: int,
    p_r_marg: float,
    eps: float = 1e-2,
) -> tuple[str, ...]:
    """Le temoin negatif du 'decoratif' — une assertion **falsifiable**.

    Le verdict 'decoratif' tient si et seulement si les QUATRE conjoncts sont
    vrais : ``P(R) marginalisee < eps``, ``C_t == 1``, ``O_t == 0``,
    ``dA_t == 0``. Chaque violation est nommee, et c'est elle qui fait
    ROUGIR le temoin (le coup n'est pas decoratif) :

    - ``P(R)`` ne tombe pas a 0 sous l'equivalence -> l'habillage change en
      realite la trajectoire (un coup qui agit, pas du vernis) ;
    - ``C_t > 1`` -> le 'renommage' n'est pas un vrai renommage (les
      extensions ne sont pas equivalentes) ;
    - ``O_t > 0`` ou ``dA_t > 0`` -> il y a un ajout reel (pas un habillage).

    Retourne le n-uplet des violations (vide = le 'decoratif' est tenu).
    """
    violations: list[str] = []
    if p_r_marg > eps:
        violations.append("P(R) marginalisee > eps : l'habillage change la trajectoire")
    if c_t != 1:
        violations.append(f"C_t = {c_t} != 1 : les extensions ne sont pas equivalentes")
    if o_t > 0:
        violations.append(f"O_t = {o_t} > 0 : ajout reel de concepts")
    if d_a_t > 0:
        violations.append(f"Delta A_t = {d_a_t} > 0 : ajout reel d'actions")
    return tuple(violations)


def bancher_mecanisme(
    mecanisme: str,
    g0: EvolutiveGame,
    g1: EvolutiveGame,
    eta: OntologicalMove,
    candidate_extensions: tuple[OntologicalMove, ...],
    equivalence: dict[str, str] | None = None,
    horizon: int = 40,
    n_sim: int = 60,
    rng: np.random.Generator | None = None,
    eps: float = 1e-2,
) -> BenchVerdict:
    """Point d'entree du banc unique : passe un mecanisme a la grille d'ICT-46.

    L'appelant transcrit l'effet du mecanisme — mesure par son **organe natif**
    de serie (volet A) ou par sa **copie pedagogique declaree** (volet B) — en
    une paire de jeux ``g0`` (avant) / ``g1`` (apres) + le coup ``eta`` qui le
    capture. Le banc mesure alors les six proxys sur cette transcription et
    **classe** le coup (``classer_proxys``), en exposant le temoin negatif
    (``temoin``). Il ne reimplimente aucun mecanisme d'une autre serie.

    ``candidate_extensions`` alimente ``C_t`` (``non_canonicity``) ;
    ``equivalence`` alimente la lecture marginalisee de ``P(R)`` (copie ->
    original). ``g1`` joue le bras ``do(R)`` et ``g0`` le bras ``do(-R)``.
    """
    if rng is None:
        rng = np.random.default_rng(0)
    o_t = expansion_ontology(g0, g1, equivalence)
    d_a_t = political_opening(g0, g1, equivalence)
    c_t = non_canonicity(g0, candidate_extensions)
    p_r = performative_power(g1, g0, horizon, n_sim, rng)
    p_r_marg = performative_power(g1, g0, horizon, n_sim, rng, equivalence)
    inst = institutionalization(g1, eta, horizon, rng)
    i_r = irreversibility_debt(eta)
    return BenchVerdict(
        mecanisme=mecanisme,
        O_t=o_t,
        dA_t=d_a_t,
        C_t=c_t,
        P_R=p_r,
        P_R_marg=p_r_marg,
        institutionnalisation=inst,
        I_R=i_r,
        classe=classer_proxys(o_t, d_a_t, c_t, p_r_marg, inst, eps),
        temoin=temoin_decoratif(o_t, d_a_t, c_t, p_r_marg, eps),
    )
