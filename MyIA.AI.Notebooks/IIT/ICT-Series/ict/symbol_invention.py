"""Invention de symboles — jeux de signalisation a vocabulaire croissant (strate 7, jambe D2 experience B, #7746).

Contexte
--------
L'experience A (``signaling_convention``) etablit la ligne de base « sans coup
ontologique » : un vocabulaire FIXE, et l'on demande si une convention emerge.
Elle montre (verdict GOULOT) qu'un vocabulaire INSUFFISANT borne strictement la
signification atteignable — c'est le resultat qui MOTIVE l'experience B.

L'experience B lève la contrainte : le vocabulaire n'est plus donne, il est
INVENTE. Partant de peu (voire un seul signal), les agents peuvent, sur echec de
coordination, faire un **coup ontologique** — creer un nouveau signal. La
question falsifiable : le vocabulaire croît-il **jusqu'a ce qu'il suffise**
(autour de ``n_states``), ni en-deca (sous-optimal) ni au-dela (goulot resolu) ?
Et ce, sous un cout d'invention qui penalise la proliferation sterile ?

C'est le passage de Lewis (convention sur un code donne) a Skyrms (*Signals*
2010, ch. « invention ») : la **signification emerge ET le repertoire de
signaux croît par besoin de compression / prediction**. Nowak & Krakauer 1999
et Hofbauer & Hoppensteadt 1998 montrent que l'information mutuelle entre etat
et signal est selecxionnee sous coordination : un signal qui distingue mieux un
etat est renforce, et l'invention d'un tel signal est payante. Le couplage
invention-erreur est l'homologue, strate 7, du Rescorla-Wagner strate 3 (la
valence apprise croît par erreur de prediction) : ici c'est le vocabulaire qui
croît par erreur de coordination.

Mecanisme
---------
Extension de Roth-Erev (cf ``signaling_convention``) avec dimension dynamique.
``InventingSignalingGame`` maintient ``Q_s[etat, signal]`` et
``Q_r[signal, action]`` dont le nombre de colonnes/lignes de signaux **croît**.
A chaque tour :

1. un etat ``s`` est tire ;
2. l'emetteur choisit un signal parmi le vocabulaire courant (softmax) ;
3. le recepteur choisit une action (softmax) ;
4. le paiement de coordination vaut 1 si ``a == s`` ;
5. le paiement de coordination vaut 1 si ``a == s`` ;
6. **sur echec** (``a != s``), avec probabilite ``invention_rate`` et si le
   vocabulaire n'a pas atteint ``max_signals``, un nouveau signal est INVENTE
   (extension des matrices ``Q`` par ``initial_q``) — mais seulement si le
   **deficit de coordination recent** (1 - succes court) **excède le cout
   d'invention** : l'agent n'invente que si c'est economiquement rentable.

L'auto-arret emerge mecaniquement : quand une bijection etat->signal->action se
forme, le taux de coordination tend vers 1, le deficit de coordination tend vers
0, et l'invention cesse (son seuil de rentabilite n'est plus atteint). Le
vocabulaire se stabilise autour de ``n_states``. Si le cout d'invention est trop
eleve, l'invention est inhibee avant coordination parfaite et les agents restent
a un vocabulaire sous-optimal — un equilibre fige deliberement atteint (pont vers
l'experience E « inhibition de l'innovation »).

Portee de ce module (cycle-1 d'un livrable multi-cycle)
-------------------------------------------------------
Module ADDITIF numpy-only, CPU. Il reutilise ``mutual_information`` de
``signaling_convention`` (pas de duplication) et fournit la classe
``InventingSignalingGame`` + 4 verdicts falsifiables : croissance-a-la-mesure,
seuil de cout d'invention, gain de compression, diversite d'ontologies. Aucune
modification des modules existants.

References
----------
Skyrms 2010 (*Signals*, ch. invention/meaning) ; Nowak & Krakauer 1999
(evolution of language, compression) ; Hofbauer & Hoppensteadt 1998 (selection
for information) ; spec #7746 (experience B : invention de symboles, croissance
du vocabulaire, gain de compression, diversite d'ontologies).
"""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np

from ict.signaling_convention import mutual_information


def _softmax(propensities: np.ndarray, temperature: float,
             rng: np.random.Generator) -> int:
    """Tire un indice selon une softmax des propensites (temperature ``T``).

    ``T`` grand = proche de l'uniforme (exploration) ; ``T`` petit = glouton
    (exploitation). ``T -> 0`` = argmax deterministe.
    """
    scaled = propensities / max(temperature, 1e-9)
    scaled = scaled - scaled.max()
    weights = np.exp(scaled)
    probs = weights / weights.sum()
    return int(rng.choice(len(probs), p=probs))


class InventingSignalingGame:
    """Jeu de signalisation Lewis/Skyrms ou le vocabulaire est INVENTE.

    Etend ``SignalingGame`` (experience A) par une dimension dynamique : le
    nombre de signaux croît sur echec de coordination, sous un cout. Voir la
    docstring du module pour le mecanisme complet.

    Parametres
    ----------
    n_states : int
        Nombre d'etats du monde (dimension de l'observation).
    n_signals_init : int
        Taille du vocabulaire INITIAL (typiquement 1 ou 2 — sous-optimal, c'est
        ce qui motive l'invention).
    max_signals : Optional[int]
        Plafond absolu du vocabulaire (anti-proliferation numerique). Defaut :
        ``n_states`` (au-dela, un signal par etat est superflu).
    n_actions : Optional[int]
        Nombre d'actions du recepteur. Defaut : ``n_states``.
    temperature : float
        Temperature softmax du choix (annealable via :meth:`train`).
    state_dist : Optional[Sequence[float]]
        Distribution des etats. Defaut : uniforme.
    initial_q : float
        Propensite initiale (> 0) des entrees existantes ET valeur de bord des
        nouveaux signaux inventes (neutre — le nouveau signal n'est ni prefere
        ni evite a sa naissance).
    invention_rate : float
        Probabilite, sur echec de coordination, d'inventer un nouveau signal
        (si le plafond n'est pas atteint). Pilotage par l'erreur.
    invention_cost : float
        Cout (seuil economique) de l'invention. L'agent n'invente sur echec que
        si le deficit de coordination recent (1 - taux de succes court) EXCEDE ce
        cout. ``0.0`` = invention gratuite (tentee des que la coordination n'est
        pas parfaite -> vocabulaire croît vers ``n_states``) ; eleve = invention
        inhibee tôt (vocabulaire sous-optimal fige). C'est le levier du verdict
        SEUIL DE COUT (#7746 experience B).
    """

    def __init__(
        self,
        n_states: int,
        n_signals_init: int = 1,
        *,
        max_signals: Optional[int] = None,
        n_actions: Optional[int] = None,
        temperature: float = 0.5,
        state_dist: Optional[Sequence[float]] = None,
        initial_q: float = 1.0,
        invention_rate: float = 0.05,
        invention_cost: float = 0.0,
        rng: Optional[np.random.Generator] = None,
    ) -> None:
        if n_states < 1:
            raise ValueError(f"n_states >= 1 requis (recu {n_states}).")
        if n_signals_init < 1:
            raise ValueError(f"n_signals_init >= 1 requis (recu {n_signals_init}).")
        n_actions = n_states if n_actions is None else n_actions
        if n_actions < 1:
            raise ValueError(f"n_actions >= 1 requis (recu {n_actions}).")
        max_signals = n_states if max_signals is None else max_signals
        if max_signals < n_signals_init:
            raise ValueError(
                f"max_signals ({max_signals}) >= n_signals_init ({n_signals_init}) requis."
            )
        if temperature <= 0.0:
            raise ValueError(f"temperature > 0 requis (recu {temperature}).")
        if initial_q <= 0.0:
            raise ValueError(f"initial_q > 0 requis (recu {initial_q}).")
        if not 0.0 <= invention_rate <= 1.0:
            raise ValueError(f"invention_rate dans [0, 1] requis (recu {invention_rate}).")
        if invention_cost < 0.0:
            raise ValueError(f"invention_cost >= 0 requis (recu {invention_cost}).")
        if state_dist is None:
            state_dist = np.full(n_states, 1.0 / n_states)
        else:
            state_dist = np.asarray(state_dist, dtype=float)
            if state_dist.shape != (n_states,):
                raise ValueError(
                    f"state_dist doit avoir {n_states} elements (recu {state_dist.shape})."
                )
            if state_dist.sum() <= 0.0 or np.any(state_dist < 0.0):
                raise ValueError("state_dist doit etre une distribution (>= 0, somme > 0).")
            state_dist = state_dist / state_dist.sum()
        self.n_states = n_states
        self.n_signals_init = n_signals_init
        self.max_signals = max_signals
        self.n_actions = n_actions
        self.temperature = temperature
        self.state_dist = state_dist
        self.initial_q = initial_q
        self.invention_rate = invention_rate
        self.invention_cost = invention_cost
        self.rng = rng if rng is not None else np.random.default_rng()
        self.reset()

    def reset(self) -> None:
        """Reinitialise : vocabulaire a ``n_signals_init``, propensites uniformes."""
        self.n_signals = self.n_signals_init
        self.n_inventions = 0
        self.Q_s = np.full((self.n_states, self.n_signals), self.initial_q, dtype=float)
        self.Q_r = np.full((self.n_signals, self.n_actions), self.initial_q, dtype=float)
        self.joint_state_signal = np.zeros((self.n_states, self.n_signals), dtype=float)
        self.success_history: List[int] = []
        self.payoff_history: List[float] = []
        self.vocab_history: List[int] = []

    def _invent(self) -> bool:
        """Etend les matrices Q d'un signal. Renvoie False si plafond atteint."""
        if self.n_signals >= self.max_signals:
            return False
        self.n_signals += 1
        # Bord neutre : le nouveau signal demarre a initial_q (ni prefere ni evite).
        self.Q_s = np.pad(self.Q_s, ((0, 0), (0, 1)), constant_values=self.initial_q)
        self.Q_r = np.pad(self.Q_r, ((0, 1), (0, 0)), constant_values=self.initial_q)
        self.joint_state_signal = np.pad(
            self.joint_state_signal, ((0, 0), (0, 1)), constant_values=0.0
        )
        self.n_inventions += 1
        return True

    def play_round(self, reinforce: bool = True) -> Tuple[int, int, int, float]:
        """Un tour de jeu. Renvoie ``(etat, signal, action, paiement_net)``.

        Le paiement net vaut 1 (coordination) moins le cout ponctuel d'une
        invention eventuelle ce tour. L'invention se declenche sur ECHEC de
        coordination selon un mecanisme economique : l'agent n'invente que si le
        deficit de coordination recent (1 - taux de succes court) EXCEDE le cout
        d'invention — i.e. l'invention est tente uniquement si elle est rentable
        (le gain espere de distinguer un nouvel etat couvre l'effort). C'est ce
        couplage cout/deficit qui produit le trade-off : un cout eleve fait cesser
        l'invention alors que la coordination est encore imparfaite (vocabulaire
        sous-optimal deliberement fige), un cout nul laisse l'invention courir
        jusqu'a coordination parfaite (vocabulaire -> ``n_states``).
        """
        state = int(self.rng.choice(self.n_states, p=self.state_dist))
        signal = _softmax(self.Q_s[state], self.temperature, self.rng)
        action = _softmax(self.Q_r[signal], self.temperature, self.rng)
        coordinated = 1 if action == state else 0
        self.joint_state_signal[state, signal] += 1.0
        self.success_history.append(coordinated)
        self.vocab_history.append(self.n_signals)
        # Invention pilotee par l'erreur ET le trade-off economique : sur echec,
        # si le deficit de coordination recent depasse le cout, avec proba invention_rate.
        invented = False
        if reinforce and coordinated == 0 and self.n_signals < self.max_signals:
            recent_fail_rate = 1.0 - self.success_rate(50)
            if recent_fail_rate > self.invention_cost and self.rng.random() < self.invention_rate:
                invented = self._invent()
        net = float(coordinated - (self.invention_cost if invented else 0.0))
        self.payoff_history.append(net)
        if reinforce and coordinated == 1:
            self.Q_s[state, signal] += 1.0
            self.Q_r[signal, action] += 1.0
        return state, signal, action, net

    def train(self, n_rounds: int, anneal_to: Optional[float] = None) -> None:
        """Apprend pendant ``n_rounds``. Annealing optionnel de la temperature."""
        if n_rounds < 0:
            raise ValueError(f"n_rounds >= 0 requis (recu {n_rounds}).")
        t0 = self.temperature
        for t in range(n_rounds):
            if anneal_to is not None and n_rounds > 1:
                frac = t / (n_rounds - 1)
                self.temperature = t0 + frac * (anneal_to - t0)
            self.play_round(reinforce=True)
        self.temperature = t0

    def success_rate(self, window: int = 500) -> float:
        """Taux de coordination BRUT (action==etat) sur les ``window`` derniers tours."""
        if not self.success_history:
            return 0.0
        recent = self.success_history[-window:]
        return float(np.mean(recent))

    def net_payoff_rate(self, window: int = 500) -> float:
        """Paiement net moyen (apres cout d'invention) sur les ``window`` derniers tours."""
        if not self.payoff_history:
            return 0.0
        recent = self.payoff_history[-window:]
        return float(np.mean(recent))

    def final_vocab_size(self) -> int:
        """Taille du vocabulaire a la fin de l'entrainement."""
        return self.n_signals

    def dominant_signal_per_state(self) -> List[int]:
        """Signal dominant par etat (argmax de la politique emettrice apres apprentissage).

        Sert a comparer les ontologies emergentes : deux runs peuvent converger
        vers des bijections etat->signal DIFFERENTES (convention arbitraire de Lewis).
        """
        # Politique emettrice moyennee sur la joint (frequence d'usage), pas Q brute,
        # car Q reflete la propensite mais l'usage revele la convention etablie.
        mapping: List[int] = []
        for s in range(self.n_states):
            if s < self.joint_state_signal.shape[0]:
                row = self.joint_state_signal[s]
                mapping.append(int(np.argmax(row)) if row.sum() > 0 else -1)
            else:
                mapping.append(-1)
        return mapping


# ---------------------------------------------------------------------------
# Bancs d'essai (protocoles #7746 D2 experience B) — chacun renvoie un verdict
# falsifiable.
# ---------------------------------------------------------------------------


def vocabulary_grows_to_fit_test(
    n_states: int = 4,
    n_signals_init: int = 1,
    n_rounds: int = 6000,
    temperature: float = 0.6,
    anneal_to: float = 0.15,
    invention_rate: float = 0.05,
    invention_cost: float = 0.0,
    window: int = 800,
    seed: int = 0,
) -> Dict[str, float]:
    """Verdict CROISSANCE-A LA-MESURE : le vocabulaire croît-il jusqu'a ``n_states`` ?

    On part d'un vocabulaire SCARSE (``n_signals_init = 1`` — un seul signal ne
    peut distinguer aucun etat, coordination ~ ``1/n_states``). Avec invention
    active, le vocabulaire doit croître et la coordination monter vers 1.0.

    Le controle negatif (falsifiabilite) : sans invention
    (``invention_rate = 0``), le vocabulaire reste a 1 et la coordination plafonne
    a ~ ``1/n_states`` (hasard). Le verdict n'est satisfait que si l'invention
    FAIT croître le vocabulaire ET depasse nettement le controle.

    Verdict falsifiable
    -------------------
    ``grew_to_fit`` est True ssi (a) le vocabulaire final atteint ``n_states``
    (croissance jusqu'a la taille suffisante), (b) le succes final est eleve
    (> 0.8), ET (c) le controle sans-invention stagne (vocab reste init, succes
    < 0.5). Un vocabulaire qui croîtrait au-dela de ``n_states`` sans gain de
    succes echouerait aussi (proliferation sterile non observee ici).
    """
    # Avec invention.
    g = InventingSignalingGame(
        n_states, n_signals_init, temperature=temperature,
        invention_rate=invention_rate, invention_cost=invention_cost,
        rng=np.random.default_rng(seed),
    )
    g.train(n_rounds, anneal_to=anneal_to)
    invented_vocab = g.final_vocab_size()
    invented_success = g.success_rate(window)
    # Controle sans invention (meme graine, invention desactivee).
    g_ctrl = InventingSignalingGame(
        n_states, n_signals_init, temperature=temperature,
        invention_rate=0.0, invention_cost=invention_cost,
        rng=np.random.default_rng(seed),
    )
    g_ctrl.train(n_rounds, anneal_to=anneal_to)
    ctrl_vocab = g_ctrl.final_vocab_size()
    ctrl_success = g_ctrl.success_rate(window)

    grew_to_fit = (
        invented_vocab >= n_states
        and invented_success > 0.8
        and ctrl_vocab <= n_signals_init
        and ctrl_success < 0.5
    )
    return {
        "n_states": float(n_states),
        "n_signals_init": float(n_signals_init),
        "invented_vocab": float(invented_vocab),
        "invented_success": invented_success,
        "control_vocab": float(ctrl_vocab),
        "control_success": ctrl_success,
        "grew_to_fit": 1.0 if grew_to_fit else 0.0,
    }


def invention_cost_tradeoff_test(
    n_states: int = 6,
    n_signals_init: int = 1,
    n_rounds: int = 8000,
    temperature: float = 0.6,
    anneal_to: float = 0.15,
    invention_rate: float = 0.05,
    window: int = 800,
    seed: int = 0,
) -> Dict[str, float]:
    """Verdict SEUIL DE COUT : existe-t-il un cout d'invention critique ?

    On balaie le cout d'invention de 0 (gratuit) a un cout eleve. Sous un seuil,
    l'invention est rentable (vocabulaire croît vers ``n_states``, coordination
    elevee) ; au-dessus, l'invention coute plus qu'elle ne rapporte et les agents
    RESTENT a un vocabulaire sous-optimal (equilibre fige deliberement atteint —
    le cout inhibe l'ontologie, pont vers l'experience E « inhibition de
    l'innovation »).

    NB honnete : la transition cout->vocabulaire est quasi-binaire pour peu
    d'etats (n_states=4 : step autour de cost~0.85) et graduelle pour un nombre
    d'etats suffisant (n_states=6 : cost 0 -> 6, 0.6 -> 5, 0.85 -> 4, 0.95 -> 3).
    On utilise donc ``n_states=6`` pour que la transition soit OBSERVABLE (un
    verdict sur un step binaire est moins informatif).

    Verdict falsifiable
    -------------------
    ``cost_threshold`` est True ssi (a) a cout nul le vocabulaire atteint
    ``n_states`` (invention rentable), (b) a cout eleve le vocabulaire reste
    strictement sous ``n_states`` (invention inhibee), ET (c) il existe entre les
    deux une transition decroissante (le vocabulaire final diminue quand le cout
    augmente). Un verdict ou le vocabulaire serait insensible au cout serait
    falsifie (l'invention ne serait pas un trade-off).
    """
    # Plage couvrant la transition graduelle observee pour n_states=6 : cout nul
    # -> saturation ; cout ~0.6 -> 1 signal sous n_states ; cout ~0.85/0.95 ->
    # invention fortement inhibee.
    costs = [0.0, 0.6, 0.85, 0.95]
    vocab_per_cost: List[float] = []
    success_per_cost: List[float] = []
    for c in costs:
        g = InventingSignalingGame(
            n_states, n_signals_init, temperature=temperature,
            invention_rate=invention_rate, invention_cost=c,
            rng=np.random.default_rng(seed),
        )
        g.train(n_rounds, anneal_to=anneal_to)
        vocab_per_cost.append(float(g.final_vocab_size()))
        success_per_cost.append(g.success_rate(window))

    vocab_free = vocab_per_cost[0]
    vocab_costly = vocab_per_cost[-1]
    # Transition : le vocabulaire final decroît avec le cout (au moins un palier).
    strictly_decreasing = any(
        vocab_per_cost[i] > vocab_per_cost[i + 1] for i in range(len(vocab_per_cost) - 1)
    )
    cost_threshold = (
        vocab_free >= n_states
        and vocab_costly < n_states
        and strictly_decreasing
    )
    return {
        "n_states": float(n_states),
        "costs": costs,  # type: ignore[dict-item]
        "vocab_per_cost": vocab_per_cost,
        "success_per_cost": success_per_cost,
        "vocab_at_free_cost": vocab_free,
        "vocab_at_high_cost": vocab_costly,
        "cost_threshold": 1.0 if cost_threshold else 0.0,
    }


def compression_gain_test(
    n_states: int = 4,
    n_signals_init: int = 1,
    n_rounds: int = 6000,
    temperature: float = 0.6,
    anneal_to: float = 0.15,
    invention_rate: float = 0.05,
    window: int = 800,
    seed: int = 0,
) -> Dict[str, float]:
    """Verdict GAIN DE COMPRESSION : l'invention accroît-elle l'information mutuelle ?

    Le « gain de compression » se mesure comme la reduction d'incertitude du
    recepteur sur l'etat grace au signal : ``I(etat ; signal) = H(etat) - H(etat | signal)``.
    Un signal non informatif (pooling) laisse toute l'incertitude ; un code
    conventionnel la leve (``I -> log2(n_states)``). L'experience A montrait
    (GOULOT) qu'un vocabulaire FIXE insuffisant plafonne la MI. Ici, l'invention
    doit lever ce plafond : la MI avec invention depasse strictement la MI sans
    invention.

    Mesure de la politique COURANTE (matrice jointe reinitialisee apres
    apprentissage, tours sans renforcement) pour ne pas confondre l'historique
    d'exploration avec la convention etablie.

    Verdict falsifiable
    -------------------
    ``compression_gain`` est True ssi (a) la MI avec invention est elevee
    (> 0.5 * log2(n_states)), ET (b) elle depasse strictement la MI sans invention
    (ratio > 1.6). Un gain nul falsifierait : l'invention ne comprime pas.
    """
    max_mi = float(np.log2(n_states))

    def _mi(inventing: bool) -> float:
        g = InventingSignalingGame(
            n_states, n_signals_init, temperature=temperature,
            invention_rate=invention_rate if inventing else 0.0,
            rng=np.random.default_rng(seed),
        )
        g.train(n_rounds, anneal_to=anneal_to)
        # Politique courante apres apprentissage.
        g.joint_state_signal[:] = 0.0
        for _ in range(window):
            g.play_round(reinforce=False)
        return mutual_information(g.joint_state_signal)

    mi_invented = _mi(True)
    mi_no_invent = _mi(False)
    ratio = mi_invented / mi_no_invent if mi_no_invent > 1e-9 else float("inf")
    compression_gain = mi_invented > 0.5 * max_mi and ratio > 1.6
    return {
        "max_mi": max_mi,
        "mi_with_invention": mi_invented,
        "mi_without_invention": mi_no_invent,
        "compression_ratio": float(ratio) if np.isfinite(ratio) else -1.0,
        "compression_gain": 1.0 if compression_gain else 0.0,
    }


def ontology_diversity_test(
    n_states: int = 4,
    n_signals_init: int = 1,
    n_rounds: int = 6000,
    temperature: float = 0.6,
    anneal_to: float = 0.15,
    invention_rate: float = 0.05,
    n_seeds: int = 6,
    window: int = 800,
) -> Dict[str, float]:
    """Verdict DIVERSITE D'ONTOLOGIES : les conventions emergentes sont-elles distinctes ?

    La theorie de Lewis (1969) dit qu'une convention est ARBITRAIRE : plusieurs
    bijections etat->signal->action sont des equilibres equally-bons. Sur des
    graines differentes, le HASARD de l'exploration doit donc faire converger
    vers des conventions DIFFERENTES (des ontologies distinctes), pas vers un
    code unique.

    On mesure, pour chaque graine, le signal dominant par etat (la convention
    etablie) et l'on compte combien de conventions DISTINCTES emergent. Pour
    ``n_states`` etats, il y a ``n_states!`` bijections possibles ; on n'en
    observe qu'une poignee, mais strictement plus d'une.

    Verdict falsifiable
    -------------------
    ``diverse`` est True ssi (a) chaque run etablit une bijection (4 signaux
    dominants distincts pour 4 etats), ET (b) au moins 2 conventions distinctes
    emergent sur les ``n_seeds`` graines. Un verdict ou toutes les graines
    convergeraient vers la MEME convention serait falsifie (la convention ne
    serait pas arbitraire).
    """
    conventions: List[Tuple[int, ...]] = []
    all_bijections = True
    final_successes: List[float] = []
    for seed in range(n_seeds):
        g = InventingSignalingGame(
            n_states, n_signals_init, temperature=temperature,
            invention_rate=invention_rate, rng=np.random.default_rng(seed),
        )
        g.train(n_rounds, anneal_to=anneal_to)
        final_successes.append(g.success_rate(window))
        # Convention = signal dominant par etat (usage, pas Q brute).
        g.joint_state_signal[:] = 0.0
        for _ in range(window):
            g.play_round(reinforce=False)
        mapping = g.dominant_signal_per_state()
        conv = tuple(mapping)
        conventions.append(conv)
        # Bijection : ``n_states`` signaux dominants distincts (et tous >= 0).
        distinct = set(mapping)
        if len(distinct) != n_states or any(m < 0 for m in mapping):
            all_bijections = False

    distinct_conventions = set(conventions)
    n_distinct = len(distinct_conventions)
    mean_success = float(np.mean(final_successes)) if final_successes else 0.0
    diverse = all_bijections and n_distinct >= 2 and mean_success > 0.7
    return {
        "n_seeds": float(n_seeds),
        "n_states": float(n_states),
        "n_distinct_conventions": float(n_distinct),
        "all_runs_bijections": 1.0 if all_bijections else 0.0,
        "mean_final_success": mean_success,
        "conventions": [list(c) for c in conventions],  # type: ignore[dict-item]
        "diverse": 1.0 if diverse else 0.0,
    }
