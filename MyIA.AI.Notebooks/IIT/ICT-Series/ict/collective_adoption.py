"""Module #7746 D2 experience C : adoption collective et seuil de performativite rho_c.

Le troisieme des cinq bancs d'essai controles de la strate 7 (#7746). L'experience A
(``signaling_convention``, #8842) etablit la baseline « vocabulaire fixe » : un couple
emetteur/recepteur apprend a coordonner. L'experience B (``symbol_invention``, #8850)
leve la contrainte : le vocabulaire est INVENTE. Cette experience C modele
l'ADOPTION COLLECTIVE : une fraction ``rho`` d'agents « instigateurs » pre-engages vers
une convention novelle, et la question de la fraction minimale ``rho_c`` pour que cette
convention devienne CAUSALE — c.-a-d. cascade vers la population entiere. C'est
l'instanciation du seuil de bascule de C4 (#7743, grammaire de propagation).

Modele
------
Une population de ``n_agents`` agents, chacun dote d'une politique Roth-Erev
(``Q_s[etat, signal]`` + ``Q_r[signal, action]``, comme dans ``signaling_convention``).
Une bijection ``cible`` (state -> signal -> action) est choisie. Une fraction ``rho``
des agents sont des « instigateurs » : leur Q est EPPINGLEE sur la cible (engagement
fort, non mis a jour). Les autres sont « naifs » (Q uniforme). A chaque tour, les agents
sont apparies aleatoirement par paires, jouent un jeu de coordination, et les agents
naifs renforcent leurs propensites (Roth-Erev). On mesure le TAUX D'ADOPTION : la
fraction des naifs dont la politique dominante egale la convention cible.

Dynamique de masse critique (Centola 2010, Schelling, Granovetter 1978) : une innovation
diffuse a fixation ssi elle depasse une fraction critique de porteurs. Sous ``rho_c``,
les naifs interagissent surtout entre eux -> convergent vers une convention arbitraire
(adoption cible ~1/n_signals, hasard). Au-dessus de ``rho_c``, la pression des
instigateurs domine -> la cible cascade (adoption -> 1).

Le couplage adoption-par-seuil est l'homologue strate-7 (multi-agent) du couplage
invention-par-erreur de l'experience B (mono-agent) et de la convention-par-renforcement
de l'experience A (mono-agent).

numpy CPU ; reutilise ``_softmax`` et ``mutual_information`` de ``signaling_convention``
(pas de duplication).
"""

from __future__ import annotations

from typing import Dict, Optional, Sequence, Tuple

import numpy as np

from ict.signaling_convention import _softmax, mutual_information


class AdoptionGame:
    """Population de ``n_agents`` jouant un jeu de signalisation avec une fraction
    ``rho`` d'instigateurs epingles sur une convention cible.

    Parametres
    ----------
    n_agents : int
        Taille de la population (>= 2, pour pouvoir apparier).
    n_states : int
        Nombre d'etats = taille du vocabulaire = nombre d'actions. La convention cible
        est la bijection identite (etat ``s`` -> signal ``s`` -> action ``s``).
    instigator_fraction : float
        Fraction ``rho`` in [0, 1] d'agents instigateurs.
    instigator_strength : float
        Propensite des cellules cibles chez les instigateurs (les autres cellules a
        ``1/instigator_strength``). Un valeur elevee => les instigateurs jouent la cible
        de maniere quasi-deterministe.
    temperature : float
        Temperature softmax. ``anneal_to`` la reduit en fin d'apprentissage
        (anti-pooling, exploitation finale).
    initial_q : float
        Propensite initiale uniforme des agents naifs (> 0).
    pin_instigators : bool
        Si Vrai (defaut), les instigateurs ne sont JAMAIS mis a jour (engagement fort).
        Si Faux, ils apprennent aussi (mais demarrent fort sur la cible).
    rng : Optional[np.random.Generator]
        Generateur aleatoire. Defaut : nouveau.
    """

    def __init__(
        self,
        n_agents: int = 24,
        n_states: int = 3,
        *,
        instigator_fraction: float = 0.3,
        instigator_strength: float = 10.0,
        temperature: float = 0.5,
        initial_q: float = 1.0,
        pin_instigators: bool = True,
        rng: Optional[np.random.Generator] = None,
    ) -> None:
        if n_agents < 2:
            raise ValueError(f"n_agents >= 2 requis (recu {n_agents}).")
        if n_states < 2:
            raise ValueError(f"n_states >= 2 requis (recu {n_states}).")
        if not 0.0 <= instigator_fraction <= 1.0:
            raise ValueError(
                f"instigator_fraction dans [0, 1] requis (recu {instigator_fraction})."
            )
        if instigator_strength <= 0.0:
            raise ValueError(f"instigator_strength > 0 requis (recu {instigator_strength}).")
        if temperature <= 0.0:
            raise ValueError(f"temperature > 0 requis (recu {temperature}).")
        if initial_q <= 0.0:
            raise ValueError(f"initial_q > 0 requis (recu {initial_q}).")

        self.n_agents = int(n_agents)
        self.n_states = int(n_states)
        self.n_signals = int(n_states)
        self.n_actions = int(n_states)
        self.instigator_fraction = float(instigator_fraction)
        self.instigator_strength = float(instigator_strength)
        self.temperature = float(temperature)
        self.initial_q = float(initial_q)
        self.pin_instigators = bool(pin_instigators)
        self.rng = rng if rng is not None else np.random.default_rng()

        # Convention cible : bijection identite. signal_per_state[s] = s, action_per_signal[m] = m.
        self.target_signal = np.arange(self.n_states)
        self.target_action = np.arange(self.n_states)
        self.reset()

    def reset(self) -> None:
        """Reinitialise la population : ``floor(rho*N)`` instigateurs epingles, le reste naif."""
        n_instig = int(round(self.instigator_fraction * self.n_agents))
        # Q_s[agent, etat, signal], Q_r[agent, signal, action]
        self.Q_s = np.full(
            (self.n_agents, self.n_states, self.n_signals), self.initial_q, dtype=float
        )
        self.Q_r = np.full(
            (self.n_agents, self.n_signals, self.n_actions), self.initial_q, dtype=float
        )
        # Masque instigateur (les n_instig premiers, apres permutation aleatoire).
        self.is_instigator = np.zeros(self.n_agents, dtype=bool)
        order = self.rng.permutation(self.n_agents)
        self.is_instigator[order[:n_instig]] = True
        # Epingler les instigateurs sur la cible.
        strong = self.instigator_strength
        weak = self.initial_q / max(self.instigator_strength, 1.0)
        for a in np.where(self.is_instigator)[0]:
            for s in range(self.n_states):
                self.Q_s[a, s, :] = weak
                self.Q_s[a, s, self.target_signal[s]] = strong
            for m in range(self.n_signals):
                self.Q_r[a, m, :] = weak
                self.Q_r[a, m, self.target_action[m]] = strong
        # Comptes joints par agent (pour mesurer la convention dominante via MI).
        self.joint_state_signal = np.zeros(
            (self.n_agents, self.n_states, self.n_signals), dtype=float
        )
        self.success_history: list[float] = []
        self.n_instigators = int(n_instig)
        self.n_naive = self.n_agents - self.n_instigators

    def play_round(self, reinforce: bool = True) -> float:
        """Un tour = ``n_agents//2`` paires aleatoires, chacune joue une coordination.

        Renvoie le taux de coordination moyen sur ce tour. Les rôles emetteur/recepteur
        sont tires aleatoirement dans chaque paire. Les agents naifs renforcent
        (Roth-Erev) en cas de succes ; les instigateurs sont epingles
        (``pin_instigators``) ou apprennent aussi.
        """
        order = self.rng.permutation(self.n_agents)
        payoffs: list[int] = []
        for i in range(0, self.n_agents - 1, 2):
            a, b = order[i], order[i + 1]
            if self.rng.random() < 0.5:
                sender, receiver = a, b
            else:
                sender, receiver = b, a
            state = int(self.rng.integers(0, self.n_states))
            signal = _softmax(self.Q_s[sender, state], self.temperature, self.rng)
            action = _softmax(self.Q_r[receiver, signal], self.temperature, self.rng)
            payoff = 1 if action == state else 0
            payoffs.append(payoff)
            # Comptes joints ( politique observee de l'emetteur).
            self.joint_state_signal[sender, state, signal] += 1.0
            if reinforce and payoff == 1:
                if not self.pin_instigators or not self.is_instigator[sender]:
                    self.Q_s[sender, state, signal] += 1.0
                if not self.pin_instigators or not self.is_instigator[receiver]:
                    self.Q_r[receiver, signal, action] += 1.0
        mean_payoff = float(np.mean(payoffs)) if payoffs else 0.0
        self.success_history.append(mean_payoff)
        return mean_payoff

    def train(self, n_rounds: int, anneal_to: Optional[float] = None) -> None:
        """Apprend pendant ``n_rounds`` tours, avec recuit de temperature optionnel."""
        if n_rounds < 0:
            raise ValueError(f"n_rounds >= 0 requis (recu {n_rounds}).")
        t0 = self.temperature
        for t in range(n_rounds):
            if anneal_to is not None and n_rounds > 1:
                frac = t / (n_rounds - 1)
                self.temperature = t0 + frac * (anneal_to - t0)
            self.play_round(reinforce=True)
        self.temperature = t0

    def _agent_adopted(self, agent: int) -> bool:
        """Un agent naif a-t-il adopte la cible ? (argmax Q_s et Q_r egaux la cible)."""
        if self.is_instigator[agent]:
            return True
        for s in range(self.n_states):
            if int(np.argmax(self.Q_s[agent, s])) != self.target_signal[s]:
                return False
        for m in range(self.n_signals):
            if int(np.argmax(self.Q_r[agent, m])) != self.target_action[m]:
                return False
        return True

    def adoption_rate(self) -> float:
        """Fraction des agents NAIFS ayant adopte la convention cible (politique dominante).

        Les instigateurs sont exclus (ils sont la source, non le resultat de la cascade).
        Si la population est entierement instigatrice (rho=1, 0 naif), renvoie 1.0 par
        convention (la cible est universelle).
        """
        if self.n_naive == 0:
            return 1.0
        adopted = sum(self._agent_adopted(a) for a in range(self.n_agents)
                      if not self.is_instigator[a])
        return float(adopted) / float(self.n_naive)

    def population_adoption(self) -> float:
        """Fraction de la population ENTIERE (instigateurs inclus) partageant la cible."""
        adopted = sum(self._agent_adopted(a) for a in range(self.n_agents))
        return float(adopted) / float(self.n_agents)

    def coordination_rate(self, window: int = 200) -> float:
        """Taux de coordination moyen sur les ``window`` derniers tours."""
        if not self.success_history:
            return 0.0
        recent = self.success_history[-window:]
        return float(np.mean(recent))

    def population_mi(self) -> float:
        """I(etat ; signal) moyen par agent (mesure de signification de la politique)."""
        if self.n_naive == 0:
            # tous instigateurs : MI cible = log2(n_states)
            return float(np.log2(self.n_states))
        mis = []
        for a in range(self.n_agents):
            if not self.is_instigator[a]:
                mis.append(mutual_information(self.joint_state_signal[a]))
        return float(np.mean(mis)) if mis else 0.0


# --- Bancs d'essai falsifiables (#7746 D2 experience C) ---


def _sweep(
    rhos: Sequence[float],
    *,
    n_agents: int,
    n_states: int,
    n_rounds: int,
    n_seeds: int,
    base_seed: int,
    anneal_to: float = 0.15,
    **kwargs,
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Sweep de rho : renvoie (rhos, adoption_moyenne, adoption_ecart_type)."""
    means = np.zeros(len(rhos))
    stds = np.zeros(len(rhos))
    for i, rho in enumerate(rhos):
        rates = []
        for s in range(n_seeds):
            g = AdoptionGame(
                n_agents=n_agents,
                n_states=n_states,
                instigator_fraction=rho,
                rng=np.random.default_rng(base_seed + 1000 * i + s),
                **kwargs,
            )
            g.train(n_rounds, anneal_to=anneal_to)
            rates.append(g.adoption_rate())
        means[i] = float(np.mean(rates))
        stds[i] = float(np.std(rates))
    return np.asarray(rhos, dtype=float), means, stds


def critical_threshold_test(
    n_agents: int = 24,
    n_states: int = 3,
    n_seeds: int = 3,
    seed: int = 0,
    *,
    n_rounds: int = 2500,
) -> Dict[str, float]:
    """Verdict SEUIL DE PERFORMATIVITE : il existe un ``rho_c`` critique.

    On balaie ``rho`` sur une grille et on cherche une transition nette (courbe en S) :
    adoption faible sous le seuil, cascade au-dessus. Verdict ``threshold_exists = 1.0``
    ssi : (i) adoption a ``rho`` faible (< 0.2) < 0.20, (ii) adoption a ``rho`` eleve
    (> 0.8) > 0.75, ET (iii) un saut prononce (au moins un pas de rho ou l'adoption
    gagne > 0.25). ``rho_c`` = milieu du saut le plus raide.
    """
    rhos = [0.05, 0.15, 0.25, 0.35, 0.5, 0.65, 0.8, 0.95]
    rhos_arr, means, stds = _sweep(
        rhos,
        n_agents=n_agents,
        n_states=n_states,
        n_rounds=n_rounds,
        n_seeds=n_seeds,
        base_seed=seed,
    )
    low = means[0]  # rho=0.05
    high = means[-1]  # rho=0.95
    diffs = np.diff(means)
    max_jump = float(diffs.max()) if len(diffs) else 0.0
    jump_idx = int(np.argmax(diffs)) if len(diffs) else 0
    rho_c = float((rhos_arr[jump_idx] + rhos_arr[jump_idx + 1]) / 2.0) if len(rhos_arr) > 1 else 0.0
    threshold_exists = 1.0 if (low < 0.20 and high > 0.75 and max_jump > 0.25) else 0.0
    return {
        "rhos": rhos_arr.tolist(),
        "adoption_mean": means.tolist(),
        "adoption_std": stds.tolist(),
        "adoption_at_low_rho": float(low),
        "adoption_at_high_rho": float(high),
        "max_jump": max_jump,
        "rho_c": rho_c,
        "threshold_exists": threshold_exists,
    }


def below_threshold_dies_test(
    n_agents: int = 24, n_states: int = 3, n_seeds: int = 4, seed: int = 0, *, n_rounds: int = 2500
) -> Dict[str, float]:
    """Verdict SOUS LE SEUIL : a ``rho`` bas (0.1), l'adoption reste < 1/n_signals + eps.

    La convention novelle meurt : les naifs convergent vers des conventions arbitraires,
    l'adoption de la cible reste au niveau du hasard.
    """
    rates = []
    for s in range(n_seeds):
        g = AdoptionGame(
            n_agents=n_agents, n_states=n_states, instigator_fraction=0.1,
            rng=np.random.default_rng(seed + s),
        )
        g.train(n_rounds, anneal_to=0.15)
        rates.append(g.adoption_rate())
    mean = float(np.mean(rates))
    chance = 1.0 / n_states
    dies = 1.0 if mean < chance + 0.15 else 0.0
    return {
        "adoption_at_low_rho": mean,
        "chance_level": chance,
        "dies": dies,
    }


def above_threshold_cascades_test(
    n_agents: int = 24, n_states: int = 3, n_seeds: int = 4, seed: int = 0, *, n_rounds: int = 2500
) -> Dict[str, float]:
    """Verdict AU-DESSUS DU SEUIL : a ``rho`` haut (0.8), l'adoption cascade -> proche de 1."""
    rates = []
    for s in range(n_seeds):
        g = AdoptionGame(
            n_agents=n_agents, n_states=n_states, instigator_fraction=0.8,
            rng=np.random.default_rng(seed + s),
        )
        g.train(n_rounds, anneal_to=0.15)
        rates.append(g.adoption_rate())
    mean = float(np.mean(rates))
    cascades = 1.0 if mean > 0.75 else 0.0
    return {
        "adoption_at_high_rho": mean,
        "cascades": cascades,
    }


def no_cascade_without_instigators_test(
    n_agents: int = 24, n_states: int = 3, n_seeds: int = 4, seed: int = 0, *, n_rounds: int = 2500
) -> Dict[str, float]:
    """Controle negatif : ``rho=0`` (aucun instigateur) -> pas de cascade vers la cible.

    Sans instigateur, la cible n'est jamais introduite : l'adoption reste au niveau du
    hasard (~1/n_states plein-adoption est tres rare). Ce controle distingue la cascade
    causale (poussee par les instigateurs) d'une convergence spontanee vers la cible.
    """
    rates = []
    for s in range(n_seeds):
        g = AdoptionGame(
            n_agents=n_agents, n_states=n_states, instigator_fraction=0.0,
            rng=np.random.default_rng(seed + s),
        )
        g.train(n_rounds, anneal_to=0.15)
        rates.append(g.adoption_rate())
    mean = float(np.mean(rates))
    no_cascade = 1.0 if mean < 0.20 else 0.0
    return {
        "adoption_at_rho_zero": mean,
        "no_cascade": no_cascade,
    }
