"""Module #7746 D2 experience D : inoculation d'un cadrage (concept/persona).

Le quatrieme des cinq bancs d'essai controles de la strate 7 (#7746). Les
experiences A-C et E ont explore la convention (A), l'invention (B), la diffusion par
masse critique (C) et l'inhibition (E). Cette experience D modele l'INOCULATION : un
cadrage (concept, persona, cadre interpretatif) est introduit chez une MINORITE
d'agents, puis se TRANSMET de proche en proche, modifie les PROTOCOLES d'interaction,
forme des COALITIONS, SURVIT a la disparition de l'instigateur, et se trouve
REINTERPRETE retroactivement par les convertis.

Distinct de l'experience C (``collective_adoption``) : C propage une CONVENTION de
coordination (une bijection etat->signal->action) par engagement fort des instigateurs
(epingles, non mis a jour). D propage un CONCEPT interprétatif (un filtre sur le monde)
par TRANSMISSION OPPORTUNISTE : un agent converti peut convertir un voisin lors d'une
interaction reussie (contagion culturelle, Sperber 1996 ; memetique, Dawkins 1976 ;
inoculation narratique, Lewandowsky 2020). La difference cruciale est la SURVIE
POST-INSTIGATEUR : en C, si l'on retire les instigateurs, la convention peut s'effondrer
(les naifs n'ont plus la source). En D, une fois le concept transmis au-dela d'un seuil,
il SURVIT sans l'instigateur — le concept est devenu ENDEMIQUE.

Mecanisme
---------
Une population de ``n_agents``, chacun avec une ``opinion`` binaire (0 = non-inocule,
1 = porte le concept). Une fraction ``seed`` est inoculee au depart. A chaque tour, les
agents sont apparies aleatoirement ; si un porte (1) interagit avec un non-porteur (0)
et que l'interaction est "convaincante" (probabilite ``transmission_rate``, modulee par
un biais de confirmation optionnel), le non-porteur est converti. Apres ``burn_in``
tours, on retire l'instigateur (les agents initialement inocules retombent a 0) et l'on
observe si le concept SURVIT (transmission endemique) ou S'EFFONDRE (retro-death).

Attendus falsifiables (#7746 spec D)
- **Transmission** : le nombre de porteurs croît au-dela de la graine initiale.
- **Seuil de survie post-instigateur** : il existe une fraction de convertis en-deca de
  laquelle le concept meurt apres retrait de l'instigateur, au-dela de laquelle il
  survive (endemie).
- **Coalition / polarisation** : les porteurs tendent a interagir entre eux (assortativite
  emergente) — la composition des paires porteur-porteur croît avec le temps.
- **Reinterpretation retroactive** : les convertis tardifs ont un profil d'adoption
  different des convertis precoces (ralenti, mais persistant) — l'age d'adoption suit
  une courbe epuisable.

numpy CPU ; auto-contenu (n'importe pas collective_adoption, evite la dependance PR #8852).
"""

from __future__ import annotations

from typing import Dict, List, Optional

import numpy as np


class ConceptInoculation:
    """Population ou un concept (opinion binaire) est inocule chez une minorite puis transmis.

    Parametres
    ----------
    n_agents : int
        Taille de la population (>= 2).
    seed_fraction : float
        Fraction ``seed`` in [0, 1] d'agents inocules au depart.
    transmission_rate : float
        Probabilite, lors d'une interaction porteur-non_porteur, que le non-porteur soit
        converti (contagion). In [0, 1].
    confirmation_bias : float
        Biais de confirmation : reduction relative de la probabilite de transmission si
        le non-porteur a deja ete expose (resistance accumulee). 0 = pas de biais.
    instigator_decay : float
        Apres ``burn_in`` tours, les instigateurs initiaux retombent a 0 avec cette
        probabilite par tour (modelise le depart progressif de l'instigateur).
        ``0.0`` = l'instigateur ne part jamais (controle).
    forget_rate : float
        Probabilite par tour qu'un converti (non-instigateur) OUBLIE le concept et
        retombe a 0, sauf s'il est reinfecte par un contact porteur ce tour. Modelise
        l'oubli culturel (la croyance doit etre reinjectee). C'est ce couplage
        transmission/oubli qui produit le seuil de SURVIE post-instigateur : sans source
        continue (instigateur), le concept ne persiste que si la densite de porteurs
        depasse le seuil epidemicologique R0 > 1 (infections > oubli).
    rng : Optional[np.random.Generator]
        Generateur aleatoire.
    """

    def __init__(
        self,
        n_agents: int = 30,
        *,
        seed_fraction: float = 0.1,
        transmission_rate: float = 0.3,
        confirmation_bias: float = 0.0,
        instigator_decay: float = 0.0,
        forget_rate: float = 0.0,
        rng: Optional[np.random.Generator] = None,
    ) -> None:
        if n_agents < 2:
            raise ValueError(f"n_agents >= 2 requis (recu {n_agents}).")
        if not 0.0 <= seed_fraction <= 1.0:
            raise ValueError(f"seed_fraction in [0, 1] requis (recu {seed_fraction}).")
        if not 0.0 <= transmission_rate <= 1.0:
            raise ValueError(f"transmission_rate in [0, 1] requis (recu {transmission_rate}).")
        if not 0.0 <= confirmation_bias <= 1.0:
            raise ValueError(f"confirmation_bias in [0, 1] requis (recu {confirmation_bias}).")
        if not 0.0 <= instigator_decay <= 1.0:
            raise ValueError(f"instigator_decay in [0, 1] requis (recu {instigator_decay}).")
        if not 0.0 <= forget_rate <= 1.0:
            raise ValueError(f"forget_rate in [0, 1] requis (recu {forget_rate}).")
        self.n_agents = int(n_agents)
        self.seed_fraction = float(seed_fraction)
        self.transmission_rate = float(transmission_rate)
        self.confirmation_bias = float(confirmation_bias)
        self.instigator_decay = float(instigator_decay)
        self.forget_rate = float(forget_rate)
        self.rng = rng if rng is not None else np.random.default_rng()
        self.reset()

    def reset(self) -> None:
        """Reinitialise : ``floor(seed*N)`` agents inocules, le reste a 0."""
        n_seed = int(round(self.seed_fraction * self.n_agents))
        self.opinion = np.zeros(self.n_agents, dtype=int)
        self.exposure = np.zeros(self.n_agents, dtype=int)  # nombre d'expositions subies
        self.is_instigator = np.zeros(self.n_agents, dtype=bool)
        order = self.rng.permutation(self.n_agents)
        self.is_instigator[order[:n_seed]] = True
        self.opinion[self.is_instigator] = 1
        self.n_seeds = int(n_seed)
        self.history: List[Dict[str, float]] = []
        self.adoption_age: List[int] = []  # tour d'adoption de chaque converti non-seed
        self.instigator_removed = False

    def play_round(self, *, instigator_present: bool = True) -> float:
        """Un tour : appariement, transmission opportuniste, oubli des convertis, decay.

        Renvoie la fraction de porteurs apres le tour. Ordre : (1) transmission aux
        non-porteurs exposes ; (2) oubli des convertis NON reinfectes ce tour
        (sauf instigateurs, qui ne sont pas soumis a l'oubli tant qu'ils sont actifs) ;
        (3) decay des instigateurs apres retrait.
        """
        order = self.rng.permutation(self.n_agents)
        n_carriers_before = int(self.opinion.sum())
        # (1) Transmission + suivi des reinfections ce tour.
        reinfected = np.zeros(self.n_agents, dtype=bool)
        for i in range(0, self.n_agents - 1, 2):
            a, b = order[i], order[i + 1]
            oa, ob = self.opinion[a], self.opinion[b]
            if oa != ob:  # un porteur, un non-porteur
                carrier = a if oa == 1 else b
                target = b if oa == 1 else a
                self.exposure[target] += 1
                # Transmission modulee par le biais de confirmation (resistance accumulee).
                eff_rate = self.transmission_rate * (1.0 - self.confirmation_bias) ** (self.exposure[target] - 1)
                if self.rng.random() < eff_rate and self.opinion[target] == 0:
                    self.opinion[target] = 1
                    reinfected[target] = True
                    self.adoption_age.append(len(self.history) + 1)
                elif self.opinion[target] == 1:
                    reinfected[target] = True  # un converti expose a un porteur = reinfecte
            elif oa == 1 and ob == 1:
                # porteur-porteur : reinfection mutuelle (les deux sont reinfectes).
                reinfected[a] = True
                reinfected[b] = True
        # (2) Oubli des convertis NON reinfectes ce tour (sauf instigateurs actifs).
        if self.forget_rate > 0.0:
            for a in range(self.n_agents):
                if self.opinion[a] == 1 and not reinfected[a]:
                    if self.is_instigator[a] and instigator_present:
                        continue  # instigateur actif = source permanente, n'oublie pas
                    if self.rng.random() < self.forget_rate:
                        self.opinion[a] = 0
        # (3) Decay instigateur (depart progressif).
        if not instigator_present and self.instigator_decay > 0.0:
            for a in range(self.n_agents):
                if self.is_instigator[a] and self.opinion[a] == 1:
                    if self.rng.random() < self.instigator_decay:
                        self.opinion[a] = 0
        n_carriers = int(self.opinion.sum())
        n_pp = self._carrier_carrier_pairs(order)
        self.history.append({
            "carrier_fraction": n_carriers / self.n_agents,
            "new_since_seed": max(0, n_carriers - n_carriers_before + self._instigators_active()),
            "pp_pair_fraction": n_pp,
        })
        return n_carriers / self.n_agents

    def _instigators_active(self) -> int:
        return int((self.is_instigator & (self.opinion == 1)).sum())

    def _carrier_carrier_pairs(self, order: np.ndarray) -> float:
        """Fraction des paires qui sont porteur-porteur (assortativite emergente)."""
        pp = 0
        total = 0
        for i in range(0, self.n_agents - 1, 2):
            a, b = order[i], order[i + 1]
            total += 1
            if self.opinion[a] == 1 and self.opinion[b] == 1:
                pp += 1
        return float(pp) / float(total) if total else 0.0

    def train(self, n_rounds: int, *, burn_in: int = 0) -> None:
        """Apprend ``n_rounds`` tours ; apres ``burn_in``, l'instigateur est retire."""
        if n_rounds < 0:
            raise ValueError(f"n_rounds >= 0 requis (recu {n_rounds}).")
        if burn_in < 0 or burn_in > n_rounds:
            raise ValueError(f"burn_in in [0, n_rounds] requis (recu {burn_in}).")
        for t in range(n_rounds):
            present = t < burn_in if burn_in > 0 else True
            if burn_in > 0 and t == burn_in:
                self.instigator_removed = True
            self.play_round(instigator_present=present)

    def carrier_fraction(self) -> float:
        """Fraction actuelle de porteurs du concept."""
        return float(self.opinion.sum()) / float(self.n_agents)

    def final_fraction(self) -> float:
        """Fraction de porteurs au dernier tour."""
        if not self.history:
            return self.carrier_fraction()
        return self.history[-1]["carrier_fraction"]

    def converted_beyond_seed(self) -> int:
        """Nombre de conversions au-dela de la graine initiale (transmission reelle)."""
        return max(0, int(self.opinion.sum()) - self.n_seeds)

    def mean_pp_pairs(self, window: int = 0) -> float:
        """Fraction moyenne de paires porteur-porteur sur les ``window`` derniers tours."""
        if not self.history:
            return 0.0
        pps = [h["pp_pair_fraction"] for h in self.history]
        recent = pps[-window:] if window > 0 else pps
        return float(np.mean(recent))


# --- Bancs d'essai falsifiables (#7746 D2 experience D) ---


def transmission_grows_test(
    n_agents: int = 30, n_seeds: int = 3, seed: int = 0, *, n_rounds: int = 300
) -> Dict[str, float]:
    """Verdict TRANSMISSION : le concept se diffuse au-dela des graines initiales.

    Avec une ``transmission_rate`` moderee et un ``confirmation_bias`` (qui empeche la
    saturation totale), le concept se diffuse au-dela des graines. Verdict
    ``transmits = 1.0`` ssi le nombre moyen de convertis au-dela de la graine > 0
    (la contagion a eu lieu, pas seulement les graines).
    """
    converted = []
    finals = []
    for s in range(n_seeds):
        g = ConceptInoculation(
            n_agents, seed_fraction=3 / n_agents, transmission_rate=0.2,
            confirmation_bias=0.5, rng=np.random.default_rng(seed + s),
        )
        g.train(n_rounds, burn_in=0)
        converted.append(g.converted_beyond_seed())
        finals.append(g.final_fraction())
    mean_converted = float(np.mean(converted))
    mean_final = float(np.mean(finals))
    transmits = 1.0 if mean_converted > 0 else 0.0
    return {
        "mean_converted_beyond_seed": mean_converted,
        "mean_final_fraction": mean_final,
        "transmits": transmits,
    }


def confirmation_bias_throttles_test(
    n_agents: int = 40, n_seeds: int = 5, seed: int = 0, *, n_rounds: int = 200
) -> Dict[str, float]:
    """Verdict BIAIS DE CONFIRMATION : plus le biais est fort, moins le concept diffuse.

    Balayer ``confirmation_bias`` : sans biais (0), le concept sature (fraction ~1) ;
    avec un biais croissant, la fraction finale DECROIT monotone (la resistance
    accumulee freine la conversion). Verdict ``throttles = 1.0`` ssi : (i) fraction a
    bias=0 est elevee (> 0.9), (ii) fraction a bias=0.9 est basse (< 0.6), ET (iii) la
    serie est monotone decroissante (au moins un palier de chute net).
    """
    biases = [0.0, 0.3, 0.5, 0.7, 0.9]
    finals: List[float] = []
    for bias in biases:
        per_seed = []
        for s in range(n_seeds):
            g = ConceptInoculation(
                n_agents, seed_fraction=4 / n_agents, transmission_rate=0.2,
                confirmation_bias=bias, rng=np.random.default_rng(seed + 100 * int(bias * 10) + s),
            )
            g.train(n_rounds, burn_in=0)
            per_seed.append(g.final_fraction())
        finals.append(float(np.mean(per_seed)))
    high = finals[0]  # bias=0
    low = finals[-1]  # bias=0.9
    diffs = np.diff(finals)
    monotone_decrease = bool(np.all(diffs <= 0.05))
    has_drop = bool(np.any(diffs < -0.1))
    throttles = 1.0 if (high > 0.9 and low < 0.6 and monotone_decrease and has_drop) else 0.0
    return {
        "biases": biases,
        "final_fraction_per_bias": finals,
        "final_at_no_bias": float(high),
        "final_at_strong_bias": float(low),
        "throttles": throttles,
    }


def instigator_removal_decline_test(
    n_agents: int = 40, n_seeds: int = 4, seed: int = 0, *, n_rounds: int = 300
) -> Dict[str, float]:
    """Verdict DECLIN POST-INSTIGATEUR : sans la source, l'oubli fait decliner le concept.

    Avec oubli (``forget_rate>0``) : si l'instigateur est PERSISTANT, le concept se
    maintient (fraction ~1, la source le reinjecte en continu) ; si l'instigateur est
    RETIRE (decay), la fraction finale est plus basse (l'oubli n'est plus compense).
    Verdict ``declines = 1.0`` ssi : (i) fraction avec instigateur persistant > 0.9,
    (ii) fraction avec instigateur retire < fraction persistante d'au moins 0.15
    (l'oubli cause un declin mesurable apres le retrait).
    """
    res: Dict[str, float] = {}
    for label, decay in [("persistent", 0.0), ("removed", 0.8)]:
        finals = []
        for s in range(n_seeds):
            g = ConceptInoculation(
                n_agents, seed_fraction=4 / n_agents, transmission_rate=0.2,
                forget_rate=0.1, instigator_decay=decay,
                rng=np.random.default_rng(seed + (1 if decay > 0 else 0) * 500 + s),
            )
            g.train(n_rounds, burn_in=30 if decay > 0 else 0)
            finals.append(g.final_fraction())
        res[label] = float(np.mean(finals))
    persistent = res["persistent"]
    removed = res["removed"]
    declines = 1.0 if (persistent > 0.9 and persistent - removed > 0.15) else 0.0
    res["persistent_fraction"] = persistent
    res["removed_fraction"] = removed
    res["declines"] = declines
    return res


def no_transmission_control_test(
    n_agents: int = 30, n_seeds: int = 3, seed: int = 0, *, n_rounds: int = 300
) -> Dict[str, float]:
    """Controle negatif : ``transmission_rate=0`` -> aucune conversion au-dela de la graine.

    Sans contagion, seul l'instigateur porte le concept : le nombre de convertis
    au-dela de la graine reste 0. Ce controle confirme que la transmission des autres
    bancs est BIEN due a la contagion, pas au hasard.
    """
    converted = []
    for s in range(n_seeds):
        g = ConceptInoculation(
            n_agents, seed_fraction=3 / n_agents, transmission_rate=0.0,
            rng=np.random.default_rng(seed + s),
        )
        g.train(n_rounds, burn_in=0)
        converted.append(g.converted_beyond_seed())
    mean_converted = float(np.mean(converted))
    no_transmission = 1.0 if mean_converted == 0.0 else 0.0
    return {
        "mean_converted_beyond_seed": mean_converted,
        "no_transmission": no_transmission,
    }
