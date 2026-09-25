# -*- coding: utf-8 -*-
"""Gouvernance multi-agents : scrutins, protocoles de consensus, choix social.

Provenance (re-fondation 2026-09-25, option 1 ai-01 sur #17353) :
- **tronc** `argumentation_analysis/agents/core/governance/` du dépôt EPITA —
  `governance_methods.py` (137 l.), `social_choice.py` (344 l.),
  `governance_agent.py` (270 l.), `metrics.py` (118 l.).
  Module vivant : dernier fix 2026-09-24 (#2576 — les métriques de consensus
  nomment ce qu'elles ne peuvent pas calculer au lieu d'un 0.0 ou un None).
- **sas** `docs/coursia_contrib/governance_voting_methods.ipynb` (19 cellules,
  2026-07-15) : le cadre pédagogique (scénario club, duels, paradoxe de
  Condorcet, manipulation de Borda / Gibbard-Satterthwaite).
- Généalogie : `2.1.6_multiagent_governance_prototype` (projet étudiant,
  juin 2025) — le tronc en est « Adapted from » et le corrigé ; ce module
  documente les deltas cœur ↔ prototype.

.. warning::
    Erreur de catégorie #1981 (le tronc l'interdit nommément) : « 7 méthodes
    de vote » est **faux**. La surface consolidée =

    - **5 scrutins** d'agrégation de préférences : `majority_voting`,
      `plurality_voting` (alias), `borda_count`, `condorcet_method`,
      `quadratic_voting` ;
    - **2 protocoles** de tolérance aux pannes (*pas* des scrutins, ne se
      comparent pas à Borda) : `byzantine_consensus`, `raft_consensus` ;
    - **8 fonctions de choix social formel** (profils de préférences) :
      `approval_voting`, `stv`, `copeland`, `kemeny_young`,
      `kemeny_young_safe`, `schulze`, `condorcet_winner`, `pairwise_matrix`.

    Total = **15 algorithmes**, pas un seul compteur interchangeable.

Deltas tronc ↔ prototype étudiant 2.1.6 (mesurés sur le source, pas supposés) :

1. `quadratic_voting` **conserve le défaut du prototype** (inchangé dans le
   tronc) : aucune somme de carrés — un agent `flexible` coupe son budget en
   deux, les autres mettent tout sur leur premier choix. Porté fidèle ;
   l'exercice 1 du notebook = implémenter le vrai vote quadratique.
2. Le tronc n'a pas de boucle de simulation de coalitions par confiance > 0.8
   (la `Simulation` du prototype, avec son `simulate_governance` au
   `method_fn` jamais appelé) : elle n'est **pas portée**. Le tronc garde les
   personnalités et la confiance dans `Agent.decide`/`negotiate`.
3. `metrics.py` du tronc traite les 3 formes de `votes` (#1273 : liste,
   tally map, per-agent map) et nomme les non-calculables (#2576) — le
   prototype retournait 0.0 ou None silencieusement.
4. `social_choice.py` (couche formelle : STV, Copeland, Kemeny-Young,
   Schulze) est **absent du prototype** — c'est l'ajout du cœur.
5. Le Q-learning epsilon-greedy et les archétypes BDI/Reactive de
   `governance_agent.py` sont portés, la `Simulation` non.

Module pur : stdlib uniquement (`random` injecté, déterministe ; `numpy`
du tronc remplacé par `random.Random`).
"""

from __future__ import annotations

import itertools
import random
from collections import Counter
from typing import Any, Dict, List, Optional, Tuple

# ─────────────────────────────────────────────────────────────────────────
# Agents (port de governance_agent.py — personnalités, confiance, Q-learning)
# ─────────────────────────────────────────────────────────────────────────

PERSONALITIES = ["stubborn", "flexible", "strategic", "random"]


class Agent:
    """Agent de vote : personnalité, préférences ordonnées, confiance, Q-learning.

    Port du `Agent` de `agents/core/governance/governance_agent.py`.
    La personnalité gouverne le vote sincère (`decide`) ; la confiance et
    les coalitions gouvernent la négociation (`negotiate`).
    """

    def __init__(self, name, personality, preferences, rng=None):
        self.name = name
        self.personality = personality  # stubborn | flexible | strategic | random
        self.preferences = list(preferences)
        self.trust: Dict[str, float] = {}
        self.coalition: Optional[str] = None
        self.memory: List[Dict[str, Any]] = []
        self.satisfaction_history: List[float] = []
        self.q_table: Dict[Tuple, float] = {}
        self.epsilon = 0.1
        self.alpha = 0.5
        self.gamma = 0.9
        self.rng = rng or random.Random(0)

    def _state(self, options):
        return (self.preferences[0] if self.preferences else "none",
                self.coalition or "none")

    def choose_action(self, options):
        """Epsilon-greedy sur la Q-table (port du tronc)."""
        if self.rng.random() < self.epsilon:
            return self.rng.choice(options)
        state = self._state(options)
        qv = [self.q_table.get((state, o), 0.0) for o in options]
        mx = max(qv)
        return self.rng.choice([o for o, q in zip(options, qv) if q == mx])

    def update_q(self, options, action, reward, next_options):
        """Mise à jour Q-learning (port du tronc)."""
        state = self._state(options)
        ns = self._state(next_options)
        nxt = max([self.q_table.get((ns, o), 0.0) for o in next_options] or [0.0])
        old = self.q_table.get((state, action), 0.0)
        self.q_table[(state, action)] = old + self.alpha * (reward + self.gamma * nxt - old)

    def decide(self, options, context=None):
        """Décision principale selon la personnalité (port du tronc)."""
        if context and self.coalition and "coalition_leader" in context:
            return context["coalition_leader"]
        if len(self.satisfaction_history) >= 3 and                 (sum(self.satisfaction_history[-3:]) / 3) < 0.3:
            if self.personality == "stubborn":
                self.personality = "flexible"
        if self.personality == "stubborn":
            return self.preferences[0]
        if self.personality == "flexible":
            if context and context.get("majority_hint") in options:
                return context["majority_hint"]
            return self.preferences[0]
        if self.personality == "strategic":
            if context and "likely_winner" in context and self.trust:
                likely = context["likely_winner"]
                if likely in self.preferences and max(self.trust.values()) > 0.7:
                    return likely
            return self.preferences[1] if len(self.preferences) > 1 else self.preferences[0]
        return self.choose_action(options)

    def update_memory(self, decision, outcome, context=None):
        """Historique + satisfaction + Q-learning (port du tronc, options portée)."""
        self.memory.append({"decision": decision, "outcome": outcome, "context": context})
        sat = (1.0 - self.preferences.index(outcome) / max(1, len(self.preferences) - 1)
               if outcome in self.preferences else 0.0)
        self.satisfaction_history.append(sat)
        if len(self.memory) > 1:
            prev = self.memory[-2]
            prev_opts = (prev["context"] or {}).get("options", [])
            if prev_opts:
                self.update_q(prev_opts, prev["decision"], sat, [])
        if context and "proposed_by" in context:
            p = context["proposed_by"]
            if p != self.name:
                self.trust[p] = min(1.0, self.trust.get(p, 0.5) + 0.1)

    def negotiate(self, options, context=None):
        """Négociation : coalition / propose / accept / argue (port du tronc)."""
        if self.trust and max(self.trust.values()) > 0.8:
            return ("form_coalition", max(self.trust, key=self.trust.get))
        if self.personality == "stubborn":
            return ("propose", self.preferences[0])
        if self.personality == "flexible":
            if context and context.get("proposed") in self.preferences[:2]:
                return ("accept", context["proposed"])
            return ("propose", self.preferences[0])
        if self.personality == "strategic":
            if context and "proposed" in context and context["proposed"] != self.preferences[0]:
                return ("argue", self.preferences[1] if len(self.preferences) > 1
                        else self.preferences[0])
            return ("propose", self.preferences[0])
        return ("propose", self.rng.choice(options))

    def propose_argument(self, option, reason):
        return {"agent": self.name, "option": option, "reason": reason}

    def receive_argument(self, argument):
        if self.personality == "flexible" and argument["option"] in self.preferences:
            idx = self.preferences.index(argument["option"])
            if idx > 0:
                self.preferences.pop(idx)
                self.preferences.insert(0, argument["option"])


class BDIAgent(Agent):
    """Agent croyances-désirs-intentions (port du tronc)."""

    def __init__(self, name, personality, preferences, rng=None):
        super().__init__(name, personality, preferences, rng)
        self.beliefs, self.desires, self.intentions = set(), set(), set()

    def decide(self, options, context=None):
        for i in self.intentions:
            if i in options:
                return i
        return super().decide(options, context)


class ReactiveAgent(Agent):
    """Agent réactif à règles (port du tronc)."""

    def __init__(self, name, personality, preferences, rng=None):
        super().__init__(name, personality, preferences, rng)
        self.rules = []

    def add_rule(self, condition, action):
        self.rules.append((condition, action))

    def decide(self, options, context=None):
        for condition, action in self.rules:
            if condition(context):
                return action(options, context)
        return super().decide(options, context)


# ─────────────────────────────────────────────────────────────────────────
# Section 1 — les 5 scrutins (agrégation de préférences)
# ─────────────────────────────────────────────────────────────────────────


def majority_voting(agents, options, context=None):
    """Scrutin majoritaire à un tour : chaque agent vote son 1er choix."""
    votes = [a.decide(options, context) for a in agents]
    return Counter(votes).most_common(1)[0][0]


def plurality_voting(agents, options, context=None):
    """Alias de majority_voting (scrutin à un vainqueur)."""
    return majority_voting(agents, options, context)


def borda_count(agents, options, context=None):
    """Score de Borda : n-1 au 1er choix, n-2 au 2e, etc."""
    n = len(options)
    scores = {o: 0 for o in options}
    for a in agents:
        for i, o in enumerate(a.preferences):
            if o in scores:
                scores[o] += n - i - 1
    return max(scores, key=scores.get)


def condorcet_method(agents, options, context=None):
    """Vainqueur de Condorcet (gagne tous ses duels) ou repli Borda."""
    n = len(options)
    wins = {o: 0 for o in options}
    for o1 in options:
        for o2 in options:
            if o1 == o2:
                continue
            o1_w = sum(a.preferences.index(o1) < a.preferences.index(o2)
                       for a in agents if o1 in a.preferences and o2 in a.preferences)
            if o1_w > len(agents) - o1_w:
                wins[o1] += 1
    for o in options:
        if wins[o] == n - 1:
            return o
    return borda_count(agents, options, context)


def quadratic_voting(agents, options, context=None):
    """Vote quadratique (défaut du prototype conservé, delta n° 1).

    .. warning::
        N'implémente PAS le coût quadratique annoncé (aucune somme de
        carrés) : un agent `flexible` coupe son budget en deux, les autres
        mettent tout sur leur premier choix. Le tronc l'a conservé tel
        quel ; l'exercice du notebook = implémenter le vrai vote
        quadratique (coût = somme des carrés des voix).
    """
    budget = (context or {}).get("quadratic_budget", 9)
    votes = {o: 0 for o in options}
    for a in agents:
        alloc = [0] * len(options)
        top = a.preferences[0] if a.preferences else options[0]
        if a.personality == "flexible" and len(options) > 1:
            ti = options.index(top) if top in options else 0
            second = a.preferences[1] if len(a.preferences) > 1 else options[0]
            si = options.index(second) if second in options else 0
            alloc[ti] = budget // 2
            alloc[si] = budget - budget // 2
        else:
            ti = options.index(top) if top in options else 0
            alloc[ti] = budget
        for i, o in enumerate(options):
            votes[o] += alloc[i]
    return max(votes, key=votes.get)


SCRUTINS = {
    "majority": majority_voting,
    "plurality": plurality_voting,
    "borda": borda_count,
    "condorcet": condorcet_method,
    "quadratic": quadratic_voting,
}


# ─────────────────────────────────────────────────────────────────────────
# Section 2 — les 2 protocoles de tolérance aux pannes (PAS des scrutins)
# ─────────────────────────────────────────────────────────────────────────


def byzantine_consensus(agents, options, context=None, rng=None):
    """Consensus byzantin : une fraction d'agents vote au hasard.

    Protocole de tolérance aux pannes, **pas** un scrutin : ne se compare
    pas à Borda (erreur de catégorie #1981). Le tronc désigne les
    byzantins comme les n PREMIERS agents (tranche déterministe) — porté
    fidèle.
    """
    ratio = (context or {}).get("byzantine_ratio", 0.2)
    rng = rng or random.Random(0)
    n_b = int(len(agents) * ratio)
    honest = agents[n_b:]
    votes = [a.decide(options, context) for a in honest]
    votes += [rng.choice(options) for _ in range(n_b)]
    return Counter(votes).most_common(1)[0][0]


def raft_consensus(agents, options, context=None, rng=None):
    """Raft : élection d'un leader + proposition ; majorité ou repli majoritaire.

    Protocole de tolérance aux pannes, **pas** un scrutin (#1981).
    """
    rng = rng or random.Random(0)
    leader = rng.choice(agents)
    proposal = leader.decide(options, context)
    accept = 1
    for a in agents:
        if a is leader:
            continue
        if proposal in a.preferences[:2]:
            accept += 1
    return proposal if accept > len(agents) // 2 else majority_voting(agents, options, context)


PROTOCOLES = {
    "byzantine": byzantine_consensus,
    "raft": raft_consensus,
}


# ─────────────────────────────────────────────────────────────────────────
# Section 3 — le choix social formel (profils de préférences)
# ─────────────────────────────────────────────────────────────────────────
#
# Fonctions sur des profils de bulletins ordonnés (List[List[str]]),
# indépendantes de la classe Agent. Ajout du cœur — absent du prototype.


def approval_voting(ballots, options, approval_threshold=2):
    """Approval voting : chaque électeur approuve ses k premiers choix."""
    counts = {o: 0 for o in options}
    for b in ballots:
        for c in b[:approval_threshold]:
            if c in counts:
                counts[c] += 1
    return (max(counts, key=counts.get) if counts else None), counts


def stv(ballots, options, seats=1):
    """Vote unique transférable (IRV pour 1 siège) : quota de Droop + transfert."""
    remaining = set(options)
    active = [list(b) for b in ballots]
    winners, rounds = [], []
    quota = len(ballots) // (seats + 1) + 1
    while remaining and len(winners) < seats:
        first = Counter()
        for b in active:
            for c in b:
                if c in remaining:
                    first[c] += 1
                    break
        if not first:
            break
        info = {"counts": dict(first), "remaining": sorted(remaining)}
        elected = [c for c, n in first.items() if n >= quota]
        if elected:
            for c in elected:
                winners.append(c)
                remaining.discard(c)
            info["elected"] = elected
            rounds.append(info)
            continue
        if len(remaining) <= seats - len(winners):
            winners.extend(sorted(remaining))
            info["elected"] = sorted(remaining)
            rounds.append(info)
            break
        lowest = min(first, key=first.get)
        remaining.discard(lowest)
        info["eliminated"] = lowest
        rounds.append(info)
    return winners, rounds


def _pref_count(ballots, a, b):
    """Nombre de bulletins préférant a à b (a absent = derrière)."""
    n = 0
    for ballot in ballots:
        ia = ballot.index(a) if a in ballot else len(ballot)
        ib = ballot.index(b) if b in ballot else len(ballot)
        if ia < ib:
            n += 1
    return n


def copeland(ballots, options):
    """Copeland : score = duels gagnés - duels perdus."""
    scores = {o: 0 for o in options}
    for a in options:
        for b in options:
            if a == b:
                continue
            aw, bw = _pref_count(ballots, a, b), _pref_count(ballots, b, a)
            if aw > bw:
                scores[a] += 1
            elif bw > aw:
                scores[a] -= 1
    return (max(scores, key=scores.get) if scores else None), scores


_MAX_KEMENY_CANDIDATES = 8


def kemeny_young(ballots, options):
    """Kemeny-Young : classement minimisant le désaccord total (O(n!), ≤ 8)."""
    if len(options) > _MAX_KEMENY_CANDIDATES:
        raise ValueError(
            f"Kemeny-Young impraticable pour {len(options)} candidats "
            f"(max {_MAX_KEMENY_CANDIDATES}) — utiliser kemeny_young_safe (#971)."
        )
    pairwise = {(a, b): _pref_count(ballots, a, b)
                for a in options for b in options if a != b}
    best_rank, best_score = None, -1
    for perm in itertools.permutations(options):
        score = sum(pairwise.get((perm[i], perm[j]), 0)
                    for i in range(len(perm)) for j in range(i + 1, len(perm)))
        if score > best_score:
            best_score, best_rank = score, list(perm)
    return best_rank, best_score


def kemeny_young_safe(ballots, options):
    """Kemeny-Young avec repli Copeland au-delà de 8 candidats (#971)."""
    if len(options) <= _MAX_KEMENY_CANDIDATES:
        ranking, score = kemeny_young(ballots, options)
        return ranking, score, False
    _, cs = copeland(ballots, options)
    return sorted(options, key=lambda o: cs.get(o, 0), reverse=True), -1, True


def schulze(ballots, options):
    """Schulze (Beatpath) : plus fort chemin entre toutes les paires."""
    n = len(options)
    idx = {o: i for i, o in enumerate(options)}
    d = [[0] * n for _ in range(n)]
    for ballot in ballots:
        for i, a in enumerate(ballot):
            if a not in idx:
                continue
            for b in ballot[i + 1:]:
                if b in idx:
                    d[idx[a]][idx[b]] += 1
    p = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j and d[i][j] > d[j][i]:
                p[i][j] = d[i][j]
    for k in range(n):
        for i in range(n):
            if i == k:
                continue
            for j in range(n):
                if j in (i, k):
                    continue
                p[i][j] = max(p[i][j], min(p[i][k], p[k][j]))
    scores = {o: 0 for o in options}
    for i in range(n):
        for j in range(n):
            if i != j and p[i][j] > p[j][i]:
                scores[options[i]] += 1
    winner = max(scores, key=scores.get) if scores else None
    paths = {options[i]: {options[j]: p[i][j] for j in range(n) if i != j}
             for i in range(n)}
    return winner, paths


def condorcet_winner(ballots, options):
    """Vainqueur de Condorcet s'il existe (gagne tous ses duels)."""
    for c in options:
        if all(c == o or _pref_count(ballots, c, o) > _pref_count(ballots, o, c)
               for o in options):
            return c
    return None


def pairwise_matrix(ballots, options):
    """Matrice des préférences pairwise à partir des bulletins."""
    matrix = {a: {b: 0 for b in options if b != a} for a in options}
    for ballot in ballots:
        for i, a in enumerate(ballot):
            if a not in matrix:
                continue
            for b in ballot[i + 1:]:
                if b in matrix.get(a, {}):
                    matrix[a][b] += 1
    return matrix


SOCIAL_CHOICE = {
    "approval": approval_voting,
    "stv": stv,
    "copeland": copeland,
    "kemeny_young": kemeny_young,
    "kemeny_young_safe": kemeny_young_safe,
    "schulze": schulze,
    "condorcet_winner": condorcet_winner,
    "pairwise_matrix": pairwise_matrix,
}
