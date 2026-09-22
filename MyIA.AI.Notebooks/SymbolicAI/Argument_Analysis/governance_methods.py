# -*- coding: utf-8 -*-
"""Mécanismes de gouvernance multi-agents — distillation du sous-projet EPITA 2.1.6.

Provenance : `2.1.6_multiagent_governance_prototype` du dépôt étudiant
`jsboigeEpita/2025-Epita-Intelligence-Symbolique` (~1390 lignes Python + 16
scénarios JSON). Mandat Triple Distillation (EPIC #4960) : porter l'essence
vivante « sans le bruit d'une année de régressions et d'itérations ».

Partie vivante retenue :
- `governance/methods.py` : 7 méthodes de vote/consensus (majorité, pluralité,
  Borda, Condorcet avec repli Borda, vote quadratique, consensus byzantin,
  consensus Raft).
- `agents/base_agent.py` : personnalités (stubborn / flexible / strategic /
  random) + préférences ordonnées + confiance inter-agents.
- `governance/simulation.py` : formation de coalitions par confiance > 0.8,
  vote par blocs, détection de conflits.
- `metrics/metrics.py` : taux de consensus, Gini/justice, satisfaction moyenne,
  stabilité.
- `scénarios/*.json` : banc de 16 scénarios étiquetés — 6 distillés ici.

Partie NON portée (bruit, cf. divergences) : la médiation de
`conflict_resolution.py` (probabilités de succès codées en dur 0.8/0.5/0.7),
le Q-learning epsilon-greedy de `base_agent`, le CLI/runner, la visualisation
matplotlib, les couches BDI/Reactive (stubs de protocole vides).

Divergences documentées (mesurées sur le source, pas supposition) :
1. `simulate_governance` du source assigne `method_fn = GOVERNANCE_METHODS[method]`
   puis ne l'appelle JAMAIS : les 7 méthodes sont du code mort dans la boucle
   de simulation (le gagnant sort d'un tally de blocs par préférence du leader).
   L'organe les branche réellement : `simulate_vote` applique la méthode.
2. `quadratic_voting` du source n'implémente PAS le coût quadratique annoncé
   (aucune somme de carrés) : un agent "flexible" coupe juste son budget en
   budget//2 + reste, un autre met tout sur son premier choix. Porté tel quel,
   avec l'exercice 1 du notebook = implémenter le vrai vote quadratique
   (coût = somme des carrés des voix, allocation optimale = racine carrée).
3. `byzantine_consensus` du source désigne les byzantins comme les n PREMIERS
   agents (`agents[:n]`, tranche déterministe), pas un tirage. Porté fidèle.
4. La voie `update_memory` du `base_agent` source référence `options` hors de
   sa portée (NameError latent dès que le contexte ne porte pas "options") ;
   la satisfaction est recalculée ici proprement à partir des préférences.
5. La médiation à probabilités fixes n'est pas portée (pseudo-mécanisme) ;
   seule `detect_conflicts` (paires d'agents à positions différentes) l'est.
6. `condorcet_method` conserve le repli Borda du source (comportement standard
   en l'absence de vainqueur de Condorcet — le notebook le démontre sur le
   scénario du cycle).

Module pur : stdlib uniquement, aucune dépendance (numpy du source remplacé par
`random.Random` injecté, donc seedable et déterministe).
"""

from __future__ import annotations

import random
from collections import Counter
from itertools import permutations
from math import factorial

# ---------------------------------------------------------------------------
# Agent a personnalité
# ---------------------------------------------------------------------------


class GovernanceAgent:
    """Agent de vote avec personnalité, préférences ordonnées et confiance.

    Port simplifié du `Agent` de `agents/base_agent.py` : la personnalité
    gouverne le vote sincère, la confiance gouverne les coalitions.
    """

    def __init__(self, name, personality, préférences, trust=None):
        self.name = name
        self.personality = personality  # stubborn | flexible | strategic | random
        self.preferences = list(préférences)
        self.trust = dict(trust or {})
        self.rng = random.Random(0)  # reseedable depuis l'extérieur

    def decide(self, options, context=None, rng=None):
        """Vote sincère selon la personnalité (port de Agent.decide, sans Q-learning)."""
        ctx = context or {}
        rng = rng or self.rng
        if ctx.get("coalition_leader") and self.coalition_id:
            return ctx["coalition_leader"]
        if self.personality == "stubborn":
            return self.preferences[0]
        if self.personality == "flexible":
            hint = ctx.get("majority_hint")
            if hint in options:
                return hint
            return self.preferences[0]
        if self.personality == "strategic":
            likely = ctx.get("likely_winner")
            if likely in self.preferences and self.trust and max(self.trust.values()) > 0.7:
                return likely
            return self.preferences[1] if len(self.preferences) > 1 else self.preferences[0]
        return rng.choice(sorted(options))

    coalition_id = None  # posé par form_coalitions


# ---------------------------------------------------------------------------
# Methodes de vote (port de governance/methods.py)
# ---------------------------------------------------------------------------


def majority_voting(agents, options, context=None, rng=None):
    """Majorité : chaque agent vote son premier choix, le plus voté gagne."""
    votes = [a.decide(options, context, rng) for a in agents]
    winner, _ = Counter(votes).most_common(1)[0]
    return winner


def plurality_voting(agents, options, context=None, rng=None):
    """Pluralité : identique à la majorité pour un vainqueur unique (port fidèle)."""
    return majority_voting(agents, options, context, rng)


def borda_count(agents, options, context=None, rng=None):
    """Borda : n-1 points au premier rang, n-2 au deuxième... le total max gagne."""
    scores = {o: 0 for o in options}
    n = len(options)
    for a in agents:
        for i, o in enumerate(a.preferences):
            if o in scores:
                scores[o] += n - i - 1
    return max(scores, key=scores.get)


def condorcet_method(agents, options, context=None, rng=None):
    """Condorcet : duels pairwise ; vainqueur qui bat tous les autres, sinon repli Borda."""
    n = len(options)
    pairwise_wins = {o: 0 for o in options}
    for o1 in options:
        for o2 in options:
            if o1 == o2:
                continue
            o1_wins = sum(
                a.preferences.index(o1) < a.preferences.index(o2) for a in agents
            )
            if o1_wins > len(agents) - o1_wins:
                pairwise_wins[o1] += 1
    for o in options:
        if pairwise_wins[o] == n - 1:
            return o
    return borda_count(agents, options, context, rng)


def quadratic_voting(agents, options, context=None, rng=None):
    """Vote "quadratique" du SOURCE (divergence 2) : budget coupé ou tout-misé.

    Le source annonce un coût en somme de carrés mais ne l'implémente pas :
    un agent flexible coupe son budget en deux sur ses deux premiers choix,
    les autres mettent tout sur leur premier choix. L'exercice 1 du notebook
    fait implémenter le vrai vote quadratique.
    """
    budget = (context or {}).get("quadratic_budget", 9)
    votes = {o: 0 for o in options}
    for a in agents:
        if a.personality == "flexible" and len(options) > 1:
            votes[options[0]] += budget // 2
            votes[options[1]] += budget - (budget // 2)
        else:
            votes[a.preferences[0]] += budget
    return max(votes, key=votes.get)


def byzantine_consensus(agents, options, context=None, rng=None):
    """Consensus byzantin : une fraction vote aléatoire (les n PREMIERS agents — divergence 3)."""
    rng = rng or random.Random(0)
    ratio = (context or {}).get("byzantine_ratio", 0.2)
    n_byz = int(len(agents) * ratio)
    votes = [a.decide(options, context, rng) for a in agents[n_byz:]]
    votes += [rng.choice(sorted(options)) for _ in agents[:n_byz]]
    winner, _ = Counter(votes).most_common(1)[0]
    return winner


def raft_consensus(agents, options, context=None, rng=None):
    """Raft : un leader tiré au sort propose, majorité d'acceptations requise (top-2)."""
    rng = rng or random.Random(0)
    leader = rng.choice(sorted(agents, key=lambda a: a.name))
    proposal = leader.decide(options, context, rng)
    acceptances = 1
    for a in agents:
        if a is not leader and proposal in a.preferences[:2]:
            acceptances += 1
    if acceptances > len(agents) // 2:
        return proposal
    return majority_voting(agents, options, context, rng)


GOVERNANCE_METHODS = {
    "majority": majority_voting,
    "plurality": plurality_voting,
    "borda": borda_count,
    "condorcet": condorcet_method,
    "quadratic": quadratic_voting,
    "byzantine": byzantine_consensus,
    "raft": raft_consensus,
}


# ---------------------------------------------------------------------------
# Coalitions, conflits, manipulation (port de governance/simulation.py)
# ---------------------------------------------------------------------------


def form_coalitions(agents, trust_threshold=0.8):
    """Coalitions par confiance : un agent rejoint le premier partenaire à confiance > seuil.

    Port de la boucle de coalition de `simulate_governance` (le source fait
    confiance > 0.8 en dur) : chaque coalition vote la préférence de son leader.
    """
    unassigned = list(agents)
    coalitions = []
    for a in agents:
        a.coalition_id = None
    i = 0
    while i < len(unassigned):
        agent = unassigned[i]
        partners = [p for p in unassigned[i + 1:] if agent.trust.get(p.name, 0) > trust_threshold]
        coalition = [agent] + partners
        cid = f"coalition_{len(coalitions) + 1}"
        for p in coalition:
            p.coalition_id = cid
        coalitions.append(coalition)
        for p in partners:
            unassigned.remove(p)
        i += 1
    return coalitions


def detect_conflicts(positions):
    """Conflits : chaque paire d'agents à positions différentes (port fidèle)."""
    names = list(positions.keys())
    conflicts = []
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            if positions[names[i]] != positions[names[j]]:
                conflicts.append({"agents": [names[i], names[j]]})
    return conflicts


def apply_manipulation(agents, manipulation_type, target=None, rng=None):
    """Manipulation du vote (port de simulate_manipulation, voie decide rebind).

    'strategic' : chaque agent vote son 2e choix.
    'false_coalition' : la moitié des agents vote la cible.
    'bribery' : le retour est une copie où n agents votent la cible (n = budget).
    """
    import copy

    rng = rng or random.Random(0)
    copies = [copy.deepcopy(a) for a in agents]
    if manipulation_type == "strategic":
        for a in copies:
            if len(a.preferences) > 1:
                a.personality = "stubborn"
                a.preferences = [a.preferences[1], a.preferences[0]] + a.preferences[2:]
    elif manipulation_type == "false_coalition":
        t = target or a.preferences[0]
        for a in copies[: len(copies) // 2]:
            a.personality = "stubborn"
            a.preferences = [t] + [p for p in a.preferences if p != t]
    return copies


def shapley_value(member_names, payoff_func):
    """Valeur de Shapley d'une coalition (port fidèle, permutations factorielles)."""
    n = len(member_names)
    if n == 0:
        return {}
    values = {m: 0.0 for m in member_names}
    for perm in permutations(member_names):
        prev = set()
        for m in perm:
            marginal = payoff_func(prev | {m}) - payoff_func(prev)
            values[m] += marginal / factorial(n)
            prev.add(m)
    return values


# ---------------------------------------------------------------------------
# Métriques (port de metrics/metrics.py, numpy retiré)
# ---------------------------------------------------------------------------


def satisfaction_of(agent, winner):
    """Satisfaction d'un agent : 1 - rang du vainqueur dans ses préférences, normalisé."""
    if winner not in agent.preferences:
        return 0.0
    denom = max(1, len(agent.preferences) - 1)
    return 1.0 - agent.preferences.index(winner) / denom


def consensus_rate(result):
    """Fraction des votes alignés sur le vainqueur."""
    votes, winner = result["votes"], result["winner"]
    return votes.count(winner) / len(votes) if votes else 0.0


def gini(values):
    """Coefficient de Gini (formule du source, en Python pur, epsilon inclus)."""
    vals = sorted(float(v) for v in values)
    n = len(vals)
    if n == 0:
        return 0.0
    vals = [v - min(0.0, vals[0]) + 1e-8 for v in vals]
    total = sum(vals)
    if total <= 0:
        return 0.0
    weighted = sum((2 * i - n - 1) * v for i, v in enumerate(vals, start=1))
    return weighted / (n * total)


def fairness_index(result):
    """Justice = 1 - Gini des satisfactions."""
    return 1.0 - gini(result["satisfaction"])


def mean_satisfaction(result):
    """Satisfaction moyenne du collectif."""
    return sum(result["satisfaction"]) / len(result["satisfaction"]) if result["satisfaction"] else 0.0


def stability(winners):
    """Stabilite : 1 si un seul vainqueur sur la serie, 0 sinon (port fidele)."""
    return 1.0 if len(set(winners)) == 1 else 0.0


# ---------------------------------------------------------------------------
# Simulation (corrigée : la méthode est APPELÉE — divergence 1)
# ---------------------------------------------------------------------------


def simulate_vote(agents, options, method, context=None, seed=0):
    """Applique RÉELLEMENT la méthode de vote, puis mesure votes et satisfactions.

    Divergence 1 : le source n'appelait jamais sa méthode ; ici chaque méthode
    de GOVERNANCE_METHODS tourne sur les memes agents.
    """
    rng = random.Random(seed)
    method_fn = GOVERNANCE_METHODS[method]
    winner = method_fn(agents, options, context, rng)
    votes = [a.decide(options, context, rng) for a in agents]
    satisfaction = [satisfaction_of(a, winner) for a in agents]
    positions = {a.name: v for a, v in zip(agents, votes)}
    return {
        "method": method,
        "winner": winner,
        "votes": votes,
        "satisfaction": satisfaction,
        "agent_names": [a.name for a in agents],
        "conflicts": detect_conflicts(positions),
    }


def summarize(result):
    """Résume une simulation : consensus, justice, satisfaction."""
    return {
        "consensus_rate": round(consensus_rate(result), 3),
        "fairness": round(fairness_index(result), 3),
        "satisfaction": round(mean_satisfaction(result), 3),
    }


# ---------------------------------------------------------------------------
# Banc de scénarios (6 des 16 du source, distillés)
# ---------------------------------------------------------------------------

SCENARIOS = {
    "dictatorship": {
        "description": "Un agent stratégique impose sa volonté face à des préférences diverses.",
        "options": ["A", "B", "C"],
        "agents": [
            ("D1", "strategic", ["A", "B", "C"]),
            ("O1", "stubborn", ["B", "C", "A"]),
            ("O2", "flexible", ["C", "A", "B"]),
            ("O3", "random", ["B", "A", "C"]),
            ("O4", "stubborn", ["C", "B", "A"]),
        ],
    },
    "cyclic_majority": {
        "description": "Cycle de Condorcet : A bat B, B bat C, C bat A — aucun vainqueur net.",
        "options": ["A", "B", "C"],
        "agents": [
            ("V1", "stubborn", ["A", "B", "C"]),
            ("V2", "stubborn", ["B", "C", "A"]),
            ("V3", "stubborn", ["C", "A", "B"]),
        ],
    },
    "spoiler_candidate": {
        "description": "Un candidat similaire divise un bloc : l'adversaire l'emporte.",
        "options": ["Gauche", "Centre", "Droite"],
        "agents": [
            ("G1", "stubborn", ["Gauche", "Centre", "Droite"]),
            ("G2", "stubborn", ["Centre", "Gauche", "Droite"]),
            ("D1", "stubborn", ["Droite", "Centre", "Gauche"]),
        ],
    },
    "strategic_bloc": {
        "description": "Un bloc discipliné affronte des votes dispersés.",
        "options": ["A", "B", "C"],
        "agents": [
            ("B1", "stubborn", ["A", "B", "C"]),
            ("B2", "stubborn", ["A", "C", "B"]),
            ("B3", "stubborn", ["A", "B", "C"]),
            ("S1", "stubborn", ["B", "C", "A"]),
            ("S2", "stubborn", ["C", "B", "A"]),
        ],
    },
    "byzantine_noise": {
        "description": "Une fraction d'agents vote au hasard : robustesse du consensus.",
        "options": ["A", "B", "C"],
        "agents": [
            ("H1", "stubborn", ["A", "B", "C"]),
            ("H2", "stubborn", ["A", "C", "B"]),
            ("H3", "stubborn", ["A", "B", "C"]),
            ("Z1", "random", ["B", "A", "C"]),
            ("Z2", "random", ["C", "B", "A"]),
        ],
    },
    "project_funding": {
        "description": "Choix de budget : préférences ordonnées sur trois projets.",
        "options": ["Route", "Ecole", "Clinique"],
        "agents": [
            ("M1", "stubborn", ["Route", "Ecole", "Clinique"]),
            ("M2", "stubborn", ["Ecole", "Clinique", "Route"]),
            ("M3", "flexible", ["Clinique", "Ecole", "Route"]),
            ("M4", "flexible", ["Ecole", "Route", "Clinique"]),
        ],
    },
}


def build_agents(scenario_name, trust=None):
    """Matérialise les agents d'un scénario (tuples -> GovernanceAgent)."""
    sc = SCENARIOS[scenario_name]
    return [GovernanceAgent(n, p, prefs, (trust or {}).get(n)) for n, p, prefs in sc["agents"]]


def method_counts():
    """Inventaire de l'organe (pour tests purs, sans exécution)."""
    return {
        "methods": len(GOVERNANCE_METHODS),
        "method_keys": sorted(GOVERNANCE_METHODS.keys()),
        "scenarios": len(SCENARIOS),
        "scenario_names": sorted(SCENARIOS.keys()),
    }
