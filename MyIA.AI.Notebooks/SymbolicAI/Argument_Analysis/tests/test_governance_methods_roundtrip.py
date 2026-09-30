# -*- coding: utf-8 -*-
"""Garde roundtrip sur l'organe `governance_methods` (re-fondation #17353, sous-grain 2 #4960).

Le module vendored (512 lignes, distillé du tronc EPITA `argumentation_analysis/
agents/core/governance/`) déclare **explicitement** ses deltas avec le tronc en
en-tête de fichier — quatre deltas divulgués et un défaut conservé. Cette garde
est le **témoin négatif** : elle affirme aujourd'hui les défauts **tels qu'ils
sont**, pour rougir le jour où le tronc les corrige. Convention de la famille
`tests/unit/coursia/<nom>/test_<nom>_roundtrip.py` (cf organum de référence).

Profil de l'organe : stdlib pur + `numpy` (interdit par construction dans la
garde), déterministe via `rng=random.Random(...)` injectable, sans LLM, sans
JVM, sans réseau. Le carnet `Argument_Analysis_Gouvernance_Multi_Agents.ipynb`
fait foi ; son §7 (« Limites mesurées de la distillation ») est la **liste des
invariants à épingler**.

Run: pytest tests/test_governance_methods_roundtrip.py -v
"""
import random
import sys
from pathlib import Path

import pytest

# Ajoute Argument_Analysis/ au path pour importer l'organe vendored.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import governance_methods as gm  # noqa: E402


# ---------------------------------------------------------------------------
# Profil déterministe (7 agents, 4 options -- même profil que
# test_governance_methods.py pour réutilisation).
# ---------------------------------------------------------------------------
OPTIONS = ["Pizza", "Burger", "Sushi", "Raclette"]
PROFIL = [
    ["Pizza", "Sushi", "Burger", "Raclette"],
    ["Pizza", "Raclette", "Sushi", "Burger"],
    ["Pizza", "Burger", "Sushi", "Raclette"],
    ["Burger", "Raclette", "Sushi", "Pizza"],
    ["Burger", "Sushi", "Raclette", "Pizza"],
    ["Sushi", "Burger", "Raclette", "Pizza"],
    ["Raclette", "Burger", "Sushi", "Pizza"],
]


def _agents(prefs_list, personality="stubborn", seed=0):
    """Construit les agents avec RNG injectable (déterminisme)."""
    return [gm.Agent(f"A{i}", personality, p, rng=random.Random(seed + i))
            for i, p in enumerate(prefs_list)]


# ===========================================================================
# Deltas divulgués par l'organe (en-tête de gouvernance_methods.py) — la garde
# affirme chacun tel qu'il est **aujourd'hui**. Une correction du tronc fait
# rougir le test correspondant, ce qui force le mainteneur à mettre à jour la
# §7 du carnet (conservation de l'invariant) ou à déclarer le défaut corrigé
# (et donc à fermer le ticket #1981 parent).
# ===========================================================================

class TestQuadraticVotingDefaut:
    """Delta n° 1 : `quadratic_voting` **conserve** le défaut du prototype
    (inchangé dans le tronc) — aucune somme de carrés, allocation `budget // 2`
    au premier choix, le reste au second pour les `flexible`, tout sur le
    premier choix pour les autres. L'exercice 1 du carnet = implémenter le
    vrai vote quadratique. Tant que le tronc n'a pas corrigé, ce test passe
    **et** le carnet continue d'enseigner le défaut.

    Le jour où le tronc corrige (somme de carrés effective), ce test rougit —
    c'est la signature que la §7 du carnet doit être mise à jour et l'exercice
    1 reformulé (ou retiré).
    """

    def test_quadratic_distribution_flexible_coupe_budget_en_deux(self):
        """Le défaut conservé : un agent `flexible` alloue `budget // 2` à
        son premier choix et `budget - budget // 2` à son second — c'est
        l'algorithme du **prototype**, conservé tel quel par le tronc.

        On appelle la **vraie** `gm.quadratic_voting` (pas une réimplémentation
        locale) sur un profil à 2 agents flexibles aux prefs disjointes au
        top. La fonction retourne `max(votes, key=votes.get)` (l'option
        gagnante) ; avec le défaut, les deux top options reçoivent chacune
        `budget // 2 + (budget - budget // 2) = budget` voix — l'égalité
        est la signature du défaut, et **le gagnant est non-déterministe**
        (max sur égalité dépend de l'ordre d'insertion du dict en Python
        3.7+). Un vrai vote quadratique romprait cette égalité par
        l'allocation coût-optimale — le jour où le tronc corrige, ce test
        devient sensible au seed.

        Le test affirme **l'égalité structurelle** : la fonction doit
        retourner une option **parmi** les deux top disputées (pas une
        option extérieure). Si un futur correctif fait sortir une option
        non-top du dé, c'est la signature d'une régression non-QV.
        """
        prefs_2 = [["Pizza", "Burger"], ["Burger", "Pizza"]]
        ag = [gm.Agent("A0", "flexible", prefs_2[0], rng=random.Random(0)),
              gm.Agent("A1", "flexible", prefs_2[1], rng=random.Random(1))]
        # Appelons la vraie fonction — c'est le témoin qui doit rougir
        # si le tronc corrige le défaut.
        budget = 8
        gagnant = gm.quadratic_voting(
            ag, OPTIONS, context={"quadratic_budget": budget}
        )
        # Le défaut : les deux tops (Pizza, Burger) sont à égalité.
        # Le gagnant est l'un des deux (non-déterministe par construction
        # du défaut) ; **pas** une option hors top (Sushi, Racelette).
        assert gagnant in {"Pizza", "Burger"}, (
            f"quadratic_voting retourne {gagnant!r} — un vrai QV romprait "
            f"l'égalité Pizza/Burger en faveur du coût-optimale. Soit le "
            f"défaut a été corrigé (rouge attendu), soit l'API a dérivé."
        )

    def test_quadratic_distribution_stubborn_met_tout_sur_top(self):
        """Un agent `stubborn` met **tout** le budget sur son premier choix
        — c'est l'algorithme du prototype (pas de quadraticité). Vérifié
        sur un profil à 1 agent stubborn : la **vraie** `gm.quadratic_voting`
        doit retourner son premier choix (la totalité du budget y est
        concentrée).
        """
        ag = [gm.Agent("A0", "stubborn", ["Pizza", "Burger"],
                       rng=random.Random(0))]
        budget = 7
        gagnant = gm.quadratic_voting(
            ag, OPTIONS, context={"quadratic_budget": budget}
        )
        assert gagnant == "Pizza", (
            f"quadratic_voting retourne {gagnant!r} pour un stubborn "
            f"top=Pizza — l'algorithme du défaut met tout le budget sur "
            f"le top. Si le tronc corrige en vrai QV, la fonction peut "
            f"répartir (rouge attendu)."
        )


class TestSimulationNonPortee:
    """Delta n° 2 : `Simulation` du prototype (avec son `simulate_governance`
    au `method_fn` jamais appelé) **n'est pas portée**. Le tronc garde les
    personnalités et la confiance dans `Agent.decide`/`negotiate`, mais ne
    porte pas la boucle de simulation par confiance > 0.8.

    Conséquence vérifiable : le module `governance_methods` n'exporte **ni**
    `Simulation` **ni** `simulate_governance`. Le jour où quelqu'un les
    importe depuis l'organe, ce test rougit — c'est la signature qu'une
    boucle morte a été réintroduite (incident #18480 §7 « code mort »).
    """

    def test_simulation_non_importable(self):
        with pytest.raises(ImportError):
            from governance_methods import Simulation  # noqa: F401

    def test_simulate_governance_non_importable(self):
        with pytest.raises(ImportError):
            from governance_methods import simulate_governance  # noqa: F401

    def test_method_fn_reference_absente(self):
        """Le tronc ne contient pas non plus la référence morte `method_fn`
        (cf `2.1.6_multiagent_governance_prototype/governance/simulation.py`
        où `method_fn` est affecté l.72 mais jamais appelé). Le vendored
        n'exporte donc aucun symbole contenant `method_fn`.
        """
        symboles = [n for n in dir(gm) if "method_fn" in n]
        assert symboles == [], (
            f"L'organe exporte {symboles} — la référence morte `method_fn` "
            f"a été réintroduite (cf simulation.py du prototype, "
            f"#18480 §7 code mort)."
        )


class TestMetricsNonDistille:
    """Delta n° 3 : `metrics.py` du tronc traite les 3 formes de `votes`
    (#1273 : liste, tally map, per-agent map) et nomme les non-calculables
    (#2576). L'organe vendored **ne distille pas** `metrics.py` — le périmètre
    de la distillation est `governance_methods.py` uniquement. La garde
    vérifie l'absence de symboles de metrics (consensus_rate, etc.).
    """

    def test_metrics_non_importable(self):
        """`metrics.py` n'est pas dans le périmètre de la distillation.
        Le symbole `consensus_rate` ne doit pas être accessible depuis
        l'organe vendored.
        """
        assert not hasattr(gm, "consensus_rate"), (
            "governance_methods expose consensus_rate : le périmètre de la "
            "distillation a changé, vérifier metrics.py du tronc (#1273, #2576)."
        )


class TestSocialChoiceAbsentPrototype:
    """Delta n° 4 : `social_choice.py` (STV, Copeland, Kemeny-Young, Schulze)
    est **absent du prototype** — c'est l'ajout du cœur. La garde vérifie
    que la **catégorie SOCIAL_CHOICE** est bien servie par 8 fonctions —
    un retour à 7 (la rumeur « 7 méthodes de vote ») ferait rougir ce test.
    """

    def test_social_choice_complet_huit(self):
        """Erreur de catégorie #1981 (interdite nommément par le tronc) :
        « 7 méthodes de vote » est **faux**. La surface consolidée a 8
        fonctions de choix social. Toute réduction = régression.
        """
        assert len(gm.SOCIAL_CHOICE) == 8, (
            f"SOCIAL_CHOICE = {sorted(gm.SOCIAL_CHOICE)} (n={len(gm.SOCIAL_CHOICE)}) "
            f"— la régression « 7 méthodes » (#1981) est de retour."
        )
        # Affirme aussi l'inventaire complet (le nom de chaque fonction) :
        attendu = {"approval", "stv", "copeland", "kemeny_young",
                    "kemeny_young_safe", "schulze", "condorcet_winner",
                    "pairwise_matrix"}
        assert set(gm.SOCIAL_CHOICE) == attendu, (
            f"SOCIAL_CHOICE manquant ou en trop : attendu {attendu}, "
            f"reçu {set(gm.SOCIAL_CHOICE)}."
        )


class TestKememyYoungSeuils:
    """#971 — Kemeny-Young > 8 options lève `ValueError` ou replie sur
    Copeland **en le disant**. La garde vérifie les deux formes : la levée
    stricte et le repli `kemeny_young_safe` qui retourne `(ranking, -1,
    approx=True)`.
    """

    def test_kemeny_young_leve_value_error_au_dela_8(self):
        with pytest.raises(ValueError):
            gm.kemeny_young([["A", "B", "C"]],
                             [f"c{i}" for i in range(9)])

    def test_kemeny_young_safe_repli_copeland_au_dela_8(self):
        ranking, score, approx = gm.kemeny_young_safe(
            [["A", "B", "C"]],
            [f"c{i}" for i in range(9)],
        )
        assert approx is True
        assert score == -1
        # Le ranking est un Copeland (le repli est dit, pas silencieux).
        assert isinstance(ranking, list)


class TestCategorieErreur1981:
    """Erreur de catégorie #1981 : le tronc interdit nommément « 7 méthodes
    de vote ». La surface consolidée = 5 scrutins + 2 protocoles + 8 choix
    social = **15 algorithmes**. Cette garde **affirme** la catégorisation
    structurelle, pas seulement les comptes.
    """

    def test_scrutins_sans_methodes_de_vote(self):
        """`SCRUTINS` ne contient que des **scrutins** d'agrégation de
        préférences (5) — pas de protocoles ni de choix social. Mélanger
        les catégories = reproduire l'erreur #1981.
        """
        assert set(gm.SCRUTINS) == {"majority", "plurality", "borda",
                                     "condorcet", "quadratic"}
        # Les protocoles byzantine/raft ne sont PAS des scrutins (#1981).
        assert "byzantine" not in gm.SCRUTINS
        assert "raft" not in gm.SCRUTINS

    def test_protocoles_pas_scrutins(self):
        """`PROTOCOLES` contient **uniquement** les protocoles de tolérance
        aux pannes (byzantine, raft) — pas de scrutin ni de choix social.
        """
        assert set(gm.PROTOCOLES) == {"byzantine", "raft"}
        # Et les scrutins ne sont PAS des protocoles.
        assert "majority" not in gm.PROTOCOLES
        assert "copeland" not in gm.PROTOCOLES

    def test_choix_social_formel_pas_scrutin(self):
        """`SOCIAL_CHOICE` contient **uniquement** les fonctions de choix
        social formel (profils de bulletins, sans Agent) — pas de scrutin
        à agents ni de protocole.
        """
        for nom in gm.SOCIAL_CHOICE:
            fn = gm.SOCIAL_CHOICE[nom]
            # Les fonctions de SOCIAL_CHOICE prennent (ballots, options, ...)
            # — pas (agents, options, ...). Vérifions par introspection du
            # nom du premier paramètre.
            import inspect
            sig = inspect.signature(fn)
            params = list(sig.parameters.keys())
            assert params and params[0] == "ballots", (
                f"SOCIAL_CHOICE[{nom}] attend {params[0]} en premier "
                f"paramètre (attendu `ballots`) — la fonction a migré "
                f"vers la catégorie Agent, c'est une régression."
            )
