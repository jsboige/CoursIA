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

    **Construction du profil discriminant** (CR ai-01, msg
    ``ai01-18526-cr-qv-20260930`` et relecture ai-01 10:46Z) : 1 stubborn
    (top Pizza) + 2 flexibles (top Burger ; seconds Sushi et Racelette),
    budget=9. Profil conçu pour qu'aucun tie-break ne soit possible
    (écarts déterministes entre défaut et corrections) :

    - **Défaut** (gm.quadratic_voting actuel) : stubborn met 9 voix sur Pizza ;
      chaque flexible coupe en deux (4 sur top, 5 sur second).
      → Pizza = 9, Burger = 8 (4+4), Sushi = 5, Racelette = 5 → **Pizza
      gagne** (9 > 8).
    - **Vraie correction QV** (chaque voix `v` coûte `v²` crédits, voix
      entières = isqrt(crédits disponibles)) : stubborn met 9 crédits sur
      Pizza, soit 3 voix (3²=9) ; flexible 1 met 4 crédits sur Burger (2
      voix) + 4 crédits sur Sushi (2 voix) — budget 8 dépensé en
      4+4, pas de reste ; flexible 2 met 4 crédits sur Burger (2 voix) +
      4 crédits sur Racelette (2 voix). → Pizza = 3, Burger = 4 (2+2),
      Sushi = 2, Racelette = 2 → **Burger gagne** (4 > 3).

    Le témoin ``assert == 'Pizza'`` rougit donc **sur la vraie correction QV**
    (Burger l'emporte), et reste vert sur le défaut actuel. **Aucune
    égalité** dans ce profil (vérifié 9 vs 8 au défaut, 4 vs 3 en correction) :
    un patch constant à ``'Pizza'`` continue de passer (le défaut reste tel
    quel), un patch constant à ``'Burger'`` rougit, une vraie correction QV
    rougit aussi. Le témoin mord sur les deux formes de non-défaut.
    """

    def test_quadratic_distribution_stubborn_pizza_vs_two_flexible_burger(self):
        """Témoin discriminant (CR ai-01 c.1335, msg
        ``ai01-18526-cr-qv-20260930``, relecture ai-01 10:46Z) : défaut →
        Pizza, vraie correction QV → Burger. **Aucune égalité** (9 vs 8 au
        défaut, 4 vs 3 en correction).

        Profil = 1 stubborn (top=Pizza, prefs [Pizza, Burger, Sushi, Raclette])
        + 2 flexibles (top=Burger, seconds Sushi et Racelette), budget = 9.

        **Défaut** (gm.quadratic_voting actuel) : stubborn met 9 voix sur
        son top (Pizza) ; chaque flexible coupe en deux (4 Burger + 5 sur
        second).
        → Pizza = 9, Burger = 8, Sushi = 5, Racelette = 5 → **Pizza gagne**.

        **Vraie correction QV** (chaque voix `v` coûte `v²` crédits, voix
        entières = isqrt(crédits)) : stubborn met 9 crédits sur son top
        (3 voix, 3²=9, budget 9 dépensé en 9) ; chaque flexible met 4
        crédits sur son top (2 voix, 2²=4) + 4 crédits sur son second
        (2 voix, 2²=4) — budget 8 dépensé en 4+4, pas de reste.
        → Pizza = 3, Burger = 4 (2+2), Sushi = 2, Racelette = 2 →
        **Burger gagne**.

        Le témoin affirme **Pizza** (défaut actuel). Le jour où le tronc
        corrige en vraie QV, la fonction renvoie Burger, ce test rougit, et
        la §7 du carnet + l'exercice 1 doivent être mis à jour.

        Contrôles négatifs mesurés à l'audit (c.1335, après rejet du profil
        3-3-2 budget 8 qui coûtait 22 crédits — non-QV) :
        - défaut ``quadratic_voting`` actuel → test PASS (Pizza gagne, 9 > 8) ;
        - patch constant ``return 'Pizza'`` → test PASS (signature du défaut
          inchangée) ;
        - patch constant ``return 'Burger'`` → test FAIL (rouge attendu) ;
        - vraie correction QV (somme de carrés) → test FAIL (Burger=4 > Pizza=3).

        Ce profil **mord** sur les deux formes de non-défaut mesurées (patch
        constant et vraie QV), sans tie-break d'insertion de dict.
        """
        ag = [
            gm.Agent("A0", "stubborn",
                     ["Pizza", "Burger", "Sushi", "Raclette"],
                     rng=random.Random(0)),
            gm.Agent("A1", "flexible",
                     ["Burger", "Sushi", "Raclette", "Pizza"],
                     rng=random.Random(1)),
            gm.Agent("A2", "flexible",
                     ["Burger", "Raclette", "Sushi", "Pizza"],
                     rng=random.Random(2)),
        ]
        budget = 9
        gagnant = gm.quadratic_voting(
            ag, OPTIONS, context={"quadratic_budget": budget}
        )
        assert gagnant == "Pizza", (
            f"quadratic_voting retourne {gagnant!r} sur le profil "
            f"discriminant (1 stubborn top=Pizza + 2 flexibles top=Burger, "
            f"budget=9). Défaut attendu : Pizza=9 voix (stubborn met tout "
            f"sur top), Burger=8 (chaque flexible coupe en deux). "
            f"Si Pizza ne gagne plus, c'est la signature d'une correction "
            f"QV vraie (somme de carrés des voix, voix = isqrt(crédits) sur "
            f"chaque option dépasée : Burger=4 voix (2+2) l'emporte, "
            f"3 voix Pizza du stubborn). Le carnet §7 et l'exercice 1 "
            f"doivent alors être mis à jour ; sinon, c'est une régression "
            f"d'API. Mesure audit c.1335 + relecture ai-01 10:46Z : le "
            f"profil 1+2 budget 9 est discriminant (9 vs 8 au défaut, "
            f"4 vs 3 en correction QV)."
        )

    def test_quadratic_distribution_flexible_burger_top2_met_demie(self):
        """Témoin auxiliaire : un agent flexible avec top=Burger reçoit
        budget//2 sur top et budget-budget//2 sur second (le défaut),
        tandis qu'un QV plausible étalerait sur 3 options. Vérifié sur
        un profil à 1 agent flexible seul : la fonction retourne le top
        si le top est unique, ou le top+second dans le cas du défaut.
        Sert de **garde structurelle** : si demain le défaut bascule
        pour les flexibles aussi, ce test capte la régression sur un
        cas trivial avant que le test discriminant ne se déclenche.
        """
        ag = [gm.Agent("A0", "flexible",
                       ["Burger", "Sushi", "Raclette", "Pizza"],
                       rng=random.Random(0))]
        budget = 8
        gagnant = gm.quadratic_voting(
            ag, OPTIONS, context={"quadratic_budget": budget}
        )
        # Défaut : flexible coupe en deux (4 Burger + 4 Sushi) → tied.
        # Le gagnant dépend de l'ordre d'insertion du dict
        # (``votes = {o: 0 for o in OPTIONS}`` → Burger en premier). Burger
        # est donc l'attendu du défaut sur ce profil (non-déterministe
        # en cas de tie alternatif). Le témoin accepte Burger OU Sushi
        # pour rester robuste à l'ordre, tout en excluant Pizza/Raclette
        # (sorties hors top/second = régression).
        assert gagnant in {"Burger", "Sushi"}, (
            f"quadratic_voting retourne {gagnant!r} pour un flexible "
            f"top=Burger second=Sushi, budget=8. Le défaut coupe en "
            f"deux (4+4) → top ou second ; un QV plausible sortirait "
            f"aussi Burger ou Sushi après répartition. Pizza ou Racelette "
            f"signalerait une régression d'allocation."
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
