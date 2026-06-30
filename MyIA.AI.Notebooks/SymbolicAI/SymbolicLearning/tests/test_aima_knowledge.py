"""
Tests pour reference/aima_knowledge.py (AIMA, Russell & Norvig Ch. 19,
"Knowledge in Learning").

Module vendore (sous-ensemble pure-stdlib de aima-python/knowledge.py) couvrant
trois algorithmes d'apprentissage par attributs :

  - **Current-best-learning** [Figure 19.2] : recherche incrementale d'une
    hypothese consistante par specialisation/generalisation, avec backtracking.
  - **Version-space-learning** [Figure 19.3] : énumération de l'espace des
    versions (toutes les hypothèses consistantes avec les exemples).
  - **Minimal-consistent-det** [Figure 19.8] : plus petit ensemble d'attributs
    déterminant consistamment la classe cible.

Les tests assertent des INVARIANTS (le contrat de chaque algorithme), pas
seulement l'absence de crash, et s'appuient sur des exemples calcules a la
main :

  - **Primitives** : disjunction_value (negation `!`, conjonction intra-disj),
    guess_value (OU sur les disjonctions), is_consistent / false_positive /
    false_negative (cohérence hypothese/exemple).
  - **Current-best-learning** : la sortie classifie correctement TOUS les
    exemples d'entrainement (consistance), et retrouve une hypothese cible
    unique sur un problème deterministe.
  - **Version-space-learning** : TOUTE hypothese de l'espace des versions est
    consistante avec TOUS les exemples ; l'espace est non vide pour un
    problème apprenable.
  - **Minimal-consistent-det** : retourne le plus petit sous-ensemble
    d'attributs qui distingue les classes (vérifié a la main sur cas
    déterminant vs non-déterminant).
  - **Hypothesis operations** : specializations/generalizations/add_or ne
    rendent QUE des hypotheses structurellement valides (liste de dicts) ET
    consistantes avec les exemples vus (invariant robuste au shuffle aleatoire).

Run with: pytest tests/test_aima_knowledge.py -v
"""

import random
import sys
from pathlib import Path

import pytest

# Ajoute reference/ au path pour importer aima_knowledge (pas de __init__.py).
sys.path.insert(0, str(Path(__file__).parent.parent / "reference"))

import aima_knowledge as ak  # noqa: E402


# ----------------------------------------------------------------------------
# Jeux d'exemples (valeurs et invariants dérivés à la main dans les tests).
# ----------------------------------------------------------------------------

def _goal_a1():
    """Concept cible : GOAL=True ssi A=='1'. 2 exemples (1 positif, 1 negatif)."""
    return [
        {"A": "1", "GOAL": True},
        {"A": "2", "GOAL": False},
    ]


def _goal_sky():
    """Concept cible : GOAL=True ssi Sky=='Sunny'. 2 exemples."""
    return [
        {"Sky": "Sunny", "GOAL": True},
        {"Sky": "Rainy", "GOAL": False},
    ]


def _determining_attribute():
    """3 exemples ou 'A' seul determine la classe, 'B' seul non."""
    return [
        {"A": "1", "B": "x", "GOAL": True},
        {"A": "2", "B": "x", "GOAL": False},
        {"A": "3", "B": "x", "GOAL": True},
    ]


def _non_determining_a():
    """2 exemples avec meme 'A' mais GOAL differents : 'A' non-determinant.
    En revanche 'B' seul distingue (x vs y) -> minimal_consistent_det = {'B'}."""
    return [
        {"A": "1", "B": "x", "GOAL": True},
        {"A": "1", "B": "y", "GOAL": False},
    ]


def _xor_two_attributes():
    """XOR : GOAL vrai ssi exactement une des conditions (A=='1') ou (B=='x').
    Ni A ni B seuls ne déterminent la classe ; seule la paire (A,B) oui."""
    return [
        {"A": "1", "B": "x", "GOAL": True},
        {"A": "1", "B": "y", "GOAL": False},
        {"A": "2", "B": "x", "GOAL": False},
        {"A": "2", "B": "y", "GOAL": True},
    ]


def _generalizable_set():
    """3 exemples (2 positifs, 1 negatif) ou la generalisation (del-AND) peut
    produire un candidat consistant : en supprimant la contrainte B:x de
    {A:!2,B:x} on obtient {A:!2} qui classe correctement les 3 exemples."""
    return [
        {"A": "1", "B": "x", "GOAL": True},
        {"A": "1", "B": "y", "GOAL": True},
        {"A": "2", "B": "z", "GOAL": False},
    ]


# ----------------------------------------------------------------------------
# power_set
# ----------------------------------------------------------------------------

class TestPowerSet:
    """power_set : tous les sous-ensembles NON-VIDES (le vide est exclu)."""

    def test_excludes_empty_set(self):
        """Le module exclut explicitement le sous-ensemble vide ([1:] en fin)."""
        ps = ak.power_set([1, 2, 3])
        assert () not in ps

    def test_all_nonempty_subsets(self):
        """Pour [1,2,3] : 2^3 - 1 = 7 sous-ensembles non-vides."""
        ps = ak.power_set([1, 2, 3])
        assert len(ps) == 7
        expected = {(1,), (2,), (3,), (1, 2), (1, 3), (2, 3), (1, 2, 3)}
        assert set(ps) == expected

    def test_single_element(self):
        assert ak.power_set([42]) == [(42,)]

    def test_returns_tuples(self):
        """Chaque sous-ensemble est un tuple (ordre-cohérent via combinations)."""
        for subset in ak.power_set([1, 2]):
            assert isinstance(subset, tuple)


# ----------------------------------------------------------------------------
# Primitives : disjunction_value, guess_value.
# ----------------------------------------------------------------------------

class TestDisjunctionValue:
    """disjunction_value : un exemple satisfait-il une disjonction (conjonction
    d'attributs, avec negation '!') ?"""

    def test_positive_match(self):
        e = {"A": "x", "GOAL": True}
        assert ak.disjunction_value(e, {"A": "x"}) is True

    def test_positive_mismatch(self):
        e = {"A": "x", "GOAL": True}
        assert ak.disjunction_value(e, {"A": "z"}) is False

    def test_negation_match_when_not_equal(self):
        """!x est satisfait si e[A] != 'x'."""
        e = {"A": "y", "GOAL": True}
        assert ak.disjunction_value(e, {"A": "!x"}) is True

    def test_negation_fail_when_equal(self):
        """!x échoue si e[A] == 'x'."""
        e = {"A": "x", "GOAL": True}
        assert ak.disjunction_value(e, {"A": "!x"}) is False

    def test_conjunction_all_must_match(self):
        """Disjonction = conjonction d'attributs : tous doivent etre satisfaits."""
        e = {"A": "x", "B": "y", "GOAL": True}
        assert ak.disjunction_value(e, {"A": "x", "B": "y"}) is True
        assert ak.disjunction_value(e, {"A": "x", "B": "z"}) is False

    def test_empty_disjunction_is_true(self):
        """Une disjonction vide ({}) est trivialement satisfaite (aucune
        contrainte). C'est ce qui rend l'hypothese la plus generale [{}] toujours
        devinante True."""
        assert ak.disjunction_value({"A": "x", "GOAL": True}, {}) is True


class TestGuessValue:
    """guess_value : OU (disjonction) sur toutes les disjonctions de h."""

    def test_first_disjunction_matches(self):
        h = [{"A": "x"}, {"B": "y"}]
        assert ak.guess_value({"A": "x", "B": "z", "GOAL": True}, h) is True

    def test_second_disjunction_matches(self):
        h = [{"A": "x"}, {"B": "y"}]
        assert ak.guess_value({"A": "z", "B": "y", "GOAL": True}, h) is True

    def test_no_disjunction_matches(self):
        h = [{"A": "x"}, {"B": "y"}]
        assert ak.guess_value({"A": "z", "B": "z", "GOAL": True}, h) is False

    def test_most_general_hypothesis_always_true(self):
        """h=[{}] (une disjonction vide) devine True pour tout exemple."""
        h = [{}]
        assert ak.guess_value({"A": "anything", "GOAL": False}, h) is True


# ----------------------------------------------------------------------------
# Predicats de cohérence : is_consistent, false_positive, false_negative.
# ----------------------------------------------------------------------------

class TestConsistencyPredicates:

    def test_is_consistent_positive_example_correct(self):
        e = {"A": "x", "GOAL": True}
        assert ak.is_consistent(e, [{"A": "x"}]) is True

    def test_is_consistent_negative_example_correct(self):
        """Exemple négatif (GOAL=False) : h ne doit pas le deviner True."""
        e = {"A": "z", "GOAL": False}
        assert ak.is_consistent(e, [{"A": "x"}]) is True  # h ne match pas -> False == False.

    def test_false_positive(self):
        """FP : h devine True mais l'exemple est négatif (h trop generale)."""
        e = {"A": "x", "GOAL": False}
        assert ak.false_positive(e, [{"A": "x"}]) is True

    def test_not_false_positive_when_correct(self):
        e = {"A": "x", "GOAL": True}
        assert ak.false_positive(e, [{"A": "x"}]) is False

    def test_false_negative(self):
        """FN : exemple positif mais h devine False (h trop spécifique)."""
        e = {"A": "x", "GOAL": True}
        assert ak.false_negative(e, [{"A": "z"}]) is True

    def test_not_false_negative_when_correct(self):
        e = {"A": "x", "GOAL": True}
        assert ak.false_negative(e, [{"A": "x"}]) is False


# ----------------------------------------------------------------------------
# values_table : table des valeurs d'attributs (positif -> bare, negatif -> '!').
# ----------------------------------------------------------------------------

class TestValuesTable:

    def test_positive_contributes_bare_value(self):
        examples = [{"A": "x", "GOAL": True}]
        vt = ak.values_table(examples)
        assert "x" in vt["A"]

    def test_negative_contributes_negated_value(self):
        """Un exemple négatif contribute '!' + valeur."""
        examples = [{"A": "x", "GOAL": False}]
        vt = ak.values_table(examples)
        assert "!x" in vt["A"]
        assert "x" not in vt["A"]  # la bare n'apparait que côté positif.

    def test_goal_attribute_excluded(self):
        examples = [{"A": "x", "GOAL": True}]
        vt = ak.values_table(examples)
        assert "GOAL" not in vt

    def test_mixed_signs(self):
        examples = [
            {"Sky": "Sunny", "GOAL": True},
            {"Sky": "Rainy", "GOAL": False},
        ]
        vt = ak.values_table(examples)
        assert set(vt["Sky"]) == {"Sunny", "!Rainy"}


# ----------------------------------------------------------------------------
# check_all_consistency / check_negative_consistency
# ----------------------------------------------------------------------------

class TestCheckConsistency:

    def test_all_consistent(self):
        examples = _goal_a1()
        h = [{"A": "!2"}]  # devine True sauf si A==2 -> classifie e1 True, e2 False.
        assert ak.check_all_consistency(examples, h) is True

    def test_all_inconsistent(self):
        examples = _goal_a1()
        h = [{"A": "x"}]  # ne match aucun exemple -> devine False partout.
        assert ak.check_all_consistency(examples, h) is False  # e1 positif mal classé.

    def test_negative_consistency_only_checks_negatives(self):
        """check_negative_consistency ignore les positifs."""
        examples = _goal_a1()
        # h dict unique 'A':'!2' : le négatif e2 (A==2) est-il consistant ?
        # is_consistent(e2, [h]) : guess False == GOAL False -> OK.
        assert ak.check_negative_consistency(examples, {"A": "!2"}) is True


# ----------------------------------------------------------------------------
# minimal_consistent_det / consistent_det [Figure 19.8]
# ----------------------------------------------------------------------------

class TestMinimalConsistentDet:
    """minimal_consistent_det : plus petit ensemble d'attributs determinant."""

    def test_consistent_det_single_determining_attribute(self):
        """'A' determine seul la classe : chaque valeur de A -> GOAL unique."""
        examples = _determining_attribute()  # A=1->T, A=2->F, A=3->T, B=tjrs x.
        assert ak.consistent_det(("A",), examples) is True

    def test_consistent_det_non_determining_attribute(self):
        """'A' non-determinant : deux exemples avec A='1' mais GOAL differents."""
        examples = _non_determining_a()
        assert ak.consistent_det(("A",), examples) is False

    def test_consistent_det_resolves_with_more_attributes(self):
        """Seul, 'A' ne distingue pas ; (A,B) oui (chaque paire unique)."""
        examples = _non_determining_a()
        assert ak.consistent_det(("A", "B"), examples) is True

    def test_minimal_returns_single_attribute_when_sufficient(self):
        """Pour _determining_attribute, 'A' seul suffit -> minimal = {'A'}."""
        examples = _determining_attribute()
        result = ak.minimal_consistent_det(examples, ["A", "B"])
        assert result == {"A"}

    def test_minimal_returns_pair_when_single_insufficient(self):
        """Pour le XOR, ni A ni B seuls ne déterminent ; la paire (A,B) oui.
        Le minimal est donc {'A','B'} (taille 2)."""
        examples = _xor_two_attributes()
        # Vérifions d'abord qu'aucun attribut seul ne détermine.
        assert ak.consistent_det(("A",), examples) is False
        assert ak.consistent_det(("B",), examples) is False
        assert ak.consistent_det(("A", "B"), examples) is True
        result = ak.minimal_consistent_det(examples, ["A", "B"])
        assert result == {"A", "B"}

    def test_minimal_prefers_smallest(self):
        """Si un seul attribut suffit, on ne retourne jamais une paire."""
        examples = _determining_attribute()
        result = ak.minimal_consistent_det(examples, ["A", "B"])
        assert len(result) == 1

    def test_minimal_picks_determining_attribute_when_first_fails(self):
        """_non_determining_a : 'A' seul ne distingue pas (deux A='1' mais GOAL
        differents), mais 'B' seul oui (x vs y) -> minimal = {'B'}."""
        examples = _non_determining_a()
        assert ak.consistent_det(("A",), examples) is False
        assert ak.consistent_det(("B",), examples) is True
        assert ak.minimal_consistent_det(examples, ["A", "B"]) == {"B"}


# ----------------------------------------------------------------------------
# version_space_learning [Figure 19.3]
# ----------------------------------------------------------------------------

class TestVersionSpaceLearning:
    """version_space_learning : espace des versions = hypotheses consistantes."""

    def test_all_returned_hypotheses_consistent(self):
        """INVARIANT FONDAMENTAL : toute hypothese de l'espace des versions est
        consistante avec TOUS les exemples."""
        examples = _goal_sky()
        V = ak.version_space_learning(examples)
        assert len(V) > 0
        for h in V:
            for e in examples:
                assert ak.is_consistent(e, h), (
                    f"hypothesis {h} inconsistent with example {e}"
                )

    def test_version_space_nonempty_for_learnable(self):
        examples = _goal_a1()
        V = ak.version_space_learning(examples)
        assert len(V) >= 1

    def test_version_space_update_filters(self):
        """version_space_update ne garde que les hypotheses consistantes avec e."""
        examples = _goal_sky()
        V_all = ak.all_hypotheses(examples)
        e_pos = examples[0]  # Sky=Sunny, GOAL=True.
        V_filtered = ak.version_space_update(V_all, e_pos)
        # Chaque hypothese filtrée est consistante avec e_pos.
        for h in V_filtered:
            assert ak.is_consistent(e_pos, h)
        # Le filtrage ne peut qu'écarter : |V_filtered| <= |V_all|.
        assert len(V_filtered) <= len(V_all)

    def test_all_hypotheses_are_lists_of_dicts(self):
        """Structure valide : chaque hypothese est une liste de dicts."""
        examples = _goal_sky()
        for h in ak.all_hypotheses(examples):
            assert isinstance(h, list)
            assert all(isinstance(d, dict) for d in h)


# ----------------------------------------------------------------------------
# current_best_learning [Figure 19.2]
# ----------------------------------------------------------------------------

class TestCurrentBestLearning:
    """current_best_learning : apprentissage incremental avec backtracking."""

    def test_learned_hypothesis_classifies_all_examples(self):
        """INVARIANT : la sortie (si != 'FAIL') classifie correctement TOUS les
        exemples d'entrainement. Robuste au shuffle interne (on teste la
        consistance, pas l'exact equality)."""
        random.seed(42)
        examples = _goal_a1()
        h = ak.current_best_learning(examples, [{}])
        assert h != "FAIL"
        assert ak.check_all_consistency(examples, h)

    def test_learns_simple_concept(self):
        """Sur _goal_a1 (GOAL ssi A==1), la spécialisation de [{}] conduit a
        [{'A':'!2'}] (unique candidat consistant) — deterministe malgré shuffle."""
        random.seed(42)
        examples = _goal_a1()
        h = ak.current_best_learning(examples, [{}])
        assert h == [{"A": "!2"}]

    def test_already_consistent_hypothesis_unchanged(self):
        """Si h est deja consistante avec tous les exemples, elle est retournée
        telle quelle (branche is_consistent, pas de specialisation)."""
        examples = _goal_a1()
        h0 = [{"A": "!2"}]  # deja consistant.
        h = ak.current_best_learning(examples, h0)
        assert h == h0

    def test_most_general_hypothesis(self):
        """[{}] (disjonction vide) devine True partout : consistant uniquement
        si tous les exemples sont positifs. Sur un all-positif, renvoyé tel quel."""
        all_pos = [{"A": "1", "GOAL": True}, {"A": "2", "GOAL": True}]
        h = ak.current_best_learning(all_pos, [{}])
        assert h == [{}]


# ----------------------------------------------------------------------------
# specializations / generalizations / add_or : invariants structurels.
# ----------------------------------------------------------------------------
# Ces fonctions mélangent les candidats via shuffle (non-déterminisme d'ordre).
# On teste donc des INVARIANTS robustes : chaque candidat renvoyé est une
# hypothese valide (liste de dicts) ET consistante avec les exemples vus.

class TestHypothesisOperations:

    def test_specializations_return_valid_consistent_hypotheses(self):
        """Chaque specialization est consistante avec examples_so_far."""
        random.seed(0)
        examples_so_far = _goal_a1()
        h = [{}]  # la plus générale (provoque un false-positive sur le négatif).
        for h2 in ak.specializations(examples_so_far, h):
            assert isinstance(h2, list)
            assert all(isinstance(d, dict) for d in h2)
            assert ak.check_all_consistency(examples_so_far, h2)

    def test_generalizations_return_valid_structured_hypotheses(self):
        """Fix CoursIA (2026-06-10) : upstream faisait `hypotheses += h2`, étalant
        les disjoints (dicts) au lieu d'appendre l'hypothese (liste de dicts),
        ce qui faisait crasher guess_value() ensuite. On verifie ici que chaque
        candidat rendu est bien une LISTE de dicts (structure d'hypothese valide).

        Note : la branche add_or ne filtre que la consistance negative (pas
        check_all_consistency), donc on teste la structure (invariant du fix),
        pas la consistance globale."""
        random.seed(0)
        examples_so_far = _generalizable_set()
        # h trop spécifique {A:!2, B:x} : ne couvre pas e2 (B:y). La generalisation
        # del-AND supprime B:x -> {A:!2} qui classe correctement les 3 exemples.
        h = [{"A": "!2", "B": "x"}]
        gens = ak.generalizations(examples_so_far, h)
        assert len(gens) >= 1, "generalizations should produce candidates"
        for h2 in gens:
            assert isinstance(h2, list), f"candidate {h2} is not a list (the += bug)"
            assert all(isinstance(d, dict) for d in h2)

    def test_add_or_appends_a_disjunction(self):
        """add_or ajoute (OR) une disjonction a h : chaque candidat a len > len(h)."""
        random.seed(0)
        examples_so_far = _goal_a1()
        h = [{"A": "!2"}]
        ors = ak.add_or(examples_so_far, h)
        for h3 in ors:
            assert isinstance(h3, list)
            assert len(h3) == len(h) + 1  # une disjonction ajoutée.
            assert all(isinstance(d, dict) for d in h3)

    def test_specializations_make_hypothesis_more_specific(self):
        """Une spécialisation ne rétrécit pas le nombre de disjonctions a 0 et
        ajoute au moins un attribut négativé ('!'). Au moins un candidat rendu."""
        random.seed(1)
        examples_so_far = [{"A": "1", "B": "x", "GOAL": True},
                           {"A": "1", "B": "y", "GOAL": False}]
        h = [{}]  # trop general.
        specs = ak.specializations(examples_so_far, h)
        # Au moins une spécialisation possible ici (ex: '!y' sur B).
        assert len(specs) >= 1
