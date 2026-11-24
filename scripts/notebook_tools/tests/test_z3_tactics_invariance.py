"""Tests de la sonde d'invariance des chaines de tactiques Z3.

Le contrat verifie ici est **falsifiable** et **reproductible** : les verdicts
doivent etre invariants d'une chaine de tactiques a l'autre, les modeles lus
doivent se prolonger en solution de l'enonce d'origine, et la lisibilite du
modele doit dependre de la chaine.

Les tests n'assertent aucun **temps** : un chronometre depend de la machine et
ne peut pas fonder un verdict.
"""

from __future__ import annotations

import os
import sys

import pytest

# Le binding z3 est une dependance declaree de la serie Z3-API
# (`MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/requirements.txt`). Sur un runner
# qui ne l'a pas installe, le module entier est ignore plutot que rouge : la
# sonde s'execute la ou la serie est outillee.
z3 = pytest.importorskip("z3")

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from z3_tactics_invariance import (
    CONFIGS,
    _solver,
    instances,
    measure,
    measure_all,
    report,
    verdicts,
)

REPETITIONS = 2


@pytest.fixture(scope="module")
def corpus() -> list:
    """Le corpus de la sonde."""
    return instances()


@pytest.fixture(scope="module")
def rows(corpus: list) -> list:
    """Une mesure complete du corpus, sous toutes les configurations."""
    return measure_all(corpus=corpus, repetitions=REPETITIONS)


def test_le_verdict_est_invariant_sous_toute_chaine(rows: list) -> None:
    """Les cinq configurations rendent le meme verdict sur chaque instance."""
    for entry in verdicts(rows):
        assert entry.status == "VERDICT_PRESERVE", (
            f"{entry.instance} : verdicts divergents {entry.verdicts}"
        )
        assert entry.distinct_verdicts == 1


def test_les_verdicts_attendus_sont_connus(rows: list) -> None:
    """Le corpus a des verdicts connus : Petersen a 3 couleurs est SAT, a 2 non."""
    expected = {
        "petersen_k3": "sat",
        "petersen_k2": "unsat",
        "send_more_money": "sat",
    }
    for entry in verdicts(rows):
        assert entry.verdicts[next(iter(entry.verdicts))] == expected[entry.instance]


def test_une_instance_unsat_ne_donne_aucun_modele(rows: list) -> None:
    """Sur une instance UNSAT, il n'y a pas de modele : ce n'est pas une illisibilite."""
    for entry in verdicts(rows):
        if entry.verdict == "unsat":
            assert entry.readable_configs == []
            assert entry.partial_configs == []
            assert entry.unreadable_configs == []
            assert set(entry.no_model_configs) == set(entry.verdicts)


def test_les_chaines_peuvent_rendre_le_modele_aveugle(rows: list) -> None:
    """La lisibilite du modele depend de la chaine de tactiques.

    C'est le resultat central de la sonde : la chaine `smt` reecrit l'enonce
    dans une forme interne, et le modele rendu ne parle plus des variables
    d'origine. Les carnets, qui comparent des sorties *reconstruites* par le
    binding, ne peuvent pas voir cette difference.
    """
    by_instance = {entry.instance: entry for entry in verdicts(rows)}
    assert "smt" in by_instance["send_more_money"].unreadable_configs
    assert "smt" in by_instance["petersen_k3"].unreadable_configs


def test_la_chaine_smt_aveugle_completement_le_modele(rows: list) -> None:
    """Sous `smt`, aucune variable d'origine n'apparait dans le modele."""
    entry = next(item for item in verdicts(rows) if item.instance == "send_more_money")
    assert entry.defined_ranges["smt"] == [0, 0]
    assert entry.defined_ranges["solveur_par_defaut"] == [8, 8]


def test_solve_eqs_masque_une_variable_sur_le_cryptarithme(rows: list) -> None:
    """`solve-eqs` elimine une variable : le modele en rend 7 sur 8.

    Falsifiable et stable : la plage de variables definies est mesuree sur
    toutes les repetitions, et la sonde expose l'ecart au lieu de le cacher
    derriere un booleen « lisible / illisible ».
    """
    entry = next(item for item in verdicts(rows) if item.instance == "send_more_money")
    assert entry.defined_ranges["simplify+solve-eqs"] == [7, 7]
    assert "simplify+solve-eqs" in entry.partial_configs
    assert "simplify+solve-eqs" not in entry.unreadable_configs


def test_la_sonde_expose_la_lisibilite_par_repetition(rows: list) -> None:
    """Chaque mesure expose le compte de variables definies, repetition par repetition."""
    for row in rows:
        if row.verdict != "sat":
            continue
        assert len(row.defined_counts) == row.total_reps
        assert row.readable_reps + row.partial_reps + row.blind_reps == row.total_reps
        assert all(0 <= count <= row.model_total for count in row.defined_counts)


def test_les_modeles_lisibles_sont_valides(rows: list) -> None:
    """Chaque modele lu se prolonge en solution de l'enonce d'origine."""
    for entry in verdicts(rows):
        assert entry.all_models_valid, (
            f"{entry.instance} : un modele ne se prolonge pas en solution"
        )


def test_les_modeles_lisibles_concordent_sur_le_corpus(rows: list) -> None:
    """Sur ce corpus, les configurations lisibles rendent la meme solution."""
    for entry in verdicts(rows):
        if entry.readable_configs:
            assert entry.readable_models_agree, (
                f"{entry.instance} : modeles lisibles en desaccord {entry.fingerprints}"
            )


def test_le_cryptarithme_a_la_solution_unique(corpus: list) -> None:
    """SEND + MORE = MONEY a une solution unique : 9567 + 1085 = 10652."""
    instance = next(item for item in corpus if item.name == "send_more_money")
    constraints, variables = instance.build()
    solver = _solver(constraints, ())
    assert solver.check() == z3.sat
    values = {
        variable.decl().name(): solver.model().eval(variable, model_completion=False).as_long()
        for variable in variables
    }
    assert values == {"S": 9, "E": 5, "N": 6, "D": 7, "M": 1, "O": 0, "R": 8, "Y": 2}
    assert 9567 + 1085 == 10652


def test_le_corpus_comporte_une_instance_unsat(corpus: list) -> None:
    """Le corpus contient un temoin negatif : chi(Petersen) > 2."""
    names = {instance.name for instance in corpus}
    assert "petersen_k2" in names
    instance = next(item for item in corpus if item.name == "petersen_k2")
    constraints, _variables = instance.build()
    solver = _solver(constraints, ())
    assert solver.check() == z3.unsat


def test_le_rapport_est_serialisable(corpus: list) -> None:
    """Le rapport se serialise en JSON (l'organe doit etre lisible par une autre voie)."""
    import json

    data = report(measure_all(corpus=corpus, repetitions=1))
    payload = json.dumps(data, ensure_ascii=False)
    assert json.loads(payload)["summary"]["instances"] == len(corpus)


def test_une_mesure_isolee_ne_depend_pas_des_autres(corpus: list) -> None:
    """Mesurer une instance sous une configuration ne depend d'aucune autre mesure."""
    instance = next(item for item in corpus if item.name == "send_more_money")
    first = measure(instance, "simplify", CONFIGS["simplify"], repetitions=1)
    second = measure(instance, "simplify", CONFIGS["simplify"], repetitions=1)
    assert first.verdict == second.verdict == "sat"
    assert first.fingerprints == second.fingerprints
