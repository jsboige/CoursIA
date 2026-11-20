"""Tests de l'oracle des paquets (oracle_paquets).

Chaque attendu est une sortie mesurée de l'oracle, figée ici pour détecter toute
dérive du module : issues des procédures à la carte, frontières de Pareto,
paquets qui battent le statu quo, gagnants unanimes et cycle majoritaire.
"""
import sys
from itertools import permutations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "examples"))

import oracle_paquets as op  # noqa: E402

SQ = op.STATU_QUO


def test_huit_issues_pour_trois_mesures() -> None:
    assert len(op.issues(["A", "B", "C"])) == 8
    assert op.nom(SQ) == "statu quo"
    assert op.nom(frozenset({"A", "B"})) == "A+B"


def test_p1_a_la_carte_rend_le_statu_quo_aux_six_ordres() -> None:
    for ordre in permutations(["A", "B", "C"]):
        assert op.carte_sincere(op.P1, list(ordre), op.V3) == SQ
        assert op.carte_sophistiquee(op.P1, list(ordre), op.V3) == SQ


def test_p1_pareto_et_paquets() -> None:
    # Le statu quo est la seule issue dominée ; les sept autres sont Pareto.
    po = op.pareto(op.P1, op.V3)
    assert len(po) == 7 and SQ not in po
    # A+B+C (3,3,3) est le seul paquet qui améliore chaque votant.
    gagnants = op.gagnants_pour_tous(op.P1, op.V3)
    assert gagnants == [frozenset({"A", "B", "C"})]
    assert op.P1[frozenset({"A", "B", "C"})] == (3, 3, 3)
    # Quatre paquets battent le statu quo à la majorité ; A+B = (4,4,-2).
    passes = op.battent_le_statu_quo(op.P1, op.V3)
    assert sorted(op.nom(s) for s in passes) == ["A+B", "A+B+C", "A+C", "B+C"]
    assert op.P1[frozenset({"A", "B"})] == (4, 4, -2)


def test_p1_cycle_majoritaire() -> None:
    """A ordre du jour ouvert, aucun vainqueur : A+B+C est battu par les paquets à deux."""
    abc = frozenset({"A", "B", "C"})
    assert sorted(op.nom(s) for s in op.battu_par(op.P1, abc, op.V3)) == ["A+B", "A+C", "B+C"]
    assert op.invaincues(op.P1, op.V3) == []


def test_p1b_le_non_votant_paie() -> None:
    abc = frozenset({"A", "B", "C"})
    assert op.P1B[abc] == (3, 3, 3, -9)
    assert sum(op.P1B[abc]) == 0
    # Avec le non-votant, plus rien n'est dominé : les huit issues sont Pareto.
    po = op.pareto(op.P1B, op.TOUS4)
    assert len(po) == 8 and SQ in po
    # Chez les seuls votants, le tableau de P1 est inchangé.
    assert op.carte_sincere(op.P1B, ["A", "B", "C"], op.V3) == SQ


def test_t_transferts_purs() -> None:
    assert len(op.T) == 8
    assert len(op.pareto(op.T, op.V3)) == 8  # même le statu quo n'est pas dominé
    assert op.gagnants_pour_tous(op.T, op.V3) == []
    passes = op.battent_le_statu_quo(op.T, op.V3)
    assert sorted(op.nom(s) for s in passes) == ["A+B", "A+C", "B+C"]
    assert op.invaincues(op.T, op.V3) == []


def test_e_extraction_deux_contre_un() -> None:
    assert len(op.pareto(op.E, op.V3)) == 4
    assert op.gagnants_pour_tous(op.E, op.V3) == []
    ab = frozenset({"A", "B"})
    assert op.E[ab] == (1, 1, -4)
    assert op.battent_le_statu_quo(op.E, op.V3) == [ab]
    assert op.invaincues(op.E, op.V3) == []


def test_p2_comptes_disjoints_laissent_passer_la_depense() -> None:
    d = frozenset({"D"})
    df = frozenset({"D", "F"})
    for ordre in (["D", "F"], ["F", "D"]):
        assert op.carte_sincere(op.P2, ordre, op.V3, op.AFFICHE_P2) == d
    # Comptes consolidés : le vote sincère rejette la dépense non financée,
    # le vote anticipé adopte le paquet D+F (1,1,1).
    assert op.carte_sincere(op.P2, ["D", "F"], op.V3) == SQ
    assert op.carte_sophistiquee(op.P2, ["D", "F"], op.V3) == df
    assert op.P2[df] == (1, 1, 1)


def test_p2_le_paquet_finance_est_seul_pareto_et_invaincu() -> None:
    df = frozenset({"D", "F"})
    assert op.pareto(op.P2, op.V3) == [df]
    assert op.invaincues(op.P2, op.V3) == [df]


if __name__ == "__main__":
    import sys
    import inspect
    _fns = [f for n, f in inspect.getmembers(sys.modules[__name__], inspect.isfunction) if n.startswith("test_")]
    _fail = 0
    for _f in _fns:
        try:
            _f()
            print(f"  PASS {_f.__name__}")
        except AssertionError as _e:
            _fail += 1
            print(f"  FAIL {_f.__name__}: {_e}")
    print(f"\n{len(_fns) - _fail}/{len(_fns)} passed")
    sys.exit(1 if _fail else 0)
