"""Tests de l'oracle de la retouche croisee (oracle_derivation).

Chaque attendu est une sortie mesurée de l'oracle, figée ici pour détecter toute
dérive du module. Le contrôle de concordance contre topology_2x2_periodic_table
vérifie que les équilibres purs de l'oracle coïncident, sur les 576 jeux, avec
l'organe natif de la série.
"""
import sys
from collections import Counter
from functools import lru_cache
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent.parent / "examples"))

import oracle_derivation as od  # noqa: E402
import topology_2x2_periodic_table as topo  # noqa: E402

JEUX = od.tous_les_jeux()


@lru_cache(maxsize=None)
def _par_taille(cout: int) -> dict:
    """Par taille de retouche, calculé une fois par coût pour tous les tests."""
    return od.par_taille(JEUX, cout)


def test_576_jeux_et_equilibres_purs() -> None:
    assert len(JEUX) == 576
    dist = Counter(len(od.equilibres_purs(j)) for j in JEUX)
    assert dict(dist) == {0: 72, 1: 432, 2: 72}


def test_concordance_avec_find_pure_nash() -> None:
    """Les équilibres de l'oracle coïncident avec l'organe natif, sur les 576 jeux."""
    for ligne, colonne in JEUX:
        a = np.array(ligne).reshape(2, 2)
        b = np.array(colonne).reshape(2, 2)
        attendu = sorted((i // 2, i % 2) for i in od.equilibres_purs((ligne, colonne)))
        assert attendu == sorted(topo.find_pure_nash(a, b)), (ligne, colonne)


def test_dilemme_et_swap() -> None:
    assert [od.CASES[i] for i in od.equilibres_purs(od.PD)] == ["DD"]
    assert od.swap((3, 1, 4, 2), 3) == (4, 1, 3, 2)  # R3 : PD -> table de Ligne du Cerf


def test_tables_par_distance() -> None:
    dist = od.tables_par_distance((1, 2, 3, 4), 3)
    assert Counter(dist.values()) == {0: 1, 1: 3, 2: 5, 3: 6}


def test_statuts_des_retouches_d_un_pas() -> None:
    """Le statut (hors / inchange / deplace) ne dépend pas du coût."""
    for cout in (0, 1):
        statut, _, _ = od.retouches_croisees(JEUX, cout)
        assert statut["equilibre inchange"] == 2016
        assert statut["hors comparaison (0 ou 2 equilibres purs avant ou apres)"] == 1152
        assert statut["equilibre deplace"] == 288
        assert sum(statut.values()) == 3456


def test_classes_des_retouches_d_un_pas() -> None:
    _, classes, _ = od.retouches_croisees(JEUX, 0)
    assert classes == Counter(
        {"neutre pour l'editeur": 2016, "perte pour l'editeur": 144,
         "gain sans effet sur l'autre": 144}
    )
    _, classes, _ = od.retouches_croisees(JEUX, 1)
    assert classes == Counter(
        {"perte pour l'editeur": 2160, "neutre pour l'editeur": 96,
         "gain sans effet sur l'autre": 48}
    )


def test_meilleure_retouche() -> None:
    assert od.meilleure_retouche(JEUX, 0) == Counter(
        {"aucune retouche croisee profitable": 720, "profitable, autre inchange": 144}
    )
    assert od.meilleure_retouche(JEUX, 1) == Counter(
        {"aucune retouche croisee profitable": 816, "profitable, autre inchange": 48}
    )


def test_retouche_de_soi() -> None:
    """Témoin GT-03e : retoucher SA table au coût 1 est presque toujours une perte."""
    assert od.retouche_de_soi(JEUX, 1) == Counter(
        {"perte pour l'editeur": 1872, "neutre pour l'editeur": 432}
    )


def _attendu(der: int, cre: int, nui: int, cad: int, dec: int, per: int, gai: int) -> Counter:
    return Counter({
        "derivation (editeur +, autre -)": der,
        "creation (editeur +, autre +)": cre,
        "gain, autre =": gai,
        "nuisance gratuite (editeur =, autre -)": nui,
        "cadeau (editeur =, autre +)": cad,
        "decorative (editeur =, autre =)": dec,
        "perte pour l'editeur": per,
    })


def test_par_taille_lecture_R_cout_0() -> None:
    r = _par_taille(0)
    assert r[("R", 1)] == (_attendu(0, 0, 432, 432, 1152, 144, 144), 1152)
    assert r[("R", 2)] == (_attendu(120, 120, 912, 912, 672, 528, 288), 2208)
    assert r[("R", 3)] == (_attendu(336, 336, 768, 768, 384, 960, 288), 3072)


def test_par_taille_lecture_I_cout_0() -> None:
    r = _par_taille(0)
    assert r[("I", 1)] == (_attendu(144, 0, 0, 0, 2016, 144, 0), 1152)
    assert r[("I", 2)] == (_attendu(504, 24, 0, 0, 2496, 528, 0), 2208)
    assert r[("I", 3)] == (_attendu(936, 24, 0, 0, 1920, 960, 0), 3072)


def test_par_taille_lecture_R_cout_1() -> None:
    r = _par_taille(1)
    assert r[("R", 1)] == (_attendu(0, 0, 0, 0, 96, 2160, 48), 1152)
    assert r[("R", 2)] == (_attendu(0, 0, 40, 40, 96, 3376, 0), 2208)
    assert r[("R", 3)] == (_attendu(0, 0, 0, 0, 0, 3840, 0), 3072)


def test_par_taille_lecture_I_cout_1() -> None:
    r = _par_taille(1)
    assert r[("I", 1)] == (_attendu(48, 0, 96, 0, 0, 2160, 0), 1152)
    assert r[("I", 2)] == (_attendu(0, 0, 168, 8, 0, 3376, 0), 2208)
    assert r[("I", 3)] == (_attendu(0, 0, 0, 0, 0, 3840, 0), 3072)


def test_symetries_lecture_R_cout_0() -> None:
    """L'espace des retouches n'est pas biaisé : dérivation == création,
    nuisance == cadeau, à chaque taille (lecture R, coût 0)."""
    r = _par_taille(0)
    for d in (1, 2, 3):
        classes, _ = r[("R", d)]
        assert classes["derivation (editeur +, autre -)"] == classes["creation (editeur +, autre +)"]
        assert classes["nuisance gratuite (editeur =, autre -)"] == classes["cadeau (editeur =, autre +)"]


def test_paires_exposees() -> None:
    for dmax, attendu in ((1, 0), (2, 120), (3, 288)):
        assert od.paires_exposees(JEUX, 0, dmax, "R") == (attendu, 864)
    for dmax, attendu in ((1, 144), (2, 264), (3, 360)):
        assert od.paires_exposees(JEUX, 0, dmax, "I") == (attendu, 864)
    for dmax in (1, 2, 3):
        assert od.paires_exposees(JEUX, 1, dmax, "R") == (0, 864)
        assert od.paires_exposees(JEUX, 1, dmax, "I") == (48, 864)


def test_dilemme_un_pas() -> None:
    apres = od.dilemme_un_pas()
    assert apres[(0, 1)] == ["DC"]
    assert apres[(0, 2)] == ["DD"]
    assert apres[(0, 3)] == ["DD"]
    assert apres[(1, 1)] == ["CD"]
    assert apres[(1, 2)] == ["DD"]
    assert apres[(1, 3)] == ["DD"]


def test_dilemme_effet_selon_la_lecture() -> None:
    """Ligne échange 1/2 chez Colonne : la dérivation se voit ou non
    selon le livre de comptes de l'autre joueur."""
    cible = od.swap(od.PD[1], 1)
    assert od.effet(od.PD, 0, cible, 0, "R") == (3, 2, 2, 0)   # Colonne garde le rang 2
    assert od.effet(od.PD, 0, cible, 0, "I") == (3, 2, 2, -1)  # ... ou tombe au rang 1


def test_temoins_taille_2_lecture_R() -> None:
    """Témoins de dérivation et de création à la taille 2 (coût 0, lecture R)."""
    jeu = ((1, 2, 3, 4), (1, 3, 4, 2))
    assert od.effet(jeu, 0, (1, 4, 2, 3), 0, "R") == (2, 3, 1, -1)
    jeu_creation = ((1, 2, 3, 4), (1, 4, 3, 2))
    assert od.effet(jeu_creation, 0, (1, 3, 2, 4), 0, "R") == (2, 3, 1, 1)


def test_effet_hors_comparaison() -> None:
    """Un jeu sans équilibre pur unique avant ou après est hors comparaison."""
    jeu = ((4, 2, 1, 3), (2, 4, 3, 1))  # matching pennies ordinal : aucun equilibre pur
    assert od.equilibres_purs(jeu) == []
    assert od.effet(jeu, 0, od.swap(jeu[1], 1), 0, "R") is None


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
