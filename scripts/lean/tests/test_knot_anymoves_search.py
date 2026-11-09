#!/usr/bin/env python3
"""Tests unitaires du miroir Python de la langue de moves etendue `_any`.

Couvre : (1) les temoins kernel de `Knots/ReidemeisterAny.lean` (paragraphe 5 :
kink nonFresh, descente degeneres, bigon vers vide, chaine r1Any), (2) le
temoin R1 historique `verifyR1_witness_passes_any`, (3) les refus attendus
(silhouette, longueur, parite wf), (4) la generation des voisins (le vide est
voisin des deux temoins descendants), (5) le corpus des plis 11n102 (67
diagrammes, tous wf, tous distincts).

Execution : `python scripts/lean/tests/test_knot_anymoves_search.py` ou pytest.
La recherche bornee elle-meme se fait via le CLI du script (`--search`), pas
dans les tests.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from knot_anymoves_search import (  # noqa: E402
    EMPTY0,
    KNOT_11N102,
    UNKNOT,
    W_BIGON_PAIR,
    W_KINK_EMPTY,
    W_NONFRESH_BIG,
    W_NONFRESH_SMALL,
    W_R1_SRC,
    W_R1_TGT,
    astar,
    canon,
    descent_dfs,
    folds,
    neighbors,
    push_chain,
    sub_label,
    sub_label2,
    verify_any_move,
    verify_any_moves,
    verify_bigon_down_any,
    verify_kink_down_any,
    verify_r3,
    wf,
)


def test_ground_truths_wf():
    for d in (KNOT_11N102, UNKNOT, W_NONFRESH_BIG, W_NONFRESH_SMALL,
              W_KINK_EMPTY, W_BIGON_PAIR, W_R1_SRC, W_R1_TGT):
        assert wf(d), d


def test_wf_refuse_parite():
    # une seule etiquette 4, une seule 3 : compte 1 != 2
    assert not wf((((1, 2, 3, 4),), 4))
    # etiquette hors borne
    assert not wf((((1, 2, 2, 5),), 4))


def test_canon_renommage_premiere_apparition():
    assert canon(()) == ()
    assert canon(((4, 1, 4, 2), (1, 2, 3, 3))) == ((1, 2, 1, 3), (2, 3, 4, 4))
    assert canon(((9, 1, 9, 2), (1, 2, 7, 7))) == canon(((4, 1, 4, 2), (1, 2, 3, 3)))


def test_sub_label():
    assert sub_label((4, 1, 4, 2), 4, 2) == (2, 1, 2, 2)
    assert sub_label((1, 2, 3, 4), 9, 7) == (1, 2, 3, 4)
    assert sub_label2((4, 1, 4, 2), 4, 1, 2, 3) == (1, 1, 1, 3)


def test_temoins_kernel_kink():
    # verifyKinkDownAny_witness_nonFresh (ReidemeisterAny.lean par. 5)
    assert verify_kink_down_any(W_NONFRESH_BIG, W_NONFRESH_SMALL)
    # descente degeneree : kink a etiquettes apparies vers le vide
    assert verify_kink_down_any(W_KINK_EMPTY, EMPTY0)


def test_temoins_kernel_bigon():
    # verifyBigonDownAny_witness_empty
    assert verify_bigon_down_any(W_BIGON_PAIR, EMPTY0)


def test_temoins_kernel_chaines():
    # verifyAnyMoves_witness_nonFresh + le R1 historique passe au _any
    assert verify_any_moves(
        [("r1Any", W_NONFRESH_BIG, W_NONFRESH_SMALL)],
        W_NONFRESH_BIG, W_NONFRESH_SMALL)
    assert verify_any_move("r1Any", W_R1_SRC, W_R1_TGT)
    assert verify_any_move("r2Any", W_BIGON_PAIR, EMPTY0)


def test_refus_attendus():
    # silhouette de kink absente (e3 != e4)
    assert not verify_kink_down_any((((1, 2, 3, 4),), 4), EMPTY0)
    # bigon exige len + 2
    assert not verify_bigon_down_any((((1, 2, 2, 4),), 4), EMPTY0)
    # non-wf est refuse par tous les verificateurs
    assert not verify_kink_down_any((((1, 2, 3, 4),), 4), UNKNOT)
    assert not verify_r3((((1, 2, 3, 4),), 4), UNKNOT)


def test_generation_descendante():
    # le vide est bien un voisin des deux temoins descendants
    empty_neighbors_kink = [c for _, c in neighbors(W_KINK_EMPTY, 13)]
    empty_neighbors_bigon = [c for _, c in neighbors(W_BIGON_PAIR, 13)]
    assert EMPTY0 in empty_neighbors_kink or UNKNOT in empty_neighbors_kink
    assert EMPTY0 in empty_neighbors_bigon or UNKNOT in empty_neighbors_bigon


def test_generation_montante_filtree():
    # depuis le petit temoin, un voisin r1Any montant existe et repasse le
    # verificateur dans l'autre sens
    ups = [c for kind, c in neighbors(W_NONFRESH_SMALL, 13) if kind == "r1Any"]
    assert ups
    for u in ups:
        assert wf(u)
        assert verify_any_move("r1Any", W_NONFRESH_SMALL, u)


def test_generation_bornee():
    # la borne de croisements est respectee par neighbors() partout
    for _, c in neighbors(W_BIGON_PAIR, 4):
        assert len(c[0]) <= 4
    for _, c in neighbors(W_BIGON_PAIR, 13):
        assert len(c[0]) <= 13


def test_corpus_67_plis():
    # C(11,0) + C(11,1) + C(11,2) = 1 + 11 + 55 = 67 departs, tous wf,
    # tous distincts, incluant le diagramme intact
    fs = folds(KNOT_11N102, 2)
    assert len(fs) == 67
    assert len(set(fs)) == 67
    assert KNOT_11N102 in fs
    for d in fs:
        assert wf(d), d


def test_descent_dfs_retrouve_une_poussee():
    # l'inverse d'une chaine de pousses est entierement descendant : la
    # descente-d'abord le retrouve la ou le ball f de l'arbre montant
    # etouffait A* (echec du checkpoint, profondeur 9-10)
    for seed in range(3):
        d = push_chain(6, seed)
        chain = descent_dfs(d, [UNKNOT, EMPTY0], max(len(d[0]), 13), 50_000)
        assert chain is not None, seed
        assert verify_any_moves(chain, d, chain[-1][2])
        assert len(chain[-1][2][0]) <= 1  # arrive au vide ou a l'unknot


def test_descent_dfs_trivial_et_budget():
    # depart deja trivial : chaine vide
    assert descent_dfs(UNKNOT, [UNKNOT, EMPTY0], 8, 100) == []
    # le diagramme intact 11n102 (noue reel) ne descend pas au vide dans un
    # budget minuscule : None, pas de faux temoin
    assert descent_dfs(KNOT_11N102, [UNKNOT, EMPTY0], 13, 30) is None


def test_astar_pondere_retrouve_une_poussee():
    # meme capacite avec A* pondere eps=3 (temoin sous-optimal accepte) :
    # la borne doit couvrir le sommet (cause structurelle du checkpoint)
    d = push_chain(6, 0)
    chain = astar(d, [UNKNOT, EMPTY0], max(len(d[0]), 13), 200_000, epsilon=3.0)
    assert chain is not None
    assert verify_any_moves(chain, d, chain[-1][2])


def test_astar_stats_distinguent_epuisement_et_budget():
    # Le certificat negatif ne vaut rien s'il ne distingue pas les deux
    # causes de `None`. Graphe fini (labels renormalises par `canon`,
    # croisements bornes) + budget large => le tas se vide : `exhausted`.
    st_ex: dict = {}
    assert astar(KNOT_11N102, [UNKNOT, EMPTY0], 13, 2_000_000,
                 epsilon=3.0, stats=st_ex) is None
    assert st_ex["exhausted"] is True
    assert 0 < st_ex["expanded"] < 2_000_000  # epuise AVANT la borne

    # Budget minuscule => borne atteinte, aucune preuve d'absence.
    st_b: dict = {}
    assert astar(KNOT_11N102, [UNKNOT, EMPTY0], 13, 5,
                 epsilon=3.0, stats=st_b) is None
    assert st_b["exhausted"] is False
    assert st_b["expanded"] >= 5


def test_descent_dfs_budget_rend_exhausted_faux():
    # Meme contrat pour la DFS, dont l'epuisement ne porte aucune preuve
    # (elagage des montees consecutives > max_up_steps).
    st: dict = {}
    assert descent_dfs(KNOT_11N102, [UNKNOT, EMPTY0], 13, 30, stats=st) is None
    assert st["exhausted"] is False
    assert st["expanded"] >= 30


