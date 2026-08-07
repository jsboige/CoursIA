#!/usr/bin/env python3
"""Tests pour scripts/sudoku/core/graph.py — la topologie du graphe de
contraintes Sudoku qui alimente le message-passing du RRN.

Couvre les deux fonctions a logique pure du module :

  - ``build_sudoku_edge_index`` : construction du graphe dirige (1620 aretes,
    20 peers/cellule). Un bug ici = topologie fausse -> message-passing RRN
    corrompu silencieusement (le modele apprend sur un graphe incorrect sans
    erreur visible).
  - ``make_batch_edge_index`` : replication du graphe pour un batch, avec
    offset des indices de noeuds (b * 81). Le guard ValueError batch_size<=0
    (ajoute par la PR etudiante #7554) est verifie.

Import direct par chemin (sys.path.insert sur core/) pour matcher la
convention de test_core_solvers.py / test_core_dataset_models.py. Importe
torch (graph.py en depend) — pytest via l'env coursia-ml-training (torch
2.6.0+cu124). CPU-only, <2s.
"""

import sys
from pathlib import Path

import pytest

torch = pytest.importorskip("torch")  # skip propre si torch absent (CI sans GPU env)

HERE = Path(__file__).resolve().parent
CORE_DIR = HERE.parent / "core"
sys.path.insert(0, str(CORE_DIR))

import graph  # noqa: E402  (torch needed, __init__.py chain bypassed)


# --------------------------------------------------------------------------
# build_sudoku_edge_index — topologie du graphe de contraintes Sudoku
# --------------------------------------------------------------------------

class TestBuildSudokuEdgeIndex:
    def test_shape_and_dtype(self):
        ei = graph.build_sudoku_edge_index()
        assert ei.shape == (2, 1620)
        assert ei.dtype == torch.long

    def test_edge_count_1620_directed(self):
        # 81 cellules x 20 peers chacune = 1620 aretes dirigees.
        ei = graph.build_sudoku_edge_index()
        assert ei.shape[1] == 1620

    def test_each_cell_has_exactly_20_incoming_edges(self):
        # Les aretes sont (j -> i) pour chaque peer j de i. Donc dst=i
        # apparait exactement 20 fois (une par peer).
        ei = graph.build_sudoku_edge_index()
        dst = ei[1].tolist()
        for cell in range(81):
            assert dst.count(cell) == 20

    def test_no_self_loops(self):
        # Une cellule n'est jamais son propre voisin.
        ei = graph.build_sudoku_edge_index()
        assert not torch.any(ei[0] == ei[1])

    def test_graph_is_symmetric_undirected(self):
        # Le graphe de contraintes Sudoku est non-oriente : si j est peer de
        # i, alors i est peer de j. Donc chaque arete (j, i) a son reverse
        # (i, j). Verifie en comparant l'ensemble des aretes a l'ensemble des
        # reverses.
        ei = graph.build_sudoku_edge_index()
        edges = set(zip(ei[0].tolist(), ei[1].tolist()))
        reversed_edges = {(d, s) for (s, d) in edges}
        assert edges == reversed_edges

    def test_cell0_peers_structure(self):
        # Cellule 0 (top-left, r=0 c=0) : peers = ligne0 (1..8) + col0
        # (9,18,...,72) + box top-left only (10,11,19,20) = 20 cellules.
        ei = graph.build_sudoku_edge_index()
        peers_of_0 = set(ei[0][ei[1] == 0].tolist())
        assert len(peers_of_0) == 20
        assert {1, 2, 3, 4, 5, 6, 7, 8} <= peers_of_0          # ligne 0
        assert {9, 18, 27, 36, 45, 54, 63, 72} <= peers_of_0   # colonne 0
        assert {10, 11, 19, 20} <= peers_of_0                  # box top-left hors ligne/col
        assert 0 not in peers_of_0

    def test_center_cell40_has_20_peers(self):
        # Cellule centrale (r=4, c=4) : sanity 20 peers, jamais elle-meme.
        ei = graph.build_sudoku_edge_index()
        peers_of_40 = set(ei[0][ei[1] == 40].tolist())
        assert len(peers_of_40) == 20
        assert 40 not in peers_of_40

    def test_all_81_nodes_present_as_destination(self):
        # Chaque cellule 0..80 doit figurer comme destination (aucun noeud
        # isole).
        ei = graph.build_sudoku_edge_index()
        assert set(ei[1].tolist()) == set(range(81))


# --------------------------------------------------------------------------
# make_batch_edge_index — replication batch avec offset de noeuds
# --------------------------------------------------------------------------

class TestMakeBatchEdgeIndex:
    def test_shape_replicates_edges_per_batch(self):
        base = graph.build_sudoku_edge_index()
        out = graph.make_batch_edge_index(base, batch_size=4)
        assert out.shape == (2, 1620 * 4)
        assert out.dtype == torch.long

    def test_toy_base_batch_offset_shifts_both_endpoints(self):
        # Base jouet : aretes (0->3), (1->4). batch_size=2 -> batch 1 offset
        # par 81 -> (81->84), (82->85). Les DEUX endpoints (src ET dst) sont
        # decales, sinon le message-passing cross-graph fuirait.
        base = torch.tensor([[0, 1], [3, 4]], dtype=torch.long)
        out = graph.make_batch_edge_index(base, batch_size=2)
        assert out.shape == (2, 4)
        # batch 0 inchange
        assert out[0, 0].item() == 0 and out[1, 0].item() == 3
        assert out[0, 1].item() == 1 and out[1, 1].item() == 4
        # batch 1 decale de 81
        assert out[0, 2].item() == 81 and out[1, 2].item() == 84
        assert out[0, 3].item() == 82 and out[1, 3].item() == 85

    def test_real_base_each_batch_nodes_in_correct_range(self):
        # Avec la vraie base, les noeuds du batch b doivent etre dans
        # [b*81, b*81+80] (aucune fuite cross-graph).
        base = graph.build_sudoku_edge_index()
        out = graph.make_batch_edge_index(base, batch_size=3)
        for b in range(3):
            batch_edges = out[:, b * 1620:(b + 1) * 1620]
            assert batch_edges.min().item() >= b * 81
            assert batch_edges.max().item() <= b * 81 + 80

    def test_batch_size_zero_raises(self):
        # Guard ajoute par la PR etudiante #7554 — verifie qu'il tient.
        base = graph.build_sudoku_edge_index()
        with pytest.raises(ValueError, match="positive"):
            graph.make_batch_edge_index(base, batch_size=0)

    def test_batch_size_negative_raises(self):
        base = graph.build_sudoku_edge_index()
        with pytest.raises(ValueError, match="positive"):
            graph.make_batch_edge_index(base, batch_size=-3)

    def test_batch_of_one_equals_base(self):
        # Cas limite batch_size=1 : la sortie doit egaler la base (offset 0).
        base = graph.build_sudoku_edge_index()
        out = graph.make_batch_edge_index(base, batch_size=1)
        assert torch.equal(out, base)
