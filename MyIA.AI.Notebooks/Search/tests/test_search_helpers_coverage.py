"""
Tests pour le module :mod:`search_helpers` (serie Search, Part1-Foundations et
au-dela).

Le module fournit les utilitaires partages de visualisation et d'aide utilises
par tous les notebooks Search : arbre de recherche (``SearchTreeNode``),
visualisation CSP / paysages de fitness / benchmarks, et navigation pedagogique.

Avant ce fichier, le module etait **orphelin de test** : importe uniquement
depuis les notebooks (via ``sys.path``), jamais par pytest (grep repo-wide =
0 import ``.py``). Ce fichier pose un garde-fou anti-regression sur la
**logique algorithmique** du module (construction d'arbre, chemin solution,
assignation de positions, generation markdown) et un smoke test sur les
fonctions de visualisation matplotlib (construction sans exception + type de
retour Figure).

Les tests assertent des INVARIANTS (le contrat de chaque fonction), pas
seulement l'absence de crash :
  - **SearchTreeNode.add_child** accumule le cout (parent.cost + cost) et
    incremente la profondeur (parent.depth + 1), et broute le lien parent.
  - **_find_solution_path** retourne le chemin racine->solution (DFS) ou None
    si aucun noeud ``is_solution`` n'existe dans l'arbre.
  - **_assign_positions** place la racine a y=1.0, dans la bande [0,1]x[0,1],
    et respecte max_depth (aucun noeud au-delà n'est positionne).
  - **navigation_header** genere le markdown attendu selon prev/next/series.

Backend matplotlib Agg (headless) force au debut pour un run sans display.

Run with: pytest tests/test_search_helpers.py -v
"""

import sys
from pathlib import Path

import matplotlib

# Backend headless : les fonctions de search_helpers retournent des Figure
# matplotlib sans les afficher ; Agg permet un run sans display (CI / cron).
matplotlib.use("Agg")

import matplotlib.figure as mfigure  # noqa: E402
import pytest  # noqa: E402

# Ajoute Search/ au path pour importer search_helpers (le module vit a la
# racine de la serie, le test dans Search/tests/).
sys.path.insert(0, str(Path(__file__).parent.parent))

import search_helpers as sh  # noqa: E402
from search_helpers import (  # noqa: E402
    SearchTreeNode,
    _assign_positions,
    _find_solution_path,
    benchmark_table,
    draw_csp_graph,
    draw_fitness_landscape,
    draw_search_tree,
    navigation_header,
    plot_benchmark,
)


# --------------------------------------------------------------------------- #
#  SearchTreeNode + add_child (logique algorithmique)                          #
# --------------------------------------------------------------------------- #


def test_node_defaults():
    """Un noeud racine a les valeurs par defaut documentees."""
    n = SearchTreeNode("root")
    assert n.state == "root"
    assert n.parent is None
    assert n.action is None
    assert n.cost == 0
    assert n.depth == 0
    assert n.children == []
    assert n.expanded is False
    assert n.is_solution is False


def test_add_child_increments_depth():
    """add_child incremente la profondeur de 1 a chaque niveau."""
    root = SearchTreeNode("A")
    child = root.add_child("B")
    grandchild = child.add_child("C")
    assert root.depth == 0
    assert child.depth == 1
    assert grandchild.depth == 2


def test_add_child_accumulates_cost():
    """add_child accumule le cout : child.cost = parent.cost + cost."""
    root = SearchTreeNode("A", cost=0)
    c1 = root.add_child("B", cost=3)
    c2 = c1.add_child("C", cost=5)
    assert root.cost == 0
    assert c1.cost == 3  # 0 + 3
    assert c2.cost == 8  # 3 + 5


def test_add_child_links_parent_and_children():
    """add_child broute le lien parent et ajoute a children."""
    root = SearchTreeNode("A")
    child = root.add_child("B", action="move")
    assert child.parent is root
    assert child.action == "move"
    assert root.children == [child]
    # add_child retourne le noeud créé pour permettre le chainage
    assert isinstance(child, SearchTreeNode)


def test_add_child_chain_depth_matches_position():
    """Une chaine de N add_child produit des profondeurs 0..N."""
    node = SearchTreeNode(0)
    for i in range(1, 5):
        node = node.add_child(i)
    # En remontant vers la racine, la profondeur decroit de 4 a 0.
    depths = []
    cur = node
    while cur is not None:
        depths.append(cur.depth)
        cur = cur.parent
    assert depths == [4, 3, 2, 1, 0]


# --------------------------------------------------------------------------- #
#  _find_solution_path (DFS recursif)                                          #
# --------------------------------------------------------------------------- #


def test_solution_path_none_when_no_solution():
    """Un arbre sans noeud is_solution retourne None."""
    root = SearchTreeNode("A")
    root.add_child("B")
    root.add_child("C")
    assert _find_solution_path(root) is None


def test_solution_path_root_is_solution():
    """Si la racine est solution, le chemin est juste [root]."""
    root = SearchTreeNode("A")
    root.is_solution = True
    assert _find_solution_path(root) == [root]


def test_solution_path_finds_deep_solution():
    """Le chemin racine -> solution a la bonne profondeur (DFS)."""
    root = SearchTreeNode("A")
    b = root.add_child("B")
    c = b.add_child("C")
    c.is_solution = True
    # Une autre branche sans solution (pour verifier qu'on ne s'y egare pas)
    root.add_child("D")
    path = _find_solution_path(root)
    assert path is not None
    assert [n.state for n in path] == ["A", "B", "C"]


def test_solution_path_returns_first_branch():
    """DFS : la premiere branche contenant une solution gagne (ordre children)."""
    root = SearchTreeNode("A")
    b = root.add_child("B")
    b.is_solution = True  # solution dans la 1re branche
    d = root.add_child("D")
    d.is_solution = True  # aussi solution dans la 2e (ignoree)
    path = _find_solution_path(root)
    assert [n.state for n in path] == ["A", "B"]


# --------------------------------------------------------------------------- #
#  _assign_positions (geometrie de l'arbre)                                    #
# --------------------------------------------------------------------------- #


def test_assign_positions_root_at_top():
    """La racine est placee a y=1.0 (sommet), x au milieu de [left,right]."""
    root = SearchTreeNode("A")
    positions = {}
    _assign_positions(root, positions, 0, 0.0, 1.0, max_depth=3)
    assert root in positions
    x, y = positions[root]
    assert y == pytest.approx(1.0)
    assert x == pytest.approx(0.5)  # milieu de [0, 1]


def test_assign_positions_respects_max_depth():
    """Aucun noeud au-dela de max_depth n'est positionne."""
    root = SearchTreeNode("A")
    child = root.add_child("B")
    grandchild = child.add_child("C")  # depth 2
    great = grandchild.add_child("D")  # depth 3
    positions = {}
    _assign_positions(root, positions, 0, 0.0, 1.0, max_depth=1)
    assert root in positions
    assert child in positions
    # depth 2 et 3 depassent max_depth=1 -> non positionnes
    assert grandchild not in positions
    assert great not in positions


def test_assign_positions_within_unit_band():
    """Toutes les positions assignees sont dans [0,1] x [0,1]."""
    root = SearchTreeNode("A")
    root.add_child("B").add_child("C")
    root.add_child("D")
    positions = {}
    _assign_positions(root, positions, 0, 0.0, 1.0, max_depth=5)
    for _, (x, y) in positions.items():
        assert 0.0 <= x <= 1.0
        assert 0.0 <= y <= 1.0


def test_assign_positions_depth_decreases_y():
    """Les enfants sont plus bas (y plus petit) que leur parent."""
    root = SearchTreeNode("A")
    child = root.add_child("B")
    positions = {}
    _assign_positions(root, positions, 0, 0.0, 1.0, max_depth=3)
    _, y_root = positions[root]
    _, y_child = positions[child]
    assert y_child < y_root


# --------------------------------------------------------------------------- #
#  navigation_header (generation markdown)                                     #
# --------------------------------------------------------------------------- #


def test_navigation_header_minimal_index_only():
    """Sans prev ni next, seul le lien Index est present."""
    out = navigation_header(3, "Informed", series="Part1-Foundations")
    assert "Navigation" in out
    assert "[Index](../README.md)" in out
    assert "<<" not in out
    assert ">>" not in out


def test_navigation_header_with_prev():
    """Le lien prev utilise le prefixe series et notebook_num - 1."""
    out = navigation_header(
        3, "Informed", series="Part1-Foundations", prev_name="Uninformed"
    )
    assert "[<< Uninformed](Part1-Foundations-2-Uninformed.ipynb)" in out
    assert "[Index](../README.md)" in out


def test_navigation_header_with_next():
    """Le lien next utilise le prefixe series et notebook_num + 1."""
    out = navigation_header(
        3, "Informed", series="Part1-Foundations", next_name="LocalSearch"
    )
    assert "[LocalSearch >>](Part1-Foundations-4-LocalSearch.ipynb)" in out


def test_navigation_header_series_prefix_split():
    """series.split('/')[0] prend le prefixe avant un '/' (series composees).."""
    out = navigation_header(2, "CSP", series="Part2-CSP/Foundations", next_name="Backtracking")
    assert "[Backtracking >>](Part2-CSP-3-Backtracking.ipynb)" in out


# --------------------------------------------------------------------------- #
#  Smoke tests visualisation matplotlib (construction + type Figure)           #
# --------------------------------------------------------------------------- #


def test_draw_search_tree_returns_figure():
    """draw_search_tree construit une Figure matplotlib sans exception."""
    root = SearchTreeNode("A")
    b = root.add_child("B")
    sol = b.add_child("C")
    sol.is_solution = True
    root.add_child("D")
    fig = draw_search_tree(root, max_depth=3)
    assert isinstance(fig, mfigure.Figure)


def test_draw_search_tree_single_root():
    """Un arbre reduit a la racine se dessine sans erreur."""
    root = SearchTreeNode("A")
    fig = draw_search_tree(root, max_depth=2)
    assert isinstance(fig, mfigure.Figure)


def test_draw_fitness_landscape_returns_figure():
    """draw_fitness_landscape trace f(x) et optionnellement un parcours."""
    fig = draw_fitness_landscape(lambda x: x ** 2, x_range=(-3, 3))
    assert isinstance(fig, mfigure.Figure)


def test_draw_fitness_landscape_with_points():
    """Avec un parcours de points, la figure se construit avec marqueurs."""
    points = [(-2.0, 4.0), (-1.0, 1.0), (0.0, 0.0)]
    fig = draw_fitness_landscape(lambda x: x ** 2, x_range=(-3, 3), points=points)
    assert isinstance(fig, mfigure.Figure)


def test_draw_csp_graph_returns_figure():
    """draw_csp_graph retourne une Figure (networkx disponible dans l'env)."""
    variables = ["WA", "NT", "SA"]
    domains = {"WA": ["red", "green"], "NT": ["green"], "SA": ["blue"]}
    constraints = [("WA", "NT"), ("NT", "SA"), ("SA", "WA")]
    fig = draw_csp_graph(variables, domains, constraints)
    # networkx est une dependance de test (verifiee dans l'env) -> Figure, pas None.
    assert isinstance(fig, mfigure.Figure)


def test_plot_benchmark_returns_figure():
    """plot_benchmark trace un bar chart des metriques."""
    results = [
        {"algorithm": "BFS", "time_ms": 12.5, "nodes_expanded": 100},
        {"algorithm": "A*", "time_ms": 8.3, "nodes_expanded": 40},
    ]
    fig = plot_benchmark(results, metric="time_ms")
    assert isinstance(fig, mfigure.Figure)


def test_benchmark_table_runs_without_error(capsys):
    """benchmark_table affiche un tableau formate sans retourner ni lever."""
    results = [
        {"algorithm": "BFS", "time_ms": 12.5, "nodes_expanded": 100,
         "solution_found": True, "optimal": True},
        {"algorithm": "DFS", "time_ms": 45.1, "nodes_expanded": 320,
         "solution_found": True, "optimal": False},
    ]
    benchmark_table(results, title="Smoke benchmark")
    captured = capsys.readouterr()
    assert "Smoke benchmark" in captured.out
    assert "BFS" in captured.out
    assert "DFS" in captured.out
