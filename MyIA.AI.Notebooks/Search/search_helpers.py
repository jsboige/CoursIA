"""
Search & Constraint Programming - Utilitaires partages

Module fournissant des fonctions de visualisation et d'aide
pour les notebooks de la serie Search.
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
from collections import deque
from typing import Any, Callable, Optional


# =============================================================================
# Visualisation d'arbres de recherche
# =============================================================================

class SearchTreeNode:
    """Noeud dans un arbre de recherche pour visualisation."""

    def __init__(self, state: Any, parent: Optional['SearchTreeNode'] = None,
                 action: Any = None, cost: float = 0, depth: int = 0):
        self.state = state
        self.parent = parent
        self.action = action
        self.cost = cost
        self.depth = depth
        self.children: list['SearchTreeNode'] = []
        self.expanded = False
        self.is_solution = False

    def add_child(self, state: Any, action: Any = None, cost: float = 0) -> 'SearchTreeNode':
        child = SearchTreeNode(state, parent=self, action=action,
                               cost=self.cost + cost, depth=self.depth + 1)
        self.children.append(child)
        return child


def draw_search_tree(root: SearchTreeNode, max_depth: int = 5,
                     title: str = "Arbre de recherche",
                     highlight_path: bool = True,
                     figsize: tuple = (14, 8)):
    """Dessine un arbre de recherche avec matplotlib."""
    fig, ax = plt.subplots(1, 1, figsize=figsize)
    ax.set_title(title, fontsize=14, fontweight='bold')
    ax.axis('off')

    # Calculer les positions des noeuds
    positions = {}
    _assign_positions(root, positions, 0, 0, 1.0, max_depth)

    if not positions:
        ax.text(0.5, 0.5, "Arbre vide", ha='center', va='center', fontsize=12)
        plt.tight_layout()
        return fig

    # Dessiner les aretes
    for node, (x, y) in positions.items():
        for child in node.children:
            if child in positions:
                cx, cy = positions[child]
                ax.plot([x, cx], [y, cy], 'k-', linewidth=0.8, alpha=0.5)

    # Dessiner les noeuds
    for node, (x, y) in positions.items():
        color = '#90EE90' if node.is_solution else ('#ADD8E6' if node.expanded else '#FFFFFF')
        circle = plt.Circle((x, y), 0.03, color=color, ec='black', linewidth=1.5, zorder=5)
        ax.add_patch(circle)
        label = str(node.state) if len(str(node.state)) < 8 else str(node.state)[:6] + ".."
        ax.text(x, y, label, ha='center', va='center', fontsize=7, zorder=6)

    # Chemin solution
    if highlight_path:
        solution = _find_solution_path(root)
        if solution:
            for i in range(len(solution) - 1):
                if solution[i] in positions and solution[i + 1] in positions:
                    x1, y1 = positions[solution[i]]
                    x2, y2 = positions[solution[i + 1]]
                    ax.plot([x1, x2], [y1, y2], 'r-', linewidth=3, alpha=0.7, zorder=4)

    # Legende
    legend_elements = [
        mpatches.Patch(facecolor='#ADD8E6', edgecolor='black', label='Explore'),
        mpatches.Patch(facecolor='#FFFFFF', edgecolor='black', label='Non explore'),
        mpatches.Patch(facecolor='#90EE90', edgecolor='black', label='Solution'),
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=9)

    ax.set_xlim(-0.1, 1.1)
    ax.set_ylim(-0.1, 1.1)
    plt.tight_layout()
    return fig


def _assign_positions(node, positions, depth, left, right, max_depth):
    """Assigne des positions (x, y) aux noeuds de l'arbre."""
    if depth > max_depth:
        return
    x = (left + right) / 2
    y = 1.0 - depth * (0.9 / max(max_depth, 1))
    positions[node] = (x, y)
    n = len(node.children)
    if n == 0:
        return
    width = (right - left) / n
    for i, child in enumerate(node.children):
        _assign_positions(child, positions, depth + 1,
                          left + i * width, left + (i + 1) * width, max_depth)


def _find_solution_path(node):
    """Trouve le chemin vers le noeud solution."""
    if node.is_solution:
        return [node]
    for child in node.children:
        path = _find_solution_path(child)
        if path:
            return [node] + path
    return None


# =============================================================================
# Visualisation de graphes CSP
# =============================================================================

def draw_csp_graph(variables: list, domains: dict, constraints: list,
                   assignment: dict = None,
                   title: str = "Graphe de contraintes",
                   figsize: tuple = (10, 8)):
    """Dessine le graphe de contraintes d'un CSP."""
    try:
        import networkx as nx
    except ImportError:
        print("NetworkX requis: pip install networkx")
        return None

    G = nx.Graph()
    G.add_nodes_from(variables)

    for c in constraints:
        if len(c) == 2:
            G.add_edge(c[0], c[1])

    fig, ax = plt.subplots(1, 1, figsize=figsize)
    pos = nx.spring_layout(G, seed=42)

    # Couleurs selon l'etat d'assignation
    colors = []
    for v in G.nodes():
        if assignment and v in assignment:
            colors.append('#90EE90')  # Assigne
        elif domains and v in domains and len(domains[v]) == 1:
            colors.append('#FFD700')  # Domaine reduit a 1
        else:
            colors.append('#ADD8E6')  # Non assigne

    nx.draw(G, pos, ax=ax, with_labels=True, node_color=colors,
            node_size=800, font_size=10, font_weight='bold',
            edge_color='gray', width=1.5)

    # Afficher les domaines
    for v in G.nodes():
        if domains and v in domains:
            x, y = pos[v]
            domain_str = str(domains[v]) if len(str(domains[v])) < 20 else f"|D|={len(domains[v])}"
            ax.text(x, y - 0.12, domain_str, ha='center', fontsize=7,
                    bbox=dict(boxstyle='round,pad=0.2', facecolor='wheat', alpha=0.5))

    ax.set_title(title, fontsize=14, fontweight='bold')
    plt.tight_layout()
    return fig


# =============================================================================
# Visualisation de paysages de fitness
# =============================================================================

def draw_fitness_landscape(func: Callable, x_range: tuple = (-5, 5),
                           points: list = None,
                           title: str = "Paysage de fitness",
                           figsize: tuple = (12, 5)):
    """Dessine un paysage de fitness 1D avec optionnellement le parcours d'un algorithme."""
    x = np.linspace(x_range[0], x_range[1], 500)
    y = np.array([func(xi) for xi in x])

    fig, ax = plt.subplots(1, 1, figsize=figsize)
    ax.plot(x, y, 'b-', linewidth=2, label='f(x)')

    if points:
        px = [p[0] for p in points]
        py = [p[1] for p in points]
        ax.plot(px, py, 'ro-', markersize=6, linewidth=1, alpha=0.7, label='Parcours')
        ax.plot(px[0], py[0], 'gs', markersize=12, label='Depart', zorder=5)
        ax.plot(px[-1], py[-1], 'r*', markersize=15, label='Arrivee', zorder=5)

    ax.set_xlabel('x', fontsize=12)
    ax.set_ylabel('f(x)', fontsize=12)
    ax.set_title(title, fontsize=14, fontweight='bold')
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)
    plt.tight_layout()
    return fig


# =============================================================================
# Benchmarking et comparaisons
# =============================================================================

def benchmark_table(results: list[dict], title: str = "Comparaison des algorithmes"):
    """Affiche un tableau de benchmark formate.

    results: liste de dicts avec cles 'algorithm', 'time_ms', 'nodes_expanded',
             'solution_found', 'optimal', etc.
    """
    print(f"\n{'=' * 70}")
    print(f"  {title}")
    print(f"{'=' * 70}")
    print(f"{'Algorithme':<25} {'Temps (ms)':<12} {'Noeuds':<10} {'Solution':<10} {'Optimal':<8}")
    print(f"{'-' * 70}")
    for r in results:
        algo = r.get('algorithm', '?')
        time_ms = r.get('time_ms', '?')
        nodes = r.get('nodes_expanded', '?')
        found = 'Oui' if r.get('solution_found', False) else 'Non'
        optimal = 'Oui' if r.get('optimal', False) else 'Non'
        print(f"{algo:<25} {str(time_ms):<12} {str(nodes):<10} {found:<10} {optimal:<8}")
    print(f"{'=' * 70}\n")


def plot_benchmark(results: list[dict], metric: str = 'time_ms',
                   title: str = "Comparaison des performances",
                   figsize: tuple = (10, 6)):
    """Graphique en barres pour comparer les performances."""
    algos = [r.get('algorithm', '?') for r in results]
    values = [r.get(metric, 0) for r in results]

    fig, ax = plt.subplots(1, 1, figsize=figsize)
    bars = ax.bar(range(len(algos)), values, color='steelblue', edgecolor='black')

    ax.set_xticks(range(len(algos)))
    ax.set_xticklabels(algos, rotation=45, ha='right', fontsize=10)
    ax.set_ylabel(metric.replace('_', ' ').title(), fontsize=12)
    ax.set_title(title, fontsize=14, fontweight='bold')
    ax.grid(axis='y', alpha=0.3)

    for bar, val in zip(bars, values):
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height(),
                f'{val:.1f}', ha='center', va='bottom', fontsize=9)

    plt.tight_layout()
    return fig


# =============================================================================
# Navigation pedagogique
# =============================================================================

def navigation_header(notebook_num: int, notebook_name: str,
                      series: str = "Foundations",
                      prev_name: str = None, next_name: str = None):
    """Genere le header de navigation Markdown."""
    prev_link = f"[<< {prev_name}]({series.split('/')[0]}-{notebook_num - 1}-{prev_name}.ipynb)" if prev_name else ""
    next_link = f"[{next_name} >>]({series.split('/')[0]}-{notebook_num + 1}-{next_name}.ipynb)" if next_name else ""
    index_link = f"[Index](../README.md)"

    return f"**Navigation** : {prev_link} | {index_link} | {next_link}"
