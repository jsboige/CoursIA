#!/usr/bin/env python3
"""Graphe de dependances entre modules d'un lake Lean -- pli 6 Origami Wolfram.

Issue #21641 (Part of #19742). Le pli 6 de l'EPIC veut mesurer « le graphe de
dependances des theoremes d'un lake » : les theoremes comme chemins d'un
systeme multiway (Wolfram, *The Empirical Metamathematics of Euclid and
Beyond*, arXiv 2107.07337).

Ce script mesure la version grossiere mais reproductible : le graphe des
**modules** (fichiers .lean) du lake, arcs = `import X.Y.Z` internes. C'est
une borne superieure du graphe de theoremes -- un module peut reexporter tout
ce qu'il importe sans qu'aucun theoreme ne soit cite. La limite est ecrite
dans le rapport ; raffiner par theoreme demande d'elaborer Lean pour resoudre
les references (cout estime, non fait ici).

Les imports externes (Mathlib, batteries...) ne sont pas des noeuds : ils
sont comptes comme frontiere (par module externe cite), sinon Mathlib
ecraserait toute mesure locale.

Usage :
    python scripts/lean/lemma_dependency_graph.py \
        --lake MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean --json

Exit codes : 0 = mesure produite ; 2 = instrument casse (lake introuvable,
aucun module).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

EXIT_OK = 0
EXIT_INSTRUMENT = 2

# Un import Lean tient sur une ligne : `import Foo.Bar.Baz`.
_IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$")
# Racines qui ne sont pas du code du lake : dependances vendorisees et
# artefacts de build.
_EXCLUDED_DIRS = {".lake", "build", ".git"}


def iter_lean_files(lake_root: Path) -> list[Path]:
    """Rend les fichiers .lean du lake, hors .lake/ et dossiers de build."""
    files: list[Path] = []
    for path in lake_root.rglob("*.lean"):
        rel_parts = path.relative_to(lake_root).parts
        if any(part in _EXCLUDED_DIRS for part in rel_parts):
            continue
        files.append(path)
    return sorted(files)


def module_name(lake_root: Path, path: Path) -> str:
    """Nom de module Lean d'un fichier : chemin relatif sans .lean, points."""
    rel = path.relative_to(lake_root).with_suffix("")
    return ".".join(rel.parts)


def parse_imports(text: str) -> list[str]:
    """Extrait les modules importes d'une source Lean (lignes `import X`)."""
    return [m.group(1) for line in text.splitlines()
            if (m := _IMPORT_RE.match(line))]


def build_graph(lake_root: Path) -> dict:
    """Construit le graphe {module: [imports internes]} + la frontiere externe.

    `external` compte, par nom de module externe, combien de modules du lake
    l'importent -- la frontiere qui dit a quoi le lake s'accroche.
    """
    files = iter_lean_files(lake_root)
    nodes = {module_name(lake_root, path) for path in files}
    graph: dict[str, list[str]] = {name: [] for name in nodes}
    external: Counter[str] = Counter()
    for path in files:
        name = module_name(lake_root, path)
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for imported in parse_imports(text):
            if imported in nodes:
                graph[name].append(imported)
            else:
                external[imported.split(".")[0]] += 1
    return {"nodes": sorted(nodes), "graph": graph, "external": dict(external)}


def _depths(graph: dict[str, list[str]]) -> tuple[dict[str, int], bool]:
    """Profondeur de chaque module (plus long chemin vers une feuille).

    Rend (profondeur, a_cycle). Un import circulaire est anormal en Lean ;
    on le signale plutot que de boucler (defense, jamais observe).
    """
    depth: dict[str, int] = {}
    visiting: set[str] = set()
    cyclic = False

    def visit(node: str) -> int:
        if node in depth:
            return depth[node]
        if node in visiting:
            nonlocal cyclic
            cyclic = True
            return 0
        visiting.add(node)
        best = 0
        for dep in graph.get(node, []):
            best = max(best, visit(dep) + 1)
        visiting.discard(node)
        depth[node] = best
        return best

    for node in graph:
        visit(node)
    return depth, cyclic


def _weak_components(graph: dict[str, list[str]]) -> int:
    """Nombre de composantes connexes (aretes non orientees)."""
    undirected: dict[str, set[str]] = defaultdict(set)
    for node, deps in graph.items():
        undirected.setdefault(node, set())
        for dep in deps:
            undirected[node].add(dep)
            undirected.setdefault(dep, set()).add(node)
    seen: set[str] = set()
    components = 0
    for start in undirected:
        if start in seen:
            continue
        components += 1
        stack = [start]
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            seen.add(node)
            stack.extend(undirected[node] - seen)
    return components


def compute_metrics(data: dict, top: int = 5) -> dict:
    """Metriques du graphe : taille, profondeur, degres, frontieres."""
    graph: dict[str, list[str]] = data["graph"]
    nodes: list[str] = data["nodes"]
    in_degree: Counter[str] = Counter()
    for deps in graph.values():
        in_degree.update(deps)
    depth, cyclic = _depths(graph)
    depths = list(depth.values())
    total_edges = sum(len(deps) for deps in graph.values())
    return {
        "modules": len(nodes),
        "internal_edges": total_edges,
        "mean_out_degree": round(total_edges / len(nodes), 3) if nodes else 0.0,
        "mean_in_degree": round(
            sum(in_degree.values()) / len(nodes), 3) if nodes else 0.0,
        "max_depth": max(depths) if depths else 0,
        "mean_depth": round(sum(depths) / len(depths), 3) if depths else 0.0,
        "leaf_modules": sum(1 for n in nodes if not graph.get(n)),
        "external_roots": dict(Counter(data["external"]).most_common(top)),
        "top_referenced": dict(in_degree.most_common(top)),
        "weak_components": _weak_components(graph),
        "cyclic": cyclic,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Graphe de dependances entre modules d'un lake Lean "
                    "(pli 6 Origami Wolfram, #21641).")
    parser.add_argument("--lake", required=True,
                        help="racine du lake (dossier contenant lakefile.lean)")
    parser.add_argument("--top", type=int, default=5,
                        help="taille des classements (default: 5)")
    parser.add_argument("--json", action="store_true",
                        help="sortie JSON complete")
    args = parser.parse_args(argv)

    lake_root = Path(args.lake)
    if not lake_root.is_dir():
        print(f"[dep-graph] lake introuvable: {lake_root}", file=sys.stderr)
        return EXIT_INSTRUMENT
    data = build_graph(lake_root)
    if not data["nodes"]:
        print(f"[dep-graph] aucun module .lean sous {lake_root}", file=sys.stderr)
        return EXIT_INSTRUMENT
    metrics = compute_metrics(data, args.top)

    if args.json:
        print(json.dumps({"lake": str(lake_root), "metrics": metrics,
                          "graph": data["graph"]}, indent=2,
                         ensure_ascii=False))
    else:
        print(f"[dep-graph] lake={lake_root}")
        for key, value in metrics.items():
            print(f"[dep-graph] {key}: {value}")
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())