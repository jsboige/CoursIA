#!/usr/bin/env python3
"""Interroge l'export Turtle du cursus, sans relire le catalogue source."""

import argparse
import sys
from collections import defaultdict
from pathlib import Path
from typing import Iterable

from rdflib import BNode, Graph, Literal, RDF, URIRef
from rdflib.namespace import DCTERMS, RDFS, SKOS

from generate_curriculum_rdf import VOCAB


RESOURCE_PREDICATES = {
    "api": VOCAB.requiresAPI,
    "gpu": VOCAB.requiresGPU,
    "cloud": VOCAB.requiresCloud,
    "wsl": VOCAB.requiresWSL,
}
RESOURCE_LABELS = {"api": "API", "gpu": "GPU", "cloud": "cloud", "wsl": "WSL"}


def load_graph(paths: Iterable[Path]) -> Graph:
    graph = Graph()
    for path in paths:
        graph.parse(path, format="turtle")
    validate_prerequisite_acyclicity(graph)
    return graph


def _notebooks(graph: Graph) -> list[URIRef]:
    return sorted(graph.subjects(RDF.type, VOCAB.Notebook), key=str)


def _identifier(graph: Graph, notebook: URIRef) -> str:
    value = graph.value(notebook, DCTERMS.identifier)
    return str(value) if value is not None else str(notebook)


def _label(graph: Graph, subject: URIRef | BNode) -> str:
    value = graph.value(subject, SKOS.prefLabel)
    if value is None:
        value = graph.value(subject, RDFS.label)
    return str(value) if value is not None else str(subject)


def _boolean_value(value: Literal, predicate: URIRef) -> bool:
    if not isinstance(value, Literal):
        raise ValueError(f"la propriété {predicate} doit être un littéral booléen RDF")
    converted = value.toPython()
    if not isinstance(converted, bool):
        raise ValueError(f"la propriété {predicate} doit contenir un booléen RDF")
    return converted


def find_notebook(graph: Graph, path: str) -> URIRef:
    matches = [
        notebook for notebook in _notebooks(graph)
        if _identifier(graph, notebook) == path
    ]
    if len(matches) != 1:
        raise KeyError(path)
    return matches[0]


def validate_prerequisite_acyclicity(graph: Graph) -> None:
    """Refuse cycles among explicit URI-to-URI prerequisite links."""
    edges: dict[URIRef, list[URIRef]] = defaultdict(list)
    for source, target in graph.subject_objects(VOCAB.prerequisite):
        if isinstance(source, URIRef) and isinstance(target, URIRef):
            edges[source].append(target)

    visiting: list[URIRef] = []
    visited: set[URIRef] = set()

    def visit(node: URIRef) -> None:
        if node in visiting:
            cycle = visiting[visiting.index(node):] + [node]
            raise ValueError("cycle de prérequis : " + " -> ".join(map(str, cycle)))
        if node in visited:
            return
        visiting.append(node)
        for successor in edges.get(node, []):
            visit(successor)
        visiting.pop()
        visited.add(node)

    for node in edges:
        visit(node)


def _path_labels(graph: Graph, notebook: URIRef) -> list[str]:
    series = graph.value(notebook, VOCAB.inSeries)
    subsection = graph.value(notebook, VOCAB.inSubseries)
    labels = [_label(graph, series)] if series is not None else []
    if subsection is not None:
        labels.append(_label(graph, subsection))
    labels.append(_label(graph, notebook))
    return labels


def list_series(graph: Graph) -> list[str]:
    series_nodes = sorted(
        graph.subjects(RDF.type, VOCAB.Series),
        key=lambda node: _label(graph, node).casefold(),
    )
    lines = []
    for series in series_nodes:
        count = sum(1 for _ in graph.subjects(VOCAB.inSeries, series))
        lines.append(f"{_label(graph, series)} ({count} carnets)")
    return lines


def list_notebooks(
    graph: Graph,
    series_filter: str | None = None,
    subseries_filter: str | None = None,
    query: str | None = None,
    limit: int | None = None,
) -> list[str]:
    needle = query.casefold() if query else None
    matches = []
    for notebook in _notebooks(graph):
        series = graph.value(notebook, VOCAB.inSeries)
        subsection = graph.value(notebook, VOCAB.inSubseries)
        if series_filter and (
            series is None or _label(graph, series).casefold() != series_filter.casefold()
        ):
            continue
        if subseries_filter and (
            subsection is None
            or _label(graph, subsection).casefold() != subseries_filter.casefold()
        ):
            continue
        identifier = _identifier(graph, notebook)
        title = _label(graph, notebook)
        if needle and needle not in (identifier + " " + title).casefold():
            continue
        matches.append(f"{title}\t{identifier}")
    matches.sort(key=str.casefold)
    return matches[:limit] if limit is not None else matches


def show_notebook(graph: Graph, path: str) -> list[str]:
    notebook = find_notebook(graph, path)
    lines = [f"Titre : {_label(graph, notebook)}", f"Chemin : {_identifier(graph, notebook)}"]
    lines.append("Parcours : " + " > ".join(_path_labels(graph, notebook)))
    for name, predicate in RESOURCE_PREDICATES.items():
        value = graph.value(notebook, predicate)
        if value is not None:
            required = _boolean_value(value, predicate)
            lines.append(f"Nécessite {RESOURCE_LABELS[name]} : {'oui' if required else 'non'}")
    duration = graph.value(notebook, VOCAB.estimatedDuration)
    status = graph.value(notebook, VOCAB.status)
    if duration is not None:
        lines.append(f"Durée estimée : {duration}")
    if status is not None:
        lines.append(f"Statut : {status}")
    prerequisites = sorted(
        (str(value) for value in graph.objects(notebook, VOCAB.prerequisite)),
        key=str.casefold,
    )
    if prerequisites:
        lines.append("Prérequis explicites : " + ", ".join(prerequisites))
    else:
        lines.append("Prérequis : non renseignés dans l'export")
    return lines


def notebooks_requiring(graph: Graph, kind: str, limit: int | None = None) -> list[str]:
    predicate = RESOURCE_PREDICATES[kind]
    matches = []
    for notebook in _notebooks(graph):
        value = graph.value(notebook, predicate)
        if value is not None and _boolean_value(value, predicate):
            matches.append(f"{_label(graph, notebook)}\t{_identifier(graph, notebook)}")
    matches.sort(key=str.casefold)
    return matches[:limit] if limit is not None else matches


def notebooks_by_resource(
    graph: Graph, kind: str, state: str, limit: int | None = None
) -> list[str]:
    predicate = RESOURCE_PREDICATES[kind]
    matches = []
    for notebook in _notebooks(graph):
        value = graph.value(notebook, predicate)
        actual = None if value is None else _boolean_value(value, predicate)
        expected = {"required": True, "not-required": False, "unknown": None}[state]
        if actual == expected:
            matches.append(f"{_label(graph, notebook)}\t{_identifier(graph, notebook)}")
    matches.sort(key=str.casefold)
    return matches[:limit] if limit is not None else matches


def prerequisites_for(graph: Graph, path: str) -> list[str]:
    notebook = find_notebook(graph, path)
    values = sorted(
        (str(value) for value in graph.objects(notebook, VOCAB.prerequisite)),
        key=str.casefold,
    )
    return values or ["Prérequis non renseignés dans l'export."]


def concepts_for(graph: Graph, query: str | None = None, limit: int | None = None) -> list[str]:
    needle = query.casefold() if query else None
    matches = []
    for concept in graph.subjects(RDF.type, SKOS.Concept):
        value = (
            _label(graph, concept)
            if isinstance(concept, (URIRef, BNode))
            else str(concept)
        )
        if not needle or needle in value.casefold():
            matches.append(f"{value}\t{concept}")
    for notebook in _notebooks(graph):
        for concept in graph.objects(notebook, VOCAB.concept):
            value = (
                _label(graph, concept)
                if isinstance(concept, (URIRef, BNode))
                else str(concept)
            )
            if needle and needle not in value.casefold():
                continue
            matches.append(f"{value}\t{_label(graph, notebook)}\t{_identifier(graph, notebook)}")
    matches = sorted(set(matches), key=str.casefold)
    return matches[:limit] if limit is not None else matches


def path_for(graph: Graph, path: str) -> list[str]:
    notebook = find_notebook(graph, path)
    return _path_labels(graph, notebook)


def _print_lines(lines: Iterable[str]) -> None:
    for line in lines:
        print(line)


def positive_int(value: str) -> int:
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("la limite doit être positive")
    return number


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--graph", required=True, type=Path, action="append",
        help="export Turtle à réunir (répéter cette option pour plusieurs fichiers)",
    )
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("series", help="lister les séries et leur nombre de carnets")
    listing = commands.add_parser("list", help="rechercher ou filtrer des carnets")
    listing.add_argument("--series")
    listing.add_argument("--subseries")
    listing.add_argument("--query", help="texte recherché dans le titre ou le chemin")
    listing.add_argument("--limit", type=positive_int, help="nombre maximal de résultats")
    show = commands.add_parser("show", help="afficher la fiche d'un carnet")
    show.add_argument("path")
    resources = commands.add_parser(
        "resources", help="lister les carnets selon leur contrainte d'exécution"
    )
    resources.add_argument("kind", choices=sorted(RESOURCE_PREDICATES))
    resources.add_argument("--limit", type=positive_int, help="nombre maximal de résultats")
    resources.add_argument(
        "--state", choices=("required", "not-required", "unknown"),
        default="required", help="état de la propriété (défaut : required)",
    )
    prerequisites = commands.add_parser(
        "prerequisites", help="lire les prérequis explicitement exportés"
    )
    prerequisites.add_argument("path")
    concepts = commands.add_parser(
        "concepts", help="lister les concepts explicitement liés aux carnets"
    )
    concepts.add_argument("--query", help="filtrer le libellé du concept")
    concepts.add_argument("--limit", type=positive_int, help="nombre maximal de résultats")
    path = commands.add_parser("path", help="afficher le chemin série > sous-série > carnet")
    path.add_argument("path")
    args = parser.parse_args(argv)

    try:
        graph = load_graph(args.graph)
        if args.command == "series":
            _print_lines(list_series(graph))
        elif args.command == "list":
            _print_lines(
                list_notebooks(graph, args.series, args.subseries, args.query, args.limit)
            )
        elif args.command == "show":
            _print_lines(show_notebook(graph, args.path))
        elif args.command == "resources":
            _print_lines(notebooks_by_resource(graph, args.kind, args.state, args.limit))
        elif args.command == "prerequisites":
            _print_lines(prerequisites_for(graph, args.path))
        elif args.command == "concepts":
            _print_lines(concepts_for(graph, args.query, args.limit))
        elif args.command == "path":
            print(" > ".join(path_for(graph, args.path)))
    except KeyError as error:
        print(f"Carnet introuvable dans l'export : {error.args[0]}", file=sys.stderr)
        return 2
    except ValueError as error:
        print(str(error), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
