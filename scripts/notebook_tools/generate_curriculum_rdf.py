#!/usr/bin/env python3
"""Construit un export Turtle du cursus depuis le catalogue généré.

Le catalogue reste la source de vérité. Les champs absents (taxonomie,
prérequis, qualifications dédiées) ne sont pas déduits ni inventés.
"""

import argparse
import json
import sys
from pathlib import Path
from urllib.parse import quote

from rdflib import Graph, Literal, Namespace, RDF, RDFS, URIRef
from rdflib.namespace import DCTERMS
from pyshacl import validate


VOCAB = Namespace("https://github.com/jsboige/CoursIA/vocab/cursus#")
DEFAULT_CATALOG = Path(__file__).resolve().parents[2] / "COURSE_CATALOG.generated.json"
DEFAULT_SHAPES = Path(__file__).with_name("curriculum-shapes.ttl")


def _resource(kind: str, key: str) -> URIRef:
    return URIRef(f"https://github.com/jsboige/CoursIA/cursus/{kind}/{quote(key, safe='')}")


def _subseries_levels(entry: dict) -> list[str]:
    """Niveaux de sous-série du catalogue, du plus haut au plus bas.

    Le catalogue expose `sous_serie_levels` (liste des niveaux) depuis #24994 ;
    `sous_serie` reste lu comme repli pour les entrées qui ne portent que ce
    champ. Aucune hiérarchie n'est déduite du chemin du carnet : seul le
    catalogue fait foi.
    """
    levels = entry.get("sous_serie_levels")
    if isinstance(levels, list):
        cleaned = [value.strip() for value in levels if isinstance(value, str) and value.strip()]
        if cleaned:
            return cleaned
    single = entry.get("sous_serie")
    if isinstance(single, str) and single.strip():
        return [single.strip()]
    return []


def build_graph(entries: list[dict]) -> Graph:
    """Convertit les champs présents du catalogue en ressources RDF."""
    graph = Graph()
    graph.bind("cursus", VOCAB)
    graph.bind("dct", DCTERMS)
    graph.bind("rdfs", RDFS)

    series_seen: set[str] = set()
    for entry in entries:
        path = entry.get("path")
        title = entry.get("title")
        series = entry.get("serie")
        if not all(isinstance(value, str) and value.strip() for value in (path, title, series)):
            raise ValueError("chaque entrée doit avoir path, title et serie non vides")

        notebook = _resource("notebook", path)
        series_uri = _resource("serie", series)
        graph.add((notebook, RDF.type, VOCAB.Notebook))
        graph.add((notebook, RDFS.label, Literal(title, lang="fr")))
        graph.add((notebook, DCTERMS.identifier, Literal(path)))
        graph.add((notebook, VOCAB.inSeries, series_uri))

        # Contraintes d'exécution réellement présentes dans le catalogue.
        # Elles sont distinctes des ressources/API précises, que le catalogue
        # ne nomme pas aujourd'hui.
        for field, predicate in (
            ("requires_api", VOCAB.requiresAPI),
            ("requires_gpu", VOCAB.requiresGPU),
            ("requires_cloud", VOCAB.requiresCloud),
            ("requires_wsl", VOCAB.requiresWSL),
        ):
            value = entry.get(field)
            if isinstance(value, bool):
                graph.add((notebook, predicate, Literal(value)))
            elif value is not None:
                raise ValueError(f"{path}: {field} doit être booléen")

        for field, predicate in (
            ("duree_estimee", VOCAB.estimatedDuration),
            ("status", VOCAB.status),
        ):
            value = entry.get(field)
            if isinstance(value, str) and value.strip():
                graph.add((notebook, predicate, Literal(value.strip(), lang="fr")))
            elif value is not None and not isinstance(value, str):
                raise ValueError(f"{path}: {field} doit être une chaîne non vide")

        if series not in series_seen:
            graph.add((series_uri, RDF.type, VOCAB.Series))
            graph.add((series_uri, RDFS.label, Literal(series, lang="fr")))
            series_seen.add(series)

        # Le catalogue ne porte pas de champs de taxonomie ou de prérequis.
        # La hiérarchie des sous-séries, elle, est dans le catalogue : le
        # générateur de catalogue l'expose depuis #24994 sous
        # `sous_serie_levels` (niveaux) et `sous_serie_path` (chemin complet).
        # L'export la reproduit telle quelle, au lieu d'aplatir l'arbre sur son
        # premier niveau -- sans cela, 639 entrees du catalogue perdaient leur
        # imbrication dans le graphe.
        levels = _subseries_levels(entry)
        parent_uri = series_uri
        deepest_uri = None
        for depth, level in enumerate(levels):
            subsection_key = f"{series}/{'/'.join(levels[:depth + 1])}"
            subsection_uri = _resource("sous-serie", subsection_key)
            graph.add((subsection_uri, RDF.type, VOCAB.Subseries))
            graph.add((subsection_uri, RDFS.label, Literal(level, lang="fr")))
            graph.add((subsection_uri, VOCAB.subseriesPath, Literal("/".join(levels[:depth + 1]))))
            if depth == 0:
                graph.add((subsection_uri, VOCAB.partOfSeries, series_uri))
            else:
                graph.add((subsection_uri, VOCAB.partOfSubseries, parent_uri))
            parent_uri = subsection_uri
            deepest_uri = subsection_uri
        if deepest_uri is not None:
            graph.add((notebook, VOCAB.inSubseries, deepest_uri))

        # Qualifications seulement si explicitement présentes dans une
        # évolution future du catalogue. Aucun champ de remplacement n'est
        # supposé ici.
        for field, predicate in (("qualification", VOCAB.qualification),
                                 ("prerequisite", VOCAB.prerequisite),
                                 ("concept", VOCAB.concept)):
            value = entry.get(field)
            if isinstance(value, str) and value.strip():
                graph.add((notebook, predicate, Literal(value.strip())))

    return graph


def validate_graph(graph: Graph, shapes_path: Path = DEFAULT_SHAPES) -> tuple[bool, str]:
    """Valide la structure commune du graphe avec les formes SHACL."""
    shapes = Graph().parse(shapes_path, format="turtle")
    conforms, report, report_text = validate(
        graph, shacl_graph=shapes, inference="none", abort_on_first=False,
        allow_infos=False, allow_warnings=False,
    )
    return bool(conforms), str(report_text)


def generate(catalog_path: Path, output_path: Path, shapes_path: Path) -> int:
    entries = json.loads(catalog_path.read_text(encoding="utf-8"))
    graph = build_graph(entries)
    conforms, report = validate_graph(graph, shapes_path)
    if not conforms:
        print(report, file=sys.stderr)
        return 1
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(graph.serialize(format="turtle", encoding="utf-8"))
    print(f"Export RDF valide : {len(graph)} triples, {output_path}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--catalog", type=Path, default=DEFAULT_CATALOG)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--shapes", type=Path, default=DEFAULT_SHAPES)
    args = parser.parse_args()
    return generate(args.catalog, args.output, args.shapes)


if __name__ == "__main__":
    raise SystemExit(main())
