#!/usr/bin/env python3
"""Construit un export Turtle du cursus depuis le catalogue généré.

Le catalogue reste la source de vérité. Les champs absents (prérequis,
qualifications dédiées) ne sont pas déduits ni inventés. La hiérarchie de
concepts, elle, vit dans les taxonomies SKOS de séries
(`docs/curriculum/taxonomy/`) : leur couche concepts est fusionnée dans le
graphe servi (#27635) par l'organe existant `curriculum_taxonomy.build_graph`.
"""

import argparse
import json
import sys
from pathlib import Path
from urllib.parse import quote

from rdflib import Graph, Literal, Namespace, RDF, RDFS, URIRef
from rdflib.namespace import DCTERMS, SKOS
from pyshacl import validate

import curriculum_taxonomy


VOCAB = Namespace("https://github.com/jsboige/CoursIA/vocab/cursus#")
DEFAULT_CATALOG = Path(__file__).resolve().parents[2] / "COURSE_CATALOG.generated.json"
DEFAULT_SHAPES = Path(__file__).with_name("curriculum-shapes.ttl")
DEFAULT_INTERFACES = Path(__file__).with_name("agent_interfaces.json")
DEFAULT_TAXONOMY_DIR = curriculum_taxonomy.REPO_ROOT / curriculum_taxonomy.TAXONOMY_DIR

# Facette « classe d'interface » (#27071) : les trois classes mesurées par le
# recensement agentique. Enumeration fermee -- une classe inconnue est refusee,
# jamais inventee.
INTERFACE_CLASSES = ("bridge", "cli", "mcp")

# Nœuds d'arbre du cursus (série, sous-série, carnet) : la couche est déjà
# émise depuis le catalogue par build_graph ci-dessous. La fusion SKOS (#27635)
# retire ces nœuds du graphe de taxonomie — la taxonomie n'apporte au TTL
# servi que sa couche concepts (schémas, concepts, citations, ontologie) ;
# un doublon d'étiquette casserait les formes SHACL (NotebookShape exige un
# rdfs:label unique).
TREE_NODE_TYPES = (VOCAB.Notebook, VOCAB.Series, VOCAB.Subseries)


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


def build_interfaces_graph(interfaces: list[dict]) -> Graph:
    """Convertit l'inventaire des interfaces agentiques en ressources RDF.

    Chaque entree porte une classe d'interface fermee (cli / mcp / bridge),
    un chemin reel du depot et le contrat d'invocation mesure. Les champs
    absents ne sont pas deduits : une description ou une semantique de
    sortie manquante reste absente du graphe.
    """
    graph = Graph()
    graph.bind("cursus", VOCAB)
    graph.bind("dct", DCTERMS)
    graph.bind("rdfs", RDFS)
    for entry in interfaces:
        name = entry.get("name")
        path = entry.get("path")
        interface_class = entry.get("class")
        contract = entry.get("contract") or {}
        usage = contract.get("usage")
        if not all(isinstance(v, str) and v.strip() for v in (name, path, interface_class, usage)):
            raise ValueError(
                "chaque interface doit avoir name, path, class et contract.usage non vides"
            )
        if interface_class not in INTERFACE_CLASSES:
            raise ValueError(f"{name}: class doit etre une de {', '.join(INTERFACE_CLASSES)}")
        interface = _resource("interface", name)
        graph.add((interface, RDF.type, VOCAB.Interface))
        graph.add((interface, RDFS.label, Literal(name, lang="fr")))
        graph.add((interface, DCTERMS.identifier, Literal(path)))
        graph.add((interface, VOCAB.interfaceClass, Literal(interface_class)))
        graph.add((interface, VOCAB.invocation, Literal(usage.strip())))
        description = entry.get("description")
        if isinstance(description, str) and description.strip():
            graph.add(
                (interface, DCTERMS.description, Literal(description.strip(), lang="fr"))
            )
        exit_semantics = contract.get("exit_semantics")
        if isinstance(exit_semantics, str) and exit_semantics.strip():
            graph.add((interface, VOCAB.exitSemantics, Literal(exit_semantics.strip())))
    return graph


def strip_tree_nodes(taxonomy_graph: Graph) -> Graph:
    """Ne garde d'un graphe de taxonomie que sa couche concepts (#27635).

    Les nœuds d'arbre (série, sous-série, carnet) émis par
    `curriculum_taxonomy.build_graph` sont retirés : le catalogue les émet
    déjà dans le graphe servi, avec des URI identiques — les garder dupliquerait
    chaque carnet avec une seconde étiquette. Restent les schémas, concepts,
    citations de cellules, prérequis de concepts et axiomes d'ontologie.
    """
    tree_nodes = {
        subject
        for node_type in TREE_NODE_TYPES
        for subject in taxonomy_graph.subjects(RDF.type, node_type)
    }
    kept = Graph()
    for prefix, namespace in taxonomy_graph.namespaces():
        kept.bind(prefix, namespace)
    for triple in taxonomy_graph:
        if triple[0] not in tree_nodes:
            kept.add(triple)
    return kept


def build_concepts_layer(
    taxonomy_dir: Path = DEFAULT_TAXONOMY_DIR,
    repo_root: Path = curriculum_taxonomy.REPO_ROOT,
) -> tuple[Graph, list[dict], list[dict]]:
    """Fusionne la couche concepts des taxonomies SKOS de séries (#27635).

    L'organe d'export existe déjà (`curriculum_taxonomy`) : chaque JSON de
    série est chargé par son validateur puis converti par son `build_graph`.
    Une série sans taxonomie est simplement absente du TTL servi — le graphe
    est une photo de la couverture réelle, jamais une interpolation. Une
    taxonomie présente mais invalide (cellule déplacée, carnet renommé) est
    exclue avec un motif nommé dans `skipped` : l'invalidation vient du
    validateur, jamais d'une dérive silencieuse du TTL.

    Rend le graphe fusionné, la liste des séries fusionnées
    (`file`, `series`, `concepts`) et la liste des exclusions
    (`file`, `reason`).
    """
    graph = Graph()
    graph.bind("cursus", VOCAB)
    graph.bind("dct", DCTERMS)
    graph.bind("rdfs", RDFS)
    merged: list[dict] = []
    skipped: list[dict] = []
    if not taxonomy_dir.is_dir():
        return graph, merged, skipped
    files = sorted(
        path for path in taxonomy_dir.glob("*.json")
        if path.name != curriculum_taxonomy.SCHEMA_FILENAME
    )
    for data_path in files:
        try:
            data = curriculum_taxonomy.load_taxonomy(data_path, repo_root)
            taxonomy_graph = curriculum_taxonomy.build_graph(data)
        except (OSError, json.JSONDecodeError, ValueError) as error:
            skipped.append({"file": data_path.name, "reason": str(error)})
            continue
        graph += strip_tree_nodes(taxonomy_graph)
        merged.append(
            {"file": data_path.name, "series": data["series"], "concepts": len(data["concepts"])}
        )
    return graph, merged, skipped


def validate_graph(graph: Graph, shapes_path: Path = DEFAULT_SHAPES) -> tuple[bool, str]:
    """Valide la structure commune du graphe avec les formes SHACL."""
    shapes = Graph().parse(shapes_path, format="turtle")
    conforms, report, report_text = validate(
        graph, shacl_graph=shapes, inference="none", abort_on_first=False,
        allow_infos=False, allow_warnings=False,
    )
    return bool(conforms), str(report_text)


def generate(
    catalog_path: Path,
    output_path: Path,
    shapes_path: Path,
    interfaces_path: Path | None = None,
    taxonomy_dir: Path | None = DEFAULT_TAXONOMY_DIR,
    repo_root: Path = curriculum_taxonomy.REPO_ROOT,
) -> int:
    entries = json.loads(catalog_path.read_text(encoding="utf-8"))
    graph = build_graph(entries)
    if interfaces_path is not None:
        inventory = json.loads(interfaces_path.read_text(encoding="utf-8"))
        graph += build_interfaces_graph(inventory.get("interfaces", []))
    concepts_count = 0
    if taxonomy_dir is not None:
        concepts_graph, merged, skipped = build_concepts_layer(taxonomy_dir, repo_root)
        graph += concepts_graph
        concepts_count = len(list(graph.subjects(RDF.type, SKOS.Concept)))
        for entry in merged:
            print(
                f"Taxonomie fusionnée : {entry['series']} ({entry['file']}) -- "
                f"{entry['concepts']} concepts"
            )
        for entry in skipped:
            print(
                f"Taxonomie exclue du TTL servi : {entry['file']} -- {entry['reason']}",
                file=sys.stderr,
            )
    conforms, report = validate_graph(graph, shapes_path)
    if not conforms:
        print(report, file=sys.stderr)
        return 1
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(graph.serialize(format="turtle", encoding="utf-8"))
    print(
        f"Export RDF valide : {len(graph)} triples, "
        f"{concepts_count} concepts, {output_path}"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--catalog", type=Path, default=DEFAULT_CATALOG)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--shapes", type=Path, default=DEFAULT_SHAPES)
    parser.add_argument(
        "--interfaces", type=Path, default=None,
        help="inventaire JSON optionnel des interfaces agentiques (classes cli/mcp/bridge)",
    )
    parser.add_argument(
        "--taxonomy-dir", type=Path, default=DEFAULT_TAXONOMY_DIR,
        help="dossier des taxonomies SKOS de séries (défaut : docs/curriculum/taxonomy)",
    )
    args = parser.parse_args()
    return generate(
        args.catalog, args.output, args.shapes, args.interfaces,
        args.taxonomy_dir,
    )


if __name__ == "__main__":
    raise SystemExit(main())
