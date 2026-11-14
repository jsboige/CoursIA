#!/usr/bin/env python3
"""Valide et exporte une taxonomie pédagogique adossée aux cellules du dépôt."""

import argparse
import json
import sys
from pathlib import Path
from uuid import UUID
from urllib.parse import quote

from rdflib import BNode, Graph, Literal, Namespace, RDF, RDFS, URIRef
from rdflib.namespace import DCTERMS, OWL, SKOS, XSD


REPO_ROOT = Path(__file__).resolve().parents[2]
TAXONOMY_DIR = "docs/curriculum/taxonomy"
SCHEMA_FILENAME = "schema.json"
DEFAULT_DATA = REPO_ROOT / TAXONOMY_DIR / "compression.json"
VOCAB = Namespace("https://github.com/jsboige/CoursIA/vocab/cursus#")
BASE = "https://github.com/jsboige/CoursIA/cursus/"
ONTOLOGY = URIRef(BASE + "ontology")


def _fail(message: str) -> None:
    raise ValueError(message)


def _cell_ids(repo_root: Path, notebooks: list[str]) -> dict[str, set[str]]:
    result: dict[str, set[str]] = {}
    for relative_path in notebooks:
        notebook_path = repo_root / relative_path
        if not notebook_path.is_file():
            _fail(f"carnet source introuvable : {relative_path}")
        try:
            notebook = json.loads(notebook_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            _fail(f"carnet source illisible {relative_path}: {error}")
        cells = notebook.get("cells")
        if not isinstance(cells, list):
            _fail(f"liste de cellules absente : {relative_path}")
        ids = [cell.get("id") for cell in cells if isinstance(cell, dict)]
        if any(not isinstance(cell_id, str) or not cell_id for cell_id in ids):
            _fail(f"cellule sans identifiant stable : {relative_path}")
        if len(ids) != len(set(ids)):
            _fail(f"identifiants de cellule dupliqués : {relative_path}")
        result[relative_path] = set(ids)
    return result


def validate_taxonomy(data: dict, repo_root: Path = REPO_ROOT) -> None:
    """Vérifie structure, unicité, citations, couverture et graphe de prérequis."""
    required_hierarchy = ["series", "subseries", "notebook", "example", "exercise"]
    if data.get("schema_version") != 1:
        _fail("schema_version doit valoir 1")
    if not isinstance(data.get("series"), str) or not data["series"].strip():
        _fail("series doit être une chaîne non vide")
    hierarchy = data.get("hierarchy")
    if hierarchy != required_hierarchy:
        _fail("hierarchy doit réserver dans cet ordre series, subseries, notebook, example, exercise")
    notebooks = data.get("notebooks")
    if not isinstance(notebooks, list) or not notebooks or len(notebooks) != len(set(notebooks)):
        _fail("notebooks doit contenir des chemins uniques")
    concepts = data.get("concepts")
    if not isinstance(concepts, list) or not concepts:
        _fail("concepts doit être une liste non vide")

    notebook_tree = data.get("notebook_tree")
    if not isinstance(notebook_tree, list) or not notebook_tree:
        _fail("notebook_tree doit matérialiser l'arbre série/sous-série/carnet")
    tree_by_decimal: dict[str, dict] = {}
    tree_by_path: set[str] = set()
    for node in notebook_tree:
        if node.get("level") not in {"series", "subseries", "notebook"}:
            _fail(f"niveau de carnet inconnu : {node.get('level')}")
        for field in ("path", "decimal_path", "label_fr"):
            if not isinstance(node.get(field), str) or not node[field].strip():
                _fail(f"champ d'arbre absent ou vide : {field}")
        if node["path"] in tree_by_path or node["decimal_path"] in tree_by_decimal:
            _fail(f"path ou decimal_path de carnet dupliqué : {node['path']}")
        if node.get("depth") != node["decimal_path"].count("."):
            _fail(f"depth incompatible avec decimal_path du carnet : {node['decimal_path']}")
        if len(node["path"].split("/")) != node["depth"] + 1:
            _fail(f"profondeur de path incompatible pour le carnet : {node['path']}")
        if node["level"] == "series":
            if node["path"] != data["series"] or node["depth"] != 0:
                _fail("la racine doit être l'unique nœud série du périmètre")
        else:
            parent_decimal = node["decimal_path"].rsplit(".", 1)[0]
            parent = tree_by_decimal.get(parent_decimal)
            if parent is None or not node["path"].startswith(parent["path"] + "/"):
                _fail(f"parent absent ou incohérent dans l'arbre des carnets : {node['path']}")
        if node["level"] == "notebook" and node.get("repository_path") not in notebooks:
            _fail(f"carnet hors périmètre déclaré : {node.get('repository_path')}")
        tree_by_decimal[node["decimal_path"]] = node
        tree_by_path.add(node["path"])
    roots = [node for node in notebook_tree if node["level"] == "series"]
    tree_notebooks = {node.get("repository_path") for node in notebook_tree if node["level"] == "notebook"}
    if len(roots) != 1 or tree_notebooks != set(notebooks):
        _fail("l'arbre doit avoir une racine et couvrir exactement les carnets déclarés")

    cells_by_notebook = _cell_ids(repo_root, notebooks)
    ids: set[str] = set()
    paths: set[str] = set()
    decimal_paths: set[str] = set()
    by_decimal: dict[str, dict] = {}
    for concept in concepts:
        for field in ("id", "path", "decimal_path", "label_fr", "label_en", "definition_fr", "definition_en"):
            if not isinstance(concept.get(field), str) or not concept[field].strip():
                _fail(f"champ concept vide ou absent : {field}")
        try:
            UUID(concept["id"])
        except ValueError:
            _fail(f"identifiant de concept non UUID : {concept['id']}")
        if concept["id"] in ids:
            _fail(f"identifiant de concept dupliqué : {concept['id']}")
        if concept["path"] in paths:
            _fail(f"path de concept dupliqué : {concept['path']}")
        if concept["decimal_path"] in decimal_paths:
            _fail(f"decimal_path dupliqué : {concept['decimal_path']}")
        if concept.get("depth") != concept["decimal_path"].count("."):
            _fail(f"depth incompatible avec decimal_path : {concept['decimal_path']}")
        parts = concept["path"].split("/")
        # Le premier segment est l'espace de nom de la série ; les segments
        # suivants suivent la profondeur comme path/decimal_path chez Argumentum.
        if len(parts) != concept["depth"] + 2 or parts[0] != data["series"].lower() or any(not part for part in parts):
            _fail(f"profondeur de path incompatible : {concept['path']}")
        if any(c.isupper() for part in parts for c in part):
            _fail(f"segment de path en majuscules : {concept['path']}")
        citations = concept.get("citations")
        if not isinstance(citations, list) or not citations:
            _fail(f"concept sans citation de cellule : {concept['id']}")
        for citation in citations:
            notebook = citation.get("notebook")
            cell_id = citation.get("cell_id")
            if notebook not in cells_by_notebook:
                _fail(f"source hors du périmètre déclaré : {notebook}")
            if cell_id not in cells_by_notebook[notebook]:
                _fail(f"cellule citée introuvable : {notebook}#{cell_id}")
        prerequisites = concept.get("prerequisites")
        if not isinstance(prerequisites, list) or len(prerequisites) != len(set(prerequisites)):
            _fail(f"prerequisites doit être une liste sans doublon : {concept['id']}")
        ids.add(concept["id"])
        paths.add(concept["path"])
        decimal_paths.add(concept["decimal_path"])
        by_decimal[concept["decimal_path"]] = concept

    if len(by_decimal) != len(concepts):
        _fail("decimal_path doit être unique")
    for concept in concepts:
        decimal_path = concept["decimal_path"]
        if concept["depth"]:
            parent_decimal = decimal_path.rsplit(".", 1)[0]
            parent = by_decimal.get(parent_decimal)
            if parent is None:
                _fail(f"nœud parent manquant : {decimal_path}")
            if not concept["path"].startswith(parent["path"] + "/"):
                _fail(f"path et decimal_path ne décrivent pas le même parent : {decimal_path}")
        for prerequisite in concept["prerequisites"]:
            if prerequisite not in ids:
                _fail(f"prérequis inconnu {prerequisite} référencé par {concept['id']}")

    # Toute la tranche déclarée doit apparaître dans au moins une citation.
    cited_notebooks = {
        citation["notebook"]
        for concept in concepts
        for citation in concept["citations"]
    }
    missing = sorted(set(notebooks) - cited_notebooks)
    if missing:
        _fail("carnets sans concept sourcé : " + ", ".join(missing))

    prerequisites = {concept["id"]: concept["prerequisites"] for concept in concepts}
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(concept_id: str) -> None:
        if concept_id in visiting:
            _fail(f"cycle de prérequis détecté autour de {concept_id}")
        if concept_id in visited:
            return
        visiting.add(concept_id)
        for prerequisite in prerequisites[concept_id]:
            visit(prerequisite)
        visiting.remove(concept_id)
        visited.add(concept_id)

    for concept_id in prerequisites:
        visit(concept_id)


def load_taxonomy(data_path: Path = DEFAULT_DATA, repo_root: Path = REPO_ROOT) -> dict:
    data = json.loads(data_path.read_text(encoding="utf-8"))
    validate_taxonomy(data, repo_root)
    return data


def discover_taxonomies(repo_root: Path = REPO_ROOT) -> list[Path]:
    """Liste les taxonomies de séries du dossier, hors schéma JSON."""
    directory = repo_root / TAXONOMY_DIR
    if not directory.is_dir():
        _fail(f"dossier de taxonomies introuvable : {directory}")
    discovered = sorted(path for path in directory.glob("*.json") if path.name != SCHEMA_FILENAME)
    if not discovered:
        _fail(f"aucune taxonomie de série dans {directory}")
    return discovered


def validate_all(repo_root: Path = REPO_ROOT) -> list[dict]:
    """Valide chaque taxonomie du dossier : la couverture devient structurelle.

    Un JSON de série ajouté au dossier entre automatiquement dans la passe —
    plus de lien « 1 JSON ↔ 1 test » à maintenir à la main (suivi #25441).
    """
    results: list[dict] = []
    failures: list[str] = []
    for data_path in discover_taxonomies(repo_root):
        try:
            data = json.loads(data_path.read_text(encoding="utf-8"))
            validate_taxonomy(data, repo_root)
        except (OSError, json.JSONDecodeError, ValueError) as error:
            failures.append(f"{data_path.name} : {error}")
        else:
            results.append({"file": data_path.name, "series": data["series"], "concepts": len(data["concepts"])})
    if failures:
        _fail("taxonomies invalides -- " + " | ".join(failures))
    return results


def build_graph(data: dict) -> Graph:
    """Construit un graphe SKOS/OWL ; les identifiants restent indépendants des chemins."""
    graph = Graph()
    graph.bind("cursus", VOCAB)
    graph.bind("dct", DCTERMS)
    graph.bind("owl", OWL)
    graph.bind("skos", SKOS)
    graph.add((ONTOLOGY, RDF.type, OWL.Ontology))
    graph.add((ONTOLOGY, DCTERMS.title, Literal("Taxonomie du cursus CoursIA", lang="fr")))
    graph.add((VOCAB.CurriculumConcept, RDF.type, OWL.Class))
    graph.add((VOCAB.CurriculumConcept, RDFS.subClassOf, SKOS.Concept))
    graph.add((VOCAB.requiresConcept, RDF.type, OWL.ObjectProperty))
    graph.add((VOCAB.requiresConcept, RDFS.domain, VOCAB.CurriculumConcept))
    graph.add((VOCAB.requiresConcept, RDFS.range, VOCAB.CurriculumConcept))
    graph.add((VOCAB.hasCellCitation, RDF.type, OWL.ObjectProperty))
    graph.add((VOCAB.CellCitation, RDF.type, OWL.Class))
    graph.add((VOCAB.cellId, RDF.type, OWL.DatatypeProperty))
    graph.add((VOCAB.cellId, RDFS.domain, VOCAB.CellCitation))
    graph.add((VOCAB.path, RDF.type, OWL.DatatypeProperty))
    graph.add((VOCAB.decimalPath, RDF.type, OWL.DatatypeProperty))
    graph.add((VOCAB.depth, RDF.type, OWL.DatatypeProperty))

    series_uri = URIRef(BASE + "serie/" + quote(data["series"], safe=""))
    graph.add((series_uri, RDF.type, VOCAB.Series))
    graph.add((series_uri, RDFS.label, Literal(data["series"], lang="fr")))
    for node in data["notebook_tree"]:
        if node["level"] == "series":
            subject = series_uri
            graph.add((subject, VOCAB.path, Literal(node["path"])))
        elif node["level"] == "subseries":
            subject = URIRef(BASE + "sous-serie/" + quote(data["series"] + "/" + node["label_fr"], safe=""))
            graph.add((subject, RDF.type, VOCAB.Subseries))
            graph.add((subject, VOCAB.partOfSeries, series_uri))
            graph.add((subject, RDFS.label, Literal(node["label_fr"], lang="fr")))
        else:
            relative_notebook_path = node["repository_path"].removeprefix("MyIA.AI.Notebooks/")
            subject = URIRef(BASE + "notebook/" + quote(relative_notebook_path, safe=""))
            graph.add((subject, RDF.type, VOCAB.Notebook))
            graph.add((subject, RDFS.label, Literal(node["label_fr"], lang="fr")))
            graph.add((subject, DCTERMS.identifier, Literal(relative_notebook_path)))
            graph.add((subject, VOCAB.inSeries, series_uri))
        graph.add((subject, VOCAB.decimalPath, Literal(node["decimal_path"])))
        graph.add((subject, VOCAB.depth, Literal(node["depth"], datatype=XSD.integer)))

    scheme = URIRef(BASE + "scheme/" + data["series"].lower())
    graph.add((scheme, RDF.type, SKOS.ConceptScheme))
    graph.add((scheme, SKOS.prefLabel, Literal(data["series"], lang="fr")))
    concepts_by_id = {concept["id"]: URIRef(BASE + "concept/" + concept["id"]) for concept in data["concepts"]}
    concepts_by_decimal = {concept["decimal_path"]: concept for concept in data["concepts"]}

    for concept in data["concepts"]:
        uri = concepts_by_id[concept["id"]]
        graph.add((uri, RDF.type, SKOS.Concept))
        graph.add((uri, RDF.type, VOCAB.CurriculumConcept))
        graph.add((uri, SKOS.inScheme, scheme))
        graph.add((uri, DCTERMS.identifier, Literal(concept["id"])))
        graph.add((uri, SKOS.prefLabel, Literal(concept["label_fr"], lang="fr")))
        graph.add((uri, SKOS.prefLabel, Literal(concept["label_en"], lang="en")))
        graph.add((uri, SKOS.definition, Literal(concept["definition_fr"], lang="fr")))
        graph.add((uri, SKOS.definition, Literal(concept["definition_en"], lang="en")))
        graph.add((uri, VOCAB.path, Literal(concept["path"])))
        graph.add((uri, VOCAB.decimalPath, Literal(concept["decimal_path"])))
        graph.add((uri, VOCAB.depth, Literal(concept["depth"], datatype=XSD.integer)))
        decimal_path = concept["decimal_path"]
        if concept["depth"]:
            parent = concepts_by_decimal[decimal_path.rsplit(".", 1)[0]]
            graph.add((uri, SKOS.broader, concepts_by_id[parent["id"]]))
        else:
            graph.add((scheme, SKOS.hasTopConcept, uri))
        for prerequisite in concept["prerequisites"]:
            graph.add((uri, VOCAB.requiresConcept, concepts_by_id[prerequisite]))
        for citation in concept["citations"]:
            notebook_uri = URIRef("https://github.com/jsboige/CoursIA/blob/main/" + citation["notebook"])
            graph.add((uri, DCTERMS.source, notebook_uri))
            citation_uri = BNode()
            graph.add((uri, VOCAB.hasCellCitation, citation_uri))
            graph.add((citation_uri, RDF.type, VOCAB.CellCitation))
            graph.add((citation_uri, DCTERMS.source, notebook_uri))
            graph.add((citation_uri, VOCAB.cellId, Literal(citation["cell_id"])))
    return graph


def generate(data_path: Path, skos_output: Path, owl_output: Path, repo_root: Path = REPO_ROOT) -> int:
    data = load_taxonomy(data_path, repo_root)
    graph = build_graph(data)
    skos_output.parent.mkdir(parents=True, exist_ok=True)
    owl_output.parent.mkdir(parents=True, exist_ok=True)
    skos_output.write_bytes(graph.serialize(format="turtle", encoding="utf-8"))
    owl_output.write_bytes(graph.serialize(format="xml", encoding="utf-8"))
    print(f"Taxonomie valide : {len(data['concepts'])} concepts, {len(graph)} triples")
    print(f"SKOS : {skos_output}")
    print(f"OWL : {owl_output}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=DEFAULT_DATA)
    parser.add_argument("--all", action="store_true",
                        help="valider toutes les taxonomies du dossier (couverture structurelle, sans export)")
    parser.add_argument("--skos-output", type=Path)
    parser.add_argument("--owl-output", type=Path)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    args = parser.parse_args()
    if not args.all and (args.skos_output is None or args.owl_output is None):
        parser.error("--skos-output et --owl-output sont requis (sauf avec --all)")
    try:
        if args.all:
            for entry in validate_all(args.repo_root):
                print(f"Taxonomie valide : {entry['series']} ({entry['file']}) -- {entry['concepts']} concepts")
            return 0
        return generate(args.data, args.skos_output, args.owl_output, args.repo_root)
    except (OSError, json.JSONDecodeError, ValueError) as error:
        print(f"Erreur de taxonomie : {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
