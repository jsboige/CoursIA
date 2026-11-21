#!/usr/bin/env python3
"""Valide, mesure et exporte les taxonomies pédagogiques adossées aux cellules du dépôt.

Une taxonomie est un fichier JSON de `docs/curriculum/taxonomy/`. Ses concepts
peuvent citer les carnets d'une autre taxonomie, requérir ses concepts
(`prerequisites`) et s'y aligner (`matches`, exact ou close) : ce sont les
ponts que `--bridges` relève et que l'export SKOS porte.
"""

import argparse
import contextlib
import json
import sys
from pathlib import Path
from uuid import UUID
from urllib.parse import quote

from rdflib import BNode, Graph, Literal, Namespace, RDF, RDFS, URIRef
from rdflib.namespace import DCTERMS, OWL, SKOS, XSD

import curriculum_taxonomy_survey as survey


REPO_ROOT = Path(__file__).resolve().parents[2]
TAXONOMY_DIR = "docs/curriculum/taxonomy"
SCHEMA_FILENAME = "schema.json"
DEFAULT_DATA = REPO_ROOT / TAXONOMY_DIR / "compression.json"
VOCAB = Namespace("https://github.com/jsboige/CoursIA/vocab/cursus#")
BASE = "https://github.com/jsboige/CoursIA/cursus/"
ONTOLOGY = URIRef(BASE + "ontology")
NOTEBOOKS_ROOT = "MyIA.AI.Notebooks/"
BLOB_PREFIX = "https://github.com/jsboige/CoursIA/blob/main/"
CONCEPT_TEXT_FIELDS = ("id", "path", "decimal_path", "label_fr", "label_en", "definition_fr", "definition_en")
CONCEPT_FIELDS = {*CONCEPT_TEXT_FIELDS, "depth", "citations", "prerequisites", "matches"}
MATCH_PREDICATES = {"exact": SKOS.exactMatch, "close": SKOS.closeMatch}


def _fail(message: str) -> None:
    raise ValueError(message)


def load_corpus(repo_root: Path = REPO_ROOT) -> dict[str, dict]:
    """Taxonomies lisibles du dossier, par nom de fichier sans extension (lues, non validées)."""
    directory = repo_root / TAXONOMY_DIR
    corpus: dict[str, dict] = {}
    if not directory.is_dir():
        return corpus
    for path in sorted(directory.glob("*.json")):
        if path.name == SCHEMA_FILENAME:
            continue
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(data, dict):
            corpus[path.stem] = data
    return corpus


def _other_taxonomies(data: dict, corpus: dict[str, dict]) -> tuple[dict[str, list[str]], set[str]]:
    """Concepts (identifiant -> prérequis) et carnets déclarés par les AUTRES taxonomies du dossier.

    Les identifiants de concept sont globaux : une taxonomie du dossier qui en
    partage un avec `data` est `data` elle-même (ou sa version sur disque), et
    elle est écartée. Le doublon d'identifiant entre deux fichiers distincts
    est refusé à part, par `cross_taxonomy_failures`.
    """
    own = {concept["id"] for concept in survey.concepts_of(data)}
    concepts: dict[str, list[str]] = {}
    notebooks: set[str] = set()
    for other in corpus.values():
        other_concepts = survey.concepts_of(other)
        if own & {concept["id"] for concept in other_concepts}:
            continue
        for concept in other_concepts:
            concepts[concept["id"]] = survey.prerequisites_of(concept)
        notebooks.update(survey.notebooks_of(other))
    return concepts, notebooks


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


def _validate_matches(concept: dict) -> None:
    """Forme du champ optionnel `matches` ; l'existence des concepts visés se contrôle ensuite."""
    matches = concept.get("matches", [])
    if not isinstance(matches, list):
        _fail(f"matches doit être une liste : {concept['id']}")
    targets: set[str] = set()
    for match in matches:
        if not isinstance(match, dict) or set(match) != {"concept", "kind"}:
            _fail(f"alignement mal formé, attendu concept et kind : {concept['id']}")
        target, kind = match["concept"], match["kind"]
        if not isinstance(target, str) or not isinstance(kind, str):
            _fail(f"alignement mal formé, concept et kind sont des chaînes : {concept['id']}")
        if kind not in MATCH_PREDICATES:
            _fail(f"kind d'alignement inconnu {kind!r}, attendu exact ou close : {concept['id']}")
        if target == concept["id"]:
            _fail(f"alignement d'un concept sur lui-même : {concept['id']}")
        if target in targets:
            _fail(f"alignement dupliqué vers {target} : {concept['id']}")
        targets.add(target)


def validate_taxonomy(data: dict, repo_root: Path = REPO_ROOT, corpus: dict[str, dict] | None = None) -> None:
    """Vérifie structure, unicité, citations, couverture, alignements et graphe de prérequis.

    `corpus` est l'ensemble des taxonomies du dossier (lu sur disque par
    défaut) : une citation, un prérequis ou un alignement peut viser le carnet
    ou le concept d'une autre taxonomie, à condition qu'il y soit déclaré.
    """
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

    foreign_concepts, foreign_notebooks = _other_taxonomies(
        data, load_corpus(repo_root) if corpus is None else corpus)
    cells_by_notebook = _cell_ids(repo_root, notebooks)
    ids: set[str] = set()
    paths: set[str] = set()
    decimal_paths: set[str] = set()
    by_decimal: dict[str, dict] = {}
    for concept in concepts:
        if not isinstance(concept, dict):
            _fail("chaque concept doit être un objet")
        for field in CONCEPT_TEXT_FIELDS:
            if not isinstance(concept.get(field), str) or not concept[field].strip():
                _fail(f"champ concept vide ou absent : {field}")
        unknown_fields = sorted(set(concept) - CONCEPT_FIELDS)
        if unknown_fields:
            _fail(f"champ concept inconnu ({', '.join(unknown_fields)}) : {concept['id']}")
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
                # Un carnet déclaré par une autre taxonomie du dossier peut être
                # cité : c'est ce qui fait un concept partagé entre deux séries.
                if notebook not in foreign_notebooks:
                    _fail(f"source hors du périmètre déclaré : {notebook}")
                cells_by_notebook.update(_cell_ids(repo_root, [notebook]))
            if cell_id not in cells_by_notebook[notebook]:
                _fail(f"cellule citée introuvable : {notebook}#{cell_id}")
        prerequisites = concept.get("prerequisites")
        if not isinstance(prerequisites, list) or len(prerequisites) != len(set(prerequisites)):
            _fail(f"prerequisites doit être une liste sans doublon : {concept['id']}")
        _validate_matches(concept)
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
        # Un prérequis vise un concept de cette taxonomie ou d'une autre du dossier.
        for prerequisite in concept["prerequisites"]:
            if prerequisite not in ids and prerequisite not in foreign_concepts:
                _fail(f"prérequis inconnu {prerequisite} référencé par {concept['id']}")
        # Un alignement relie deux vocabulaires : il vise toujours une autre taxonomie.
        for match in concept.get("matches", []):
            if match["concept"] in ids:
                _fail(f"alignement interne à la taxonomie ({match['concept']}) : {concept['id']}")
            if match["concept"] not in foreign_concepts:
                _fail(f"concept aligné inconnu {match['concept']} référencé par {concept['id']}")

    # Toute la tranche déclarée doit apparaître dans au moins une citation.
    cited_notebooks = {
        citation["notebook"]
        for concept in concepts
        for citation in concept["citations"]
    }
    missing = sorted(set(notebooks) - cited_notebooks)
    if missing:
        _fail("carnets sans concept sourcé : " + ", ".join(missing))

    # Le graphe de prérequis est suivi à travers les taxonomies : un cycle qui
    # passe par une autre série est un cycle.
    prerequisites = dict(foreign_concepts)
    prerequisites.update({concept["id"]: concept["prerequisites"] for concept in concepts})
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(concept_id: str) -> None:
        if concept_id in visiting:
            _fail(f"cycle de prérequis détecté autour de {concept_id}")
        if concept_id in visited:
            return
        visiting.add(concept_id)
        for prerequisite in prerequisites.get(concept_id, []):
            visit(prerequisite)
        visiting.remove(concept_id)
        visited.add(concept_id)

    for concept in concepts:
        visit(concept["id"])


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


def cross_taxonomy_failures(corpus: dict[str, dict]) -> list[str]:
    """Incohérences qui ne se voient qu'en lisant plusieurs taxonomies ensemble."""
    concept_files: dict[str, list[str]] = {}
    notebook_files: dict[str, list[str]] = {}
    kinds: dict[frozenset[str], set[str]] = {}
    for name, data in corpus.items():
        for notebook in survey.notebooks_of(data):
            notebook_files.setdefault(notebook, []).append(name)
        for concept in survey.concepts_of(data):
            concept_files.setdefault(concept["id"], []).append(name)
            for target, kind in survey.matches_of(concept):
                kinds.setdefault(frozenset((concept["id"], target)), set()).add(kind)
    failures: list[str] = []
    for concept_id, names in sorted(concept_files.items()):
        if len(names) > 1:
            failures.append(
                f"identifiant de concept déclaré par plusieurs taxonomies ({', '.join(names)}) : {concept_id}")
    for notebook, names in sorted(notebook_files.items()):
        if len(names) > 1:
            failures.append(f"carnet déclaré par plusieurs taxonomies ({', '.join(names)}) : {notebook}")
    for pair in sorted(kinds, key=sorted):
        if len(kinds[pair]) > 1:
            failures.append("alignement réciproque contradictoire, exact d'un côté et close de l'autre : "
                            + " / ".join(sorted(pair)))
    # Deux concepts d'une même taxonomie rendus identiques par une chaîne
    # d'alignements exacts : l'un des alignements est faux, ou c'est un doublon.
    concept_owner = survey.owners(corpus)[0]
    for members in survey.exact_classes(corpus):
        seen: dict[str, str] = {}
        for member in members:
            name = concept_owner.get(member)
            if name is None:
                continue
            if name in seen:
                failures.append(
                    f"alignements exacts qui identifient deux concepts de {name} : {seen[name]} / {member}")
                break
            seen[name] = member
    return failures


def validate_all(repo_root: Path = REPO_ROOT) -> list[dict]:
    """Valide chaque taxonomie du dossier, puis leur cohérence d'ensemble.

    Un JSON de série ajouté au dossier entre automatiquement dans la passe :
    aucun lien « un JSON, un test » à maintenir à la main.
    """
    results: list[dict] = []
    failures: list[str] = []
    corpus = load_corpus(repo_root)
    for data_path in discover_taxonomies(repo_root):
        try:
            data = json.loads(data_path.read_text(encoding="utf-8"))
            validate_taxonomy(data, repo_root, corpus)
        except (OSError, json.JSONDecodeError, ValueError) as error:
            failures.append(f"{data_path.name} : {error}")
        else:
            results.append({"file": data_path.name, "series": data["series"], "concepts": len(data["concepts"])})
    failures.extend(f"ensemble du dossier : {failure}" for failure in cross_taxonomy_failures(corpus))
    if failures:
        _fail("taxonomies invalides -- " + " | ".join(failures))
    return results


def _concept_uri(concept_id: str) -> URIRef:
    return URIRef(BASE + "concept/" + concept_id)


def _notebook_uri(repository_path: str) -> URIRef:
    """Nœud d'un carnet : le même que dans l'export du catalogue."""
    return URIRef(BASE + "notebook/" + quote(repository_path.removeprefix(NOTEBOOKS_ROOT), safe=""))


def build_graph(data: dict, taxonomy: str | None = None, graph: Graph | None = None) -> Graph:
    """Construit un graphe SKOS/OWL ; les identifiants restent indépendants des chemins.

    `taxonomy` est le nom du fichier sans extension : s'il est donné, concepts
    et carnets portent `rdfs:isDefinedBy` vers leur taxonomie. `graph` permet
    de réunir plusieurs taxonomies dans un même graphe ; un prérequis ou un
    alignement vers une autre taxonomie y retrouve alors le concept visé.
    """
    if graph is None:
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
    graph.add((VOCAB.Taxonomy, RDF.type, OWL.Class))
    graph.add((VOCAB.cellId, RDF.type, OWL.DatatypeProperty))
    graph.add((VOCAB.cellId, RDFS.domain, VOCAB.CellCitation))
    graph.add((VOCAB.path, RDF.type, OWL.DatatypeProperty))
    graph.add((VOCAB.decimalPath, RDF.type, OWL.DatatypeProperty))
    graph.add((VOCAB.depth, RDF.type, OWL.DatatypeProperty))

    taxonomy_uri = None
    if taxonomy is not None:
        taxonomy_uri = URIRef(BASE + "taxonomy/" + quote(taxonomy, safe=""))
        graph.add((taxonomy_uri, RDF.type, VOCAB.Taxonomy))
        graph.add((taxonomy_uri, RDFS.label, Literal(taxonomy)))

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
            subject = _notebook_uri(node["repository_path"])
            graph.add((subject, RDF.type, VOCAB.Notebook))
            graph.add((subject, RDFS.label, Literal(node["label_fr"], lang="fr")))
            graph.add((subject, DCTERMS.identifier,
                       Literal(node["repository_path"].removeprefix(NOTEBOOKS_ROOT))))
            graph.add((subject, VOCAB.inSeries, series_uri))
            if taxonomy_uri is not None:
                graph.add((subject, RDFS.isDefinedBy, taxonomy_uri))
        graph.add((subject, VOCAB.decimalPath, Literal(node["decimal_path"])))
        graph.add((subject, VOCAB.depth, Literal(node["depth"], datatype=XSD.integer)))

    scheme = URIRef(BASE + "scheme/" + data["series"].lower())
    graph.add((scheme, RDF.type, SKOS.ConceptScheme))
    graph.add((scheme, SKOS.prefLabel, Literal(data["series"], lang="fr")))
    concepts_by_decimal = {concept["decimal_path"]: concept for concept in data["concepts"]}

    for concept in data["concepts"]:
        uri = _concept_uri(concept["id"])
        graph.add((uri, RDF.type, SKOS.Concept))
        graph.add((uri, RDF.type, VOCAB.CurriculumConcept))
        graph.add((uri, SKOS.inScheme, scheme))
        if taxonomy_uri is not None:
            graph.add((uri, RDFS.isDefinedBy, taxonomy_uri))
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
            graph.add((uri, SKOS.broader, _concept_uri(parent["id"])))
        else:
            graph.add((scheme, SKOS.hasTopConcept, uri))
        # Prérequis et alignements peuvent viser le concept d'une autre
        # taxonomie : l'URI se calcule de l'identifiant, sans table locale.
        for prerequisite in concept["prerequisites"]:
            graph.add((uri, VOCAB.requiresConcept, _concept_uri(prerequisite)))
        for target, kind in survey.matches_of(concept):
            graph.add((uri, MATCH_PREDICATES[kind], _concept_uri(target)))
        for citation in concept["citations"]:
            notebook_uri = URIRef(BLOB_PREFIX + citation["notebook"])
            graph.add((uri, DCTERMS.source, notebook_uri))
            # Lien carnet -> concept, sur le nœud du carnet : c'est par lui
            # qu'un concept cité par deux séries se lit dans le graphe.
            graph.add((_notebook_uri(citation["notebook"]), VOCAB.concept, uri))
            citation_uri = BNode()
            graph.add((uri, VOCAB.hasCellCitation, citation_uri))
            graph.add((citation_uri, RDF.type, VOCAB.CellCitation))
            graph.add((citation_uri, DCTERMS.source, notebook_uri))
            graph.add((citation_uri, VOCAB.cellId, Literal(citation["cell_id"])))
    return graph


def _write_graph(graph: Graph, skos_output: Path, owl_output: Path) -> None:
    skos_output.parent.mkdir(parents=True, exist_ok=True)
    owl_output.parent.mkdir(parents=True, exist_ok=True)
    skos_output.write_bytes(graph.serialize(format="turtle", encoding="utf-8"))
    owl_output.write_bytes(graph.serialize(format="xml", encoding="utf-8"))
    print(f"SKOS : {skos_output}")
    print(f"OWL : {owl_output}")


def generate(data_path: Path, skos_output: Path, owl_output: Path, repo_root: Path = REPO_ROOT) -> int:
    data = load_taxonomy(data_path, repo_root)
    graph = build_graph(data, data_path.stem)
    print(f"Taxonomie valide : {len(data['concepts'])} concepts, {len(graph)} triples")
    _write_graph(graph, skos_output, owl_output)
    return 0


def generate_all(skos_output: Path, owl_output: Path, repo_root: Path = REPO_ROOT) -> list[dict]:
    """Valide tout le dossier puis écrit un seul graphe qui réunit ses taxonomies."""
    results = validate_all(repo_root)
    graph = None
    for name, data in load_corpus(repo_root).items():
        graph = build_graph(data, name, graph)
    print(f"Export réuni : {len(results)} taxonomies, "
          f"{sum(entry['concepts'] for entry in results)} concepts, {len(graph)} triples")
    _write_graph(graph, skos_output, owl_output)
    return results


def survey_report(repo_root: Path = REPO_ROOT, density: bool = True, bridges: bool = True) -> dict:
    """Relevé demandé sur toutes les taxonomies lisibles du dossier (mesure, sans validation)."""
    corpus = load_corpus(repo_root)
    if not corpus:
        _fail(f"aucune taxonomie lisible dans {repo_root / TAXONOMY_DIR}")
    report: dict = {}
    if density:
        report["density"] = survey.density(corpus)
    if bridges:
        report["bridges"] = survey.bridges(corpus)
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=DEFAULT_DATA)
    parser.add_argument("--all", action="store_true",
                        help="valider toutes les taxonomies du dossier ; avec --skos-output et --owl-output, "
                             "écrire leur export réuni")
    parser.add_argument("--density", action="store_true",
                        help="relever la densité de toutes les taxonomies du dossier")
    parser.add_argument("--bridges", action="store_true",
                        help="relever les ponts entre les taxonomies du dossier")
    parser.add_argument("--json", action="store_true", help="écrire le relevé en JSON")
    parser.add_argument("--skos-output", type=Path)
    parser.add_argument("--owl-output", type=Path)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    args = parser.parse_args(argv)
    survey_mode = args.density or args.bridges
    export = args.skos_output is not None and args.owl_output is not None
    if (args.skos_output is None) != (args.owl_output is None):
        parser.error("--skos-output et --owl-output vont ensemble")
    if not (args.all or survey_mode or export):
        parser.error("--skos-output et --owl-output sont requis (sauf avec --all, --density ou --bridges)")
    if args.json and not survey_mode:
        parser.error("--json accompagne --density ou --bridges")
    reconfigure = getattr(sys.stdout, "reconfigure", None)
    if callable(reconfigure):
        reconfigure(encoding="utf-8")  # libellés hors de la page de code d'une console Windows
    try:
        # En JSON, la sortie standard ne porte que le relevé.
        with contextlib.redirect_stdout(sys.stderr) if args.json else contextlib.nullcontext():
            if args.all:
                results = (generate_all(args.skos_output, args.owl_output, args.repo_root)
                           if export else validate_all(args.repo_root))
                for entry in results:
                    print(f"Taxonomie valide : {entry['series']} ({entry['file']}) -- {entry['concepts']} concepts")
            elif export:
                generate(args.data, args.skos_output, args.owl_output, args.repo_root)
        if survey_mode:
            report = survey_report(args.repo_root, args.density, args.bridges)
            if args.json:
                print(json.dumps(report, ensure_ascii=False, indent=2))
            else:
                renderers = {"density": survey.render_density, "bridges": survey.render_bridges}
                print("\n\n".join(renderers[name](part) for name, part in report.items()))
        return 0
    except (OSError, json.JSONDecodeError, ValueError) as error:
        print(f"Erreur de taxonomie : {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
