import copy
import json
import sys
from pathlib import Path

from rdflib import Graph, Literal, RDF, URIRef
from rdflib.namespace import DCTERMS, OWL, SKOS

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from curriculum_taxonomy import (  # noqa: E402
    DEFAULT_DATA,
    SCHEMA_FILENAME,
    VOCAB,
    build_graph,
    discover_taxonomies,
    generate,
    load_taxonomy,
    validate_all,
    validate_taxonomy,
)


def test_every_taxonomy_json_in_the_folder_is_valid_and_discovered():
    """Couverture structurelle : un JSON de série ajouté au dossier entre automatiquement (suivi #25441)."""
    directory = DEFAULT_DATA.parent
    expected = sorted(path for path in directory.glob("*.json") if path.name != SCHEMA_FILENAME)
    discovered = discover_taxonomies()
    assert [path.name for path in discovered] == [path.name for path in expected]
    assert len(discovered) >= 5
    results = validate_all()
    assert {entry["file"] for entry in results} == {path.name for path in expected}
    assert all(entry["concepts"] > 0 for entry in results)


def test_validate_all_names_the_failing_file(tmp_path):
    taxonomy_dir = tmp_path / "docs" / "curriculum" / "taxonomy"
    taxonomy_dir.mkdir(parents=True)
    (taxonomy_dir / SCHEMA_FILENAME).write_text("{}", encoding="utf-8")
    (taxonomy_dir / "serie-a.json").write_text(json.dumps({"schema_version": 2}), encoding="utf-8")
    try:
        validate_all(tmp_path)
    except ValueError as error:
        assert "serie-a.json" in str(error)
        assert "schema_version" in str(error)
    else:
        raise AssertionError("une taxonomie invalide doit être nommée par validate_all")


def test_compression_slice_cites_real_cells_and_covers_every_root_notebook():
    data = load_taxonomy()
    assert len(data["notebooks"]) == 7
    assert len(data["concepts"]) >= 15
    assert data["hierarchy"] == ["series", "subseries", "notebook", "example", "exercise"]
    assert [node["level"] for node in data["notebook_tree"]].count("series") == 1
    assert [node["level"] for node in data["notebook_tree"]].count("notebook") == 7
    cited = {citation["notebook"] for concept in data["concepts"] for citation in concept["citations"]}
    assert cited == set(data["notebooks"])


def test_graph_exports_bilingual_skos_concepts_prerequisites_and_live_notebook_links():
    data = load_taxonomy()
    graph = build_graph(data)
    assert (None, RDF.type, OWL.Ontology) in graph
    concepts = set(graph.subjects(RDF.type, SKOS.Concept))
    assert len(concepts) == len(data["concepts"])
    notebooks = set(graph.subjects(RDF.type, VOCAB.Notebook))
    assert len(notebooks) == 7
    assert all((notebook, VOCAB.inSeries, None) in graph for notebook in notebooks)
    assert any(graph.objects(concept, SKOS.prefLabel) for concept in concepts)
    assert any(graph.objects(concept, VOCAB.requiresConcept) for concept in concepts)
    source_links = set(graph.objects(None, DCTERMS.source))
    assert len(source_links) == len(data["notebooks"])
    for link in source_links:
        relative = URIRef(str(link).replace("https://github.com/jsboige/CoursIA/blob/main/", "", 1))
        assert (Path(__file__).resolve().parents[3] / str(relative)).is_file()
    for concept in data["concepts"]:
        subject = URIRef("https://github.com/jsboige/CoursIA/cursus/concept/" + concept["id"])
        for citation in concept["citations"]:
            source = URIRef("https://github.com/jsboige/CoursIA/blob/main/" + citation["notebook"])
            assert (subject, DCTERMS.source, source) in graph
            matches = {
                node for node in graph.objects(subject, VOCAB.hasCellCitation)
                if (node, DCTERMS.source, source) in graph
                and (node, VOCAB.cellId, Literal(citation["cell_id"])) in graph
            }
            assert len(matches) == 1


def test_unknown_prerequisite_is_rejected():
    data = copy.deepcopy(load_taxonomy())
    data["concepts"][0]["prerequisites"] = ["e0f54e86-45c7-4d0f-b018-0a0149a88d43"]
    try:
        validate_taxonomy(data)
    except ValueError as error:
        assert "prérequis inconnu" in str(error)
    else:
        raise AssertionError("un prérequis inconnu doit être refusé")


def test_prerequisite_cycle_is_rejected():
    data = copy.deepcopy(load_taxonomy())
    first, second = data["concepts"][:2]
    first["prerequisites"] = [second["id"]]
    second["prerequisites"] = [first["id"]]
    try:
        validate_taxonomy(data)
    except ValueError as error:
        assert "cycle de prérequis" in str(error)
    else:
        raise AssertionError("un cycle de prérequis doit être refusé")


def test_nonexistent_cell_citation_is_rejected():
    data = copy.deepcopy(load_taxonomy())
    data["concepts"][0]["citations"][0]["cell_id"] = "cellule-inventee"
    try:
        validate_taxonomy(data)
    except ValueError as error:
        assert "cellule citée introuvable" in str(error)
    else:
        raise AssertionError("une citation de cellule inexistante doit être refusée")


def test_uppercase_path_segment_is_rejected():
    data = copy.deepcopy(load_taxonomy())
    parts = data["concepts"][0]["path"].split("/")
    parts[-1] = "SujetMajuscule"
    data["concepts"][0]["path"] = "/".join(parts)
    try:
        validate_taxonomy(data)
    except ValueError as error:
        assert "segment de path en majuscules" in str(error)
    else:
        raise AssertionError("un segment de path en majuscules doit être refusé")


def test_export_writes_parseable_skos_and_owl(tmp_path):
    skos_path = tmp_path / "compression.ttl"
    owl_path = tmp_path / "compression.owl"
    second_skos_path = tmp_path / "compression-second.ttl"
    second_owl_path = tmp_path / "compression-second.owl"
    assert generate(DEFAULT_DATA, skos_path, owl_path) == 0
    assert generate(DEFAULT_DATA, second_skos_path, second_owl_path) == 0
    skos_graph = Graph().parse(skos_path, format="turtle")
    owl_graph = Graph().parse(owl_path, format="xml")
    assert skos_graph.isomorphic(Graph().parse(second_skos_path, format="turtle"))
    assert owl_graph.isomorphic(Graph().parse(second_owl_path, format="xml"))
    assert (None, RDF.type, SKOS.Concept) in skos_graph
    assert (None, RDF.type, OWL.Ontology) in owl_graph
