import copy
import json
import sys
from pathlib import Path

from rdflib import Graph, Literal, RDF, URIRef
from rdflib.namespace import DCTERMS, OWL, SKOS

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from curriculum_taxonomy import (  # noqa: E402
    DEFAULT_DATA,
    VOCAB,
    build_graph,
    generate,
    load_taxonomy,
    validate_taxonomy,
)


def test_compression_slice_cites_real_cells_and_covers_every_root_notebook():
    data = load_taxonomy()
    assert len(data["notebooks"]) == 7
    assert len(data["concepts"]) >= 15
    assert data["hierarchy"] == ["series", "subseries", "notebook", "example", "exercise"]
    cited = {citation["notebook"] for concept in data["concepts"] for citation in concept["citations"]}
    assert cited == set(data["notebooks"])


def test_graph_exports_bilingual_skos_concepts_prerequisites_and_live_notebook_links():
    data = load_taxonomy()
    graph = build_graph(data)
    assert (None, RDF.type, OWL.Ontology) in graph
    concepts = set(graph.subjects(RDF.type, SKOS.Concept))
    assert len(concepts) == len(data["concepts"])
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
