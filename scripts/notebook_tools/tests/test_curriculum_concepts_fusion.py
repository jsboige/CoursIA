"""Fusion de la couche concepts SKOS dans le TTL du cursus (#27635)."""

import json
import sys
from pathlib import Path

import pytest
from rdflib import RDF, Graph
from rdflib.namespace import DCTERMS, SKOS

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import curriculum_taxonomy
from generate_curriculum_rdf import (
    VOCAB,
    build_concepts_layer,
    build_graph,
    generate,
    strip_tree_nodes,
    validate_graph,
)
from query_curriculum import (
    concepts_by_series,
    concepts_for_notebook,
    notebooks_for_concept,
    main,
)

REPO_ROOT = curriculum_taxonomy.REPO_ROOT
TAXONOMY_DIR = REPO_ROOT / curriculum_taxonomy.TAXONOMY_DIR
COMPRESSION_NOTEBOOK = "Compression/Compression-01-ShannonFano-Prefixe-Python.ipynb"


@pytest.fixture(scope="module")
def concepts_layer():
    graph, merged, skipped = build_concepts_layer(TAXONOMY_DIR, REPO_ROOT)
    assert not skipped, skipped
    return graph, merged


@pytest.fixture(scope="module")
def served_graph(concepts_layer):
    catalog = [
        {"path": COMPRESSION_NOTEBOOK, "title": "Compression-01", "serie": "Compression"},
        {"path": "GenAI/LLM/API.ipynb", "title": "API", "serie": "GenAI"},
    ]
    graph = build_graph(catalog)
    graph += concepts_layer[0]
    return graph


def test_strip_tree_nodes_keeps_only_the_concept_layer():
    data = curriculum_taxonomy.load_taxonomy(TAXONOMY_DIR / "compression.json", REPO_ROOT)
    full = curriculum_taxonomy.build_graph(data)
    stripped = strip_tree_nodes(full)
    for node_type in (VOCAB.Notebook, VOCAB.Series, VOCAB.Subseries):
        assert not list(stripped.subjects(RDF.type, node_type))
    assert len(list(stripped.subjects(RDF.type, SKOS.Concept))) == 18
    assert list(stripped.subjects(RDF.type, SKOS.ConceptScheme))
    assert list(stripped.subjects(RDF.type, VOCAB.CellCitation))
    assert len(stripped) < len(full)


def test_build_concepts_layer_merges_valid_and_skips_invalid(tmp_path):
    (tmp_path / "compression.json").write_bytes(
        (TAXONOMY_DIR / "compression.json").read_bytes()
    )
    (tmp_path / "broken.json").write_text(
        json.dumps({"series": "Broken", "concepts": []}), encoding="utf-8"
    )
    graph, merged, skipped = build_concepts_layer(tmp_path, REPO_ROOT)
    assert [entry["series"] for entry in merged] == ["Compression"]
    assert [entry["file"] for entry in skipped] == ["broken.json"]
    assert "schema_version" in skipped[0]["reason"]
    assert len(list(graph.subjects(RDF.type, SKOS.Concept))) == 18


def test_build_concepts_layer_without_directory_is_empty(tmp_path):
    graph, merged, skipped = build_concepts_layer(tmp_path / "absent", REPO_ROOT)
    assert len(graph) == 0
    assert merged == [] and skipped == []


def test_served_graph_conforms_to_shapes(served_graph):
    conforms, report = validate_graph(served_graph)
    assert conforms, report


def test_shapes_reject_concept_without_scheme(served_graph):
    graph = Graph()
    graph += served_graph
    concept = next(graph.subjects(RDF.type, SKOS.Concept))
    graph.remove((concept, SKOS.inScheme, None))
    conforms, report = validate_graph(graph)
    assert not conforms
    assert "inScheme" in report


def test_generate_end_to_end_counts_every_declared_concept(tmp_path, capsys):
    from generate_curriculum_rdf import DEFAULT_SHAPES

    catalog_path = tmp_path / "catalog.json"
    catalog_path.write_text(json.dumps([
        {"path": COMPRESSION_NOTEBOOK, "title": "Compression-01", "serie": "Compression"},
    ]), encoding="utf-8")
    output = tmp_path / "curriculum.ttl"
    assert generate(catalog_path, output, DEFAULT_SHAPES, None, TAXONOMY_DIR) == 0
    expected = sum(
        len(json.loads(path.read_text(encoding="utf-8"))["concepts"])
        for path in sorted(TAXONOMY_DIR.glob("*.json"))
        if path.name != curriculum_taxonomy.SCHEMA_FILENAME
    )
    graph = Graph()
    graph.parse(output, format="turtle")
    assert len(list(graph.subjects(RDF.type, SKOS.Concept))) == expected
    assert "concepts" in capsys.readouterr().out


def test_query_concepts_by_series(served_graph):
    lines = concepts_by_series(served_graph, "compression")
    assert len(lines) == 18
    assert all("/concept/" in line for line in lines)


def test_query_concepts_for_notebook_lists_citing_cells(served_graph):
    lines = concepts_for_notebook(served_graph, COMPRESSION_NOTEBOOK)
    assert lines
    assert all("\t" in line for line in lines)
    assert any(line.split("\t")[-1] for line in lines)


def test_query_notebooks_for_concept_accepts_uuid(served_graph):
    concept = next(served_graph.subjects(RDF.type, SKOS.Concept))
    identifier = str(served_graph.value(concept, DCTERMS.identifier))
    lines = notebooks_for_concept(served_graph, identifier)
    assert lines
    with pytest.raises(KeyError):
        notebooks_for_concept(served_graph, "concept-inexistant")


def test_cli_concepts_readings(tmp_path, capsys, served_graph):
    graph_path = tmp_path / "served.ttl"
    served_graph.serialize(graph_path, format="turtle")

    assert main(["--graph", str(graph_path), "concepts", "--series", "Compression"]) == 0
    assert "concept/" in capsys.readouterr().out

    assert main([
        "--graph", str(graph_path), "concepts", "--notebook", COMPRESSION_NOTEBOOK,
    ]) == 0
    assert capsys.readouterr().out.strip()

    concept = next(served_graph.subjects(RDF.type, SKOS.Concept))
    identifier = str(served_graph.value(concept, DCTERMS.identifier))
    assert main(["--graph", str(graph_path), "concepts", "--concept", identifier]) == 0
    assert capsys.readouterr().out.strip()


def test_cli_rejects_two_readings_at_once(tmp_path, served_graph):
    graph_path = tmp_path / "served.ttl"
    served_graph.serialize(graph_path, format="turtle")
    with pytest.raises(SystemExit):
        main([
            "--graph", str(graph_path), "concepts",
            "--series", "Compression", "--notebook", COMPRESSION_NOTEBOOK,
        ])


def test_gateway_concepts_action(served_graph):
    from curriculum_gateway import service

    ok = service.handle(served_graph, {"action": "concepts", "series": "Compression"})
    assert ok["status"] == "ok" and len(ok["results"]) == 18
    by_notebook = service.handle(
        served_graph, {"action": "concepts", "notebook": COMPRESSION_NOTEBOOK}
    )
    assert by_notebook["status"] == "ok" and by_notebook["results"]
    ambiguous = service.handle(
        served_graph,
        {"action": "concepts", "series": "Compression", "notebook": COMPRESSION_NOTEBOOK},
    )
    assert ambiguous["status"] == "invalid"
    unknown = service.handle(
        served_graph, {"action": "concepts", "concept": "concept-inexistant"}
    )
    assert unknown["status"] == "not_found"