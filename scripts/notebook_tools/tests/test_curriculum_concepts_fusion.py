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
    build_graph,
    build_taxonomy_graph,
    generate,
    validate_graph,
)
from query_curriculum import (
    concepts_by_series,
    concepts_of_notebook,
    notebooks_for_concept,
    main,
)

REPO_ROOT = curriculum_taxonomy.REPO_ROOT
TAXONOMY_DIR = REPO_ROOT / curriculum_taxonomy.TAXONOMY_DIR
COMPRESSION_NOTEBOOK = "InformationCalcul/Compression/Compression-01-ShannonFano-Prefixe-Python.ipynb"


def compression_concept_count() -> int:
    """Concepts déclarés par la taxonomie Compression, lu dans la donnée.

    La tranche T4 de #26646 a densifié la série entière (21 carnets) : le
    compte ne s'épingle plus à la main, il se lit dans le fichier que l'export
    doit servir en entier.
    """
    data = curriculum_taxonomy.load_taxonomy(TAXONOMY_DIR / "compression.json", REPO_ROOT)
    return len(data["concepts"])


@pytest.fixture(scope="module")
def concepts_layer():
    return build_taxonomy_graph(TAXONOMY_DIR)


@pytest.fixture(scope="module")
def served_graph(concepts_layer):
    catalog = [
        {"path": COMPRESSION_NOTEBOOK, "title": "Compression-01", "serie": "Compression"},
        {"path": "GenAI/LLM/API.ipynb", "title": "API", "serie": "GenAI"},
    ]
    graph = build_graph(catalog)
    graph += concepts_layer
    return graph


def test_concepts_only_graph_keeps_no_tree_nodes():
    data = curriculum_taxonomy.load_taxonomy(TAXONOMY_DIR / "compression.json", REPO_ROOT)
    full = curriculum_taxonomy.build_graph(data)
    stripped = curriculum_taxonomy.build_graph(data, emit_structure=False)
    for node_type in (VOCAB.Notebook, VOCAB.Series, VOCAB.Subseries):
        assert not list(stripped.subjects(RDF.type, node_type))
    assert len(list(stripped.subjects(RDF.type, SKOS.Concept))) == len(data["concepts"])
    assert list(stripped.subjects(RDF.type, SKOS.ConceptScheme))
    assert list(stripped.subjects(RDF.type, VOCAB.CellCitation))
    assert len(stripped) < len(full)


def test_build_taxonomy_graph_fuses_series_concepts(concepts_layer):
    # La fusion (--taxonomy-dir, #25001) porte tous les concepts de compression
    # parmi ceux de toutes les séries déclarées, sans nœud d'arbre dupliqué.
    for node_type in (VOCAB.Notebook, VOCAB.Series, VOCAB.Subseries):
        assert not list(concepts_layer.subjects(RDF.type, node_type))
    schemes = {
        str(s) for s in concepts_layer.subjects(RDF.type, SKOS.ConceptScheme)
    }
    assert any(s.endswith("compression") for s in schemes)
    compression_concepts = [
        c for c in concepts_layer.subjects(RDF.type, SKOS.Concept)
        if any(str(sch).endswith("compression")
               for sch in concepts_layer.objects(c, SKOS.inScheme))
    ]
    assert len(compression_concepts) == compression_concept_count()


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
    assert len(lines) == compression_concept_count()
    assert all("/concept/" in line for line in lines)


def test_query_concepts_of_notebook_lists_citing_cells(served_graph):
    lines = concepts_of_notebook(served_graph, COMPRESSION_NOTEBOOK)
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
    assert ok["status"] == "ok" and len(ok["results"]) == compression_concept_count()
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