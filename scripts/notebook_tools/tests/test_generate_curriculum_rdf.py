import sys
from pathlib import Path

from rdflib import RDF

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from generate_curriculum_rdf import VOCAB, build_graph, validate_graph


def test_catalogue_fixture_builds_and_passes_shacl():
    entries = [
        {"path": "SymbolicAI/SemanticWeb/SW-11-Python-KnowledgeGraphs.ipynb",
         "title": "Knowledge Graphs", "serie": "SymbolicAI",
         "sous_serie": "SemanticWeb"},
        {"path": "SymbolicAI/SemanticWeb/SW-8-Python-SHACL.ipynb",
         "title": "SHACL", "serie": "SymbolicAI", "sous_serie": "SemanticWeb",
         "concept": "SHACL", "qualification": "BETA"},
    ]
    graph = build_graph(entries)
    notebooks = list(graph.subjects(RDF.type, VOCAB.Notebook))
    assert len(notebooks) == 2
    assert (notebooks[0], VOCAB.inSeries, None) in graph
    assert any(graph.objects(subject, VOCAB.inSubseries) for subject in notebooks)
    assert any(graph.objects(subject, VOCAB.concept) for subject in notebooks)
    conforms, report = validate_graph(graph)
    assert conforms, report


def test_shacl_rejects_notebook_without_series():
    graph = build_graph([{"path": "A.ipynb", "title": "A", "serie": "A"}])
    notebook = next(graph.subjects(RDF.type, VOCAB.Notebook))
    graph.remove((notebook, VOCAB.inSeries, None))
    conforms, report = validate_graph(graph)
    assert not conforms
    assert "inSeries" in report


def test_required_catalogue_fields_are_not_fabricated():
    try:
        build_graph([{"path": "A.ipynb", "serie": "A"}])
    except ValueError as error:
        assert "title" in str(error)
    else:
        raise AssertionError("une entrée invalide doit être refusée")
