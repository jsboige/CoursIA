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


def test_nested_subseries_keep_their_parent_link():
    """Une sous-série à plusieurs niveaux est émise comme une chaîne (#24994)."""
    entries = [{
        "path": "CaseStudies/Diagnostic-Medical/solution/Diagnostic-Medical.ipynb",
        "title": "Diagnostic Medical", "serie": "CaseStudies",
        "sous_serie": "Diagnostic-Medical",
        "sous_serie_levels": ["Diagnostic-Medical", "solution"],
    }]
    graph = build_graph(entries)
    subseries = set(graph.subjects(RDF.type, VOCAB.Subseries))
    assert len(subseries) == 2

    parent = next(graph.objects(None, VOCAB.partOfSubseries))
    child = next(graph.subjects(VOCAB.partOfSubseries))
    assert (child, VOCAB.partOfSubseries, parent) in graph, "l'enfant pointe son parent"
    assert (parent, RDF.type, VOCAB.Subseries) in graph
    assert (child, RDF.type, VOCAB.Subseries) in graph
    series_uri = next(graph.objects(parent, VOCAB.partOfSeries))
    assert str(series_uri).endswith("/serie/CaseStudies")
    assert (child, VOCAB.partOfSubseries, parent) in graph

    notebook = next(graph.subjects(RDF.type, VOCAB.Notebook))
    deepest = next(graph.objects(notebook, VOCAB.inSubseries))
    assert deepest == child, "le carnet pointe la sous-série la plus profonde"
    assert str(next(graph.objects(child, VOCAB.subseriesPath))) == "Diagnostic-Medical/solution"


def test_flat_subseries_keeps_its_historical_uri():
    """Une entrée à un seul niveau garde l'URI d'avant #24994."""
    entries = [{
        "path": "SymbolicAI/SemanticWeb/SW-8-Python-SHACL.ipynb",
        "title": "SHACL", "serie": "SymbolicAI",
        "sous_serie": "SemanticWeb", "sous_serie_levels": ["SemanticWeb"],
    }]
    graph = build_graph(entries)
    subseries = next(graph.subjects(RDF.type, VOCAB.Subseries))
    assert str(subseries).endswith("/sous-serie/SymbolicAI%2FSemanticWeb")
    assert (subseries, VOCAB.partOfSeries, None) in graph


def test_shacl_accepts_a_nested_subseries_chain():
    entries = [{
        "path": "X/Y.ipynb", "title": "Y", "serie": "X",
        "sous_serie": "A", "sous_serie_levels": ["A", "B", "C"],
    }]
    graph = build_graph(entries)
    conforms, report = validate_graph(graph)
    assert conforms, report


def test_subseries_without_any_level_stays_absent():
    graph = build_graph([{"path": "A.ipynb", "title": "A", "serie": "A"}])
    assert not list(graph.subjects(RDF.type, VOCAB.Subseries))
