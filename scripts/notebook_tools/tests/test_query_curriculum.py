import sys
from pathlib import Path

import pytest
from rdflib import BNode, Graph, Literal, RDF, URIRef
from rdflib.namespace import DCTERMS, RDFS, SKOS

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from generate_curriculum_rdf import VOCAB, build_graph
from query_curriculum import (
    find_notebook,
    list_notebooks,
    main,
    notebooks_by_resource,
    notebooks_requiring,
    path_for,
    validate_prerequisite_acyclicity,
)


@pytest.fixture
def curriculum_graph():
    return build_graph([
        {
            "path": "SymbolicAI/SemanticWeb/SW-11-KnowledgeGraphs.ipynb",
            "title": "Knowledge graphs", "serie": "SymbolicAI",
            "sous_serie": "SemanticWeb", "requires_api": False,
            "requires_gpu": False, "requires_cloud": False, "requires_wsl": False,
            "duree_estimee": "45min", "status": "READY",
        },
        {
            "path": "GenAI/LLM/API.ipynb", "title": "API des modèles",
            "serie": "GenAI", "sous_serie": "LLM", "requires_api": True,
            "requires_gpu": False, "requires_cloud": True, "requires_wsl": False,
        },
    ])


def test_query_filters_use_exported_graph(curriculum_graph):
    api = notebooks_requiring(curriculum_graph, "api")
    assert len(api) == 1
    assert "GenAI/LLM/API.ipynb" in api[0]
    no_api = notebooks_by_resource(curriculum_graph, "api", "not-required")
    assert len(no_api) == 1
    assert "SW-11-KnowledgeGraphs.ipynb" in no_api[0]
    assert list_notebooks(curriculum_graph, series_filter="symbolicai") == [
        "Knowledge graphs\tSymbolicAI/SemanticWeb/SW-11-KnowledgeGraphs.ipynb"
    ]
    assert path_for(curriculum_graph, "SymbolicAI/SemanticWeb/SW-11-KnowledgeGraphs.ipynb") == [
        "SymbolicAI", "SemanticWeb", "Knowledge graphs"
    ]


def test_unknown_notebook_uri_is_rejected(curriculum_graph):
    with pytest.raises(KeyError, match="absent.ipynb"):
        find_notebook(curriculum_graph, "absent.ipynb")


def test_cli_reports_unknown_notebook_path(tmp_path, curriculum_graph, capsys):
    graph_path = tmp_path / "catalogue.ttl"
    curriculum_graph.serialize(graph_path, format="turtle")

    result = main(["--graph", str(graph_path), "show", "absent.ipynb"])
    assert result == 2
    assert "Carnet introuvable" in capsys.readouterr().err


def test_prerequisite_cycle_is_rejected():
    graph = Graph()
    first = URIRef("https://example.test/notebook/first")
    second = URIRef("https://example.test/notebook/second")
    graph.add((first, RDF.type, VOCAB.Notebook))
    graph.add((second, RDF.type, VOCAB.Notebook))
    graph.add((first, VOCAB.prerequisite, second))
    graph.add((second, VOCAB.prerequisite, first))
    with pytest.raises(ValueError, match="cycle de prérequis"):
        validate_prerequisite_acyclicity(graph)


def test_cli_refuses_graph_with_prerequisite_cycle(tmp_path, capsys):
    graph = Graph()
    first = URIRef("https://example.test/notebook/first")
    second = URIRef("https://example.test/notebook/second")
    graph.add((first, VOCAB.prerequisite, second))
    graph.add((second, VOCAB.prerequisite, first))
    graph_path = tmp_path / "cycle.ttl"
    graph.serialize(graph_path, format="turtle")

    result = main(["--graph", str(graph_path), "series"])
    assert result == 2
    assert "cycle de prérequis" in capsys.readouterr().err


def test_acyclic_prerequisite_chain_is_accepted():
    graph = Graph()
    first = URIRef("https://example.test/notebook/first")
    second = URIRef("https://example.test/notebook/second")
    third = URIRef("https://example.test/notebook/third")
    graph.add((first, VOCAB.prerequisite, second))
    graph.add((second, VOCAB.prerequisite, third))
    validate_prerequisite_acyclicity(graph)


def test_resource_query_rejects_untyped_boolean():
    graph = Graph()
    notebook = URIRef("https://example.test/notebook/api")
    graph.add((notebook, RDF.type, VOCAB.Notebook))
    graph.add((notebook, DCTERMS.identifier, Literal("api.ipynb")))
    graph.add((notebook, RDFS.label, Literal("API", lang="fr")))
    graph.add((notebook, VOCAB.requiresAPI, Literal("false")))
    with pytest.raises(ValueError, match="booléen RDF"):
        notebooks_requiring(graph, "api")


def test_real_catalogue_export_conforms_and_exposes_resource_fields(tmp_path):
    import json

    root = Path(__file__).resolve().parents[3]
    catalogue = json.loads((root / "COURSE_CATALOG.generated.json").read_text(encoding="utf-8"))
    graph = build_graph(catalogue)

    for field, predicate in (
        ("requires_api", VOCAB.requiresAPI),
        ("requires_gpu", VOCAB.requiresGPU),
        ("requires_cloud", VOCAB.requiresCloud),
        ("requires_wsl", VOCAB.requiresWSL),
    ):
        expected = sum(entry.get(field) is True for entry in catalogue)
        actual = sum(value.toPython() is True for value in graph.objects(None, predicate))
        assert actual == expected
    assert sum(1 for _ in graph.objects(None, VOCAB.estimatedDuration)) == sum(
        bool(entry.get("duree_estimee")) for entry in catalogue
    )
    assert sum(1 for _ in graph.objects(None, VOCAB.status)) == sum(
        bool(entry.get("status")) for entry in catalogue
    )


def test_show_prerequisites_reports_missing_metadata(curriculum_graph):
    from query_curriculum import prerequisites_for

    path = "SymbolicAI/SemanticWeb/SW-11-KnowledgeGraphs.ipynb"
    assert prerequisites_for(curriculum_graph, path) == [
        "Prérequis non renseignés dans l'export."
    ]


def test_multiple_exports_are_merged_and_skos_blank_node_labels_are_read(
    tmp_path, curriculum_graph, capsys
):
    first_path = tmp_path / "catalogue.ttl"
    second_path = tmp_path / "concepts.ttl"
    curriculum_graph.serialize(first_path, format="turtle")

    taxonomy = Graph()
    notebook = find_notebook(
        curriculum_graph,
        "SymbolicAI/SemanticWeb/SW-11-KnowledgeGraphs.ipynb",
    )
    concept = BNode("concept")
    taxonomy.add((notebook, VOCAB.concept, concept))
    taxonomy.add((concept, RDF.type, SKOS.Concept))
    taxonomy.add((concept, SKOS.prefLabel, Literal("Graphe de connaissances", lang="fr")))
    taxonomy.serialize(second_path, format="turtle")

    result = main([
        "--graph", str(first_path), "--graph", str(second_path),
        "concepts", "--query", "connaissances",
    ])
    output = capsys.readouterr().out
    assert result == 0
    assert "Graphe de connaissances" in output
    assert "SW-11-KnowledgeGraphs.ipynb" in output


def _hierarchy_graph(levels):
    return build_graph([{
        "path": "GenAI/LLM/RAG/Advanced/Demo.ipynb",
        "title": "Démo", "serie": "GenAI",
        "sous_serie": levels[-1] if levels else "",
        "sous_serie_levels": levels,
    }])


@pytest.mark.parametrize("levels", [[], ["LLM"], ["LLM", "RAG", "Advanced"]])
def test_path_uses_all_exported_subseries_in_order(levels):
    graph = _hierarchy_graph(levels)
    assert path_for(graph, "GenAI/LLM/RAG/Advanced/Demo.ipynb") == [
        "GenAI", *levels, "Démo"
    ]


def test_nested_path_and_show_through_turtle_cli(tmp_path, capsys):
    graph_path = tmp_path / "nested.ttl"
    _hierarchy_graph(["LLM", "RAG", "Advanced"]).serialize(graph_path, format="turtle")
    path = "GenAI/LLM/RAG/Advanced/Demo.ipynb"
    expected = "GenAI > LLM > RAG > Advanced > Démo"
    assert main(["--graph", str(graph_path), "path", path]) == 0
    assert capsys.readouterr().out.strip() == expected
    assert main(["--graph", str(graph_path), "show", path]) == 0
    assert "Parcours : " + expected in capsys.readouterr().out


@pytest.mark.parametrize("cycle_kind", ["self", "ancestor"])
def test_subseries_cycle_is_rejected_in_reader_and_cli(cycle_kind, tmp_path, capsys):
    graph = _hierarchy_graph(["LLM", "RAG", "Advanced"])
    path = "GenAI/LLM/RAG/Advanced/Demo.ipynb"
    notebook = find_notebook(graph, path)
    leaf = graph.value(notebook, VOCAB.inSubseries)
    root = graph.value(graph.value(leaf, VOCAB.partOfSubseries), VOCAB.partOfSubseries)
    if cycle_kind == "self":
        graph.remove((leaf, VOCAB.partOfSubseries, None))
        graph.add((leaf, VOCAB.partOfSubseries, leaf))
    else:
        graph.add((root, VOCAB.partOfSubseries, leaf))
    with pytest.raises(ValueError, match="cycle de sous-séries"):
        path_for(graph, path)
    graph_path = tmp_path / "cycle.ttl"
    graph.serialize(graph_path, format="turtle")
    assert main(["--graph", str(graph_path), "path", path]) == 2
    assert "cycle de sous-séries" in capsys.readouterr().err


@pytest.mark.parametrize("relation", ["inSubseries", "partOfSubseries"])
def test_multiple_subseries_parents_are_rejected(relation, tmp_path, capsys):
    graph = _hierarchy_graph(["LLM", "RAG", "Advanced"])
    path = "GenAI/LLM/RAG/Advanced/Demo.ipynb"
    notebook = find_notebook(graph, path)
    leaf = graph.value(notebook, VOCAB.inSubseries)
    subject = notebook if relation == "inSubseries" else leaf
    graph.add((subject, VOCAB[relation], URIRef("https://example.test/other")))
    with pytest.raises(ValueError, match="plusieurs.*sous-série"):
        path_for(graph, path)
    graph_path = tmp_path / "ambiguous.ttl"
    graph.serialize(graph_path, format="turtle")
    assert main(["--graph", str(graph_path), "show", path]) == 2
    assert "plusieurs" in capsys.readouterr().err
