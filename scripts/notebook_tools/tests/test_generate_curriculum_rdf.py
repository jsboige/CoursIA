import sys
from pathlib import Path

from rdflib import DCTERMS, Literal, RDF, URIRef

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from generate_curriculum_rdf import (
    VOCAB,
    build_graph,
    build_interfaces_graph,
    build_taxonomy_graph,
    validate_graph,
)


def test_catalogue_fixture_builds_and_passes_shacl():
    entries = [
        {"path": "SymbolicAI/SemanticWeb/SW-11-Python-KnowledgeGraphs.ipynb",
         "title": "Knowledge Graphs", "serie": "SymbolicAI",
         "sous_serie": "SemanticWeb", "requires_api": False,
         "requires_gpu": True, "requires_cloud": False, "requires_wsl": False,
         "duree_estimee": "45 min", "status": "READY"},
        {"path": "SymbolicAI/SemanticWeb/SW-8-Python-SHACL.ipynb",
         "title": "SHACL", "serie": "SymbolicAI", "sous_serie": "SemanticWeb",
         "concept": "SHACL", "qualification": "BETA", "requires_api": True,
         "requires_gpu": False, "requires_cloud": False, "requires_wsl": False},
    ]
    graph = build_graph(entries)
    notebooks = list(graph.subjects(RDF.type, VOCAB.Notebook))
    assert len(notebooks) == 2
    assert (notebooks[0], VOCAB.inSeries, None) in graph
    assert any(graph.objects(subject, VOCAB.inSubseries) for subject in notebooks)
    assert any(graph.objects(subject, VOCAB.concept) for subject in notebooks)
    # Les propriétés doivent suivre chaque carnet exact, pas seulement conserver
    # les mêmes compteurs si leur attribution ou leur polarité dérive.
    api = URIRef("https://github.com/jsboige/CoursIA/cursus/notebook/SymbolicAI%2FSemanticWeb%2FSW-8-Python-SHACL.ipynb")
    no_api = URIRef("https://github.com/jsboige/CoursIA/cursus/notebook/SymbolicAI%2FSemanticWeb%2FSW-11-Python-KnowledgeGraphs.ipynb")
    assert (api, VOCAB.requiresAPI, Literal(True)) in graph
    assert (no_api, VOCAB.requiresAPI, Literal(False)) in graph
    assert (api, VOCAB.requiresGPU, Literal(False)) in graph
    assert (no_api, VOCAB.requiresGPU, Literal(True)) in graph
    api_values = [value.toPython() for value in graph.objects(None, VOCAB.requiresAPI)]
    assert True in api_values and False in api_values
    assert any(graph.objects(subject, VOCAB.estimatedDuration) for subject in notebooks)
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


def test_resource_fields_reject_values_with_wrong_types():
    try:
        build_graph([{"path": "A.ipynb", "title": "A", "serie": "A", "requires_api": "yes"}])
    except ValueError as error:
        assert "requires_api" in str(error)
    else:
        raise AssertionError("un booléen de ressource invalide doit être refusé")


def test_interfaces_emit_class_path_and_contract():
    interfaces = [
        {"class": "cli", "name": "count_code_sorry",
         "path": "scripts/lean/count_code_sorry.py",
         "description": "Compte les sorry reels.",
         "contract": {"usage": "python scripts/lean/count_code_sorry.py --json",
                      "exit_semantics": "0 = compte rendu"}},
        {"class": "mcp", "name": "sk08", "path": "a/b/",
         "contract": {"usage": "dotnet run"}},
    ]
    graph = build_interfaces_graph(interfaces)
    assert len(list(graph.subjects(RDF.type, VOCAB.Interface))) == 2
    cli = URIRef("https://github.com/jsboige/CoursIA/cursus/interface/count_code_sorry")
    assert (cli, VOCAB.interfaceClass, Literal("cli")) in graph
    assert (cli, DCTERMS.identifier, Literal("scripts/lean/count_code_sorry.py")) in graph
    assert (cli, VOCAB.invocation, Literal("python scripts/lean/count_code_sorry.py --json")) in graph
    assert (cli, VOCAB.exitSemantics, Literal("0 = compte rendu")) in graph
    # l'entree sans description ne porte pas de description (champ absent, non invente)
    mcp = URIRef("https://github.com/jsboige/CoursIA/cursus/interface/sk08")
    assert not list(graph.objects(mcp, DCTERMS.description))


def test_interfaces_pass_shacl_with_valid_class():
    graph = build_interfaces_graph([
        {"class": "bridge", "name": "amd_lean_bridge",
         "path": "MyIA.AI.Notebooks/GameTheory/amd_lean_bridge.py",
         "contract": {"usage": "module Python"}},
    ])
    conforms, report = validate_graph(graph)
    assert conforms, report


def test_combined_catalogue_and_interfaces_pass_shacl():
    """La facette interface coexiste avec les formes carnet sans se salir mutuellement."""
    graph = build_graph([{"path": "A/B.ipynb", "title": "B", "serie": "A"}])
    graph += build_interfaces_graph([
        {"class": "cli", "name": "q", "path": "scripts/q.py",
         "contract": {"usage": "python scripts/q.py"}},
    ])
    assert list(graph.subjects(RDF.type, VOCAB.Notebook))
    assert list(graph.subjects(RDF.type, VOCAB.Interface))
    conforms, report = validate_graph(graph)
    assert conforms, report


def test_interfaces_reject_unknown_class():
    try:
        build_interfaces_graph([
            {"class": "rest", "name": "x", "path": "p", "contract": {"usage": "u"}},
        ])
    except ValueError as error:
        assert "class" in str(error)
    else:
        raise AssertionError("une classe inconnue doit être refusée")


def test_interfaces_reject_missing_usage():
    try:
        build_interfaces_graph([{"class": "cli", "name": "x", "path": "p"}])
    except ValueError as error:
        assert "usage" in str(error)
    else:
        raise AssertionError("un contrat sans usage doit être refusé")


REPO_ROOT = Path(__file__).resolve().parents[3]
TAXONOMY_DIR = REPO_ROOT / "docs" / "curriculum" / "taxonomy"


def test_taxonomy_merge_emits_concepts_only_and_joins_catalogue_notebooks():
    """Fusion --taxonomy-dir (#25001) : concepts sans structure, jointure par URI.

    Témoin sur données réelles : catalogue réel + 9 taxonomies réelles. La
    fusion n'émet ni série ni carnet de la taxonomie (une seule source de
    structure : le catalogue) ; chaque lien cursus:concept atterrit sur un
    nœud carnet du catalogue.
    """
    import json

    catalog = json.loads((REPO_ROOT / "COURSE_CATALOG.generated.json").read_text(encoding="utf-8"))
    graph = build_graph(catalog)
    notebooks_before = set(graph.subjects(RDF.type, VOCAB.Notebook))
    concepts_graph = build_taxonomy_graph(TAXONOMY_DIR)

    # Concepts seuls : aucune structure de taxonomie ne s'ajoute.
    assert not set(concepts_graph.subjects(RDF.type, VOCAB.Series))
    assert not set(concepts_graph.subjects(RDF.type, VOCAB.Subseries))
    assert not set(concepts_graph.subjects(RDF.type, VOCAB.Notebook))

    graph += concepts_graph
    notebooks_after = set(graph.subjects(RDF.type, VOCAB.Notebook))
    assert notebooks_after == notebooks_before  # aucun doublon de carnet

    linked = [
        notebook for notebook in notebooks_after
        if (notebook, VOCAB.concept, None) in graph
    ]
    assert linked, "aucun carnet du catalogue ne reçoit de concept"
    assert any(True for _ in graph.triples((None, VOCAB.requiresConcept, None)))


def test_merged_graph_conforms_and_dangling_prerequisite_is_refused():
    """Le graphe fusionné passe les formes ; un prérequis pendant est refusé."""
    import json

    catalog = json.loads((REPO_ROOT / "COURSE_CATALOG.generated.json").read_text(encoding="utf-8"))
    graph = build_graph(catalog)
    graph += build_taxonomy_graph(TAXONOMY_DIR)
    conforms, report = validate_graph(graph)
    assert conforms, report

    # Témoin négatif : un requiresConcept vers un concept absent du graphe
    # viole sh:class cursus:CurriculumConcept de ConceptShape.
    concept = next(graph.subjects(RDF.type, VOCAB.CurriculumConcept))
    dangling = URIRef("https://github.com/jsboige/CoursIA/cursus/concept/00000000-0000-0000-0000-00000000dead")
    graph.add((concept, VOCAB.requiresConcept, dangling))
    conforms, report = validate_graph(graph)
    assert not conforms
    assert "requiresConcept" in report
