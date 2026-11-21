"""Densité et ponts des taxonomies du cursus, sur trois taxonomies figées.

Les fixtures de `fixtures/curriculum_taxonomy/` décrivent trois séries
fictives. Aucun test ne lit les taxonomies réelles du dépôt ni le réseau :
les carnets sont recréés dans un dossier temporaire à partir de
`notebooks.json`, réduits à leurs identifiants de cellule.

- Alpha : trois carnets, cinq concepts, aucun lien sortant.
- Beta : deux carnets, cinq concepts. Elle porte tous les ponts déclarés vers
  Alpha : un alignement `exact`, un alignement `close`, un prérequis, et un
  concept qui cite un carnet d'Alpha. Deux ponts restent candidats : un
  libellé identique à la typographie près, une définition identique.
- Gamma : un carnet, deux concepts, isolée. C'est le témoin négatif.
"""

import copy
import json
import sys
from pathlib import Path

import pytest
from rdflib import Graph, RDF, URIRef
from rdflib.namespace import RDFS, SKOS

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))
import curriculum_taxonomy as organ
import curriculum_taxonomy_survey as survey
import query_curriculum as reader

FIXTURES = Path(__file__).resolve().parent / "fixtures" / "curriculum_taxonomy"
SCHEMA = Path(__file__).resolve().parents[2] / "docs" / "curriculum" / "taxonomy" / "schema.json"
ROOT = "MyIA.AI.Notebooks/"
A = [f"a0000000-0000-4000-8000-{number:012d}" for number in range(1, 6)]
B = [f"b0000000-0000-4000-8000-{number:012d}" for number in range(1, 6)]
G = [f"c0000000-0000-4000-8000-{number:012d}" for number in range(1, 3)]
ABSENT = "d0000000-0000-4000-8000-000000000001"
NO_BRIDGE = ["Aucun pont entre taxonomies dans l'export."]


def fixture(name: str) -> dict:
    return json.loads((FIXTURES / f"{name}.json").read_text(encoding="utf-8"))


def make_repo(root: Path, names=("alpha", "beta", "gamma"), mutate=None) -> Path:
    """Dépôt minimal : taxonomies figées et carnets réduits à leurs cellules."""
    directory = root / organ.TAXONOMY_DIR
    directory.mkdir(parents=True)
    for name in names:
        data = fixture(name)
        if mutate is not None:
            mutate(name, data)
        (directory / f"{name}.json").write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
    for path, cells in fixture("notebooks").items():
        notebook = root / path
        notebook.parent.mkdir(parents=True, exist_ok=True)
        notebook.write_text(json.dumps({
            "cells": [{"id": cell, "cell_type": "markdown", "metadata": {}, "source": []} for cell in cells],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }), encoding="utf-8")
    return root


def concept_of(data: dict, concept_id: str) -> dict:
    return next(concept for concept in data["concepts"] if concept["id"] == concept_id)


def on(taxonomy: str, concept_id: str, change):
    """Mutation d'un seul concept d'une seule taxonomie, pour `make_repo`."""
    def mutate(name: str, data: dict) -> None:
        if name == taxonomy:
            change(concept_of(data, concept_id))
    return mutate


def uri(concept_id: str) -> URIRef:
    return URIRef(organ.BASE + "concept/" + concept_id)


@pytest.fixture
def repo(tmp_path):
    return make_repo(tmp_path)


@pytest.fixture
def merged_graph(repo, tmp_path):
    """Export réuni des trois taxonomies, relu depuis son fichier Turtle."""
    skos = tmp_path / "out" / "taxonomies.ttl"
    organ.generate_all(skos, tmp_path / "out" / "taxonomies.owl", repo)
    return reader.load_graph([skos])


# --- Les fixtures sont valides, ensemble et contre le schéma ---------------


def test_fixtures_validate_together(repo):
    results = organ.validate_all(repo)
    assert [(entry["file"], entry["concepts"]) for entry in results] == [
        ("alpha.json", 5), ("beta.json", 5), ("gamma.json", 2),
    ]
    assert organ.cross_taxonomy_failures(organ.load_corpus(repo)) == []


def test_fixtures_and_matches_field_conform_to_the_schema():
    jsonschema = pytest.importorskip("jsonschema")
    validator = jsonschema.Draft202012Validator(json.loads(SCHEMA.read_text(encoding="utf-8")))
    for name in ("alpha", "beta", "gamma"):
        assert list(validator.iter_errors(fixture(name))) == []
    for broken in ({"concept": A[1], "kind": "same"}, {"concept": A[1]},
                   {"concept": A[1], "kind": "exact", "note": "x"}):
        data = fixture("beta")
        concept_of(data, B[0])["matches"] = [broken]
        assert list(validator.iter_errors(data)), broken
    data = fixture("beta")
    concept_of(data, B[0])["match"] = [{"concept": A[1], "kind": "exact"}]
    assert list(validator.iter_errors(data))


# --- Relevé de densité ------------------------------------------------------


def test_density_measures_each_taxonomy(repo):
    report = organ.survey_report(repo, bridges=False)["density"]
    rows = {row["taxonomy"]: row for row in report["taxonomies"]}
    assert list(rows) == ["alpha", "beta", "gamma"]
    alpha = rows["alpha"]
    assert (alpha["series"], alpha["notebooks"], alpha["concepts"], alpha["citations"]) == ("Alpha", 3, 5, 7)
    # Alpha-02 est cité par deux concepts d'Alpha et par un concept de Beta.
    assert alpha["per_notebook"] == {
        ROOT + "Alpha/Alpha-01.ipynb": 2, ROOT + "Alpha/Alpha-02.ipynb": 3, ROOT + "Alpha/Alpha-03.ipynb": 2,
    }
    assert alpha["concepts_per_notebook"] == {"min": 2, "median": 2, "max": 3}
    assert (alpha["single_citation_concepts"], alpha["single_notebook_concepts"]) == (3, 4)
    beta = rows["beta"]
    assert (beta["notebooks"], beta["concepts"], beta["citations"]) == (2, 5, 7)
    assert beta["concepts_per_notebook"] == {"min": 3, "median": 3, "max": 3}
    assert (beta["single_citation_concepts"], beta["single_notebook_concepts"]) == (3, 3)
    assert rows["gamma"]["concepts_per_notebook"] == {"min": 2, "median": 2, "max": 2}
    assert all(row["zero_notebooks"] == [] for row in rows.values())
    assert report["total"] == {
        "taxonomies": 3, "notebooks": 6, "concepts": 12, "citations": 16,
        "concepts_per_notebook": {"min": 2, "median": 2.5, "max": 3},
        "zero_notebooks": 0, "single_citation_concepts": 8, "single_notebook_concepts": 9,
    }


def test_density_names_a_declared_notebook_without_concept(repo):
    corpus = organ.load_corpus(repo)
    # Les deux concepts qui citent Alpha-03 disparaissent : le carnet reste déclaré.
    corpus["alpha"]["concepts"] = [c for c in corpus["alpha"]["concepts"] if c["id"] not in (A[3], A[4])]
    report = survey.density(corpus)
    alpha = report["taxonomies"][0]
    assert alpha["zero_notebooks"] == [ROOT + "Alpha/Alpha-03.ipynb"]
    assert alpha["concepts_per_notebook"]["min"] == 0
    assert report["total"]["zero_notebooks"] == 1
    assert "alpha : " + ROOT + "Alpha/Alpha-03.ipynb" in survey.render_density(report)


# --- Relevé des ponts -------------------------------------------------------


def test_bridges_lists_the_three_declared_families_and_the_candidates(repo):
    report = organ.survey_report(repo, density=False)["bridges"]
    assert report["summary"] == {
        "taxonomies": 3, "shared_concepts": 1, "cross_prerequisites": 1,
        "exact": 1, "close": 1, "candidates": 2, "duplicates_in_taxonomy": 0,
    }
    shared = report["shared_concepts"][0]
    assert (shared["concept"], shared["taxonomy"], shared["taxonomies"]) == (B[1], "beta", ["alpha", "beta"])
    assert shared["notebooks"] == [ROOT + "Alpha/Alpha-02.ipynb", ROOT + "Beta/Beta-01.ipynb"]
    crossing = report["cross_prerequisites"][0]
    assert (crossing["concept"], crossing["requires"]["concept"], crossing["requires"]["taxonomy"]) == (
        B[2], A[0], "alpha")
    assert {(entry["kind"], tuple(ref["concept"] for ref in entry["concepts"]))
            for entry in report["alignments"]} == {("exact", (A[1], B[0])), ("close", (A[2], B[3]))}
    assert [[ref["concept"] for ref in members] for members in report["exact_classes"]] == [[A[1], B[0]]]
    # Le libellé commun de la paire alignée n'est plus un candidat ; restent
    # le libellé identique à la typographie près et la définition identique.
    assert {(tuple(entry["reasons"]), tuple(ref["concept"] for ref in entry["concepts"]))
            for entry in report["candidates"]} == {(("label",), (A[3], B[4])), (("definition",), (A[4], B[3]))}
    assert report["pairs"] == {"alpha <-> beta": {
        "shared_concepts": 1, "cross_prerequisites": 1, "exact": 1, "close": 1, "candidates": 2,
    }}


def test_two_taxonomies_without_bridge_give_zero_bridge(tmp_path):
    """Témoin négatif : Alpha et Gamma ne se citent pas, ne se requièrent pas, ne s'alignent pas."""
    repo = make_repo(tmp_path, names=("alpha", "gamma"))
    organ.validate_all(repo)
    report = organ.survey_report(repo, density=False)["bridges"]
    assert report["summary"] == {
        "taxonomies": 2, "shared_concepts": 0, "cross_prerequisites": 0,
        "exact": 0, "close": 0, "candidates": 0, "duplicates_in_taxonomy": 0,
    }
    assert report["pairs"] == {}
    assert "aucun pont, déclaré ou candidat" in survey.render_bridges(report)
    skos = tmp_path / "out.ttl"
    organ.generate_all(skos, tmp_path / "out.owl", repo)
    assert reader.bridges_for(reader.load_graph([skos])) == NO_BRIDGE


def test_reciprocal_alignment_counts_once(tmp_path):
    repo = make_repo(tmp_path, mutate=on(
        "alpha", A[1], lambda concept: concept.update(matches=[{"concept": B[0], "kind": "exact"}])))
    organ.validate_all(repo)
    assert organ.survey_report(repo, density=False)["bridges"]["summary"]["exact"] == 1
    skos = tmp_path / "out.ttl"
    organ.generate_all(skos, tmp_path / "out.owl", repo)
    lines = reader.bridges_for(reader.load_graph([skos]))
    assert sum("\talignement exact\t" in line for line in lines) == 1


def test_duplicate_inside_one_taxonomy_is_not_a_bridge(repo):
    corpus = organ.load_corpus(repo)
    concept_of(corpus["gamma"], G[1])["label_fr"] = "entropie"
    report = survey.bridges(corpus)
    assert report["summary"]["candidates"] == 2
    assert [[ref["concept"] for ref in entry["concepts"]] for entry in report["duplicates_in_taxonomy"]] == [G]


def test_normalize_ignores_case_accents_and_punctuation():
    assert survey.normalize("Fonction d'utilité") == survey.normalize("fonction d’UTILITE")
    assert survey.normalize("Jeu à somme nulle") == survey.normalize("JEU A SOMME-NULLE") == "jeu a somme nulle"
    assert survey.normalize(None) == ""


# --- Validation des alignements, prérequis et citations entre taxonomies ----


def test_match_to_a_concept_declared_nowhere_is_refused(tmp_path):
    """Témoin négatif : l'identifiant visé n'existe dans aucune taxonomie du dossier."""
    repo = make_repo(tmp_path, mutate=on(
        "beta", B[0], lambda concept: concept.update(matches=[{"concept": ABSENT, "kind": "exact"}])))
    with pytest.raises(ValueError, match=f"beta.json : concept aligné inconnu {ABSENT}"):
        organ.validate_all(repo)
    with pytest.raises(ValueError, match="concept aligné inconnu"):
        organ.load_taxonomy(repo / organ.TAXONOMY_DIR / "beta.json", repo)


@pytest.mark.parametrize("matches, message", [
    ([{"concept": B[0], "kind": "exact"}], "alignement d'un concept sur lui-même"),
    ([{"concept": B[1], "kind": "close"}], "alignement interne à la taxonomie"),
    ([{"concept": A[1], "kind": "same"}], "kind d'alignement inconnu"),
    ([{"concept": A[1], "kind": "exact", "note": "x"}], "alignement mal formé"),
    ([{"concept": A[1]}], "alignement mal formé"),
    ([{"concept": 7, "kind": "exact"}], "alignement mal formé"),
    ([{"concept": A[1], "kind": "exact"}, {"concept": A[1], "kind": "close"}], "alignement dupliqué"),
    ({"concept": A[1], "kind": "exact"}, "matches doit être une liste"),
])
def test_malformed_match_is_refused(tmp_path, matches, message):
    repo = make_repo(tmp_path, mutate=on("beta", B[0], lambda concept: concept.update(matches=matches)))
    with pytest.raises(ValueError, match=message):
        organ.validate_all(repo)


def test_empty_matches_list_and_absent_field_are_both_accepted(tmp_path):
    repo = make_repo(tmp_path, mutate=on("gamma", G[0], lambda concept: concept.update(matches=[])))
    assert len(organ.validate_all(repo)) == 3


def test_unknown_concept_field_is_refused(tmp_path):
    # Une faute de frappe sur `matches` ne doit pas passer pour une absence d'alignement.
    repo = make_repo(tmp_path, mutate=on(
        "beta", B[0], lambda concept: concept.update(match=[{"concept": A[1], "kind": "exact"}])))
    with pytest.raises(ValueError, match=r"champ concept inconnu \(match\)"):
        organ.validate_all(repo)


def test_prerequisite_may_target_another_taxonomy_but_not_an_unknown_concept(tmp_path):
    repo = make_repo(tmp_path / "ok")
    data = organ.load_taxonomy(repo / organ.TAXONOMY_DIR / "beta.json", repo)
    assert concept_of(data, B[2])["prerequisites"] == [A[0]]
    broken = make_repo(tmp_path / "broken", mutate=on(
        "beta", B[2], lambda concept: concept.update(prerequisites=[ABSENT])))
    with pytest.raises(ValueError, match=f"prérequis inconnu {ABSENT}"):
        organ.validate_all(broken)


def test_prerequisite_cycle_through_another_taxonomy_is_refused(tmp_path):
    # Beta « Induction à rebours » requiert déjà Alpha « Graphe d'états » ; l'inverse ferme la boucle.
    repo = make_repo(tmp_path, mutate=on("alpha", A[0], lambda concept: concept.update(prerequisites=[B[2]])))
    with pytest.raises(ValueError, match="cycle de prérequis"):
        organ.validate_all(repo)


@pytest.mark.parametrize("citation, message", [
    ({"notebook": ROOT + "Alpha/Alpha-02.ipynb", "cell_id": "absente"}, "cellule citée introuvable"),
    ({"notebook": ROOT + "Delta/Delta-01.ipynb", "cell_id": "d1-c1"}, "source hors du périmètre déclaré"),
])
def test_citation_of_another_taxonomy_notebook_is_checked(tmp_path, citation, message):
    repo = make_repo(tmp_path, mutate=on("beta", B[1], lambda concept: concept["citations"].append(citation)))
    with pytest.raises(ValueError, match=message):
        organ.validate_all(repo)


def test_validating_one_taxonomy_ignores_its_own_copy_on_disk(repo):
    # La taxonomie relue depuis le disque n'est pas une « autre » taxonomie pour elle-même.
    data = fixture("beta")
    organ.validate_taxonomy(data, repo)
    mutated = copy.deepcopy(data)
    concept_of(mutated, B[0])["matches"] = [{"concept": B[1], "kind": "exact"}]
    with pytest.raises(ValueError, match="alignement interne à la taxonomie"):
        organ.validate_taxonomy(mutated, repo)


def test_folder_level_inconsistencies_are_named(repo):
    def failures(change) -> list[str]:
        corpus = organ.load_corpus(repo)
        change(corpus)
        return organ.cross_taxonomy_failures(corpus)

    assert failures(lambda corpus: concept_of(corpus["gamma"], G[0]).update(id=A[0])) == [
        f"identifiant de concept déclaré par plusieurs taxonomies (alpha, gamma) : {A[0]}"]
    assert failures(lambda corpus: corpus["gamma"]["notebooks"].append(ROOT + "Alpha/Alpha-01.ipynb")) == [
        f"carnet déclaré par plusieurs taxonomies (alpha, gamma) : {ROOT}Alpha/Alpha-01.ipynb"]
    contradictory = failures(lambda corpus: concept_of(corpus["alpha"], A[1]).update(
        matches=[{"concept": B[0], "kind": "close"}]))
    assert contradictory == [
        f"alignement réciproque contradictoire, exact d'un côté et close de l'autre : {A[1]} / {B[0]}"]
    # Deux concepts de Beta déclarés identiques au même concept d'Alpha.
    collapsed = failures(lambda corpus: concept_of(corpus["beta"], B[4]).update(
        matches=[{"concept": A[1], "kind": "exact"}]))
    assert collapsed == [f"alignements exacts qui identifient deux concepts de beta : {B[0]} / {B[4]}"]


def test_folder_level_inconsistency_fails_the_whole_pass(tmp_path):
    repo = make_repo(tmp_path, mutate=on(
        "alpha", A[1], lambda concept: concept.update(matches=[{"concept": B[0], "kind": "close"}])))
    with pytest.raises(ValueError, match="ensemble du dossier : alignement réciproque contradictoire"):
        organ.validate_all(repo)


# --- Export SKOS/OWL --------------------------------------------------------


def test_export_carries_matches_cross_prerequisites_and_notebook_links(repo):
    data = organ.load_taxonomy(repo / organ.TAXONOMY_DIR / "beta.json", repo)
    graph = organ.build_graph(data, "beta")
    assert (uri(B[0]), SKOS.exactMatch, uri(A[1])) in graph
    assert (uri(B[3]), SKOS.closeMatch, uri(A[2])) in graph
    assert (uri(B[2]), organ.VOCAB.requiresConcept, uri(A[0])) in graph
    # Citations multiples : le concept est lié à chacun des carnets qui le citent.
    for notebook in ("Beta%2FBeta-01.ipynb", "Alpha%2FAlpha-02.ipynb"):
        assert (URIRef(organ.BASE + "notebook/" + notebook), organ.VOCAB.concept, uri(B[1])) in graph
    assert len(list(graph.objects(uri(B[1]), organ.VOCAB.hasCellCitation))) == 2
    taxonomy = URIRef(organ.BASE + "taxonomy/beta")
    assert (taxonomy, RDF.type, organ.VOCAB.Taxonomy) in graph
    assert all((uri(concept_id), RDFS.isDefinedBy, taxonomy) in graph for concept_id in B)
    # Sans nom de taxonomie, l'export reste celui d'avant, alignements compris.
    anonymous = organ.build_graph(data)
    assert (None, RDFS.isDefinedBy, None) not in anonymous
    assert (uri(B[0]), SKOS.exactMatch, uri(A[1])) in anonymous


def test_merged_export_is_written_once_for_the_whole_folder(repo, tmp_path, capsys):
    skos, owl = tmp_path / "out" / "all.ttl", tmp_path / "out" / "all.owl"
    assert organ.main(["--all", "--skos-output", str(skos), "--owl-output", str(owl),
                       "--repo-root", str(repo)]) == 0
    output = capsys.readouterr().out
    assert "Export réuni : 3 taxonomies, 12 concepts" in output
    assert output.count("Taxonomie valide :") == 3
    turtle = Graph().parse(skos, format="turtle")
    assert len(set(turtle.subjects(RDF.type, SKOS.Concept))) == 12
    assert len(set(turtle.subjects(RDF.type, organ.VOCAB.Taxonomy))) == 3
    # Dans le graphe réuni, la cible d'un alignement est un concept décrit.
    assert (uri(A[1]), SKOS.prefLabel, None) in turtle and (uri(B[0]), SKOS.exactMatch, uri(A[1])) in turtle
    owl_graph = Graph().parse(owl, format="xml")
    assert len(owl_graph) == len(turtle)


def test_single_export_still_requires_both_outputs(repo, tmp_path):
    with pytest.raises(SystemExit):
        organ.main(["--data", str(repo / organ.TAXONOMY_DIR / "beta.json"), "--repo-root", str(repo)])
    with pytest.raises(SystemExit):
        organ.main(["--all", "--skos-output", str(tmp_path / "seul.ttl"), "--repo-root", str(repo)])
    with pytest.raises(SystemExit):
        organ.main(["--all", "--json", "--repo-root", str(repo)])


# --- Ligne de commande du relevé --------------------------------------------


def test_cli_json_output_is_the_survey_and_nothing_else(repo, capsys):
    assert organ.main(["--all", "--density", "--bridges", "--json", "--repo-root", str(repo)]) == 0
    captured = capsys.readouterr()
    assert json.loads(captured.out) == organ.survey_report(repo)
    # Les lignes de validation ne se mêlent pas au JSON.
    assert "Taxonomie valide : Alpha (alpha.json)" in captured.err
    assert organ.main(["--bridges", "--json", "--repo-root", str(repo)]) == 0
    assert list(json.loads(capsys.readouterr().out)) == ["bridges"]


def test_cli_text_output(repo, capsys):
    assert organ.main(["--density", "--bridges", "--repo-root", str(repo)]) == 0
    output = capsys.readouterr().out
    assert "Densité des taxonomies" in output
    assert "Carnets déclarés sans aucun concept : aucun" in output
    assert "Alignements déclarés : 1 exact, 1 close" in output
    assert "  alpha <-> beta : partagés 1, prérequis 1, exact 1, close 1, candidats 2" in output
    assert "gamma <->" not in output and "<-> gamma" not in output


def test_cli_survey_fails_cleanly_without_taxonomy(tmp_path, capsys):
    assert organ.main(["--density", "--repo-root", str(tmp_path)]) == 1
    assert "aucune taxonomie lisible" in capsys.readouterr().err


def test_survey_measures_a_folder_that_does_not_validate(tmp_path, capsys):
    # Le relevé lit ce qui est écrit ; c'est --all qui refuse.
    repo = make_repo(tmp_path, mutate=on(
        "beta", B[0], lambda concept: concept.update(matches=[{"concept": ABSENT, "kind": "exact"}])))
    assert organ.main(["--bridges", "--repo-root", str(repo)]) == 0
    assert "(concept hors du dossier)" in capsys.readouterr().out
    assert organ.main(["--all", "--bridges", "--repo-root", str(repo)]) == 1
    assert "concept aligné inconnu" in capsys.readouterr().err


# --- Interrogation de l'export ----------------------------------------------


def test_reader_lists_bridges_by_pair_and_agrees_with_the_survey(repo, merged_graph):
    lines = reader.bridges_for(merged_graph)
    assert lines == [
        f"alpha <-> beta\talignement close\tHeuristique admissible = Voisinage\t{A[2]}\t{B[3]}",
        f"alpha <-> beta\talignement exact\tFonction d'utilité = Fonction d'utilité\t{A[1]}\t{B[0]}",
        f"alpha <-> beta\tconcept partagé\tÉquilibre\t{B[1]}",
        f"alpha <-> beta\tprérequis\tInduction à rebours requiert Graphe d'états\t{B[2]}\t{A[0]}",
    ]
    summary = organ.survey_report(repo, density=False)["bridges"]["summary"]
    families = [line.split("\t")[1] for line in lines]
    assert families.count("concept partagé") == summary["shared_concepts"]
    assert families.count("prérequis") == summary["cross_prerequisites"]
    assert families.count("alignement exact") == summary["exact"]
    assert families.count("alignement close") == summary["close"]
    assert reader.bridges_for(merged_graph, limit=1) == lines[:1]


def test_reader_lists_the_concepts_of_a_notebook(merged_graph):
    expected = [
        f"Équilibre\t{B[1]}\tbeta\ta2-c2",
        f"Graphe d'états\t{A[0]}\talpha\ta2-c1",
        f"Heuristique admissible\t{A[2]}\talpha\ta2-c2, a2-c3",
    ]
    assert sorted(reader.concepts_of_notebook(merged_graph, ROOT + "Alpha/Alpha-02.ipynb")) == sorted(expected)
    # Le chemin s'accepte aussi sans le dossier racine des carnets.
    assert sorted(reader.concepts_of_notebook(merged_graph, "Alpha/Alpha-02.ipynb")) == sorted(expected)
    assert reader.concepts_of_notebook(merged_graph, "Alpha/Alpha-02.ipynb", query="heuristique") == [expected[2]]
    assert len(reader.concepts_of_notebook(merged_graph, "Gamma/Gamma-01.ipynb")) == 2
    with pytest.raises(KeyError):
        reader.concepts_of_notebook(merged_graph, "Alpha/Absent.ipynb")


def test_reader_cli_bridges_and_concepts_by_notebook(repo, tmp_path, capsys):
    skos = tmp_path / "out" / "all.ttl"
    organ.generate_all(skos, tmp_path / "out" / "all.owl", repo)
    capsys.readouterr()
    assert reader.main(["--graph", str(skos), "bridges"]) == 0
    assert capsys.readouterr().out.count("alpha <-> beta\t") == 4
    assert reader.main(["--graph", str(skos), "concepts", "--notebook", ROOT + "Beta/Beta-02.ipynb"]) == 0
    output = capsys.readouterr().out
    assert f"Voisinage\t{B[3]}\tbeta\tb2-c2" in output and len(output.splitlines()) == 3
    assert reader.main(["--graph", str(skos), "concepts", "--notebook", "Alpha/Absent.ipynb"]) == 2
    assert "Carnet introuvable" in capsys.readouterr().err


def test_reader_names_what_lies_outside_the_loaded_graphs(repo, tmp_path):
    # Export de la seule taxonomie Beta : ses ponts mènent hors du graphe chargé.
    skos = tmp_path / "beta.ttl"
    organ.generate(repo / organ.TAXONOMY_DIR / "beta.json", skos, tmp_path / "beta.owl", repo)
    lines = reader.bridges_for(reader.load_graph([skos]))
    assert len(lines) == 4
    assert all(line.startswith(f"beta <-> {reader.OUTSIDE}\t") for line in lines)
