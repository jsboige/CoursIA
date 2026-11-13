import json
import sys
from pathlib import Path

from rdflib import Graph, RDF
from rdflib.namespace import OWL, SKOS

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from curriculum_taxonomy import generate, load_taxonomy, validate_taxonomy  # noqa: E402


# Repo-root-relative location of the Planners taxonomy (parents[3] = repo root).
PLANNERS_DATA = Path(__file__).resolve().parents[3] / "docs/curriculum/taxonomy/planners.json"


def test_planners_spine_is_valid_and_covers_its_notebooks():
    # load_taxonomy runs validate_taxonomy against the real repo, so every cited
    # cell_id is checked for real and every declared notebook must be cited.
    data = load_taxonomy(PLANNERS_DATA)
    assert data["series"] == "Planners"
    assert len(data["notebooks"]) == 6
    assert len(data["concepts"]) >= 20
    cited = {citation["notebook"] for concept in data["concepts"] for citation in concept["citations"]}
    assert cited == set(data["notebooks"])


def test_planners_prerequisite_graph_is_known_and_acyclic():
    data = json.loads(PLANNERS_DATA.read_text(encoding="utf-8"))
    # validate_taxonomy raises "prérequis inconnu" / "cycle de prérequis" on a problem.
    validate_taxonomy(data)


def test_planners_export_writes_parseable_skos_and_owl(tmp_path):
    # Guards the SKOS/OWL export of this tranche: the two tests above only exercise
    # load/validate, never generate (Hermes minor point on #25445).
    skos_path = tmp_path / "planners.ttl"
    owl_path = tmp_path / "planners.owl"
    assert generate(PLANNERS_DATA, skos_path, owl_path) == 0
    skos_graph = Graph().parse(skos_path, format="turtle")
    owl_graph = Graph().parse(owl_path, format="xml")
    assert (None, RDF.type, SKOS.Concept) in skos_graph
    assert (None, RDF.type, OWL.Ontology) in owl_graph
    # The README/CI claim for the tranche: 26 concepts.
    concepts = set(skos_graph.subjects(RDF.type, SKOS.Concept))
    assert len(concepts) == 26
