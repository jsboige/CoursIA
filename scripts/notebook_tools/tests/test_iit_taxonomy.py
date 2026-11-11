import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from curriculum_taxonomy import load_taxonomy, validate_taxonomy  # noqa: E402


# Repo-root-relative location of the IIT taxonomy (parents[3] = repo root).
IIT_DATA = Path(__file__).resolve().parents[3] / "docs/curriculum/taxonomy/iit.json"


def test_iit_spine_is_valid_and_covers_its_notebooks():
    # load_taxonomy runs validate_taxonomy against the real repo, so every cited
    # cell_id is checked for real and every declared notebook must be cited.
    data = load_taxonomy(IIT_DATA)
    assert data["series"] == "IIT"
    # 10 notebooks: the 9 of tranche 1 plus IIT-02 (tranche 2, ids stabilized).
    assert len(data["notebooks"]) == 10
    assert len(data["concepts"]) >= 24
    cited = {citation["notebook"] for concept in data["concepts"] for citation in concept["citations"]}
    assert cited == set(data["notebooks"])


def test_iit_prerequisite_graph_is_known_and_acyclic():
    data = json.loads(IIT_DATA.read_text(encoding="utf-8"))
    # validate_taxonomy raises "prérequis inconnu" / "cycle de prérequis" on a problem.
    validate_taxonomy(data)
