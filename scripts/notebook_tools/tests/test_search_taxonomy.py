import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from curriculum_taxonomy import load_taxonomy, validate_taxonomy  # noqa: E402


# Repo-root-relative location of the Search taxonomy (parents[3] = repo root).
SEARCH_DATA = Path(__file__).resolve().parents[3] / "docs/curriculum/taxonomy/search.json"


def test_search_spine_is_valid_and_covers_its_notebooks():
    # load_taxonomy runs validate_taxonomy against the real repo, so every cited
    # cell_id is checked for real and every declared notebook must be cited.
    data = load_taxonomy(SEARCH_DATA)
    assert data["series"] == "Search"
    # Floors, not pins: the taxonomy covers the six foundation notebooks and the
    # twenty notebooks of the constraint sub-series (C# twins included), and must
    # not shrink back to the six-notebook spine.
    assert len(data["notebooks"]) >= 26
    assert len(data["concepts"]) >= 100
    cited = {citation["notebook"] for concept in data["concepts"] for citation in concept["citations"]}
    declared = set(data["notebooks"])
    # Aucune declaration morte : tout carnet declare est cite par au moins un concept.
    assert declared <= cited
    # Une citation hors du perimetre declare doit etre un carnet declare par une
    # AUTRE taxonomie du dossier : c'est ce qui fait un pont inter-series (T3 de
    # #26646), et c'est la regle que validate_taxonomy applique deja.
    foreign = cited - declared
    other_declared = set()
    for other_path in sorted(SEARCH_DATA.parent.glob("*.json")):
        if other_path.name == SEARCH_DATA.name:
            continue
        other_declared.update(json.loads(other_path.read_text(encoding="utf-8")).get("notebooks") or [])
    assert foreign <= other_declared, f"citations hors perimetre non declarees ailleurs : {sorted(foreign - other_declared)}"


def test_search_prerequisite_graph_is_known_and_acyclic():
    data = json.loads(SEARCH_DATA.read_text(encoding="utf-8"))
    # validate_taxonomy raises "prérequis inconnu" / "cycle de prérequis" on a problem.
    validate_taxonomy(data)
