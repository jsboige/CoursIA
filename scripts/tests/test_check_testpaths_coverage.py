"""Tests du garde de dérive testpaths (#10903).

Le garde vit dans scripts/check_testpaths_coverage.py : il compare les
testpaths de pytest.ini aux cibles pytest réelles des workflows CI et rougit
sur tout testpath ni couvert ni déclaré CI-EXCLUDED.
"""

from __future__ import annotations

from scripts.check_testpaths_coverage import (
    extract_run_targets,
    is_covered,
    load_ci_excluded,
    load_testpaths,
)
from scripts.check_testpaths_coverage import REPO_ROOT


def test_extract_run_targets_multiline_backslash() -> None:
    """La continuation par backslash d'un bloc run: | ne coupe pas l'extraction."""
    wf = (REPO_ROOT / ".github/workflows/scripts-tests.yml").read_text(encoding="utf-8")
    targets = extract_run_targets(wf)
    assert "scripts/tests" in targets
    assert "MyIA.AI.Notebooks/GameTheory/tests" in targets
    assert "MyIA.AI.Notebooks/QuantConnect/scripts/tests" in targets


def test_extract_run_targets_single_line() -> None:
    """Un `run: pytest <chemin>` sur une ligne est extrait."""
    text = """      - name: Run tests
        run: pytest MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/tests --tb=short -v
"""
    assert extract_run_targets(text) == {
        "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/tests"
    }


def test_extract_run_targets_ignores_comments() -> None:
    """Un commentaire mentionnant un chemin ne compte pas comme couverture."""
    text = """      # scripts/tests est couvert par le run ci-dessous
        run: |
          pytest \\
            scripts/lean/tests \\
            --tb=short -q
"""
    targets = extract_run_targets(text)
    assert "scripts/lean/tests" in targets
    # Le commentaire seul n'ajoute rien (déjà couvert par le run, mais on
    # vérifie que les chemins ne sortent pas des blocs run).
    assert len({t for t in targets if t.startswith("scripts/")}) == 1


def test_is_covered_exact_and_ancestor() -> None:
    assert is_covered("scripts/tests", ["scripts/tests"])
    assert is_covered("scripts/lean/tests", ["scripts"])  # ancêtre
    assert not is_covered("scripts/audit/tests", ["scripts/tests"])  # voisin
    assert not is_covered("GradeBookApp", ["scripts/tests"])


def test_guard_green_on_current_main() -> None:
    """Sur l'état actuel, tous les testpaths sont couverts ou exclus."""
    testpaths = load_testpaths(REPO_ROOT / "pytest.ini")
    excluded = load_ci_excluded(REPO_ROOT)
    from scripts.check_testpaths_coverage import WORKFLOW_COVERAGE

    covered_dirs = sorted(
        {
            t
            for targets in WORKFLOW_COVERAGE.values()
            for t in targets
            if not t.endswith(".py")
        }
    )
    uncovered = [tp for tp in testpaths if not is_covered(tp, covered_dirs) and tp not in excluded]
    assert uncovered == [], f"testpaths non couverts: {uncovered}"
    # Le testpath `tests` racine a été retiré de pytest.ini (reliquat vide).
    assert "tests" not in testpaths
