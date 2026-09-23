"""Tests du garde de dérive testpaths (#10903).

Le garde vit dans scripts/check_testpaths_coverage.py : il compare les
testpaths de pytest.ini aux cibles pytest réelles des workflows CI et rougit
sur tout testpath ni couvert ni déclaré CI-EXCLUDED.

#17250 : ajoute la séparation entre étapes `pytest --collect-only` (floors,
qui sondent la collecte sans exécuter) et étapes d'exécution effectives.
Un dossier qui n'apparaît que dans un floor ne couvre pas un testpath.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_testpaths_coverage import (  # noqa: E402
    REPO_ROOT,
    WORKFLOW_COVERAGE,
    _partition_run_blocks,
    extract_run_targets,
    is_covered,
    load_ci_excluded,
    load_testpaths,
)


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


def test_extract_run_targets_root_dir_without_slash() -> None:
    """Un répertoire racine du dépôt (pas de /, ex. GradeBookApp) est extrait.

    Les flags pytest (--tb=short, -q) ne le sont pas (famille 5 de #14615).
    """
    text = """        run: |
          pytest \\
            scripts/lean/tests \\
            GradeBookApp \\
            --tb=short -q
"""
    targets = extract_run_targets(text)
    assert "GradeBookApp" in targets
    assert "--tb=short" not in targets and "-q" not in targets


def test_is_covered_exact_and_ancestor() -> None:
    assert is_covered("scripts/tests", ["scripts/tests"])
    assert is_covered("scripts/lean/tests", ["scripts"])  # ancêtre
    assert not is_covered("scripts/audit/tests", ["scripts/tests"])  # voisin
    assert not is_covered("GradeBookApp", ["scripts/tests"])


def test_guard_green_on_current_main() -> None:
    """Sur l'état actuel, tous les testpaths sont couverts ou exclus."""
    testpaths = load_testpaths(REPO_ROOT / "pytest.ini")
    excluded = load_ci_excluded(REPO_ROOT)

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


# --- #17250 : séparation des floors `--collect-only` ---


def test_partition_floor_pur_exclut_covered() -> None:
    """Un step `python -m pytest X --collect-only -q` seul met X en floor,
    pas en covered. Si le testpath X n'apparaît que dans ce bloc,
    extract_run_targets ne le retourne pas — c'est le défaut pré-existant
    que #17250 ferme.
    """
    text = (
        "- name: Audit floor\n"
        "        run: |\n"
        "          N=$(python -m pytest scripts/audit/tests "
        "--collect-only -q 2>/dev/null)\n"
        "          if [ -z \"$N\" ]; then exit 1; fi\n"
    )
    covered, floors = _partition_run_blocks(text)
    assert "scripts/audit/tests" not in covered
    assert "scripts/audit/tests" in floors


def test_partition_execution_seule_va_en_covered() -> None:
    """Un step d'exécution pure met ses cibles en covered, jamais en floor."""
    text = (
        "        run: |\n"
        "          pytest scripts/tests scripts/lean/tests --tb=short -q\n"
    )
    covered, floors = _partition_run_blocks(text)
    assert "scripts/tests" in covered
    assert "scripts/lean/tests" in covered
    assert "scripts/tests" not in floors


def test_partition_run_et_floor_dans_blocs_freres_isoles() -> None:
    """Mutation A mesurée dans #17250 : un floor et un run principal dans
    le même step séparent leurs cibles, le floor n'exécute pas le testpath.
    Si on retire `scripts/audit/tests` de la liste pytest partagée,
    extract_run_targets ne le voit plus, et `is_covered` conclut NOT
    covered — c'est précisément la dérive que le fix ferme.
    """
    text = (
        "      - name: Audit floor\n"
        "        if: always()\n"
        "        env:\n"
        "          AUDIT_TESTS_FLOOR: 455\n"
        "        run: |\n"
        "          N=$(python -m pytest scripts/audit/tests "
        "--collect-only -q 2>/dev/null)\n"
        "      - name: Real coverage\n"
        "        run: |\n"
        "          pytest \\\n"
        "            scripts/tests \\\n"
        "            scripts/lean/tests \\\n"
        "            --tb=short -q\n"
    )
    covered, _floors = _partition_run_blocks(text)
    # Le testpath `scripts/audit/tests` n'apparaît QUE dans le floor ; il
    # n'est pas couvert, donc il déclenchera le ROUGE du checker si on
    # l'ajoute à pytest.ini sans le recabler.
    assert "scripts/audit/tests" not in covered
    assert "scripts/tests" in covered


def test_partition_neutralite_lignes_non_pytest() -> None:
    """Les lignes `if / echo / exit / fi` qui mentionnent `--collect-only`
    dans leur texte (message d'erreur, comparaison) n'invalident pas la
    classification floor du bloc. Seule une ligne invoquant `pytest` est
    classificatoire. Reproduction directe de la cause-racine mesurée
    dans #17250.
    """
    text = (
        "- name: Audit floor\n"
        "        run: |\n"
        "          N=$(python -m pytest scripts/audit/tests "
        "--collect-only -q 2>/dev/null)\n"
        "          if [ -z \"$N\" ] || [ \"$N\" -eq 0 ]; then\n"
        "            echo \"::error::--collect-only returned no tests.\"\n"
        "            exit 1\n"
        "          fi\n"
    )
    covered, floors = _partition_run_blocks(text)
    assert "scripts/audit/tests" in floors
    assert "scripts/audit/tests" not in covered
