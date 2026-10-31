"""Tests du garde de dérive testpaths (#10903).

Le garde vit dans scripts/check_testpaths_coverage.py : il compare les
testpaths de pytest.ini aux cibles pytest réelles des workflows CI et rougit
sur tout testpath ni couvert ni déclaré CI-EXCLUDED.

#17250 : ajoute la séparation entre étapes `pytest --collect-only` (floors,
qui sondent la collecte sans exécuter) et étapes d'exécution effectives.
Un dossier qui n'apparaît que dans un floor ne couvre pas un testpath.

#22735 : ajoute le second sens — l'ARBorescence confrontée à la couverture.
Le sens historique ne voit que les testpaths DÉCLARÉS ; une suite présente
sur le disque sous `scripts/**/tests/` mais absente de pytest.ini ET de la
couverture CI lui était invisible (huit suites vertes en local, jamais
rejouées). Les tests de cette section prouvent que ce second sens rougit
quand il doit — un contrôle incapable de rougir n'est pas un contrôle.

#22735 : ajoute le troisième sens — l'INVARIANT de résolution des noms de
modules pytest. Deux suites `tests/` sans paquet parent résolvent le même nom
de module (`tests.conftest`) et la collecte tombe en "Plugin already
registered under a different name" ; l'option ini
`consider_namespace_packages` (pytest >= 8.0) ferme la classe.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_testpaths_coverage import (  # noqa: E402
    REPO_ROOT,
    WORKFLOW_COVERAGE,
    _partition_run_blocks,
    check_namespace_option,
    discover_suites,
    extract_run_targets,
    is_covered,
    load_ci_excluded,
    load_testpaths,
    missing_declared_suites,
    uncovered_suites,
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
    # Second sens (#22735) : aucune suite sur le disque sans exécution CI.
    assert uncovered_suites(REPO_ROOT) == [], "suites sur disque non exécutées"
    assert missing_declared_suites(REPO_ROOT) == [], "suites déclarées absentes"


# --- #22735 : second sens, l'arborescence confrontée à la couverture ---


def _make_suite(root: Path, rel: str) -> None:
    """Pose une suite de tests (un répertoire + un `test_*.py`)."""
    target = root / rel
    target.mkdir(parents=True, exist_ok=True)
    (target / "test_x.py").write_text("def test_x():\n    assert True\n", encoding="utf-8")


def _make_workflow(root: Path, targets: list[str]) -> None:
    """Pose un workflow dont le run pytest invoque exactement `targets`."""
    wf_dir = root / ".github" / "workflows"
    wf_dir.mkdir(parents=True, exist_ok=True)
    body = " \\\n            ".join(targets)
    (wf_dir / "w.yml").write_text(
        "name: t\non: [push]\njobs:\n  t:\n    steps:\n"
        "      - name: Run tests\n"
        "        run: |\n"
        "          python -m pytest \\\n            " + body + " -q\n",
        encoding="utf-8",
    )


def test_discover_suites_only_counts_family_dirs(tmp_path: Path) -> None:
    """Seul `scripts/**/tests` contenant un `test_*.py` compte comme suite."""
    _make_suite(tmp_path, "scripts/foo/tests")
    _make_suite(tmp_path, "scripts/bar/baz/tests")
    (tmp_path / "scripts" / "notasuite").mkdir(parents=True, exist_ok=True)
    (tmp_path / "scripts" / "notasuite" / "test_x.py").write_text("", encoding="utf-8")
    (tmp_path / "scripts" / "vide" / "tests").mkdir(parents=True, exist_ok=True)
    assert discover_suites(tmp_path) == [
        "scripts/bar/baz/tests",
        "scripts/foo/tests",
    ]


def test_uncovered_suite_is_detected(tmp_path: Path) -> None:
    """Une suite sur le disque qu'aucun workflow n'exécute doit être signalée."""
    _make_suite(tmp_path, "scripts/foo/tests")
    _make_workflow(tmp_path, ["scripts/other/tests"])
    assert uncovered_suites(tmp_path) == ["scripts/foo/tests"]


def test_wired_suite_is_not_reported(tmp_path: Path) -> None:
    """Une suite sur le disque exécutée par un workflow n'est pas signalée."""
    _make_suite(tmp_path, "scripts/foo/tests")
    _make_workflow(tmp_path, ["scripts/foo/tests"])
    assert uncovered_suites(tmp_path) == []


def test_ci_excluded_suite_is_not_reported(tmp_path: Path) -> None:
    """Une suite volontairement exclue (marqueur CI-EXCLUDED) n'est pas signalée."""
    _make_suite(tmp_path, "scripts/foo/tests")
    _make_workflow(tmp_path, ["scripts/other/tests"])
    wf = tmp_path / ".github" / "workflows" / "w.yml"
    wf.write_text(
        wf.read_text(encoding="utf-8")
        + "# CI-EXCLUDED: scripts/foo/tests — motif ecrit\n",
        encoding="utf-8",
    )
    assert uncovered_suites(tmp_path) == []


def test_missing_declared_suite_is_detected(tmp_path: Path) -> None:
    """Une suite déclarée câblée mais absente de l'arbre doit être signalée."""
    coverage = {".github/workflows/w.yml": ["scripts/foo/tests"]}
    assert missing_declared_suites(tmp_path, coverage) == ["scripts/foo/tests"]
    _make_suite(tmp_path, "scripts/foo/tests")
    assert missing_declared_suites(tmp_path, coverage) == []


def test_cli_is_red_on_an_uncovered_suite(tmp_path: Path) -> None:
    """Le code de sortie de la CLI suit le verdict : 1 sur une suite non jouée."""
    import subprocess

    _make_suite(tmp_path, "scripts/foo/tests")
    _make_workflow(tmp_path, ["scripts/other/tests"])
    (tmp_path / "pytest.ini").write_text(
        "[pytest]\ntestpaths =\n    scripts/other/tests\n", encoding="utf-8"
    )
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "scripts/check_testpaths_coverage.py"),
         "--repo-root", str(tmp_path)],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert proc.returncode == 1, proc.stdout
    assert "FAIL scripts/foo/tests" in proc.stdout


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


# --- Inventaire des suites non declarees (#23359, perimetre restant) ---------
#
# Le guard ne compare que les testpaths DECLARES : un dossier de tests present
# dans le depot mais absent de pytest.ini lui est invisible, et il reste vert
# dessus (cas mesure : SymbolicAI/Argument_Analysis, 174 tests non collectes).
# `--inventory` part du depot au lieu de la declaration.


def test_discover_test_dirs_borne_la_convention(tmp_path: Path) -> None:
    """Seuls les dossiers nommes `tests`/`test` portant un `test_*.py` sortent.

    Un module `test_*.py` co-localise avec du code (gateway, helpers) est un
    test de voisinage, pas une suite : l'inventaire ne le nomme pas.
    """
    from check_testpaths_coverage import discover_test_dirs

    (tmp_path / "scripts" / "alpha" / "tests").mkdir(parents=True)
    (tmp_path / "scripts" / "alpha" / "tests" / "test_a.py").write_text("", encoding="utf-8")
    (tmp_path / "scripts" / "beta" / "gateway").mkdir(parents=True)
    (tmp_path / "scripts" / "beta" / "gateway" / "test_g.py").write_text("", encoding="utf-8")
    (tmp_path / "scripts" / "gamma" / "tests" / "_archive").mkdir(parents=True)
    (tmp_path / "scripts" / "gamma" / "tests" / "_archive" / "test_z.py").write_text("", encoding="utf-8")

    found = discover_test_dirs(tmp_path)

    assert found == ["scripts/alpha/tests"]


def test_run_inventory_un_testpath_declare_couvre_ses_sous_dossiers(
    tmp_path: Path,
) -> None:
    """Un dossier inclus dans un testpath declare n'est pas un trou."""
    from check_testpaths_coverage import run_inventory

    (tmp_path / "scripts" / "alpha" / "tests" / "unit").mkdir(parents=True)
    (tmp_path / "scripts" / "alpha" / "tests" / "unit" / "test_u.py").write_text(
        "", encoding="utf-8"
    )
    (tmp_path / "scripts" / "beta" / "tests").mkdir(parents=True)
    (tmp_path / "scripts" / "beta" / "tests" / "test_b.py").write_text("", encoding="utf-8")

    unwatched = run_inventory(
        tmp_path, ["scripts/alpha/tests"], {}, strict=True
    )

    assert unwatched == ["scripts/beta/tests"]


def test_run_inventory_est_advisory_par_defaut(tmp_path: Path) -> None:
    """Sans `--strict`, un trou d'inventaire n'est pas un echec : il est liste."""
    from check_testpaths_coverage import run_inventory

    (tmp_path / "scripts" / "beta" / "tests").mkdir(parents=True)
    (tmp_path / "scripts" / "beta" / "tests" / "test_b.py").write_text("", encoding="utf-8")

    assert run_inventory(tmp_path, [], {}, strict=False) == []
    assert run_inventory(tmp_path, [], {}, strict=True) == ["scripts/beta/tests"]
# --- #22735 : troisième sens, l'invariant de résolution des noms de modules ---


def _make_repo_with_option(root: Path, *, option: bool, pin: bool) -> None:
    """Repo minimal : pytest.ini (avec ou sans option) + workflow (avec ou sans pin)."""
    ini = "[pytest]\ntestpaths =\n    scripts/tests\n"
    if option:
        ini += "consider_namespace_packages = true\n"
    (root / "pytest.ini").write_text(ini, encoding="utf-8")
    wf_dir = root / ".github" / "workflows"
    wf_dir.mkdir(parents=True, exist_ok=True)
    pip = (
        '          pip install "pytest>=8" pytest-xdist\n'
        if pin
        else "          pip install pytest-xdist\n"
    )
    (wf_dir / "w.yml").write_text(
        "name: t\non: [push]\njobs:\n  t:\n    steps:\n" + pip, encoding="utf-8"
    )


def test_namespace_option_green_on_current_repo() -> None:
    """Sur l'état actuel, l'invariant de résolution des noms de modules est tenu."""
    assert check_namespace_option(REPO_ROOT) == []


def test_missing_namespace_option_is_detected(tmp_path: Path) -> None:
    """Sans l'option dans pytest.ini, l'invariant est violé et signalé."""
    _make_repo_with_option(tmp_path, option=False, pin=True)
    problems = check_namespace_option(tmp_path)
    assert len(problems) == 1
    assert "consider_namespace_packages" in problems[0]


def test_missing_pytest_pin_is_detected(tmp_path: Path) -> None:
    """Sans pin `pytest >= 8` dans un workflow, l'option serait ignorée sans bruit.

    Le défaut ne laisserait aucune trace (simple `PytestConfigWarning`) : le
    garde le rend donc visible avant qu'il ne revienne en CI.
    """
    _make_repo_with_option(tmp_path, option=True, pin=False)
    problems = check_namespace_option(tmp_path)
    assert len(problems) == 1
    assert "pytest>=8" in problems[0]
