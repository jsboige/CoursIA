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

import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_testpaths_coverage import (  # noqa: E402
    CI_EXCLUDED_BASELINE,
    ENTRY_POINT_WORKFLOW,
    REPO_ROOT,
    WORKFLOW_COVERAGE,
    _partition_run_blocks,
    check_namespace_option,
    collectible_item_count,
    discover_suites,
    excluded_population,
    extract_run_targets,
    file_coverage,
    is_covered,
    is_test_file_name,
    load_ci_excluded,
    load_testpaths,
    missing_declared_suites,
    plan_problems,
    ratchet_problems,
    uncovered_suites,
    verify_declared_test_cwd,
)

import check_testpaths_coverage as ctc  # noqa: E402


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


def test_extract_run_targets_retire_les_guillemets() -> None:
    """Une cible entre guillemets est une cible (#26759, revue du coordinateur).

    Le job `adk-contracts` de `scripts-tests.yml` cite ses deux cibles entre
    guillemets : sans retrait des guillemets, elles sortaient « NON JOUÉE »
    alors que la CI les joue.
    """
    text = """        run: |
          pytest \\
            "scripts/tests/test_adk_runtime_contracts.py" \\
            'config/test_providers.py' \\
            --tb=short -q
"""
    targets = extract_run_targets(text)
    assert "scripts/tests/test_adk_runtime_contracts.py" in targets
    assert "config/test_providers.py" in targets
    assert '"scripts/tests/test_adk_runtime_contracts.py"' not in targets
    assert "'config/test_providers.py'" not in targets


def test_les_cibles_du_job_adk_sont_reconnues_sur_le_workflow_reel() -> None:
    """Contrôle positif sur le workflow réel : les deux cibles existent.

    Sans ce test, le retrait des guillemets pourrait casser la détection
    sans qu'aucune cible réelle ne soit vérifiée.
    """
    wf = (REPO_ROOT / ".github/workflows/scripts-tests.yml").read_text(encoding="utf-8")
    targets = extract_run_targets(wf)
    assert ("MyIA.AI.Notebooks/ML/DataScienceWithAgents/"
            "07-Orchestration-d-Agents/utils/test_adk_runtime_contracts.py") in targets
    assert ("MyIA.AI.Notebooks/ML/DataScienceWithAgents/"
            "07-Orchestration-d-Agents/config/test_providers.py") in targets


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
    # Critère 1 de #25366 : `tests` racine est joué par le run pytest partagé
    # de scripts-tests.yml et déclaré dans WORKFLOW_COVERAGE (T0). Il est donc
    # DANS les testpaths — un pytest lancé à la main voit ce que la CI voit.
    # (Il en avait été retiré quand le répertoire était un reliquat vide.)
    assert "tests" in testpaths
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
# dessus (cas mesure : SymbolicAI/ArgumentAnalysis, 174 tests non collectes).
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
    """Sans `--strict`, un trou d'inventaire n'est pas un echec : il est
    liste. Depuis T4 (#25366), le RETOUR porte la liste dans les deux
    modes — le drapeau ne change que l'impression (INFO vs FAIL) et le
    verdict, portés par main()."""
    from check_testpaths_coverage import run_inventory

    (tmp_path / "scripts" / "beta" / "tests").mkdir(parents=True)
    (tmp_path / "scripts" / "beta" / "tests" / "test_b.py").write_text("", encoding="utf-8")

    assert run_inventory(tmp_path, [], {}, strict=False) == ["scripts/beta/tests"]
    assert run_inventory(tmp_path, [], {}, strict=True) == ["scripts/beta/tests"]


def test_run_inventory_une_cible_dossier_de_workflow_couvre(tmp_path: Path) -> None:
    """Controle positif : un dossier joue par un workflow dedie ne sort pas.

    C'est le defaut fondateur de #23648 : l'inventaire ne lisait que
    `pytest.ini` et annoncait comme non surveillees des suites qu'un workflow
    joue, dont `Geometry/tests` qui figure pourtant dans WORKFLOW_COVERAGE.
    """
    from check_testpaths_coverage import run_inventory

    _make_suite(tmp_path, "MyIA.AI.Notebooks/Geometry/tests")
    _make_suite(tmp_path, "scripts/beta/tests")

    unwatched = run_inventory(
        tmp_path,
        [],
        {},
        strict=True,
        workflow_coverage={"w.yml": ["MyIA.AI.Notebooks/Geometry/tests"]},
        workflow_test_cwd={},
    )

    assert unwatched == ["scripts/beta/tests"]


def test_run_inventory_un_perimetre_test_cwd_couvre(tmp_path: Path) -> None:
    """Un perimetre `test-cwd` declare couvre le dossier qu'il designe."""
    from check_testpaths_coverage import run_inventory

    _make_suite(tmp_path, "MyIA.AI.Notebooks/IIT/ICT-Series/tests")
    _make_suite(tmp_path, "MyIA.AI.Notebooks/IIT/ICT-Series/scripts/tests")

    unwatched = run_inventory(
        tmp_path,
        [],
        {},
        strict=True,
        workflow_coverage={},
        workflow_test_cwd={"ict-tests.yml": ["MyIA.AI.Notebooks/IIT/ICT-Series/tests"]},
    )

    assert unwatched == ["MyIA.AI.Notebooks/IIT/ICT-Series/scripts/tests"]


def test_run_inventory_une_cible_fichier_rend_partiellement_surveille(
    tmp_path: Path,
) -> None:
    """Une cible-fichier dedans ne couvre pas le dossier, mais l'en retire pas.

    Le dossier n'est pas declare couvert (les autres tests du dossier ne
    tournent pas), il n'est pas declare trou non plus (un test tourne) : le
    sortir comme l'un ou l'autre affirmerait plus que la mesure.
    """
    from check_testpaths_coverage import run_inventory

    _make_suite(tmp_path, "MyIA.AI.Notebooks/Sudoku/tests")

    unwatched = run_inventory(
        tmp_path,
        [],
        {},
        strict=True,
        workflow_coverage={"w.yml": ["MyIA.AI.Notebooks/Sudoku/tests/test_dlx.py"]},
        workflow_test_cwd={},
    )

    assert unwatched == []


def _make_matrix_workflow(root: Path, cwd: str, args: str) -> None:
    """Pose un workflow a matrice portant un couple test-cwd / test-args."""
    wf_dir = root / ".github" / "workflows"
    wf_dir.mkdir(parents=True, exist_ok=True)
    (wf_dir / "w.yml").write_text(
        "name: t\non: [push]\njobs:\n  t:\n    strategy:\n      matrix:\n"
        "        include:\n"
        f"          - test-cwd: {cwd}\n"
        f'            test-args: "{args}"\n',
        encoding="utf-8",
    )


def test_verify_declared_test_cwd_accepte_la_jointure(tmp_path: Path) -> None:
    """Le perimetre se valide par le `test-cwd` ou par la jointure cwd/args."""
    from check_testpaths_coverage import verify_declared_test_cwd

    _make_matrix_workflow(tmp_path, "S/tests", ".")
    assert (
        verify_declared_test_cwd(
            tmp_path, False, test_cwd={".github/workflows/w.yml": ["S/tests"]}
        )
        == []
    )

    (tmp_path / ".github" / "workflows" / "w.yml").unlink()
    _make_matrix_workflow(tmp_path, "S", "tests")
    assert (
        verify_declared_test_cwd(
            tmp_path, False, test_cwd={".github/workflows/w.yml": ["S/tests"]}
        )
        == []
    )


def test_verify_declared_test_cwd_rougit_sur_un_perimetre_absent(
    tmp_path: Path,
) -> None:
    """Un perimetre declare que le workflow ne joue plus est une derive."""
    from check_testpaths_coverage import verify_declared_test_cwd

    _make_matrix_workflow(tmp_path, "S/tests", ".")

    problems = verify_declared_test_cwd(
        tmp_path, False, test_cwd={".github/workflows/w.yml": ["S/other/tests"]}
    )

    assert len(problems) == 1
    assert "S/other/tests" in problems[0]
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


def _jeux_de_labels_runs_on(runs_on: object) -> list[list[str]]:
    """Jeux de labels vises par un `runs-on`, dans l'ordre d'apparition.

    La forme statique est une liste ; la forme hybride auditee (#26386) est une
    expression a deux jambes :

        ${{ (GARD) && fromJSON('["..."]') || fromJSON('["..."]') }}

    Les deux lectures renvoient la meme structure, ce qui permet d'asserter les
    jambes -- et non la chaine entiere.
    """
    if isinstance(runs_on, list):
        return [[str(label) for label in runs_on]]
    expression = str(runs_on)
    return [
        [str(label) for label in json.loads(jeu)]
        for jeu in re.findall(r"fromJSON\(\s*'(\[[^\]]*\])'\s*\)", expression)
    ]


def test_scripts_workflow_triggers_native_decide_changes_without_scoping_main_pushes() -> None:
    """The Conway ratchet must run for its own source changes on PRs and main.

    Main pushes are intentionally unfiltered for #24828's red-main sentinel;
    pull requests retain the scoped trigger, including the native_decide subject.
    """
    yaml = __import__("pytest").importorskip("yaml")
    wf_path = REPO_ROOT / ".github/workflows/scripts-tests.yml"
    with wf_path.open(encoding="utf-8") as fh:
        workflow = yaml.load(fh, Loader=yaml.BaseLoader)

    triggers = workflow["on"]
    assert "paths" not in triggers["push"]
    pr_paths = triggers["pull_request"]["paths"]
    assert "MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean/**.lean" in pr_paths
    # Keep both the original ADK contracts tree and the #25201 refactor target.
    assert "MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/**" in pr_paths
    assert "MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/**" in pr_paths

    job = workflow["jobs"]["scripts-tests"]
    assert job["name"] == "Scripts Tests (CPU)"
    # Le job reste sur le parc auto-heberge. Depuis #26386 le `runs-on` est une
    # forme hybride auditee : la jambe `push` vise le slot reserve de main
    # {self-hosted, coursia-main, coursia-linux}, le repli vise le pool des PR
    # {self-hosted, coursia-ephemeral, coursia-linux}. Depuis #21978 une jambe
    # LOURDE ({self-hosted, coursia-persistent, coursia-linux}) peut
    # s'intercaler entre les deux : elle n'est atteinte que si un operateur
    # pose la variable de depot `CI_HEAVY_PERSISTENT` (absente par defaut),
    # et sa forme est auditee par
    # `scripts/ci/check_self_hosted_runner_policy.py`.
    # On asserte les JAMBES (leur role et leur ordre), pas la chaine entiere :
    # le repli ne peut pas glisser vers `ubuntu-latest`, et une jambe
    # intermediaire ne peut pas ouvrir un pool non declare.
    MAIN_SLOT = ["self-hosted", "coursia-main", "coursia-linux"]
    PR_POOL = ["self-hosted", "coursia-ephemeral", "coursia-linux"]
    HEAVY_FAMILY = ["self-hosted", "coursia-persistent", "coursia-linux"]
    runs_on = job["runs-on"]
    if isinstance(runs_on, list):
        assert runs_on == PR_POOL
    else:
        assert "github.event_name == 'push'" in str(runs_on), (
            "la forme hybride doit rester gardee par l'evenement -- sans la "
            "garde, la jambe du slot reserve de main serait atteinte par toute PR"
        )
        jeux = _jeux_de_labels_runs_on(runs_on)
        assert jeux[0] == MAIN_SLOT, (
            "la premiere jambe est le slot reserve de main -- la chaine "
            f"commence par {jeux[0]}"
        )
        assert jeux[-1] == PR_POOL, (
            "la derniere jambe est le repli sur le pool des PR -- le repli "
            f"est {jeux[-1]}"
        )
        for jambe in jeux[1:-1]:
            assert jambe == HEAVY_FAMILY, (
                "une jambe intermediaire ne peut viser que la famille "
                f"lourde auditee -- trouve {jambe}"
            )


def test_adk_job_targets_existing_refactor_files_for_run_and_collection() -> None:
    """The ADK steps must execute and collect tests from their live tree."""
    import pytest

    yaml = pytest.importorskip("yaml")
    wf_path = REPO_ROOT / ".github/workflows/scripts-tests.yml"
    with wf_path.open(encoding="utf-8") as fh:
        workflow = yaml.load(fh, Loader=yaml.BaseLoader)

    steps = workflow["jobs"]["adk-contracts"]["steps"]
    runs = "\n".join(step.get("run", "") for step in steps)
    root = "MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents"
    contract = f"{root}/utils/test_adk_runtime_contracts.py"
    providers = f"{root}/config/test_providers.py"
    assert runs.count(contract) == 2, "runtime contract run and collection floor must target the live tree"
    assert runs.count(providers) == 2, "provider test run and collection floor must target the live tree"
    assert "Track2-GoogleADK" not in runs
    assert (REPO_ROOT / contract).is_file()
    assert (REPO_ROOT / providers).is_file()
# --- #25366 T0 : basenames dupliqués + convergence CI -> testpaths ----------
#
# Cinquième sens : deux répertoires de tests découverts qui portent le même
# basename de module obligent tout le dépôt à `--import-mode importlib`
# (le workflow le documente comme load-bearing à cause de ces doublons).
# Sixième sens : une cible-dossier CI absente des testpaths est invisible
# d'un `pytest` racine — l'inverse du sens historique. T0 rend ces deux
# mesures possibles et strict par défaut sous `--inventory` ; T1/T2 trient
# la dette, T4 câble les sens dans la garde CI.


def test_duplicate_basenames_detecte_la_collision(tmp_path: Path) -> None:
    """Deux suites découvertes portant le même module sont signalées."""
    from check_testpaths_coverage import duplicate_basenames

    _make_suite(tmp_path, "scripts/alpha/tests")
    _make_suite(tmp_path, "scripts/beta/tests")

    assert duplicate_basenames(tmp_path) == {
        "test_x.py": ["scripts/alpha/tests", "scripts/beta/tests"]
    }


def test_duplicate_basenames_compte_les_modules_dappui(tmp_path: Path) -> None:
    """Un module d'appui non-test compte autant : c'est lui aussi un nom de
    module top-level en collision (cas mesuré : `scan_slidev_composition`,
    cité sans préfixe test_ par le commentaire du run partagé)."""
    from check_testpaths_coverage import duplicate_basenames

    _make_suite(tmp_path, "scripts/alpha/tests")
    _make_suite(tmp_path, "scripts/beta/tests")
    # Des noms de test distincts : seule la collision helpers.py doit sortir.
    (tmp_path / "scripts/alpha/tests/test_x.py").unlink()
    (tmp_path / "scripts/beta/tests/test_x.py").unlink()
    (tmp_path / "scripts/alpha/tests/test_a.py").write_text("", encoding="utf-8")
    (tmp_path / "scripts/beta/tests/test_b.py").write_text("", encoding="utf-8")
    (tmp_path / "scripts/alpha/tests/helpers.py").write_text("", encoding="utf-8")
    (tmp_path / "scripts/beta/tests/helpers.py").write_text("", encoding="utf-8")

    assert duplicate_basenames(tmp_path) == {
        "helpers.py": ["scripts/alpha/tests", "scripts/beta/tests"]
    }


def test_duplicate_basenames_exempte_init_et_conftest(tmp_path: Path) -> None:
    """`__init__.py` (marqueur de paquet) et `conftest.py` (spécial-casé par
    pytest) ne créent pas de collision — critère 3 de #25366 les excepte."""
    from check_testpaths_coverage import duplicate_basenames

    _make_suite(tmp_path, "scripts/alpha/tests")
    _make_suite(tmp_path, "scripts/beta/tests")
    (tmp_path / "scripts/alpha/tests/test_x.py").unlink()
    (tmp_path / "scripts/beta/tests/test_x.py").unlink()
    (tmp_path / "scripts/alpha/tests/test_a.py").write_text("", encoding="utf-8")
    (tmp_path / "scripts/beta/tests/test_b.py").write_text("", encoding="utf-8")
    for rel in ("scripts/alpha/tests", "scripts/beta/tests"):
        for name in ("__init__.py", "conftest.py"):
            (tmp_path / rel / name).write_text("", encoding="utf-8")

    assert duplicate_basenames(tmp_path) == {}


def test_duplicate_basenames_ne_compte_que_les_enfants_directs(
    tmp_path: Path,
) -> None:
    """Un fichier dans un sous-dossier non découvert ne collisionne pas au
    niveau du parent : seuls les enfants directs des répertoires découverts
    entrent en collision comme modules top-level."""
    from check_testpaths_coverage import duplicate_basenames

    _make_suite(tmp_path, "scripts/alpha/tests")
    _make_suite(tmp_path, "scripts/beta/tests")
    (tmp_path / "scripts/alpha/tests/test_x.py").unlink()
    (tmp_path / "scripts/alpha/tests/test_a.py").write_text("", encoding="utf-8")
    (tmp_path / "scripts/alpha/tests/unit").mkdir()
    (tmp_path / "scripts/alpha/tests/unit/test_b.py").write_text("", encoding="utf-8")

    assert duplicate_basenames(tmp_path) == {}


def test_duplicate_basenames_plafond_sur_main_actuel() -> None:
    """Contrôle positif sur le dépôt réel : le sens voit la dette connue.

    1 basename restant sur cet arbre, mesuré après la fusion des deux tranches
    (#25366 ; T2 #26137 a retiré `tests/test_batch_reexecute.py` racine ;
    T2 #26541 a préfixé 10 basenames génériques ; T2-residu #27066 a renommé
    les copies stratégiques, retire `test_check_cell_source_parses.py` et
    `test_check_public_anchor.py` ; T2 ICT a préfixé les 16 paires du hub
    série ICT). Chaque tranche abaisse le plafond de son propre côté ; le
    survivant `test_utils.py` est porté par deux projets-exemples Vibe-Coding,
    qui sont des données de démonstration et non des suites du dépôt. Le
    plafond est un cliquet inversé : il rougit sur un doublon NOUVEAU, verdit
    quand T2 en supprime — jamais l'inverse.
    """
    from check_testpaths_coverage import duplicate_basenames

    dupes = duplicate_basenames(REPO_ROOT)
    assert len(dupes) <= 1, f"dette de doublons en hausse : {len(dupes)} > 1"
    assert "test_check_cell_source_parses.py" not in dupes
    assert "test_utils.py" in dupes
    assert len(dupes["test_utils.py"]) == 2


def test_discover_test_dirs_voit_la_racine_tests(tmp_path: Path) -> None:
    """#25366 T0 : `tests/` à la racine du dépôt fait partie de l'inventaire."""
    from check_testpaths_coverage import discover_test_dirs

    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "test_r.py").write_text("", encoding="utf-8")
    _make_suite(tmp_path, "scripts/alpha/tests")

    assert discover_test_dirs(tmp_path) == ["scripts/alpha/tests", "tests"]


def test_coverage_without_testpaths_vert_sur_la_racine_tests() -> None:
    """Critère 1 de #25366, tranché en T1 : `tests` (racine) est joué par le
    run partagé de la CI ET déclaré dans les testpaths — un pytest lancé à la
    main voit ce que la CI voit, le trou le plus étroit est fermé.

    Contrôle de non-régression : si une cible-dossier jouée par la CI ressort
    des testpaths (retrait de l'entrée ou de sa déclaration), ce test rougit.
    """
    from check_testpaths_coverage import coverage_without_testpaths

    testpaths = load_testpaths(REPO_ROOT / "pytest.ini")
    excluded = load_ci_excluded(REPO_ROOT)

    assert "tests" in testpaths
    assert coverage_without_testpaths(testpaths, excluded) == []


def test_coverage_without_testpaths_vert_quand_declare(tmp_path: Path) -> None:
    """Une cible-dossier dans les testpaths ne sort pas ; une cible-fichier
    n'est pas concernée ; une exclusion écrite compte comme triée."""
    from check_testpaths_coverage import coverage_without_testpaths

    coverage = {
        "w.yml": ["scripts/alpha/tests", "Sudoku/tests/test_dlx.py"]
    }

    assert coverage_without_testpaths(["scripts/alpha/tests"], {}, coverage) == []
    assert coverage_without_testpaths(["scripts/other/tests"], {}, coverage) == [
        "scripts/alpha/tests"
    ]
    assert (
        coverage_without_testpaths(
            [], {"scripts/alpha/tests": "motif ecrit"}, coverage
        )
        == []
    )


def test_cli_inventory_est_strict_par_defaut(tmp_path: Path) -> None:
    """#25366 T0 : sans drapeau, --inventory marque les trous FAIL ; avec
    --advisory, il les marque INFO (le downgrade se voit dans la sortie)."""
    import subprocess

    _make_suite(tmp_path, "scripts/beta/tests")
    (tmp_path / "pytest.ini").write_text(
        "[pytest]\ntestpaths =\n    scripts/alpha/tests\n", encoding="utf-8"
    )

    def _run(*flags: str) -> str:
        proc = subprocess.run(
            [sys.executable, str(REPO_ROOT / "scripts/check_testpaths_coverage.py"),
             "--repo-root", str(tmp_path), "--inventory", *flags],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
        )
        return proc.stdout

    assert "FAIL scripts/beta/tests" in _run()
    assert "INFO scripts/beta/tests" in _run("--advisory")


def test_cli_inventory_advisory_est_vert_sur_main() -> None:
    """Sur le dépôt réel, la dette connue (répertoires hors CI et basenames
    dupliqués) listée en advisory ne fait pas échouer : c'est le mode mesure
    de T1/T2, exit 0 garanti.

    Depuis T1 (#25366), `tests` racine n'est plus un trou : il est dans les
    testpaths, donc la ligne de convergence ne le liste plus.
    """
    import subprocess

    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "scripts/check_testpaths_coverage.py"),
         "--repo-root", str(REPO_ROOT), "--inventory", "--advisory"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert proc.returncode == 0, proc.stdout
    assert "\n  INFO tests\n" not in proc.stdout
    assert "FAIL" not in proc.stdout


# --- #25366 T4 : le ratchet — dette connue tolérée, NOUVEAU refusé ---


def test_write_load_baseline_roundtrip(tmp_path: Path) -> None:
    """Baseline : écriture/relecture fidèles, absente ou mal formée = SystemExit."""
    import pytest

    from check_testpaths_coverage import (
        load_inventory_baseline,
        write_inventory_baseline,
    )

    bl = tmp_path / "baseline.json"
    write_inventory_baseline(
        bl,
        ["a/tests"],
        {"t.py": ["a/tests", "b/tests"]},
        ["old/tests/test_a.py"],
    )
    data = load_inventory_baseline(bl)
    assert data["unwatched"] == ["a/tests"]
    assert data["duplicate_basenames"] == {"t.py": ["a/tests", "b/tests"]}
    assert data["unplayed"] == ["old/tests/test_a.py"]

    with pytest.raises(SystemExit):
        load_inventory_baseline(tmp_path / "absente.json")
    (tmp_path / "malformee.json").write_text('{"unwatched": 3}', encoding="utf-8")
    with pytest.raises(SystemExit):
        load_inventory_baseline(tmp_path / "malformee.json")


def _baseline_dette_connue() -> dict:
    return {
        "unwatched": ["orphan/tests"],
        "duplicate_basenames": {"t.py": ["a/tests", "b/tests"]},
        "unplayed": ["old/tests/test_a.py"],
    }


def test_judge_tolere_la_dette_connue() -> None:
    """Findings strictement égaux à la baseline : zéro échec."""
    from check_testpaths_coverage import judge_inventory_against_baseline

    assert (
        judge_inventory_against_baseline(
            ["orphan/tests"],
            {"t.py": ["a/tests", "b/tests"]},
            ["old/tests/test_a.py"],
            _baseline_dette_connue(),
        )
        == []
    )


def test_judge_rougit_sur_doublon_nouveau() -> None:
    from check_testpaths_coverage import judge_inventory_against_baseline

    failures = judge_inventory_against_baseline(
        [],
        {"new.py": ["x/tests", "y/tests"]},
        [],
        _baseline_dette_connue(),
    )
    assert any("NOUVEAU" in f and "new.py" in f for f in failures)


def test_judge_rougit_sur_croissance_laterale() -> None:
    """Un TROISIÈME répertoire sur un doublon connu rougit — le simple compte
    de basenames (plafond T0) ne le voyait pas : la dette restait à 30."""
    from check_testpaths_coverage import judge_inventory_against_baseline

    failures = judge_inventory_against_baseline(
        [],
        {"t.py": ["a/tests", "b/tests", "c/tests"]},
        [],
        _baseline_dette_connue(),
    )
    assert any("CROISSANCE" in f and "c/tests" in f for f in failures)


def test_judge_rougit_sur_dossier_non_trie_nouveau() -> None:
    from check_testpaths_coverage import judge_inventory_against_baseline

    failures = judge_inventory_against_baseline(
        ["orphan/tests", "newcomer/tests"], {}, [], _baseline_dette_connue()
    )
    assert any("non trié" in f and "newcomer/tests" in f for f in failures)
    assert not any("orphan/tests" in f for f in failures)


def test_judge_tolere_le_retrait_partiel() -> None:
    """T2 en cours : retirer une copie d'un doublon connu verdit (sous-ensemble)."""
    from check_testpaths_coverage import judge_inventory_against_baseline

    failures = judge_inventory_against_baseline(
        [], {"t.py": ["a/tests"]}, [], _baseline_dette_connue()
    )
    assert failures == []


# ---------------------------------------------------------------------------
# #26736 : septième sens (couverture par fichier) et huitième sens
# (cliquet sur la population CI-EXCLUDED + plan de remédiation).
# ---------------------------------------------------------------------------


def _make_test_module(root: Path, rel: str, items: int = 1) -> Path:
    """Pose un fichier de test portant `items` items collectibles."""
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    body = "\n".join(f"def test_x{i}():\n    assert True" for i in range(items))
    path.write_text(body + "\n", encoding="utf-8")
    return path


def test_is_test_file_name_suit_les_motifs_pytest_par_defaut() -> None:
    """pytest.ini ne fixe pas `python_files` : les motifs par défaut
    s'appliquent — `test_*.py` ET `*_test.py` (les deux camps du dépôt)."""
    assert is_test_file_name("test_alpha.py")
    assert is_test_file_name("alpha_test.py")
    assert not is_test_file_name("alpha.py")
    assert not is_test_file_name("conftest.py")


def test_collectible_item_count_compte_les_items_pytest(tmp_path: Path) -> None:
    """Un item collectible = fonction `test_*` (async comprise) ou classe
    `Test*`. Un helper sans `test_` ne compte pas."""
    path = tmp_path / "probe.py"
    path.write_text(
        "def test_a():\n    pass\n\n\n"
        "async def test_b():\n    pass\n\n\n"
        "class TestC:\n    pass\n\n\n"
        "def helper():\n    pass\n",
        encoding="utf-8",
    )
    assert collectible_item_count(path) == 3


def test_file_coverage_signale_un_fichier_qu_aucune_jambe_ne_collecte(
    tmp_path: Path,
) -> None:
    """Le septième sens descend au niveau du FICHIER : un test co-localisé
    avec du code, dans un répertoire que rien ne joue, est nommé."""
    _make_test_module(
        tmp_path, "MyIA.AI.Notebooks/Serie/tests/test_gateway.py", items=2
    )
    coverage = file_coverage(tmp_path, {})
    assert coverage["collected"] == 0
    paths = [f["path"] for f in coverage["unplayed"]]
    assert paths == ["MyIA.AI.Notebooks/Serie/tests/test_gateway.py"]
    finding = coverage["unplayed"][0]
    assert finding["items"] == 2
    # A defaut de jambe candidate, l'organe nomme le point d'entree unique.
    assert finding["candidates"] == [ENTRY_POINT_WORKFLOW]


def test_file_coverage_ne_signale_pas_un_fichier_joue_par_une_cible_dossier(
    tmp_path: Path,
) -> None:
    """Un fichier sous la cible-dossier d'un workflow est joue : il ne doit
    pas apparaitre dans la population non jouee."""
    _make_test_module(tmp_path, "MyIA.AI.Notebooks/Serie/tests/test_a.py")
    _make_workflow(tmp_path, ["MyIA.AI.Notebooks/Serie/tests"])
    coverage = file_coverage(tmp_path, {})
    assert coverage["unplayed"] == []
    assert coverage["collected"] == 1


def test_file_coverage_compte_la_population_exclue_a_part(
    tmp_path: Path,
) -> None:
    """Un fichier sous un chemin CI-EXCLUDED n'est pas « non joue » : il est
    DECLARE exclu, donc connu, et compte par le cliquet."""
    _make_test_module(tmp_path, "MyIA.AI.Notebooks/Serie/tests/test_a.py")
    excluded = {"MyIA.AI.Notebooks/Serie/tests": "raison mesuree"}
    coverage = file_coverage(tmp_path, excluded)
    assert coverage["unplayed"] == []
    assert coverage["excluded"] == 1


def test_excluded_population_compte_marqueurs_fichiers_et_items(
    tmp_path: Path,
) -> None:
    """La population reellement exclue est comptee en trois grandeurs."""
    _make_test_module(tmp_path, "MyIA.AI.Notebooks/Serie/tests/test_a.py", items=3)
    excluded = {"MyIA.AI.Notebooks/Serie/tests": "raison"}
    population = excluded_population(tmp_path, excluded)
    assert population["marqueurs"] == 1
    assert population["fichiers"] == 1
    assert population["items"] == 3
    assert population["orphelins"] == []


def test_excluded_population_signale_un_marqueur_orphelin(
    tmp_path: Path,
) -> None:
    """Un marqueur dont le chemin n'existe plus n'exclut plus rien : il est
    signale (le marqueur se reecrit dans le workflow, pas dans cet organe)."""
    excluded = {"MyIA.AI.Notebooks/Serie/renommee/tests": "raison"}
    population = excluded_population(tmp_path, excluded)
    assert population["orphelins"] == ["MyIA.AI.Notebooks/Serie/renommee/tests"]
    assert population["fichiers"] == 0


def test_ratchet_rougit_des_que_la_population_croit() -> None:
    """Le cliquet mord sur le COMPTE, pas sur la presence du marqueur."""
    population = {
        "marqueurs": CI_EXCLUDED_BASELINE["marqueurs"],
        "fichiers": CI_EXCLUDED_BASELINE["fichiers"],
        "items": CI_EXCLUDED_BASELINE["items"] + 1,
    }
    problems = ratchet_problems(population)
    assert problems, "une hausse de la population doit etre signalee"
    assert "items" in problems[0]


def test_ratchet_est_vert_au_niveau_de_reference() -> None:
    """A la baseline, le cliquet ne dit rien."""
    assert ratchet_problems(dict(CI_EXCLUDED_BASELINE)) == []


def test_ratchet_ne_rougit_pas_sur_une_baisse() -> None:
    """Une baisse est une bonne nouvelle (une exclusion levee) : elle ne
    bloque pas, elle invite a rebaseliner."""
    population = {
        "marqueurs": CI_EXCLUDED_BASELINE["marqueurs"] - 1,
        "fichiers": CI_EXCLUDED_BASELINE["fichiers"],
        "items": CI_EXCLUDED_BASELINE["items"],
    }
    assert ratchet_problems(population) == []


def test_plan_signale_une_exclusion_sans_cible_declaree(
    monkeypatch,
) -> None:
    """Chaque exclusion declare sa cible de remediation : une exclusion
    muette n'a pas de chemin de sortie."""
    monkeypatch.setattr(ctc, "CI_EXCLUDED_PLAN", {})
    problems = plan_problems({"MyIA.AI.Notebooks/Serie/tests": "raison"})
    assert problems
    assert "MyIA.AI.Notebooks/Serie/tests" in problems[0]


def test_plan_signale_une_cible_sans_exclusion(monkeypatch) -> None:
    """Reciproquement, une cible declaree pour une exclusion absente est
    une derive du plan."""
    monkeypatch.setattr(
        ctc, "CI_EXCLUDED_PLAN", {"MyIA.AI.Notebooks/Serie/tests": "quotidien"}
    )
    problems = plan_problems({})
    assert problems
    assert "MyIA.AI.Notebooks/Serie/tests" in problems[0]


def test_plan_signale_une_cible_inconnue(monkeypatch) -> None:
    """Une cible hors enumeration est une faute de frappe, pas une cible."""
    monkeypatch.setattr(
        ctc, "CI_EXCLUDED_PLAN", {"MyIA.AI.Notebooks/Serie/tests": "demain"}
    )
    problems = plan_problems({"MyIA.AI.Notebooks/Serie/tests": "raison"})
    assert problems
    assert "inconnue" in problems[0]


def test_plan_couvre_toutes_les_exclusions_reelles_du_depot() -> None:
    """Sur le depot reel, chaque marqueur CI-EXCLUDED a une cible declaree :
    le plan ne laisse aucun orphan de remediation."""
    excluded = load_ci_excluded(REPO_ROOT)
    assert excluded, "le depot doit porter des marqueurs CI-EXCLUDED"
    assert plan_problems(excluded) == []


def test_population_reelle_ne_depasse_pas_la_baseline() -> None:
    """Le cliquet est mesure sur le depot reel : la population exclue ne
    doit pas depasser la baseline enregistree."""
    excluded = load_ci_excluded(REPO_ROOT)
    population = excluded_population(REPO_ROOT, excluded)
    assert population["marqueurs"] == CI_EXCLUDED_BASELINE["marqueurs"]
    assert population["fichiers"] <= CI_EXCLUDED_BASELINE["fichiers"]
    assert population["items"] <= CI_EXCLUDED_BASELINE["items"]
    assert ratchet_problems(population) == []


def test_invocation_simple_reste_verte_sur_le_depot_reel() -> None:
    """L'organe tourne dans une jambe DEJA PAYEE (voie rapide) : le cliquet
    est bloquant, mais la dette de couverture par fichier reste advisory.
    L'invocation simple doit donc rendre 0 sur le depot reel."""
    import subprocess

    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "scripts/check_testpaths_coverage.py"),
         "--repo-root", str(REPO_ROOT)],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert proc.returncode == 0, proc.stdout
    assert "Population CI-EXCLUDED" in proc.stdout


def test_judge_rougit_sur_fichier_non_collecte_nouveau() -> None:
    """#26759 rend le sens fichier strict sous --inventory : depuis cette
    PR, le juge T4 couvre aussi ce sens — un fichier de test que la
    baseline ne connaît pas rougit, un fichier connu est toléré."""
    from check_testpaths_coverage import judge_inventory_against_baseline

    failures = judge_inventory_against_baseline(
        [],
        {},
        ["old/tests/test_a.py", "fresh/tests/test_new.py"],
        _baseline_dette_connue(),
    )
    assert any(
        "NOUVEAU" in f and "fresh/tests/test_new.py" in f for f in failures
    )
    assert not any("old/tests/test_a.py" in f for f in failures)


def test_cli_ratchet_vert_sur_main_avec_baseline() -> None:
    """Contrôle sur le dépôt réel : la dette committée est tolérée (rc 0).

    C'est l'invocation exacte que la fast lane rend (T4 #25366). Si ce test
    rougit sur une PR, l'arbre porte un finding NOUVEAU — ou, sur main, une
    baseline périmée qu'une tranche T1/T2 a fait rétrécir sans la régénérer.
    """
    import subprocess

    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "scripts/check_testpaths_coverage.py"),
         "--repo-root", str(REPO_ROOT), "--inventory",
         "--baseline", "scripts/tests/baseline_testpaths_inventory.json"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=str(REPO_ROOT),
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr

def test_cli_ratchet_baseline_manquante_est_rouge() -> None:
    """Une baseline absente ne rend jamais la garde muette : rouge explicite."""
    import subprocess

    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "scripts/check_testpaths_coverage.py"),
         "--repo-root", str(REPO_ROOT), "--inventory",
         "--baseline", "scripts/tests/inexistante.json"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=str(REPO_ROOT),
    )
    assert proc.returncode != 0
    assert "baseline ratchet introuvable" in (proc.stdout + proc.stderr)


def test_cli_ratchet_rougit_sur_un_doublon_nouveau(tmp_path: Path) -> None:
    """Contrôle positif bout-en-bout : doublon ajouté après baseline -> rouge."""
    import subprocess

    (tmp_path / "scripts" / "alpha" / "tests").mkdir(parents=True)
    (tmp_path / "scripts" / "alpha" / "tests" / "test_shared.py").write_text(
        "", encoding="utf-8"
    )
    (tmp_path / "scripts" / "gamma" / "tests").mkdir(parents=True)
    (tmp_path / "scripts" / "gamma" / "tests" / "test_shared.py").write_text(
        "", encoding="utf-8"
    )
    (tmp_path / "pytest.ini").write_text(
        "[pytest]\ntestpaths =\n    scripts/alpha/tests\n", encoding="utf-8"
    )
    bl = tmp_path / "baseline.json"

    def _run() -> "subprocess.CompletedProcess[str]":
        return subprocess.run(
            [sys.executable, str(REPO_ROOT / "scripts/check_testpaths_coverage.py"),
             "--repo-root", str(tmp_path), "--inventory",
             "--baseline", str(bl)],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
        )

    write = subprocess.run(
        [sys.executable, str(REPO_ROOT / "scripts/check_testpaths_coverage.py"),
         "--repo-root", str(tmp_path), "--inventory", "--write-baseline", str(bl)],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert write.returncode == 0, write.stdout + write.stderr
    # Le rc du run intermediaire n'est pas l'objet : sur un depot minimal,
    # les QUATRE SENS HISTORIQUES rougissent aussi (testpath non couvert,
    # option namespace absente). Ce que T4 garantit ici, c'est la section
    # ratchet : la dette enregistree est toleree, aucun finding nouveau.
    green = _run()
    assert "aucun finding nouveau" in green.stdout
    assert "NOUVEAU" not in green.stdout

    (tmp_path / "scripts" / "d1" / "tests").mkdir(parents=True)
    (tmp_path / "scripts" / "d1" / "tests" / "test_brand.py").write_text(
        "", encoding="utf-8"
    )
    (tmp_path / "scripts" / "d2" / "tests").mkdir(parents=True)
    (tmp_path / "scripts" / "d2" / "tests" / "test_brand.py").write_text(
        "", encoding="utf-8"
    )
    red = _run()
    assert red.returncode == 1
    # Sous-chaines ASCII uniquement : le stdout capture depend de l'encodage
    # console de l'enfant (cp1252 sur ce siege, utf-8 sur le runner), les
    # accents ne traversent pas les deux mondes de facon stable.
    assert "NOUVEAU" in red.stdout
    assert "test_brand.py" in red.stdout
    assert "d1/tests" in red.stdout and "d2/tests" in red.stdout
