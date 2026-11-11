"""Tests de `changed_scripts_tests` (#22468 tranche 4).

Contrat verifie ici, dans cet ordre :

1. **controle positif** : un diff de PR qui touche un module d'une suite
   rend une portee restreinte (suite specifique + suite generique
   ``scripts/tests``), dans l'ordre du workflow ;
2. **garde-fou de la tranche** : workflow, pytest.ini, conftest.py, script
   d'install, chien de garde et l'organe lui-meme forcent la pleine suite ;
3. **fail-open** : lecteurs en echec -> pleine suite avec raisons nommees ;
   chemins hors table -> pleine suite ; portee restreinte vide -> pleine
   suite ; workflow_dispatch -> pleine suite sans lire le diff ;
4. **aires de veille** : derivation parent (suite X/tests veille X/),
   overrides (suite racine tests, suites fichiers agent_tests/v4/gateway),
   selecteur additionnel du registre arxiv (#17850) ;
5. **CLI** : JSON sur stdout, raison sur stderr, rc 2 bruyant quand le bloc
   pytest du workflow est illisible (meme semantique que guard_test_root
   #19026 -- jamais de liste inventee).
"""
import importlib.util
import sys
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "changed_scripts_tests",
    Path(__file__).resolve().parents[1] / "changed_scripts_tests.py",
)
mod = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(mod)

# Extrait representatif de la liste du workflow (ordre preserve) : la
# generique scripts/tests, une suite de dossier scripts/X/tests, la racine
# tests, des suites fichiers (agent_tests, v4, gateway), un dossier non-tests
# (ArgumentAnalysis) et GradeBookApp.
SUITES = [
    "scripts/tests",
    "scripts/ci/tests",
    "tests",
    "scripts/notebook_tools/tests",
    "scripts/sudoku/tests",
    "MyIA.AI.Notebooks/GameTheory/tests",
    "MyIA.AI.Notebooks/GameTheory/gateway/test_openspiel_cfr_core.py",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_bg_tree_lock.py",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_prover_guards.py",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/tests/test_narration.py",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/test_bake_bank.py",
    "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/gateway/test_run_gateway.py",
    "MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis",
    "dotnet/GradeBookApp",
]


def _scope(event, paths, suite_list=None, readers=None):
    return mod.scope(
        event, suite_list if suite_list is not None else SUITES,
        readers=[("diff", lambda _base: paths)] if readers is None else readers,
    )


# ---------------------------------------------------------------- 1. positif

def test_positive_control_module_de_suite():
    mode, suites, reason = _scope("pull_request", [
        "scripts/sudoku/generator.py",
        "scripts/sudoku/tests/test_generator.py",
    ])
    assert mode == "restricted"
    # Suite specifique + suite generique scripts/tests (parent scripts/),
    # dans l'ordre du workflow, sans doublon.
    assert suites == ["scripts/tests", "scripts/sudoku/tests"]
    assert "2 suite(s)" in reason and "source diff" in reason


def test_une_seule_suite_fichier_selectionnee_sans_generique():
    # Un chemin v4 ne tombe PAS sous scripts/ : pas de suite generique.
    mode, suites, _ = _scope("pull_request", [
        "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/p5_tts.py",
    ])
    assert mode == "restricted"
    assert suites == [
        "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/tests/test_narration.py",
        "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/test_bake_bank.py",
    ]


def test_source_agent_tests_selectionne_ses_5_fichiers():
    mode, suites, _ = _scope("pull_request", [
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/provider_gate.py",
    ])
    assert mode == "restricted"
    assert suites == [
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_bg_tree_lock.py",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_prover_guards.py",
    ]


def test_gametheory_regroupe_ses_deux_entrees():
    mode, suites, _ = _scope("pull_request", [
        "MyIA.AI.Notebooks/GameTheory/game_theory_utils.py",
    ])
    assert mode == "restricted"
    assert suites == [
        "MyIA.AI.Notebooks/GameTheory/tests",
        "MyIA.AI.Notebooks/GameTheory/gateway/test_openspiel_cfr_core.py",
    ]


def test_suite_racine_ne_veuille_pas_le_depot_entier():
    mode, suites, _ = _scope("pull_request", ["tests/test_integration_x.py"])
    assert mode == "restricted"
    assert suites == ["tests"]


def test_dossier_non_tests_veille_son_propre_arbre():
    mode, suites, _ = _scope("pull_request", [
        "MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/argumentation_lib/x.py",
    ])
    assert mode == "restricted"
    assert suites == ["MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis"]


# ------------------------------------------------- 2. garde-fou de la tranche

def test_workflow_force_pleine_suite():
    mode, suites, reason = _scope("pull_request", [
        "scripts/sudoku/generator.py",
        ".github/workflows/autre.yml",
    ])
    assert mode == "full"
    assert suites == SUITES
    assert "producteur du verdict" in reason


def test_pytest_ini_et_conftest_forcent_pleine_suite():
    for path in ("pytest.ini", "scripts/tests/conftest.py"):
        mode, suites, reason = _scope("pull_request", [path])
        assert mode == "full", path
        assert "producteur du verdict" in reason


def test_organe_install_et_watchdog_forcent_pleine_suite():
    for path in ("scripts/ci/changed_scripts_tests.py",
                 "scripts/ci/install_scripts_tests_deps.sh",
                 "scripts/ci/xdist_watchdog.py",
                 "scripts/ci/guard_test_root.py"):
        mode, _, reason = _scope("pull_request", [path])
        assert mode == "full", path
        assert "producteur du verdict" in reason


def test_registre_arxiv_selectionne_la_suite_generique():
    mode, suites, _ = _scope("pull_request", ["arxiv_attributions_registry.yaml"])
    assert mode == "restricted"
    assert suites == ["scripts/tests"]


# ----------------------------------------------------------------- 3. fail-open

def test_lecteurs_en_echec_pleine_suite_raisons_nommees():
    def boom(_base):
        raise RuntimeError("quota epuise")

    mode, suites, reason = mod.scope(
        "pull_request", SUITES,
        readers=[("api", boom), ("autre", boom)],
    )
    assert mode == "full"
    assert suites == SUITES
    assert "portee illisible" in reason
    assert "api: RuntimeError: quota epuise" in reason
    assert "autre: RuntimeError: quota epuise" in reason


def test_chemins_hors_table_pleine_suite():
    mode, suites, reason = _scope("pull_request", [
        "scripts/sudoku/generator.py",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean/Foo.lean",
    ])
    assert mode == "full"
    assert suites == SUITES
    assert "chemins hors table" in reason


def test_portee_vide_pleine_suite():
    mode, suites, reason = _scope("pull_request", [])
    assert mode == "full"
    assert suites == SUITES
    assert "aucune suite" in reason


def test_workflow_dispatch_pleine_suite_sans_lire_le_diff():
    called = []

    def reader(_base):  # pragma: no cover - ne doit pas tourner
        called.append(1)
        return ["scripts/sudoku/generator.py"]

    mode, suites, reason = mod.scope(
        "workflow_dispatch", SUITES, readers=[("diff", reader)]
    )
    assert mode == "full"
    assert suites == SUITES
    assert not called
    assert "workflow_dispatch" in reason


def test_evenement_inconnu_pleine_suite():
    mode, _, reason = _scope("schedule", ["scripts/sudoku/generator.py"])
    assert mode == "full"
    assert "non restreint" in reason


def test_push_chaine_d_un_seul_macon():
    mode, suites, reason = mod.scope(
        "push", SUITES, readers=[("diff HEAD~1", lambda _b: ["dotnet/GradeBookApp/x.py"])]
    )
    assert mode == "restricted"
    assert suites == ["dotnet/GradeBookApp"]
    assert "source diff HEAD~1" in reason


# ------------------------------------------------------------ 4. aires de veille

def test_watch_areas_derivation_parent():
    assert mod.watch_areas("scripts/sudoku/tests") == ("scripts/sudoku/",)
    assert mod.watch_areas("scripts/ci/tests") == ("scripts/ci/",)
    # La generique scripts/tests veille TOUT scripts/ + le registre #17850.
    assert mod.watch_areas("scripts/tests") == (
        "scripts/", "arxiv_attributions_registry.yaml")


def test_watch_areas_overrides():
    assert mod.watch_areas("tests") == ("tests/",)
    v4 = mod.watch_areas(
        "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/tests/test_narration.py")
    assert v4 == ("MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/",)


def test_selects_egalite_et_prefixe():
    assert mod._selects("scripts/sudoku/", "scripts/sudoku/tests/test_x.py")
    assert mod._selects("scripts/sudoku/", "scripts/sudoku")
    assert not mod._selects("scripts/sudoku/", "scripts/sudoku_autre/x.py")


def test_chemins_normalises_windows():
    mode, suites, _ = _scope("pull_request", ["\\scripts\\sudoku\\generator.py"])
    assert mode == "restricted"
    assert suites == ["scripts/tests", "scripts/sudoku/tests"]


# ---------------------------------------------------------------------- 5. CLI

def test_main_json_sur_stdout_raison_sur_stderr(capsys, tmp_path):
    wf = tmp_path / "wf.yml"
    wf.write_text(
        "      run: |\n"
        "        pytest \\\n"
        "          scripts/tests \\\n"
        "          scripts/sudoku/tests \\\n"
        "          -n \"$xdist_n\" --dist loadscope -q\n",
        encoding="utf-8",
    )
    rc = mod.main(["--event", "pull_request",
                   "--workflow", str(wf),
                   "--token", "x",
                   "--pr", "42",
                   "--repo", "jsboige/CoursIA"])
    assert rc == 0
    out = capsys.readouterr()
    import json
    payload = json.loads(out.out)
    assert payload["mode"] == "full"  # pas de vrai diff ici : lecteurs en echec
    assert payload["suites"] == ["scripts/tests", "scripts/sudoku/tests"]
    assert "pleine suite" in payload["reason"]
    assert payload["reason"] in out.err


def test_main_rc2_bruyant_sur_workflow_illisible(capsys, tmp_path):
    wf = tmp_path / "wf.yml"
    wf.write_text("rien d'utile ici\n", encoding="utf-8")
    rc = mod.main(["--event", "pull_request", "--workflow", str(wf)])
    assert rc == 2
    assert "bloc pytest introuvable" in capsys.readouterr().err


def test_integration_vrai_workflow_depuis_le_depot():
    """Verrou d'integration : le vrai workflow de ce depot se parse et les
    aires de veille couvrent sa liste entiere (chaque suite a au moins une
    aire non vide)."""
    suites = mod.parse_collected_paths(mod.DEFAULT_WORKFLOW)
    assert suites, "bloc pytest introuvable dans le vrai workflow"
    for suite in suites:
        areas = mod.watch_areas(suite)
        assert areas, f"aucune aire de veille pour {suite}"
        assert all(a for a in areas), f"aire vide pour {suite}"
