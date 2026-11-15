"""Tests de `changed_scripts_tests` (#22468 tranche 4).

Contrat verifie ici, dans cet ordre :

1. **controle positif** : un diff de PR qui touche un module d'une suite
   rend une portee restreinte (suite specifique + suite generique
   ``scripts/tests``), dans l'ordre du workflow ;
2. **garde-fou de la tranche** : workflow, pytest.ini, conftest.py, script
   d'install, chien de garde et l'organe lui-meme forcent la pleine suite ;
3. **fail-open** : lecteurs en echec -> pleine suite avec raisons nommees ;
   delegation hors table en echec ou sans suite couvrante -> pleine suite ;
   portee restreinte vide -> pleine suite ; workflow_dispatch -> pleine
   suite sans lire le diff ;
3bis. **delegation hors table (#25510)** : un chemin hors de toute aire de
   veille delegue a l'organe natif select_tests.py — la regle R4 (portee
   depot) couvre par construction tout changement ; une suite sans test R4
   ni citation reste EXCLUE (le trou que le lot 4x/jour borne) ;
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


def _native_repo(tmp_path):
    """Depot synthetique pour la delegation hors table (#25510) : une suite
    a portee depot (R4 stricte : REPO_ROOT.rglob) et une suite aveugle (ni
    parcours, ni citation, ni convention de nom)."""
    r4 = tmp_path / "pkgA" / "tests"
    r4.mkdir(parents=True)
    (r4 / "test_scan.py").write_text(
        "from pathlib import Path\n"
        "REPO_ROOT = Path(__file__).resolve().parents[2]\n"
        "def test_scan():\n"
        "    for p in REPO_ROOT.rglob('*.py'):\n"
        "        assert p\n",
        encoding="utf-8",
    )
    blind = tmp_path / "pkgB" / "tests"
    blind.mkdir(parents=True)
    (blind / "test_local.py").write_text(
        "def test_local():\n    assert True\n", encoding="utf-8"
    )
    return tmp_path


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
                 "scripts/ci/guard_test_root.py",
                 "scripts/ci/select_tests.py"):  # organe de la delegation (#25510)
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


def test_chemins_hors_table_delegue_a_la_selection_native(tmp_path):
    """#25510 : un chemin hors table delegue a select_tests.py (regle R4,
    portee depot) au lieu de rendre la pleine suite."""
    _native_repo(tmp_path)
    mode, suites, reason = mod.scope(
        "pull_request", ["pkgA/tests", "pkgB/tests"],
        readers=[("diff", lambda _b: ["MyIA.AI.Notebooks/Serie/x-CSharp.ipynb"])],
        repo_root=tmp_path,
    )
    assert mode == "restricted"
    assert suites == ["pkgA/tests"]  # pkgB : sans test R4 ni citation, EXCLUE
    assert "R4 native" in reason
    assert "1 chemin(s) hors table" in reason


def test_mapped_et_hors_table_union_dans_l_ordre_du_workflow(tmp_path):
    """Le profil marathon II (twin_pairs.d + carnets) : les suites d'aire et
    les suites R4 de la delegation fusionnent, dans l'ordre du workflow."""
    _native_repo(tmp_path)
    mode, suites, reason = mod.scope(
        "pull_request", ["pkgB/tests", "pkgA/tests", "scripts/tests"],
        readers=[("diff", lambda _b: [
            "scripts/notebook_tools/twin_pairs.d/serie-01.yaml",
            "MyIA.AI.Notebooks/Serie/x.ipynb"])],
        repo_root=tmp_path,
    )
    assert mode == "restricted"
    assert suites == ["pkgA/tests", "scripts/tests"]
    assert "R4 native" in reason


def test_hors_table_sans_couverture_native_pleine_suite(tmp_path):
    """Depot sans test a portee depot : aucun filet R4, le repli pleine
    suite reste (le gain ne doit jamais acheter un silence)."""
    blind = tmp_path / "pkgB" / "tests"
    blind.mkdir(parents=True)
    (blind / "test_local.py").write_text(
        "def test_local():\n    assert True\n", encoding="utf-8"
    )
    mode, suites, reason = mod.scope(
        "pull_request", ["pkgB/tests"],
        readers=[("diff", lambda _b: ["MyIA.AI.Notebooks/Serie/x.ipynb"])],
        repo_root=tmp_path,
    )
    assert mode == "full"
    assert suites == ["pkgB/tests"]
    assert "aucune suite native couvrante" in reason


def test_delegation_en_echec_pleine_suite_raison_nommee(monkeypatch):
    """L'organe natif indisponible -> fail-OPEN documente, jamais une
    selection muette."""

    def boom(_root, _changed):
        raise RuntimeError("organe natif absent")

    monkeypatch.setattr(mod, "_select_native", boom)
    mode, suites, reason = mod.scope(
        "pull_request", ["scripts/tests"],
        readers=[("diff", lambda _b: ["MyIA.AI.Notebooks/Serie/x.ipynb"])],
    )
    assert mode == "full"
    assert suites == ["scripts/tests"]
    assert "chemins hors table" in reason
    assert "delegation en echec" in reason
    assert "organe natif absent" in reason


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


def test_push_sur_main_reste_en_pleine_suite():
    """Le push sur main joue TOUT (revue ai-01 5867133827, point 1).

    Le filet : une erreur de portee sur main est imputee a ce seul commit, et
    ne se voit qu'a la PR suivante qui touche la suite du test -- c'est elle
    qui reçoit le rouge, pour une casse introduite deux commits plus tot.
    Le gain de la tranche porte sur les PRs, pas sur le push.

    Controle positif du retrait : si la branche `push` du repli pleine suite
    disparait, ce test rougit.
    """
    mode, suites, reason = mod.scope(
        "push", SUITES, readers=[("diff HEAD~1", lambda _b: ["dotnet/GradeBookApp/x.py"])]
    )
    assert mode == "full"
    assert suites == SUITES
    assert "push sur main" in reason


# ------------------------------------------------------------ 4. aires de veille

def test_watch_areas_derivation_parent():
    assert mod.watch_areas("scripts/sudoku/tests") == ("scripts/sudoku/",)
    assert mod.watch_areas("scripts/ci/tests") == ("scripts/ci/",)
    # La generique scripts/tests veille TOUT scripts/ + ses selecteurs
    # additionnels (registre #17850, prosody_lab relu via ancres __file__,
    # arete #25360 setup_wsl_lean4.sh).
    assert mod.watch_areas("scripts/tests") == (
        "scripts/", "arxiv_attributions_registry.yaml",
        "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/",
        "MyIA.AI.Notebooks/GameTheory/scripts/setup_wsl_lean4.sh")


def test_watch_areas_overrides():
    assert mod.watch_areas("tests") == (
        "tests/", "scripts/ci/", "scripts/notebook_tools/")
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

def test_main_json_sur_stdout_raison_sur_stderr(capsys, tmp_path, monkeypatch):
    # Revue ai-01 12/11 (DM c2819, review 5869404472) : le test appelait les
    # lecteurs REELS sur --pr 42 -- vert en CI (pas de jeton, lecteur API en
    # echec), rouge sur un poste ou gh est authentifie (l'API repond, le mode
    # n'est plus "full"). Doubles deterministes : les deux lecteurs echouent,
    # main rend le repli pleine suite -- le contrat mesure ici est la SORTIE
    # (JSON stdout + raison stderr), pas la lecture.
    def _reader_broken(*_args):
        raise RuntimeError("double de test : lecteur volontairement en echec")

    monkeypatch.setattr(mod, "_local_diff_paths", _reader_broken)
    monkeypatch.setattr(mod, "_api_pr_paths", _reader_broken)
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


def test_main_lit_le_jeton_dans_l_environnement(monkeypatch, tmp_path):
    """Revue ai-01 11/11 (job 130763938091) : le jeton vient de
    l'ENVIRONNEMENT, jamais d'un `--token` sur la ligne de commande.

    Le pas de workflow dedie le pose (`env: GH_TOKEN`) ; le pas `Run tests`
    ne le porte plus, pour que la suite pytest n'herite pas d'un jeton
    ambiant (deux tests le mesuraient). Ce test verrouille la LECTURE : un
    refactor qui reviendrait a `args.token` rendrait `None` ici.
    """
    wf = tmp_path / "wf.yml"
    wf.write_text(
        "      run: |\n"
        "        pytest \\\n"
        "          scripts/tests \\\n"
        "          scripts/sudoku/tests \\\n"
        "          -n \"$xdist_n\" --dist loadscope -q\n",
        encoding="utf-8",
    )
    monkeypatch.setenv("GH_TOKEN", "jeton-env")
    monkeypatch.delenv("GITHUB_TOKEN", raising=False)
    captures = {}

    def faux_scope(event, suite_list, **kw):
        captures.update(kw)
        return "full", ["scripts/tests"], "test"

    monkeypatch.setattr(mod, "scope", faux_scope)
    rc = mod.main(["--event", "pull_request", "--workflow", str(wf)])
    assert rc == 0
    assert captures["token"] == "jeton-env"


def test_main_refuse_un_token_en_argument(capsys, tmp_path):
    """Le drapeau `--token` n'existe plus : argparse doit le rejeter (SystemExit)."""
    import pytest
    wf = tmp_path / "wf.yml"
    wf.write_text(
        "      run: |\n        pytest scripts/tests -q\n", encoding="utf-8"
    )
    with pytest.raises(SystemExit):
        mod.main(["--workflow", str(wf), "--token", "x"])


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


def test_integration_profil_marathon_delegation_mesuree():
    """#25510, mesure du plan : le profil des PRs du marathon II (carnets +
    twin_pairs.d/) rendait 37/37 par le repli hors table ; la delegation
    native le restreint (14 suites mesurees le 2026-11-12). Bornes larges --
    le plancher R4 derive quand des tests a portee depot sont ajoutes ou
    retires -- mais le sens est verrouille : restreint, tres en-deca de la
    pleine suite, et les trois suites jumelles (racine, scripts generique,
    notebook_tools pour twin_pairs.d) presentes."""
    suites = mod.parse_collected_paths(mod.DEFAULT_WORKFLOW)
    marathon = [
        "MyIA.AI.Notebooks/NLP/02_NGrammes_Modeles_De_Langage-CSharp.ipynb",
        "MyIA.AI.Notebooks/NLP/02_NGrammes_Modeles_De_Langage.ipynb",
        "MyIA.AI.Notebooks/NLP/README.md",
        "scripts/notebook_tools/twin_pairs.d/nlp-02-ngrammes.yaml",
    ]
    mode, selected, reason = mod.scope(
        "pull_request", suites,
        readers=[("diff", lambda _b: marathon)],
    )
    assert mode == "restricted"
    assert set(selected) <= set(suites)
    assert 5 <= len(selected) < len(suites)
    for expected in ("tests", "scripts/tests", "scripts/notebook_tools/tests"):
        assert expected in selected, expected
    assert "R4 native" in reason
    # La suite pin du controle positif (scripts/validation/tests, sans test
    # R4 ni citation litterale du carnet ou d'un README) reste EXCLUE :
    # c'est le trou temoin que le lot 4x/jour (P3) borne. Ce test a vu le
    # defaut R3 initial (review #26253) -- le garder strict.
    if "scripts/validation/tests" in suites:
        assert "scripts/validation/tests" not in selected


def test_integration_profil_temoin_pin_exclu():
    """#25510, controle positif : sur le profil temoin (edition du carnet
    pin + un twin_pairs.d/), la delegation retient des suites restreintes
    qui EXCLUENT scripts/validation/tests -- le pin n'y est selectionne par
    aucune regle (nom du carnet construit par concatenation : R3-aveugle ;
    aucun parcours d'arborescence : R4-aveugle ; convention test_<stem>.py
    : R2-aveugle). La selection restreinte passe donc VERT sur ce profil,
    et seul le lot 4x/jour (P3, slow-lane.yml) joue le pin."""
    suites = mod.parse_collected_paths(mod.DEFAULT_WORKFLOW)
    temoin = [
        "MyIA.AI.Notebooks/Sudoku/Sudoku-01-Backtracking-Python.ipynb",
        "scripts/notebook_tools/twin_pairs.d/sudoku-01-backtracking.yaml",
    ]
    mode, selected, reason = mod.scope(
        "pull_request", suites,
        readers=[("diff", lambda _b: temoin)],
    )
    assert mode == "restricted", reason
    assert set(selected) <= set(suites)
    # le pin est hors selection : c'est le trou temoin que le lot borne.
    assert "scripts/validation/tests" not in selected, selected
