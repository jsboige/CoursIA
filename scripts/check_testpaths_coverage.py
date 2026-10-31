#!/usr/bin/env python3
"""Guard de dérive : testpaths pytest.ini vs couverture CI.

Compare les testpaths déclarés dans pytest.ini (les suites du dépôt) à la
couverture réelle des workflows qui invoquent pytest. Rougit sur tout
testpath ni couvert par un workflow ni déclaré `CI-EXCLUDED`.

Couverture = cibles déclarées dans WORKFLOW_COVERAGE. Chaque cible déclarée
doit apparaître littéralement dans son fichier workflow : si un run perd une
cible sans mise à jour ici, le guard le détecte (dérive workflow sans
mise à jour du guard, dans les deux sens).

Exclusions = marqueurs `# CI-EXCLUDED: <testpath> — <raison>` lus dans les
fichiers workflows (co-localisés avec les runs qu'ils exemptent).

Second sens (#22735) : le sens ci-dessus ne voit que les testpaths DÉCLARÉS.
Une suite présente sur le disque sous `scripts/**/tests/` mais absente des
DEUX listes (pytest.ini et couverture CI) lui était invisible — huit suites
vertes en local, jouées par aucun workflow (#22735). Le garde confronte donc
aussi l'ARBORESCENCE à la couverture : une suite sur disque que rien n'exécute
est un rouge, et une suite déclarée câblée mais disparue de l'arbre aussi.

Troisième sens (#22735) : l'INVARIANT de résolution des noms de modules pytest.
pytest dérive le nom de module du paquet le plus proche portant `__init__.py` ;
deux suites `tests/` sans paquet parent (`scripts/genai-stack/tests` et
`agent_tests/tests`) se résolvent alors TOUTES DEUX en `tests.conftest`, et
pluggy refuse d'enregistrer le même objet sous deux noms ("Plugin already
registered under a different name"). L'option ini
`consider_namespace_packages` (pytest >= 8.0) ferme la classe de défaut. Le
garde vérifie qu'elle est déclarée ET qu'un workflow fige pytest >= 8 : sur
une version antérieure, l'option serait ignorée SANS BRUIT (simple
`PytestConfigWarning`) et le défaut reviendrait sans laisser de trace.

Usage:
    python scripts/check_testpaths_coverage.py [--verbose] [--repo-root DIR]

Exit 0 = aucune dérive. Exit 1 = au moins un testpath non couvert non exclu,
une cible déclarée disparue de son workflow, une suite sur disque non
exécutée par la CI, une suite déclarée disparue de l'arbre, ou l'invariant de
résolution des noms de modules pytest violé.
"""

from __future__ import annotations

import argparse
import configparser
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
PYTEST_INI = REPO_ROOT / "pytest.ini"

# Cibles pytest par workflow (déclarées, source de vérité du guard). Chacune
# doit apparaître verbatim dans le fichier : le guard échoue si une cible
# disparaît du workflow sans mise à jour ici. Les cibles FICHIER (ex.
# test_gitleaks_*.py) ne couvrent aucun testpath (un testpath = un dossier
# entier) — elles sont déclarées pour la vérification verbatim, pas pour la
# couverture.
WORKFLOW_COVERAGE: dict[str, list[str]] = {
    ".github/workflows/scripts-tests.yml": [
        "scripts/tests",
        # scripts/secrets/tests : dir entier (famille 4 de #14615) — les 2
        # modules gitleaks y skip sans binaire (gate binaire = secret-scan.yml,
        # cibles fichier ci-dessous).
        "scripts/secrets/tests",
        "scripts/notebook_tools/tests",
        "scripts/lean/tests",
        "scripts/translation/tests",
        "scripts/audit/tests",
        # scripts/fallacy_detection/tests : dir entier (#17580) — la garde
        # argumentum_snapshot (14 tests) devient un test de la collection.
        "scripts/fallacy_detection/tests",
        # #22735 : huit suites de `scripts/**/tests/` etaient vertes en local
        # et jouees par AUCUN workflow -- absentes aussi de pytest.ini, donc
        # invisibles des DEUX sens de ce garde : datasets, genai-stack,
        # hashlife, i18n, qc-mcp-lite, smartcontracts, sudoku, validation.
        # Cables dans la jambe CPU de ce workflow le 2026-10-26 ; hermeticite
        # mesuree firsthand (aucun Docker, aucun reseau ; `genai-stack` a
        # exige `bcrypt`, deja dans le pip install du job), 666 tests cumules.
        # EXCEPTION mesuree le 2026-10-27 : `qc-mcp-lite` ne se joue pas dans
        # le run partage -- `server.py` l.31 importe `mcp.server.fastmcp` a la
        # collection et le SDK MCP n'est pas dans le pip install de ce job
        # (run #122006788867 : `ModuleNotFoundError: No module named 'mcp'`).
        # Elle a son propre job dedie dans le MEME workflow (`qc-mcp-lite-
        # tests`, SDK epingle 1.30.0) : la cible reste couverte par ce
        # fichier, l'env reste isole.
        "scripts/datasets/tests",
        "scripts/genai-stack/tests",
        "scripts/hashlife/tests",
        "scripts/i18n/tests",
        "scripts/qc-mcp-lite/tests",
        "scripts/smartcontracts/tests",
        "scripts/sudoku/tests",
        "scripts/validation/tests",
        # scripts/ci/tests : deja cable dans le run pytest (famille #22234)
        # mais absent des testpaths de pytest.ini -- la convergence
        # local <-> CI est un invariant de ce garde (#22735).
        "scripts/ci/tests",
        "MyIA.AI.Notebooks/GameTheory/tests",
        "MyIA.AI.Notebooks/QuantConnect/scripts/tests",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_bg_tree_lock.py",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_prover_forensic_guards.py",
        "MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-Python-For-Data-Science/tests",
        # scripts/quantconnect/tests : dir entier (famille 3 de #14615) —
        # 254 tests / 9 modules, hermétique (mesure firsthand 2026-09-05 :
        # 253 verts + 1 skip de donnée, yfinance absent de l'env).
        "scripts/quantconnect/tests",
        # GradeBookApp : dir entier (famille 5 de #14615) — 15 tests
        # (test_fuzzy_match_group.py seul), deps rapidfuzz/unidecode/openpyxl
        # ajoutées au pip install du job, zéro PII (journal auto-créé).
        "GradeBookApp",
        # SymbolicAI/Argument_Analysis : dir entier (issue #17248) — 174 tests
        # sur 5 fichiers, 0,5-0,9 s, stdlib + effets de bord mockes (aucun
        # reseau). La suite EXISTAIT deja mais n'etait collectee par AUCUNE CI :
        # absente de pytest.ini ET de ce dict ET sans marqueur CI-EXCLUDED — or
        # ce guard ne compare que les testpaths DECLARES, donc il restait VERT
        # sur un dossier entier non surveille (mesure 2026-09-21 : exit 0 alors
        # que 174 tests ne tournaient nulle part). Ventilation mesuree : tests/
        # test_state_manager_plugin 50, tests/test_argumentation_state 50,
        # tests/test_runner 31, test_install_jdk_portable 24,
        # tests/test_jvm_compat_reporting 19 ; floor CI pose a 174. La branche
        # `tarfile` de install_jdk_portable (test l.203, platform.system pinne a
        # "Linux") est deja exercee localement : python 3.11 des deux cotes
        # (local 3.11.9, python-version '3.11' du job), et pytest.ini porte deja
        # `filterwarnings = ignore::DeprecationWarning`.
        "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis",
    ],
    ".github/workflows/ml-tests.yml": [
        "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/tests",
    ],
    # genai-helpers-tests.yml : famille GenAI helpers, dir entier (tranche 2
    # de #13746) — 138 tests (errants racine helpers/ + helpers/tests/),
    # deps numpy/requests/python-dotenv/pillow/librosa au pip install du job.
    ".github/workflows/genai-helpers-tests.yml": [
        "MyIA.AI.Notebooks/GenAI/shared/helpers",
    ],
    ".github/workflows/secret-scan.yml": [
        "scripts/secrets/tests/test_gitleaks_qwen_rule.py",
        "scripts/secrets/tests/test_gitleaks_10143_classes.py",
    ],
    # ict-tests.yml : scopé à MyIA.AI.Notebooks/IIT/ICT-Series (test-cwd
    # local, test-args relatifs) — ne couvre aucun testpath de la racine.
    # Présent dans le dict avec liste vide = inspecté et tranché volontaire.
    ".github/workflows/ict-tests.yml": [],
    # sudoku-tests.yml : cible-FICHIER (câblage de #22375 tranche 1a, PR
    # empilée sur #22474). Cible fichier = vérification verbatim seulement,
    # aucune couverture de testpath : le dossier `Sudoku/tests/` contient
    # aussi `test_thermal_safe_train.py` (entraînement torch, ~35 s de
    # collecte seule) qu'un garde léger ne doit PAS collecter — d'où pas
    # d'entrée `pytest.ini` testpaths et pas de cible-dossier ici.
    ".github/workflows/sudoku-tests.yml": [
        "MyIA.AI.Notebooks/Sudoku/tests/test_dlx_certificates.py",
    ],
    # geometry-tests.yml : dir entier (issue #23359) — 13 tests Z3/sympy du
    # pont réel real_geometry_bridge.py (tests/test_real_geometry_bridge.py
    # seul fichier), 1.7 s, deps sympy + z3-solver au pip install du job.
    # Avant ce câblage, le dossier n'était ni dans pytest.ini ni collecté
    # par aucune CI : le guard restait vert parce qu'il ne compare que les
    # testpaths DÉCLARÉS (même angle mort que #17248 sur Argument_Analysis).
    ".github/workflows/geometry-tests.yml": [
        "MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/tests",
    ],
}

# Marqueur d'exclusion : `# CI-EXCLUDED: <testpath> — <raison>` en commentaire
# d'un workflow. L'em-dash "—" est le séparateur (format #10903).
CI_EXCLUDED_MARKER = re.compile(r"^\s*#\s*CI-EXCLUDED:\s*(\S+?)\s*—\s*(.+)$")

# Une suite de tests de la famille `scripts/**/tests/` : le repertoire doit
# porter au moins un `test_*.py` pour compter comme suite (#22735).
SUITE_DIR_RE = re.compile(r"^scripts/(?:[^/]+/)*tests$")


def load_testpaths(pytest_ini: Path) -> list[str]:
    """Lit les testpaths de pytest.ini (ordre de déclaration préservé)."""
    parser = configparser.ConfigParser()
    with pytest_ini.open(encoding="utf-8") as fh:
        parser.read_file(fh)
    raw = parser.get("pytest", "testpaths")
    return [line.strip() for line in raw.splitlines() if line.strip()]


def load_ci_excluded(repo_root: Path) -> dict[str, str]:
    """Lit les marqueurs CI-EXCLUDED dans tous les workflows."""
    excluded: dict[str, str] = {}
    for wf in sorted((repo_root / ".github/workflows").glob("*.yml")):
        for line in wf.read_text(encoding="utf-8").splitlines():
            m = CI_EXCLUDED_MARKER.match(line)
            if m:
                path, reason = m.group(1), m.group(2).strip()
                if path in excluded:
                    raise SystemExit(
                        f"CI-EXCLUDED dupliqué pour {path} "
                        f"({excluded[path]} vs {reason})"
                    )
                excluded[path] = reason
    return excluded


def _partition_run_blocks(text: str) -> tuple[set[str], set[str]]:
    """Sépare les cibles en (couvertes, floors) selon les blocs `run:` réels.

    Chaque ligne `run: |` initie un nouveau bloc ; la fermeture se base
    sur l'**indentation du `run: |`** : toute ligne indentée **strictement
    plus** que `run: |` appartient au bloc, toute ligne à la même
    indentation ou moins le ferme. On distingue les steps frères en
    s'appuyant strictement sur cette règle YAML — l'implémentation
    d'origine considérait la condition `non indentée`, ce qui fusionnait
    indûment des steps `run: |` frères quand le premier était aligné en
    colonne 0.

    Un bloc est classé `floor` si toutes ses lignes actives (non
    commentaire, non vide) contiennent `--collect-only`. Sinon (au moins
    une ligne d'exécution pure), il est classé `covered`.

    Le défaut mesuré dans #17250 : un step floor `--collect-only`
    satisfaisait verbatim le garde de dérive. La séparation selon le rôle
    du bloc ferme ce défaut sans changer l'API publique.
    """
    covered: set[str] = set()
    floors: set[str] = set()
    block_targets: set[str] = set()
    block_collect_only: bool | None = None
    block_indent: int | None = None

    def _flush() -> None:
        nonlocal block_targets, block_collect_only, covered, floors
        if block_collect_only is True:
            floors |= block_targets
        elif block_collect_only is False:
            covered |= block_targets
        block_targets = set()
        block_collect_only = None
        block_indent = None

    def _indent(line: str) -> int:
        n = 0
        for ch in line:
            if ch == " ":
                n += 1
            elif ch == "\t":
                n += 1
            else:
                break
        return n

    for line in text.splitlines():
        # Détection d'un début de bloc `run: |` à n'importe quelle indentation
        stripped_no_indent = line.lstrip(" \t")
        if stripped_no_indent.startswith("run: |"):
            # Ferme tout bloc en cours avant d'en ouvrir un nouveau
            _flush()
            block_indent = _indent(line)
            block_collect_only = None
            continue
        if stripped_no_indent.startswith("run: pytest"):
            # Ferme tout bloc en cours avant d'émettre la ligne inline
            _flush()
            for token in stripped_no_indent.split()[2:]:
                _maybe_target(token, covered)
            continue
        if block_indent is None:
            # Pas dans un bloc `run: |`
            continue
        # Dans un bloc : ligne vide ou commentaire = neutre
        if not line.strip() or line.lstrip(" \t").startswith("#"):
            continue
        # Vérifie qu'on est encore DANS le bloc : indentation strictement
        # supérieure à celle du `run: |`.
        cur_indent = _indent(line)
        if cur_indent <= block_indent:
            _flush()
            # Traite la ligne courante comme nouveau départ
            stripped = line.lstrip(" \t")
            if stripped.startswith("run: |"):
                block_indent = _indent(line)
                block_collect_only = None
            elif stripped.startswith("run: pytest"):
                for token in stripped.split()[2:]:
                    _maybe_target(token, covered)
                block_indent = None
            continue
        # Ligne à l'intérieur du bloc : on l'analyse
        # On ne classe une ligne que si elle invoque explicitement `pytest` —
        # les lignes `if [...] then`, `echo "::error::..."`, `exit 1` etc.
        # portent souvent le mot `--collect-only` dans leur texte sans être
        # une commande de collecte. Une ligne qui appelle `pytest` SANS
        # `--collect-only` invalide la classification floor du bloc.
        is_pytest = "pytest" in line
        has_collect = "--collect-only" in line
        if is_pytest and block_collect_only is None:
            # Premier appel pytest du bloc : on initie la classification
            block_collect_only = has_collect
        elif is_pytest and block_collect_only is True and not has_collect:
            # Un vrai pytest sans --collect-only dans le même bloc =
            # exécution, pas floor pur
            block_collect_only = False
        # Les lignes non-pytest (if/echo/exit/fi/fail) sont neutres pour
        # la classification : elles n'invalident ni n'établissent le floor.
        for token in line.split():
            _maybe_target(token, block_targets)

    _flush()
    return covered, floors


def extract_run_targets(text: str) -> set[str]:
    """Cibles de couverture d'un workflow : chemins sous un bloc `run:` réel.

    Les steps de garde `--collect-only` (`#17250`) sont **exclus** : leur
    rôle est de sonder la collecte d'un dossier, pas de l'exécuter — si
    la seule mention d'un testpath est dans un tel step, le testpath n'est
    pas couvert en exécution.

    Retourne les tokens qui ressemblent à un chemin relatif (contient `/`,
    finit en `.py`, ou token nu sans slash ni caractère shell, ex.
    `GradeBookApp`). Chaque bloc `run: |` est traité comme un step
    indépendant (fermeture par indentation stricte).
    """
    covered, _floors = _partition_run_blocks(text)
    return covered


def _maybe_target(token: str, targets: set[str]) -> None:
    """Ajoute le token s'il ressemble à un chemin relatif.

    Chemin = contient un `/`, finit en `.py`, OU est un token nu sans slash
    ni caractère shell (cas des répertoires racine du dépôt, ex. GradeBookApp
    — famille 5 de #14615). Les flags (préfixe `-`) et variables (`$`) ne
    sont jamais des cibles.
    """
    if token in ("\\",) or token.startswith("-") or "$" in token:
        return
    if "/" in token or token.endswith(".py") or re.fullmatch(r"[A-Za-z0-9_.-]+", token):
        targets.add(token)


def verify_declared_targets(repo_root: Path, verbose: bool) -> list[str]:
    """Vérifie que chaque cible déclarée apparaît dans un bloc `run:` réel.

    Le check se fait sur les cibles extraites des blocs `run:` (pas une
    recherche verbatim dans le fichier : un commentaire mentionnant un chemin
    ne satisfait pas la couverture — c'est précisément la dérive que le garde
    doit attraper).
    """
    problems: list[str] = []
    for wf_rel, targets in WORKFLOW_COVERAGE.items():
        wf_path = repo_root / wf_rel
        if not wf_path.exists():
            problems.append(f"workflow déclaré introuvable: {wf_rel}")
            continue
        run_targets = extract_run_targets(wf_path.read_text(encoding="utf-8"))
        for target in targets:
            if target not in run_targets:
                problems.append(
                    f"cible déclarée disparue du run réel: {wf_rel} -> {target} "
                    f"(retirée du run ? mettre à jour WORKFLOW_COVERAGE)"
                )
            elif verbose:
                print(f"  [ok] {wf_rel} couvre {target}")
    return problems


def is_covered(testpath: str, covered_dirs: list[str]) -> bool:
    """Un testpath est couvert si une cible-dossier lui est égale ou ancêtre."""
    return any(
        testpath == c or testpath.startswith(c + "/") for c in covered_dirs
    )


# Racines balayées par l'inventaire. Le guard ci-dessus ne compare que les
# testpaths DÉCLARÉS dans pytest.ini : un dossier de tests présent dans le
# dépôt mais absent de pytest.ini lui est invisible, et il reste VERT dessus
# (constat mesuré sur SymbolicAI/Argument_Analysis, 174 tests non collectés —
# cf. le commentaire de WORKFLOW_COVERAGE). L'inventaire ferme ce côté-là :
# il part du dépôt, pas de la déclaration.
INVENTORY_ROOTS = ("MyIA.AI.Notebooks", "scripts", "GradeBookApp")


TEST_DIR_NAMES = {"tests", "test"}
SKIP_PARTS = {"__pycache__", ".ipynb_checkpoints", ".lake", "_archive"}


def discover_test_dirs(repo_root: Path) -> list[str]:
    """Dossiers-racines de tests du dépôt, hors caches et archives.

    Critère : le dossier s'appelle `tests`/`test` ET porte au moins un
    `test_*.py`. Volontairement borné à la convention de nommage : un module
    `test_*.py` co-localisé avec du code (gateway, helpers, config) est un test
    unitaire de voisinage, pas une suite — l'inventaire ne prétend pas le
    juger, il ne nomme que les suites qu'aucune déclaration ne vise.
    """
    found: set[str] = set()
    for root_rel in INVENTORY_ROOTS:
        root = repo_root / root_rel
        if not root.is_dir():
            continue
        for module in root.rglob("test_*.py"):
            parts = module.parts
            if any(p in SKIP_PARTS for p in parts):
                continue
            if module.parent.name not in TEST_DIR_NAMES:
                continue
            found.add(module.parent.relative_to(repo_root).as_posix())
    return sorted(found)


def run_inventory(
    repo_root: Path, testpaths: list[str], excluded: dict[str, str], strict: bool
) -> list[str]:
    """Liste les dossiers de tests qu'aucune déclaration ne surveille.

    Un dossier est surveillé s'il est lui-même un testpath déclaré, s'il est
    contenu dans un testpath déclaré, ou s'il est CI-EXCLUDED. Le reste est le
    trou d'inventaire : des tests qui existent et que rien ne nomme.
    """
    unwatched: list[str] = []
    for d in discover_test_dirs(repo_root):
        if any(d == tp or d.startswith(tp + "/") for tp in testpaths):
            continue
        if d in excluded:
            continue
        unwatched.append(d)

    print(f"Inventaire des dossiers de tests : {len(unwatched)} non surveillé(s)")
    for d in unwatched:
        print(f"  {'FAIL' if strict else 'INFO'} {d}")
    if unwatched and not strict:
        print(
            "  (advisory : exit 0. Les câbler dans pytest.ini ou les déclarer "
            "`# CI-EXCLUDED: <dossier> — <raison>` ; `--strict` fait rougir.)"
        )
    return unwatched if strict else []
# --- #22735 : second sens, l'arborescence confrontée à la couverture ---


def discover_suites(repo_root: Path) -> list[str]:
    """Suites de tests présentes sur le disque sous `scripts/**/tests/`.

    Une suite est un répertoire dont le chemin relatif matches SUITE_DIR_RE
    et qui contient au moins un `test_*.py`. La découverte est faite sur
    l'ARBRE, jamais sur une liste déclarée : c'est tout l'objet du second
    sens -- une suite absente des deux listes (pytest.ini et workflows) doit
    quand même être vue.
    """
    scripts_dir = repo_root / "scripts"
    if not scripts_dir.is_dir():
        return []
    suites: set[str] = set()
    for test_file in scripts_dir.rglob("test_*.py"):
        rel_dir = test_file.parent.relative_to(repo_root).as_posix()
        if SUITE_DIR_RE.match(rel_dir):
            suites.add(rel_dir)
    return sorted(suites)


def all_run_targets(repo_root: Path) -> set[str]:
    """Cibles pytest réellement exécutées par l'ensemble des workflows."""
    targets: set[str] = set()
    for wf in sorted((repo_root / ".github/workflows").glob("*.yml")):
        targets |= extract_run_targets(wf.read_text(encoding="utf-8"))
    return targets


def uncovered_suites(repo_root: Path) -> list[str]:
    """Suites présentes sur le disque qu'aucun workflow n'exécute.

    Le garde historique ne voit que les testpaths DÉCLARÉS : une suite
    absente de pytest.ini ET de la couverture CI lui est invisible. Cette
    fonction ferme ce trou (#22735 : huit suites vertes en local, jamais
    rejouées automatiquement).
    """
    covered = sorted(all_run_targets(repo_root))
    excluded = load_ci_excluded(repo_root)
    return [
        suite
        for suite in discover_suites(repo_root)
        if not is_covered(suite, covered) and suite not in excluded
    ]


def missing_declared_suites(
    repo_root: Path,
    coverage: dict[str, list[str]] | None = None,
) -> list[str]:
    """Suites déclarées câblées dans WORKFLOW_COVERAGE mais absentes de l'arbre.

    Une cible déclarée qui a disparu du disque laisserait le garde croire
    à une couverture qui n'existe plus -- le pendant exact de la dérive
    « cible déclarée disparue du run réel », mais côté arbre.
    """
    coverage = WORKFLOW_COVERAGE if coverage is None else coverage
    missing: list[str] = []
    for targets in coverage.values():
        for target in targets:
            if target.endswith(".py") or not SUITE_DIR_RE.match(target):
                continue
            if not (repo_root / target).is_dir():
                missing.append(target)
    return sorted(set(missing))


# --- #22735 : troisième sens, l'invariant de résolution des noms de modules ---

# Nom de l'option ini qui étend la résolution de paquet aux paquets-espace de
# noms (pytest >= 8.0). Sans elle, le nom de module d'un fichier est dérivé du
# seul paquet le plus proche portant `__init__.py`.
NAMESPACE_OPTION = "consider_namespace_packages"

# Un workflow doit figer pytest >= 8 : avant 8.0, l'option ci-dessus n'existe
# pas et pytest l'ignorerait sans bruit (un simple `PytestConfigWarning`).
PYTEST_PIN_RE = re.compile(r"pytest\s*>=\s*8(?:\.\d+)*")


def check_namespace_option(repo_root: Path) -> list[str]:
    """Vérifie l'invariant de désambiguïsation des noms de modules pytest.

    Deux conditions, toutes deux nécessaires :

    1. `pytest.ini` déclare l'option — sans elle, deux suites `tests/` sans
       paquet parent suffisent à faire tomber la collecte entière d'un job
       ("Plugin already registered under a different name") ;
    2. un workflow fige `pytest >= 8` — l'option n'existe pas avant 8.0 et
       serait alors ignorée sans bruit, donc le défaut reviendrait sans
       laisser de trace.

    Le contrôle est exercé sur l'ARBRE (pytest.ini + workflows), jamais sur une
    liste déclarée : c'est la suppression effective de l'option qu'il faut
    voir, pas la mise à jour d'un manifeste.
    """
    problems: list[str] = []
    ini_path = repo_root / "pytest.ini"
    parser = configparser.ConfigParser()
    try:
        with ini_path.open(encoding="utf-8") as fh:
            parser.read_file(fh)
    except OSError:
        return [f"pytest.ini illisible: {ini_path}"]
    raw = (parser.get("pytest", NAMESPACE_OPTION, fallback="") or "").strip().lower()
    if raw not in ("true", "1", "yes", "on"):
        problems.append(
            f"pytest.ini ne déclare pas `{NAMESPACE_OPTION} = true` — deux "
            "suites `tests/` sans paquet parent résolvent alors le même nom de "
            "module (`tests.conftest`) et la collecte tombe en "
            "\"Plugin already registered under a different name\""
        )
    pinned = False
    for wf in sorted((repo_root / ".github/workflows").glob("*.yml")):
        for line in wf.read_text(encoding="utf-8").splitlines():
            if "pip install" in line and PYTEST_PIN_RE.search(line):
                pinned = True
                break
        if pinned:
            break
    if not pinned:
        problems.append(
            f"aucun workflow ne fige `pytest>=8` — l'option `{NAMESPACE_OPTION}` "
            "n'existe pas avant pytest 8.0 et y serait ignorée sans bruit"
        )
    return problems


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    ap.add_argument(
        "--inventory",
        action="store_true",
        help="Inventorier les dossiers de tests du dépôt qu'aucune déclaration "
        "pytest.ini ne surveille (advisory, exit 0 sauf --strict).",
    )
    ap.add_argument(
        "--strict",
        action="store_true",
        help="Avec --inventory : faire rougir sur un dossier non surveillé.",
    )
    args = ap.parse_args()

    repo_root = args.repo_root.resolve()
    testpaths = load_testpaths(repo_root / "pytest.ini")
    excluded = load_ci_excluded(repo_root)

    # Cibles-dossier uniquement (les cibles fichier ne couvrent aucun testpath).
    covered_dirs = sorted(
        {
            t
            for targets in WORKFLOW_COVERAGE.values()
            for t in targets
            if not t.endswith(".py")
        }
    )

    if args.verbose:
        print(f"[info] {len(testpaths)} testpaths, "
              f"{len(covered_dirs)} cibles-dossier, "
              f"{len(excluded)} exclusions CI-EXCLUDED")

    problems = verify_declared_targets(repo_root, args.verbose)

    uncovered: list[str] = []
    for tp in testpaths:
        if is_covered(tp, covered_dirs):
            if args.verbose:
                print(f"  [ok] couvert: {tp}")
        elif tp in excluded:
            if args.verbose:
                print(f"  [ok] exclu:   {tp} — {excluded[tp]}")
        else:
            uncovered.append(tp)

    if uncovered:
        print("Testpaths non couverts et non CI-EXCLUDED :")
        for tp in uncovered:
            print(f"  FAIL {tp}")
    elif args.verbose:
        print("[ok] tous les testpaths sont couverts ou exclus")

    if problems:
        print("Dérives de cibles déclarées :")
        for p in problems:
            print(f"  FAIL {p}")

    # Second sens (#22735) : l'arborescence confrontée à la couverture.
    uncovered_disk = uncovered_suites(repo_root)
    if uncovered_disk:
        print("Suites de tests sur le disque, non exécutées par la CI "
              "et non CI-EXCLUDED :")
        for suite in uncovered_disk:
            print(f"  FAIL {suite}")
    elif args.verbose:
        print(f"[ok] {len(discover_suites(repo_root))} suites sur le disque, "
              "toutes exécutées par la CI")

    missing = missing_declared_suites(repo_root)
    if missing:
        print("Suites déclarées câblées mais absentes de l'arbre :")
        for suite in missing:
            print(f"  FAIL {suite}")

    # Troisième sens (#22735) : l'invariant de résolution des noms de modules.
    namespace_problems = check_namespace_option(repo_root)
    if namespace_problems:
        print("Invariant de résolution des noms de modules pytest :")
        for p in namespace_problems:
            print(f"  FAIL {p}")

    # Inventaire (#23359) : les suites qu'aucune declaration pytest.ini ne vise.
    # Sens distinct des deux precedents -- ceux-ci confrontent l'arbre aux
    # workflows, celui-ci aux testpaths declares de pytest.ini.
    inventory = (
        run_inventory(repo_root, testpaths, excluded, args.strict)
        if args.inventory
        else []
    )

    return 1 if (
        uncovered
        or problems
        or uncovered_disk
        or missing
        or namespace_problems
        or inventory
    ) else 0


if __name__ == "__main__":
    sys.exit(main())
