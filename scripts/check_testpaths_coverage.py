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

Quatrième sens (#23359, `--inventory`) : les trois précédents partent tous de
la DÉCLARATION (`pytest.ini`, dicts du garde), donc une suite que rien ne
déclare reste invisible. `--inventory` part de l'ARBORESCENCE et liste les
dossiers de tests qu'aucune des trois sources ne joue — `testpaths` de
pytest.ini, cibles de `WORKFLOW_COVERAGE`, périmètres `test-cwd` de
`WORKFLOW_TEST_CWD`. Un périmètre `test-cwd` existe parce que certains
workflows (matrice `ict-tests.yml`) jouent pytest DANS un dossier sans que ce
chemin apparaisse dans un bloc `run:` : il se déclare dans le dict et se
confronte au fichier, comme les cibles de `WORKFLOW_COVERAGE`.

Cinquième sens (#25366 T0, sous `--inventory`) : les BASENAMES de modules
dupliqués entre répertoires de tests découverts. Deux suites qui portent le
même `test_*.py` (ou le même module d'appui) obligent tout le dépôt à
l'`--import-mode importlib` global de pytest.ini — le workflow le documente
lui-même comme load-bearing à cause de ces doublons (36 basenames mesurés
le 2026-11-09, dont un triple). `__init__.py` et `conftest.py` sont exemptés
(l'un marque les paquets, l'autre est spécial-casé par pytest).

Sixième sens (#25366 T0, sous `--inventory`) : la CONVERGENCE CI -> testpaths,
l'inverse du sens historique. Une cible-dossier que la CI joue mais que
`testpaths` ne déclare pas est invisible d'un `pytest` local à la racine :
ce que la CI voit, le local doit le voir (mesuré le 2026-11-09 : `tests/` à
la racine est dans ce cas). Les périmètres `test-cwd` de WORKFLOW_TEST_CWD
en sont exclus : joués dans leur propre cwd de workflow (matrice ICT), ils
ne relèvent pas du `pytest` racine.

Depuis #25366 T0, `--inventory` est STRICT PAR DÉFAUT (exit 1 sur un dossier
non surveillé, un basename dupliqué ou une cible sans testpath) ; `--advisory`
rétrograde en exit 0. Les quatre sens historiques restent bloquants dans
toute invocation, comme depuis #10903.

Usage:
    python scripts/check_testpaths_coverage.py [--verbose] [--repo-root DIR]
    python scripts/check_testpaths_coverage.py --inventory [--advisory]

Exit 0 = aucune dérive. Exit 1 = au moins un testpath non couvert non exclu,
une cible déclarée disparue de son workflow, une suite sur disque non
exécutée par la CI, une suite déclarée disparue de l'arbre, l'invariant de
résolution des noms de modules pytest violé, un périmètre `test-cwd` déclaré
absent de son workflow ; ou, sous `--inventory` (strict par défaut) : un
dossier de tests que rien ne surveille, un basename de module porté par
plusieurs répertoires découverts, une cible-dossier CI absente des testpaths.
"""

from __future__ import annotations

import argparse
import configparser
import posixpath
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
        # `tests` racine (#25366 T0) : joue par le run pytest partage depuis
        # toujours (3e cible du bloc), mais jamais declare ici ni dans les
        # testpaths -- un pytest local a la racine ne le voyait pas. La
        # declaration ferme la derive declaration <-> reel ; la CONVERGENCE
        # (CI -> testpaths, sixieme sens) rougit dessus tant que le critere 1
        # de #25366 n'est pas tranche (dans testpaths ou exclu par ecrit).
        "tests",
        # scripts/secrets/tests : dir entier (famille 4 de #14615) — les 2
        # modules gitleaks y skip sans binaire (gate binaire = secret-scan-controls.yml,
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
        # ICT-Series scripts/tests : dir entier (#23730, classe #22735) —
        # 45 tests sur 3 fichiers (protocol, records, reward_dynamics),
        # hermétiques (stdlib, 0,2 s mesuré). La suite était collectée par
        # ict-tests.yml en cwd local mais absente des testpaths de la racine
        # ET de la jambe CPU : câblée des trois côtés dans la même PR
        # (pytest.ini testpaths, liste pytest de ce workflow, ce dict).
        "MyIA.AI.Notebooks/IIT/ICT-Series/scripts/tests",
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
        "dotnet/GradeBookApp",
        # SymbolicAI/ArgumentAnalysis : dir entier (issue #17248) — 174 tests
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
        "MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis",
        # T1-B de #25366 : derive declaration <-> reel, SENS workflow -> dict.
        # Le contrat verbatim ne garde que le sens dict -> workflow (une cible
        # declaree disparue du run rougit) ; l'inverse -- une cible jouee par
        # le run mais jamais declaree -- etait invisible. Les 12 entrees qui
        # suivent sont des cibles LITERALES du bloc pytest partage ci-dessus,
        # jouees de fait, declarees ici pour la premiere fois (mesure 2026-11-11
        # depuis le tapis #25366 : 0 occurrence dans ce dict, presentes dans le
        # run). Aucune n'est un testpath pytest.ini : ce sont des cibles-fichier
        # (ou fichiers co-localises), le tri dir-entier reste celui du volet A.
        # Effet inventaire attendu : v4/tests et Lean/agent_tests/tests passent
        # « non surveille » -> « partiellement surveille » (meme classe que
        # Sudoku/tests), refletant le reel : 5 fichiers joues sur 18 pour v4.
        "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/tests/test_p5_narrator_routing.py",
        "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/tests/test_p5_customvoice_narrator.py",
        "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/tests/test_qwen_tts_client.py",
        "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/tests/test_p2_segment_dedup.py",
        "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/tests/test_narration.py",
        # test_bake_bank.py vit a la racine de prosody_lab/ (pas dans tests/) :
        # cible-fichier jouee, le dir prosody_lab/tests (test_onset_chunk.py
        # seul, non joue) reste du ressort du volet A.
        "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/test_bake_bank.py",
        # agent_tests : le dict declarait deja test_bg_tree_lock.py et
        # test_prover_forensic_guards.py ; le run joue trois fichiers de plus.
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_prover_guards.py",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_lean_utils.py",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_provider_gate_18709.py",
        # Tests co-localises avec du code (gateway), motif test-cwd sans
        # testpath : ni dans pytest.ini ni dir, cibles-fichier seules.
        "MyIA.AI.Notebooks/GameTheory/gateway/test_openspiel_cfr_core.py",
        "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/gateway/test_z3_sudoku_core.py",
        "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/gateway/test_run_gateway.py",
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
    # genai-texte-tests.yml : famille GenAI Texte (#25018 pli 0 v2, point 4
    # de l'acceptance) — dir entier, 24 tests collectés (test_structured_
    # outputs_core.py seul fichier), hermétiques (serveur uvicorn loopback,
    # clients injectés ; aucun appel réseau externe), deps httpx/uvicorn/
    # pydantic/openai/jsonschema/fastapi au pip install du job. Sans cette
    # entrée, le testpath ajouté à pytest.ini par la MÊME PR rendait ce garde
    # rouge : il ne compare qu'aux workflows DÉCLARÉS ici, jamais à
    # l'arborescence des workflows (mesuré sur la tête 75bca05ae20,
    # 2026-11-12 — `testpaths vs CI coverage: failure @01:21:24Z`).
    ".github/workflows/genai-texte-tests.yml": [
        "MyIA.AI.Notebooks/GenAI/Texte",
    ],
    # Les deux modules gitleaks vivent dans secret-scan-controls.yml depuis
    # #25510 (tranche T-B) : le job `positive-controls` y a demenage avec eux.
    ".github/workflows/secret-scan-controls.yml": [        "scripts/secrets/tests/test_gitleaks_qwen_rule.py",
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
    # testpaths DÉCLARÉS (même angle mort que #17248 sur ArgumentAnalysis).
    ".github/workflows/geometry-tests.yml": [
        "MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/tests",
    ],
}

# Périmètres `test-cwd` (inventaire #23359, review ai-01 sur #23648) : un
# workflow peut jouer pytest DANS un dossier sans que ce chemin apparaisse dans
# un bloc `run:` — `ict-tests.yml` porte un couple `test-cwd:` / `test-args:`
# par entrée de matrice et sa commande est `pytest ${{ matrix.test-args }}`.
# Le contrat de `WORKFLOW_COVERAGE` (cible verbatim dans un bloc `run:`) ne peut
# donc pas l'exprimer, et un inventaire qui ne lit que pytest.ini annonce comme
# « non surveillés » des dossiers qu'un workflow joue : mesuré sur la tête de
# #23648, `tests/` et `ict/tests/` de la série ICT en faisaient partie.
#
# Le périmètre se DÉCLARE ici plutôt que de se parser depuis la matrice (choix
# laissé à la lane par la review), puis se CONFRONTE au fichier via
# `verify_declared_test_cwd` : une entrée doit être un `test-cwd` du workflow ou
# la jointure `<test-cwd>/<test-args>` d'une paire réellement écrite dans ce
# fichier. Une dérive du workflow sans mise à jour d'ici rougit, dans les deux
# sens, comme pour `WORKFLOW_COVERAGE`.
WORKFLOW_TEST_CWD: dict[str, list[str]] = {
    ".github/workflows/ict-tests.yml": [
        # test-cwd: MyIA.AI.Notebooks/IIT/ICT-Series + test-args: tests
        "MyIA.AI.Notebooks/IIT/ICT-Series/tests",
        # test-cwd: MyIA.AI.Notebooks/IIT/ICT-Series/ict/tests + test-args: .
        "MyIA.AI.Notebooks/IIT/ICT-Series/ict/tests",
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
    finit en `.py`, ou token nu sans slash ni caractère shell — ex.
    historique `GradeBookApp`, devenu `dotnet/GradeBookApp` au move de la
    famille A #13751). Chaque bloc `run: |` est traité comme un step
    indépendant (fermeture par indentation stricte).
    """
    covered, _floors = _partition_run_blocks(text)
    return covered


def _maybe_target(token: str, targets: set[str]) -> None:
    """Ajoute le token s'il ressemble à un chemin relatif.

    Chemin = contient un `/`, finit en `.py`, OU est un token nu sans slash
    ni caractère shell (cas des répertoires racine du dépôt — ex. historique
    GradeBookApp, famille 5 de #14615, devenu dotnet/GradeBookApp au move
    #13751). Les flags (préfixe `-`) et variables (`$`) ne
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


def verify_declared_test_cwd(
    repo_root: Path,
    verbose: bool,
    test_cwd: dict[str, list[str]] | None = None,
) -> list[str]:
    """Confronte les périmètres `test-cwd` déclarés au fichier workflow.

    Une entrée de `WORKFLOW_TEST_CWD` est valide si le workflow porte un
    `test-cwd: <dir>` égal au périmètre, ou un couple `test-cwd: <dir>` /
    `test-args: <arg>` dont la jointure normalisée donne le périmètre. Le
    produit cartésien des valeurs du fichier est volontairement large : toute
    jointure acceptée est réellement écrite dans le fichier, et un chemin qui
    n'y figure pas rougit — c'est la dérive que ce contrôle doit attraper.
    """
    problems: list[str] = []
    declared = WORKFLOW_TEST_CWD if test_cwd is None else test_cwd
    for wf_rel, perimeters in declared.items():
        wf_path = repo_root / wf_rel
        if not wf_path.exists():
            problems.append(f"workflow déclaré introuvable: {wf_rel}")
            continue
        text = wf_path.read_text(encoding="utf-8")
        cwds = re.findall(r"test-cwd:\s*(\S+)", text)
        # `test-args` peut porter des drapeaux (`-n $XDIST_N`) : seule la
        # première valeur non vide compte, et un drapeau ne produira jamais une
        # jointure égale à un périmètre réel.
        args = re.findall(r"test-args:\s*\"?([^\s\"]+)", text) or ["."]
        joints = {posixpath.normpath(c) for c in cwds}
        joints |= {posixpath.normpath(f"{c}/{a}") for c in cwds for a in args}
        for perim in perimeters:
            if posixpath.normpath(perim) not in joints:
                problems.append(
                    "périmètre test-cwd déclaré absent du workflow: "
                    f"{wf_rel} -> {perim} (workflow modifié ? mettre à jour "
                    "WORKFLOW_TEST_CWD)"
                )
            elif verbose:
                print(f"  [ok] {wf_rel} joue {perim}")
    return problems


def is_covered(testpath: str, covered_dirs: list[str]) -> bool:
    """Un testpath est couvert si une cible-dossier lui est égale ou ancêtre."""
    return any(
        testpath == c or testpath.startswith(c + "/") for c in covered_dirs
    )


# Racines balayées par l'inventaire. Le guard ci-dessus ne compare que les
# testpaths DÉCLARÉS dans pytest.ini : un dossier de tests présent dans le
# dépôt mais absent de pytest.ini lui est invisible, et il reste VERT dessus
# (constat mesuré sur SymbolicAI/ArgumentAnalysis, 174 tests non collectés —
# cf. le commentaire de WORKFLOW_COVERAGE). L'inventaire ferme ce côté-là :
# il part du dépôt, pas de la déclaration.
INVENTORY_ROOTS = ("MyIA.AI.Notebooks", "scripts", "dotnet/GradeBookApp", "tests")


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
    repo_root: Path,
    testpaths: list[str],
    excluded: dict[str, str],
    strict: bool,
    workflow_coverage: dict[str, list[str]] | None = None,
    workflow_test_cwd: dict[str, list[str]] | None = None,
) -> list[str]:
    """Liste les dossiers de tests qu'aucune déclaration ne surveille.

    Un dossier est surveillé s'il est un testpath déclaré, contenu dans un
    testpath déclaré, CI-EXCLUDED, ou joué par un workflow — cible-dossier de
    `WORKFLOW_COVERAGE` ou périmètre `test-cwd` de `WORKFLOW_TEST_CWD`. Les
    trois sources comptent : un dossier peut n'être couvert que par un workflow
    dédié, et le taire ferait dire à l'inventaire l'inverse de ce qu'il mesure.

    Un dossier dont une cible-FICHIER de `WORKFLOW_COVERAGE` tombe à
    l'intérieur est « partiellement surveillé » : certains de ses tests
    tournent, pas les autres. Il ne sort pas comme trou, mais il n'est pas
    déclaré couvert non plus — la mesure exacte est celle-là.
    """
    folder_targets: list[str] = []
    file_targets: list[str] = []
    coverage = WORKFLOW_COVERAGE if workflow_coverage is None else workflow_coverage
    perimeters_by_wf = (
        WORKFLOW_TEST_CWD if workflow_test_cwd is None else workflow_test_cwd
    )
    for targets in coverage.values():
        for target in targets:
            (file_targets if target.endswith(".py") else folder_targets).append(target)
    for perimeters in perimeters_by_wf.values():
        folder_targets.extend(perimeters)

    unwatched: list[str] = []
    partial: list[str] = []
    for d in discover_test_dirs(repo_root):
        if any(d == tp or d.startswith(tp + "/") for tp in testpaths):
            continue
        if d in excluded:
            continue
        if is_covered(d, folder_targets):
            continue
        if any(f.startswith(d + "/") for f in file_targets):
            partial.append(d)
            continue
        unwatched.append(d)

    print(
        "Inventaire des dossiers de tests hors pytest.ini et hors couverture "
        f"workflow : {len(unwatched)} non surveillé(s)"
    )
    for d in unwatched:
        print(f"  {'FAIL' if strict else 'INFO'} {d}")
    if partial:
        print(
            f"  Partiellement surveillés (une cible-fichier de workflow tombe "
            f"dedans) : {len(partial)}"
        )
        for d in partial:
            print(f"    - {d}")
    if unwatched and not strict:
        print(
            "  (advisory : exit 0. Se câblent en ajoutant le dossier à "
            "`testpaths` de pytest.ini, en le déclarant comme cible de "
            "`WORKFLOW_COVERAGE` s'il a son workflow dédié, ou en le nommant "
            "`# CI-EXCLUDED: <dossier> — <raison>` ; strict est le défaut "
            "depuis #25366 T0, `--advisory` rétrograde.)"
        )
    return unwatched if strict else []


# --- #25366 T0 : cinquième et sixième sens, la consolidation mesurable ---

# Basnames exemptés du sens « duplication » : présents dans la quasi-totalité
# des suites, ils ne créent pas de collision de module pytest — `conftest.py`
# est spécial-casé par pytest lui-même, `__init__.py` marque un paquet.
BASENAME_EXEMPT = {"__init__.py", "conftest.py"}


def duplicate_basenames(repo_root: Path) -> dict[str, list[str]]:
    """Basenames de modules portés par >= 2 répertoires de tests découverts.

    Ne voit que les ENFANTS DIRECTS de chaque répertoire découvert : ce sont
    eux qui entrent en collision comme noms de modules top-level quand pytest
    insère chaque répertoire de tests dans sys.path (le défaut `import file
    mismatch` que `--import-mode importlib` absorbe aujourd'hui globalement,
    cf. le commentaire du run partagé dans scripts-tests.yml). Un sous-dossier
    paquet (portant `__init__.py`) résout un nom qualifié et ne collisionne
    pas : il n'est donc pas compté au niveau du parent.

    Critère 3 de #25366 : « basenames dupliqués = 0 entre répertoires
    découverts, `__init__.py` et `conftest.py` exceptés » — cette fonction
    est la mesure de ce critère. T2 tranche chaque copie (copie unique,
    surplus supprimé avec preuve, ou redirection d'import) ; ce sens ne
    préjuge pas de l'équivalence de contenu des copies.
    """
    by_basename: dict[str, set[str]] = {}
    for d in discover_test_dirs(repo_root):
        for py in (repo_root / d).glob("*.py"):
            if py.name in BASENAME_EXEMPT:
                continue
            by_basename.setdefault(py.name, set()).add(d)
    return {
        name: sorted(dirs)
        for name, dirs in sorted(by_basename.items())
        if len(dirs) > 1
    }


def coverage_without_testpaths(
    testpaths: list[str],
    excluded: dict[str, str],
    workflow_coverage: dict[str, list[str]] | None = None,
) -> list[str]:
    """Cibles-dossier que la CI joue mais que `testpaths` ne déclare pas.

    Le sens historique vérifie testpaths -> couverture (tout déclarée est
    jouée) ; celui-ci vérifie l'inverse, couverture -> testpaths : une
    cible-dossier CI absente des testpaths est invisible d'un `pytest` lancé
    à la racine, qui ne lit que `testpaths`. La convergence local <-> CI est
    l'invariant déjà énoncé pour `scripts/ci/tests` (#22735) — ici il devient
    une mesure générale (critère 1 de #25366 : mesuré le 2026-11-09, `tests/`
    à la racine est dans ce cas).

    Périmètre volontaire : seules les cibles-dossier de WORKFLOW_COVERAGE.
    Les périmètres `test-cwd` (matrice ICT) jouent pytest DANS leur propre
    cwd de workflow, pas depuis la racine — ils ne relèvent pas du pytest
    local racine. Les cibles-fichier ne déclarent pas un dossier entier.
    """
    coverage = WORKFLOW_COVERAGE if workflow_coverage is None else workflow_coverage
    folder_targets = sorted(
        {
            t
            for targets in coverage.values()
            for t in targets
            if not t.endswith(".py")
        }
    )
    return [
        t
        for t in folder_targets
        if t not in excluded
        and not any(t == tp or t.startswith(tp + "/") for tp in testpaths)
    ]


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
        help="Inventorier les dossiers de tests qu'aucune déclaration ne "
        "surveille, les basenames de modules dupliqués entre répertoires "
        "découverts et les cibles-dossier CI absentes des testpaths. Strict "
        "par défaut depuis #25366 T0 ; --advisory rétrograde en exit 0.",
    )
    ap.add_argument(
        "--strict",
        action="store_true",
        help="Rendre l'inventaire bloquant (défaut depuis #25366 T0 ; "
        "conservé pour compatibilité avec les appels existants).",
    )
    ap.add_argument(
        "--advisory",
        action="store_true",
        help="Rétrograder l'inventaire et ses sens en advisory : lister sans "
        "faire échouer (exit 0). Les quatre sens historiques restent "
        "bloquants dans tous les cas.",
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
    problems += verify_declared_test_cwd(repo_root, args.verbose)

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

    # Inventaire (#23359) et sens de consolidation (#25366 T0). Depuis T0,
    # l'inventaire est STRICT PAR DÉFAUT (--advisory rétrograde) : le rouge
    # est le signal qui motive les tranches T1 (trier les répertoires) et
    # T2 (dédoubler les basenames), pas une régression à corriger d'urgence.
    # La garde CI (fast lane) appelle ce script sans --inventory : les sens
    # de consolidation y entrent en T4, une fois la dette triée.
    strict = args.strict or not args.advisory
    inventory: list[str] = []
    dupes: dict[str, list[str]] = {}
    convergence: list[str] = []
    if args.inventory:
        inventory = run_inventory(repo_root, testpaths, excluded, strict)
        # Cinquième sens (#25366 T0) : basenames dupliqués.
        dupes = duplicate_basenames(repo_root)
        if dupes:
            print(
                f"Basenames de modules portés par >= 2 répertoires de tests "
                f"découverts : {len(dupes)}"
            )
            for name, dirs in dupes.items():
                print(f"  {'FAIL' if strict else 'INFO'} {name} — {', '.join(dirs)}")
        elif args.verbose:
            print("[ok] aucun basename dupliqué entre répertoires découverts")
        # Sixième sens (#25366 T0) : convergence CI -> testpaths.
        convergence = coverage_without_testpaths(testpaths, excluded)
        if convergence:
            print(
                "Cibles-dossier jouées par la CI, absentes des testpaths "
                "(un pytest racine ne les voit pas) :"
            )
            for t in convergence:
                print(f"  {'FAIL' if strict else 'INFO'} {t}")
        elif args.verbose:
            print("[ok] toutes les cibles-dossier CI sont dans les testpaths")

    # `run_inventory` ne rend des trous qu'en strict ; les deux sens de
    # #25366 suivent la même règle : listés en advisory, rouges en strict.
    return 1 if (
        uncovered
        or problems
        or uncovered_disk
        or missing
        or namespace_problems
        or inventory
        or (strict and (dupes or convergence))
    ) else 0


if __name__ == "__main__":
    sys.exit(main())
