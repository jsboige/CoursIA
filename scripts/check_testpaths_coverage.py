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

Septième sens (#25366 T5, #26736) : la COUVERTURE PAR FICHIER. Les six sens
précédents raisonnent sur des répertoires, des déclarations ou des noms de
modules ; un fichier de test co-localisé avec du code (gateway, helpers) est
invisible à tous. L'organe descend donc au niveau du FICHIER : tout
`test_*.py` / `*_test.py` portant au moins un item collectible est classé
JOUE (cible-dossier d'un workflow, cible-fichier, périmètre `test-cwd`) ou
NON JOUE. Un fichier non joué est nommé avec la jambe CANDIDATE — celle qui
cite déjà des fichiers de son répertoire, à défaut le point d'entrée unique
du câblage (`scripts-tests.yml`). Ce sens est ADVISORY dans l'invocation
simple (la dette est réelle et connue : 96 fichiers mesurés le 2026-11-15)
et STRICT sous `--inventory`.

Huitième sens (#25366 T5, #26736) : le CLIQUET sur la population exclue. Un
marqueur `CI-EXCLUDED` satisfait la garde sans qu'aucune jambe ne joue le
répertoire : sans cliquet, la population exclue pouvait croître sans bruit
(26 marqueurs / 66 fichiers / 1097 items mesurés sur `main` le 2026-11-15).
L'organe compte la population RÉELLEMENT exclue (marqueurs, fichiers à item
collectible, items) et rougit dès qu'elle dépasse la baseline
`CI_EXCLUDED_BASELINE`. Ce sens est BLOQUANT dans toute invocation. Il
s'accompagne d'un PLAN : chaque exclusion déclare sa cible de remédiation
(étage quotidien, jambe PR, exclusion motivée qui reste) dans
`CI_EXCLUDED_PLAN` — un cliquet sans plan ne fait que geler la dette.

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
absent de son workflow, la population CI-EXCLUDED en hausse au-dessus de la
baseline, une exclusion sans cible de remédiation déclarée ; ou, sous
`--inventory` (strict par défaut) : un dossier de tests que rien ne surveille,
un basename de module porté par plusieurs répertoires découverts, une
cible-dossier CI absente des testpaths, un fichier de test qu'aucune jambe ne
collecte.
"""

from __future__ import annotations

import argparse
import configparser
import json
import os
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
        # scripts/humor_detection/tests : dir entier (#20301) — 12 tests de
        # la campagne ColBERT (annotation_campaign), hors reseau, memes deps
        # stdlib+pytest que fallacy_detection (le module importe Reply de
        # fallacy_detection.generate_teacher_corpus).
        "scripts/humor_detection/tests",
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
        # scripts/curriculum/tests : suite neuve de #27657 (temoins des
        # fonctions pures du generateur de carte des prerequis), pure et sans
        # reseau. Cablee des trois cotes dans la meme PR (pytest.ini,
        # liste pytest de scripts-tests.yml, ce dict) -- sans quoi le second
        # sens du garde (#22735) la voyait sur le disque et non jouee.
        "scripts/curriculum/tests",
        "MyIA.AI.Notebooks/GameTheory/tests",
        # ICT-Series scripts/tests : dir entier (#23730, classe #22735) —
        # 45 tests sur 3 fichiers (protocol, records, reward_dynamics),
        # hermétiques (stdlib, 0,2 s mesuré). La suite était collectée par
        # ict-tests.yml en cwd local mais absente des testpaths de la racine
        # ET de la jambe CPU : câblée des trois côtés dans la même PR
        # (pytest.ini testpaths, liste pytest de ce workflow, ce dict).
        "MyIA.AI.Notebooks/IIT/ICT-Series/scripts/tests",
        "MyIA.AI.Notebooks/QuantConnect/scripts/tests",
        # HalloweenIndicator-QC/tests (#27482) : dossier neuf apporté avec son
        # test (trace d'ombre, AlgorithmImports maquetté, 13 tests en 0,1 s),
        # câblé des trois côtés dans la même PR.
        "MyIA.AI.Notebooks/QuantConnect/projects/HalloweenIndicator-QC/tests",
        # Option-Wheel/tests (#28618) : dossier neuf apporte avec son test,
        # hermétique (AlgorithmImports maquetté, zéro réseau ; 8 tests en
        # 0,12 s en local). Cablé des trois côtés dans la même PR — testpaths,
        # bloc pytest littéral de ce workflow, ce dict — plutôt que déclaré en
        # dette tolérée : un test ajouté pour prouver un plafond doit tourner.
        "MyIA.AI.Notebooks/QuantConnect/projects/Option-Wheel/tests",
        # BitcoinRegimeGate-QC/tests (#27482) : marqueur CI-EXCLUDED leve. Le
        # tri T1 l'avait range en « classe hypothesis » ; son fichier unique
        # n'importe pas hypothesis (maquette AlgorithmImports, stdlib + pytest)
        # et passe depuis la racine sous PYTHONNOUSERSITE=1 (36 tests, 0,2 s).
        "MyIA.AI.Notebooks/QuantConnect/projects/BitcoinRegimeGate-QC/tests",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_bg_tree_lock.py",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_prover_forensic_guards.py",
        "MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-Python-For-Data-Science/tests",
        # Probas/Causalite/tests (T1-finale #25366) : dernier dossier non
        # trie, cable des trois cotes dans la meme PR (pytest.ini testpaths,
        # bloc pytest litteral de ce workflow, ce dict) ; dowhy installe par
        # le script partage d'installation. 107 tests verts mesures en local
        # (Python 3.13, dowhy 0.14, 137,87 s depuis la racine du depot).
        "MyIA.AI.Notebooks/Probas/Causalite/tests",
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
    # Depuis #28619 la jambe joue trois cibles-fichier, toutes déclarées :
    # `test_inference_trace.py` entree par #27222 mais jamais inscrite ici
    # (derive declaration <-> reel du meme garde), et `test_path_profile.py`
    # (#27214), que la CI ne collectait pas. Une cible déclarée doit
    # apparaitre VERBATIM dans un bloc `run:` du workflow
    # (verify_declared_targets) : retirer l'une des trois du pytest rougit.
    ".github/workflows/sudoku-tests.yml": [
        "MyIA.AI.Notebooks/Sudoku/tests/test_dlx_certificates.py",
        "MyIA.AI.Notebooks/Sudoku/tests/test_inference_trace.py",
        "MyIA.AI.Notebooks/Sudoku/tests/test_path_profile.py",
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

# --- #25366 T5 (#26736) : le plan et la baseline de la population exclue ---
#
# Un marqueur `CI-EXCLUDED` SATISFAIT la garde : le répertoire est compté
# comme couvert alors qu'aucune jambe ne le joue (« pas encore », dit le
# fichier lui-même). Le COMPTE de cette population n'était recompté par
# personne : elle pouvait croître sans bruit.
#
# `CI_EXCLUDED_PLAN` donne à chaque exclusion sa CIBLE de remediation. La
# cible est lue par l'organe : une exclusion sans cible déclarée est un
# défaut (elle n'ira nulle part), une cible sans exclusion est un résidu.
#
#   `quotidien`        — l'étage quotidien de la CI (#25510 : tests lourds
#                        en lot sur l'arbre fusionné). Cible par defaut :
#                        le user veut moins de rejeux des mêmes tests.
#   `jambe-pr`         — le run pytest partage, une fois le prerequis leve
#                        (hermeticite runner demontree, dependance presente
#                        dans l'image CI). Reserve aux petits volumes.
#   `exclusion-motivee`— l'exclusion reste : le motif ne disparaitra pas
#                        (fixture jouee depuis sa propre racine).
PLAN_TARGETS = ("quotidien", "jambe-pr", "exclusion-motivee")

CI_EXCLUDED_PLAN: dict[str, str] = {
    # --- verts locaux, hermeticite runner a demontrer (T1 #25366) ---
    # Petits volumes, hermetiques : ils rejoignent le run pytest partage
    # des que l'hermeticite du runner est demontree.
    "MyIA.AI.Notebooks/InformationCalcul/Compression/tests": "jambe-pr",
    "MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/tests": "jambe-pr",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/tests": "jambe-pr",
    "MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/examples/sample_project/tests": "jambe-pr",
    "MyIA.AI.Notebooks/ML/ML.Net/tests": "jambe-pr",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/tests": "jambe-pr",
    "MyIA.AI.Notebooks/SymbolicAI/scripts/tests": "jambe-pr",
    # Volumes lourds ou environnement a part : l'etage quotidien.
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/tests": "quotidien",
    "MyIA.AI.Notebooks/Probas/Infer/tests": "quotidien",
    "MyIA.AI.Notebooks/Probas/PyMC/tests": "quotidien",
    "MyIA.AI.Notebooks/Search/tests": "quotidien",
    "MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/tests": "quotidien",
    # --- dependance absente ou Python requis (T1 #25366) ---
    # La dependance n'est pas dans l'image CI : le lot attend son
    # installation, puis l'etage quotidien (une image dediee).
    # Causal-Bridges/tests (devenu Probas/Causalite/tests au rename #26392)
    # quitte le plan en T1-finale : dowhy installe par le script partage,
    # dossier cable dans scripts-tests.yml et pytest.ini (#25366).
    "MyIA.AI.Notebooks/Probas/DecisionTheory/voi/tests": "quotidien",
    "MyIA.AI.Notebooks/QuantConnect/projects/AdaptiveAssetAllocation/tests": "quotidien",
    "MyIA.AI.Notebooks/QuantConnect/projects/Crypto-MultiCanal/tests": "quotidien",
    "MyIA.AI.Notebooks/QuantConnect/projects/Filing-Language-Stability/tests": "quotidien",
    "MyIA.AI.Notebooks/QuantConnect/projects/FuturesTrend/tests": "quotidien",
    "MyIA.AI.Notebooks/QuantConnect/projects/LowBeta-Industries-QC/tests": "quotidien",
    "MyIA.AI.Notebooks/QuantConnect/projects/MacroFactorRotation-QC/tests": "quotidien",
    "MyIA.AI.Notebooks/QuantConnect/projects/MomentumStrategy/tests": "quotidien",
    "MyIA.AI.Notebooks/QuantConnect/projects/Paradox46Benchmarks/tests": "quotidien",
    "MyIA.AI.Notebooks/QuantConnect/projects/Portfolio-IBKR-Coinbase-Hybrid/paper_harness/tests": "quotidien",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/tests": "quotidien",
    # --- fixture de demonstration (T1 #25366) ---
    # Joue depuis sa propre racine (import src.*) : l'exclusion reste.
    "MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/01-decouverte/demo-2-references-contexte/ressources/projet-exemple/tests": "exclusion-motivee",
}

# La baseline du cliquet, mesuree sur `main` au 2026-11-15 (tete
# 463c59de75e0c) : 26 marqueurs, 66 fichiers portant au moins un item
# collectible, 1097 items collectibles. Toute CROISSANCE de l'un des trois
# compteurs fait rouge ; une baisse verdit et invite a rebaseline.
#
# Les 611 « tests verts » du triage sont un SOUS-ensemble mesure en local
# (conda projet-is) : ils ne sont pas recomputables par l'organe. Le
# compteur `items` est l'invariant mecanique qui les englobe.
#
# #27201 et #27121 / #27122 : population mesuree apres fusion des controles
# de finitude et de fenetre datee : 26 marqueurs, 67 fichiers, 1110 items.
# collectible_item_count compte les fonctions/classes, pas les cas parametres
# de pytest : les 145 cas executes dans le harness sont une mesure distincte.
# Le plafond precedent de 1134 confondait ces deux unites ; il est resserre.
# Toujours hors CI racine : ce relevement ne pretend pas ajouter une
# couverture CI. La suite complete se rejoue depuis le dossier du projet.
# T1-finale #25366 : retrait du marqueur orphelin Causal-Bridges (le chemin
# mort n'excluait plus rien depuis le rename #26392) : 25 marqueurs. Les
# fichiers et items ne bougent pas (67 / 1110) : l'orphelin ne comptait
# pour aucun fichier, le dossier Causalite n'a jamais ete dans la population.
# #27482 : BitcoinRegimeGate-QC/tests quitte la population (marqueur leve,
# dossier cable des trois cotes) : 24 marqueurs, 66 fichiers, 1083 items.
# #19694 : le marqueur de 04-Applications/v4/tests est au niveau du DOSSIER,
# donc tout test ajoute dans ses limites compte dans la population meme
# lorsqu'une jambe le joue. `test_p5_audiocpp_fish_route.py` (21 tests
# hermetiques, monkeypatch et tmp_path seulement, 2,7 s en local) y entre et
# est cable dans scripts-tests.yml comme ses cinq voisins : 67 fichiers,
# 1104 items. L'exclusion du dossier n'est pas levee pour autant (les tests
# restants du dossier ne sont toujours pas joues par la CI).
CI_EXCLUDED_BASELINE = {"marqueurs": 24, "fichiers": 67, "items": 1104}

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

    Les guillemets de tête et de queue sont retirés AVANT le test de forme :
    le job `adk-contracts` de `scripts-tests.yml` cite ses cibles entre
    guillemets (`"scripts/tests/test_adk_runtime_contracts.py"`), et une
    cible entre guillemets est nonetheless exécutée par la CI — sans ce
    retrait, la cible sortait « NON JOUÉE » alors que la CI la joue (mesure
    du 2026-11-15, revue du coordinateur sur #26759).
    """
    token = token.strip().strip("\"'")
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
            "  (câblage : ajouter le dossier à `testpaths` de pytest.ini, le "
            "déclarer comme cible de `WORKFLOW_COVERAGE` s'il a son workflow "
            "dédié, ou le nommer `# CI-EXCLUDED: <dossier> — <raison>` ; "
            "strict est le défaut depuis #25366 T0, `--advisory` rétrograde, "
            "`--baseline` tolère la dette connue et refuse le nouveau.)"
        )
    # Depuis T4 (#25366), le retour porte TOUJOURS la liste des trous :
    # le drapeau strict ne decide plus de la donnee mais de l'impression
    # (FAIL vs INFO) -- le verdict appartient a main(), qui connait le
    # mode (advisory, baseline, strict).
    return unwatched


# --- #25366 T0 : cinquième et sixième sens, la consolidation mesurable ---

# Basnames exemptés du sens « duplication » : présents dans la quasi-totalité
# des suites, ils ne créent pas de collision de module pytest — `conftest.py`
# est spécial-casé par pytest lui-même, `__init__.py` marque un paquet.
BASENAME_EXEMPT = {"__init__.py", "conftest.py"}


def duplicate_basenames(
    repo_root: Path, excluded: dict[str, str] | None = None
) -> dict[str, list[str]]:
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

    Paire tolérée quand TOUS ses répertoires portent un marqueur
    CI-EXCLUDED (T1-finale #25366) : même symétrie que le tri des dossiers
    (« les exclusions déclarées comptent comme triées »). Une collision qui
    vit entièrement dans la population déclarée-exclue — deux
    projets-exemple pédagogiques homonymes, par exemple — est connue et
    écrite ; la compter rougirait un critère que le mécanisme dit déjà
    tranché. Une collision MIXTE (un répertoire exclu, un répertoire vivant)
    reste comptée : le répertoire vivant collisionne réellement.
    """
    excluded = excluded or {}
    by_basename: dict[str, set[str]] = {}
    for d in discover_test_dirs(repo_root):
        for py in (repo_root / d).glob("*.py"):
            if py.name in BASENAME_EXEMPT:
                continue
            by_basename.setdefault(py.name, set()).add(d)
    return {
        name: sorted(dirs)
        for name, dirs in sorted(by_basename.items())
        if len(dirs) > 1 and not all(d in excluded for d in dirs)
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


# --- #25366 T4 : le ratchet — dette connue tolérée, NOUVEAU refusé ---

def write_inventory_baseline(
    path: Path,
    unwatched: list[str],
    dupes: dict[str, list[str]],
    unplayed: list[str],
) -> None:
    """Écrit la baseline de dette connue des sens d'inventaire.

    Format JSON : {"unwatched": [...], "duplicate_basenames": {nom:
    [répertoires]}, "unplayed": [...]}. Le sens fichier (couverture par
    fichier de #26759) est baseliné depuis que #26759 le rend strict
    sous --inventory. Régénérer quand une tranche T1/T2 résorbe de la
    dette (le jugement le rappelle par des lignes « régénérer »).
    """
    payload = {
        "description": (
            "Dette connue des sens d'inventaire de #25366 (dossiers de "
            "tests non triés, basenames dupliqués) et du sens fichier "
            "de #26759 (fichiers qu'aucune jambe ne collecte). Ratchet "
            "T4 : ces entrées sont tolérées, tout finding NOUVEAU fait "
            "rougir la garde. Régénération : python "
            "scripts/check_testpaths_coverage.py --inventory "
            "--write-baseline scripts/tests/baseline_testpaths_inventory.json"
        ),
        "unwatched": sorted(unwatched),
        "duplicate_basenames": {
            k: sorted(v) for k, v in sorted(dupes.items())
        },
        "unplayed": sorted(unplayed),
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True)
        + "\n",
        encoding="utf-8",
    )


def load_inventory_baseline(path: Path) -> dict:
    """Charge la baseline ; absente ou mal formée = blocage explicite.

    Une baseline manquante ne rend JAMAIS la garde muette : c'est un
    rouge actionnable (corriger le chemin ou régénérer), pas un vert.
    """
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise SystemExit(
            f"baseline ratchet introuvable : {path} — la régénérer par "
            "--write-baseline (jamais un vert silencieux)"
        )
    except json.JSONDecodeError as exc:
        raise SystemExit(f"baseline ratchet illisible ({path}) : {exc}")
    if (
        not isinstance(data, dict)
        or not isinstance(data.get("unwatched"), list)
        or not isinstance(data.get("duplicate_basenames"), dict)
        or not isinstance(data.get("unplayed"), list)
    ):
        raise SystemExit(
            f"baseline ratchet mal formée ({path}) : clés 'unwatched' "
            "(liste), 'duplicate_basenames' (dict) et 'unplayed' "
            "(liste) attendues — régénérer par --write-baseline"
        )
    return data


def judge_inventory_against_baseline(
    unwatched: list[str],
    dupes: dict[str, list[str]],
    unplayed: list[str],
    baseline: dict,
) -> list[str]:
    """T4 : la dette de la baseline est tolérée, le NOUVEAU rougit.

    - dossier non trié : toléré ssi listé dans la baseline ;
    - basename dupliqué : toléré ssi ses répertoires sur l'arbre sont
      un SOUS-ENSEMBLE de ceux de la baseline — retirer une copie
      (progression T2) verdit, en ajouter une (croissance latérale,
      invisible au simple compte de basenames) rougit ;
    - le sixième sens (convergence CI -> testpaths) n'est PAS baseliné :
      mesuré à zéro sur main (critère 1 tranché en T1), toute récidive
      rougit sans tolérance.
    """
    failures: list[str] = []

    base_unwatched = set(baseline.get("unwatched", []))
    for d in unwatched:
        if d in base_unwatched:
            print(f"  [baseline] dette connue (tolérée) : {d}")
        else:
            failures.append(
                f"dossier de tests non trié, absent de la baseline : {d}"
            )
    for d in sorted(base_unwatched - set(unwatched)):
        print(f"  [baseline] dette résorbée — régénérer la baseline : {d}")

    base_dupes: dict[str, list[str]] = baseline.get(
        "duplicate_basenames", {}
    )
    for name, dirs in dupes.items():
        if name not in base_dupes:
            failures.append(
                f"basename dupliqué NOUVEAU, absent de la baseline : "
                f"{name} — {', '.join(dirs)}"
            )
            continue
        extra = sorted(set(dirs) - set(base_dupes[name]))
        if extra:
            failures.append(
                f"basename dupliqué en CROISSANCE : {name} porte des "
                f"répertoires absents de la baseline : {', '.join(extra)}"
            )
        else:
            removed = sorted(set(base_dupes[name]) - set(dirs))
            if removed:
                print(
                    f"  [baseline] dette réduite — régénérer la baseline : "
                    f"{name} ({', '.join(removed)} en moins)"
                )
            else:
                print(f"  [baseline] dette connue (tolérée) : {name}")
    for name in sorted(set(base_dupes) - set(dupes.keys())):
        print(f"  [baseline] dette résorbée — régénérer la baseline : {name}")

    base_unplayed = set(baseline.get("unplayed", []))
    for f in unplayed:
        if f in base_unplayed:
            print(f"  [baseline] dette connue (tolérée) : {f}")
        else:
            failures.append(
                "fichier de test non collecté NOUVEAU, absent de la "
                f"baseline : {f}"
            )
    for f in sorted(base_unplayed - set(unplayed)):
        print(f"  [baseline] dette résorbée — régénérer la baseline : {f}")

    if failures:
        print("Ratchet inventaire (#25366 T4) — findings NOUVEAUX :")
        for f in failures:
            print(f"  FAIL {f}")
    elif unwatched or dupes:
        print(
            f"[ok] ratchet : aucun finding nouveau "
            f"({len(unwatched)} dossier(s) non trié(s), "
            f"{len(dupes)} basename(s) dupliqué(s), "
            f"{len(unplayed)} fichier(s) non collecté(s) — dette de "
            "baseline tolérée)"
        )
    return failures


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


# --- #25366 T5 (#26736) : septième et huitième sens, le FICHIER et le COMPTE ---
#
# Les six sens precedents raisonnent en répertoires ou en cibles DÉCLARÉES.
# Deux questions restaient sans réponse, et ce sont celles que pose l'EPIC
# (« zero test invisible ») :
#
#   1. la COUVERTURE AU NIVEAU DU FICHIER : dans un répertoire couvert par
#      une cible-dossier, un fichier peut n'être collecté par AUCUNE jambe
#      (une cible-fichier qui ne le cite pas, un motif de nom, un cwd
#      différent) ;
#   2. le CLIQUET sur la POPULATION EXCLUE : un marqueur `CI-EXCLUDED`
#      satisfait la garde sans qu'aucune jambe ne joue le répertoire, et
#      rien ne recomptait cette population.
#
# Aucun second organe n'est créé : les deux sens prolongent celui-ci.

# `pytest.ini` ne fixe pas `python_files` : les motifs par défaut de pytest
# s'appliquent — `test_*.py` et `*_test.py`.
def is_test_file_name(name: str) -> bool:
    """Le nom suit-il un motif de collecte pytest ?"""
    return name.startswith("test_") or name.endswith("_test.py")


# Un item collectible : une fonction `test_*` (async comprise) ou une classe
# `Test*`. Meme filtre que le census du 2026-11-15.
COLLECTIBLE_ITEM_RE = re.compile(r"^(?:async\s+)?def\s+test_\w+|^class\s+Test\w*")


def collectible_item_count(path: Path) -> int:
    """Nombre d'items collectibles d'un fichier de test.

    Lecture tolerateuse : un fichier illisible ne vaut pas « zero item »
    (il vaut « inconnu »), et l'appelant le traite comme non collectible.
    """
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return 0
    return sum(1 for line in text.splitlines()
               if COLLECTIBLE_ITEM_RE.match(line.strip()))


def iter_python_files(root: Path):
    """Fichiers `.py` sous `root`, en ELAGUANT les caches et les archives.

    `rglob` descend dans `.lake` et `__pycache__` : sur ce dépôt, la
    recherche par glob depasse le budget de la voie rapide. Le parcours
    elague les repertoires exclus avant de descendre.
    """
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_PARTS]
        for name in filenames:
            if name.endswith(".py"):
                yield Path(dirpath) / name


def discover_test_files(repo_root: Path) -> dict[str, int]:
    """Fichiers de test portant au moins un item collectible.

    {chemin relatif -> nombre d'items}. L'inventaire descend au niveau du
    FICHIER : un `test_*.py` co-localise avec du code (gateway, helpers)
    est un test unitaire de voisinage, tout aussi invisible s'il n'est
    joue par aucune jambe.
    """
    found: dict[str, int] = {}
    for root_rel in INVENTORY_ROOTS:
        root = repo_root / root_rel
        if not root.is_dir():
            continue
        for module in iter_python_files(root):
            if not is_test_file_name(module.name):
                continue
            items = collectible_item_count(module)
            if items:
                found[module.relative_to(repo_root).as_posix()] = items
    return dict(sorted(found.items()))


def workflow_targets_by_workflow(repo_root: Path) -> dict[str, set[str]]:
    """Cibles litterales de chaque workflow (blocs `run:` reels)."""
    out: dict[str, set[str]] = {}
    for wf in sorted((repo_root / ".github/workflows").glob("*.yml")):
        targets = extract_run_targets(wf.read_text(encoding="utf-8"))
        if targets:
            out[wf.relative_to(repo_root).as_posix()] = targets
    return out


# Point d'entree unique du cablage (#26736) : le run pytest partage de
# scripts-tests.yml. Il est nomme quand aucun workflow ne cite de fichier
# du repertoire du fichier non joue.
ENTRY_POINT_WORKFLOW = ".github/workflows/scripts-tests.yml"


def file_coverage(repo_root: Path, excluded: dict[str, str]) -> dict:
    """Couverture par fichier : ce qui est joue, ce qui ne l'est pas.

    Un fichier est JOUE si l'un de ces quatre cas se presente :

    - une cible-DOSSIER d'un workflow le contient (pytest collecte
      recursivement le dossier) ;
    - il est une cible-FICHIER d'un workflow ;
    - il est sous un perimetre `test-cwd` (joue depuis son propre cwd --
      matrice ICT) ;
    - il est sous un chemin `CI-EXCLUDED` : DECLARE exclu, donc connu et
      compte par le cliquet, mais pas joue (le cliquet le dit).

    Le reste est NON JOUE : c'est la population invisible que l'EPIC
    nomme. Pour chaque fichier non joue, l'organe nomme la jambe qui
    POURRAIT le prendre (celle qui cite des fichiers du meme repertoire),
    ou, a defaut, le point d'entree du cablage.
    """
    targets_by_wf = workflow_targets_by_workflow(repo_root)
    dir_targets: list[tuple[str, str]] = []
    file_targets: dict[str, list[str]] = {}
    for wf, targets in targets_by_wf.items():
        for target in targets:
            if target.endswith(".py"):
                file_targets.setdefault(target, []).append(wf)
            elif (repo_root / target).is_dir():
                dir_targets.append((wf, target))
    # Perimetres `test-cwd` : joues depuis leur propre cwd.
    for wf, perimeters in WORKFLOW_TEST_CWD.items():
        for perimeter in perimeters:
            if (repo_root / perimeter).is_dir():
                dir_targets.append((wf, perimeter))

    # Les workflows qui citent des FICHIERS d'un repertoire : c'est la
    # jambe qui pourrait prendre un fichier voisin non cite.
    legs_by_dir: dict[str, list[str]] = {}
    for target, wfs in file_targets.items():
        legs_by_dir.setdefault(str(Path(target).parent.as_posix()), []).extend(wfs)

    unplayed: list[dict] = []
    collected = 0
    excluded_count = 0
    for rel, items in discover_test_files(repo_root).items():
        if any(rel == ex or rel.startswith(ex + "/") for ex in excluded):
            excluded_count += 1
            continue
        leg = None
        for wf, directory in dir_targets:
            if rel.startswith(directory + "/"):
                leg = wf
                break
        if leg is None:
            leg = next((wf for wf in file_targets.get(rel, [])), None)
        if leg is not None:
            collected += 1
            continue
        candidates = sorted(set(legs_by_dir.get(
            str(Path(rel).parent.as_posix()), [])))
        unplayed.append({
            "path": rel,
            "items": items,
            "candidates": candidates or [ENTRY_POINT_WORKFLOW],
        })
    return {
        "collected": collected,
        "excluded": excluded_count,
        "unplayed": unplayed,
    }


def excluded_population(repo_root: Path, excluded: dict[str, str]) -> dict:
    """Population reellement exclue : marqueurs, fichiers, items, orphelins.

    Un marqueur ORPHELIN pointe un chemin qui n'existe plus sur l'arbre
    (renommage depuis) : il n'exclut plus rien, et la population qu'il
    pretendait couvrir a change de chemin. Il est signale — l'ecriture du
    marqueur appartient au fichier de workflow, pas a cet organe.
    """
    files = 0
    items = 0
    orphans: list[str] = []
    for path in sorted(excluded):
        target = repo_root / path
        if not target.exists():
            orphans.append(path)
            continue
        if target.is_file():
            modules = [target]
        else:
            modules = [m for m in iter_python_files(target)
                       if is_test_file_name(m.name)]
        for module in modules:
            count = collectible_item_count(module)
            if count:
                files += 1
                items += count
    return {
        "marqueurs": len(excluded),
        "fichiers": files,
        "items": items,
        "orphelins": orphans,
    }


def ratchet_problems(population: dict) -> list[str]:
    """Le cliquet : la population exclue ne doit pas CROITRE.

    C'est le COMPTE qui est verifie, pas la presence du marqueur. Une
    baisse verdit et invite a rebaseline (le message le dit).
    """
    problems: list[str] = []
    for key, baseline in CI_EXCLUDED_BASELINE.items():
        value = int(population.get(key, 0))
        if value > baseline:
            problems.append(
                f"population CI-EXCLUDED en hausse : {key} = {value} > "
                f"baseline {baseline} (+{value - baseline}) — lever une "
                f"exclusion (ou justifier l'ajout) avant de rebaseliner"
            )
    return problems


def plan_problems(excluded: dict[str, str]) -> list[str]:
    """Chaque exclusion a une cible de remediation declaree, et reciproquement."""
    problems: list[str] = []
    for path in sorted(excluded):
        target = CI_EXCLUDED_PLAN.get(path)
        if target is None:
            problems.append(
                f"exclusion sans cible declaree : {path} — ajouter "
                f"l'entree dans CI_EXCLUDED_PLAN ({', '.join(PLAN_TARGETS)})"
            )
        elif target not in PLAN_TARGETS:
            problems.append(
                f"cible d'exclusion inconnue ({target}) : {path}"
            )
    for path in sorted(CI_EXCLUDED_PLAN):
        if path not in excluded:
            problems.append(
                f"cible declaree pour une exclusion absente : {path} — "
                f"retirer l'entree de CI_EXCLUDED_PLAN ou reecrire le "
                f"marqueur CI-EXCLUDED"
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
    ap.add_argument(
        "--baseline",
        type=Path,
        default=None,
        help="Ratchet #25366 T4 : juger les sens d'inventaire contre la "
        "dette connue enregistrée dans ce JSON — tolérée telle quelle, "
        "tout finding NOUVEAU (dossier non trié inédit, basename "
        "dupliqué inédit ou en croissance) fait échouer. Exige "
        "--inventory.",
    )
    ap.add_argument(
        "--write-baseline",
        type=Path,
        default=None,
        help="Écrire la dette actuelle comme baseline du ratchet puis "
        "sortir (régénération T1/T2). Exige --inventory.",
    )
    args = ap.parse_args()

    if not args.inventory and (args.baseline or args.write_baseline):
        ap.error("--baseline et --write-baseline exigent --inventory")
    if args.baseline is not None and args.write_baseline is not None:
        ap.error("--baseline et --write-baseline sont exclusifs")

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

    strict = args.strict or not args.advisory

    # Huitième sens (#25366 T5, #26736) : le CLIQUET sur la population
    # exclue. Il est BLOQUANT dans toute invocation, y compris dans la voie
    # rapide : c'est le COMPTE qui est verifie, pas la presence du marqueur.
    # Un marqueur `CI-EXCLUDED` satisfait la garde (le repertoire est
    # compte comme couvert) sans qu'aucune jambe ne le joue — sans ce
    # cliquet, la population pouvait croitre sans bruit.
    population = excluded_population(repo_root, excluded)
    ratchet = ratchet_problems(population)
    plan_issues = plan_problems(excluded)
    print(
        f"Population CI-EXCLUDED : {population['marqueurs']} marqueur(s), "
        f"{population['fichiers']} fichier(s) a item collectible, "
        f"{population['items']} item(s) collectible(s) "
        f"(baseline {CI_EXCLUDED_BASELINE['marqueurs']} / "
        f"{CI_EXCLUDED_BASELINE['fichiers']} / "
        f"{CI_EXCLUDED_BASELINE['items']})"
    )
    for problem in ratchet:
        print(f"  FAIL {problem}")
    for problem in plan_issues:
        print(f"  FAIL {problem}")
    for orphan in population["orphelins"]:
        print(
            f"  INFO marqueur CI-EXCLUDED orphelin (chemin absent de l'arbre) : "
            f"{orphan} — il n'exclut plus rien ; le chemin a peut-etre ete "
            f"renomme (le marqueur se reecrit dans le workflow, pas ici)"
        )

    # Septième sens (#25366 T5, #26736) : la COUVERTURE PAR FICHIER. Un
    # fichier qui porte au moins un item collectible et qu'aucune cible de
    # workflow ne collecte est signale. La dette est reelle et connue : le
    # sens est donc ADVISORY dans l'invocation simple (la voie rapide
    # imprime le compte et les premiers noms) et STRICT sous `--inventory`,
    # comme les sens de consolidation de #25366 T0.
    coverage = file_coverage(repo_root, excluded)
    unplayed = coverage["unplayed"]
    # Le sens fichier est STRICT sous `--inventory` (comme les sens de
    # consolidation) et ADVISORY dans l'invocation simple : la dette est
    # reelle et connue, elle se vide par tranches, pas par un rouge bloque.
    file_strict = bool(args.inventory) and strict
    if unplayed:
        print(
            f"Fichiers de test a item collectible qu'aucune jambe ne "
            f"collecte : {len(unplayed)}"
        )
        for finding in (unplayed if args.inventory else unplayed[:20]):
            print(
                f"  {'FAIL' if file_strict and args.baseline is None else 'INFO'}"
                f" {finding['path']} "
                f"({finding['items']} item(s)) — jambe candidate : "
                f"{', '.join(finding['candidates'])}"
            )
        if not args.inventory and len(unplayed) > 20:
            print(
                f"  ... et {len(unplayed) - 20} autre(s) — liste complete : "
                f"`python scripts/check_testpaths_coverage.py --inventory`"
            )
    elif args.verbose:
        print(
            f"[ok] les {coverage['collected']} fichiers de test a item "
            f"collectible sont collectes par une jambe"
        )

    # Inventaire (#23359) et sens de consolidation (#25366 T0). Depuis T0,
    # l'inventaire est STRICT PAR DÉFAUT (--advisory rétrograde) : le rouge
    # est le signal qui motive les tranches T1 (trier les répertoires) et
    # T2 (dédoubler les basenames), pas une régression à corriger d'urgence.
    # Depuis T4 (#25366), la garde CI (fast lane) appelle ce script AVEC
    # --inventory --baseline : la dette connue (baseline JSON committée)
    # est tolérée, tout finding NOUVEAU rougit la PR — la classe ne peut
    # plus revenir ni croître pendant que T2 épuise la dette.
    write_mode = args.write_baseline is not None
    inventory: list[str] = []
    dupes: dict[str, list[str]] = {}
    convergence: list[str] = []
    baseline_failures: list[str] = []
    if args.inventory:
        # En mode baseline, l'impression des trous reste INFO (le verdict
        # du ratchet est porté par judge_inventory_against_baseline) ; en
        # mode écriture, strict=True pour lister la dette enregistrée.
        inventory = run_inventory(
            repo_root,
            testpaths,
            excluded,
            (strict or write_mode) and args.baseline is None,
        )
        # Cinquième sens (#25366 T0) : basenames dupliqués.
        dupes = duplicate_basenames(repo_root, excluded)
        if dupes:
            print(
                f"Basenames de modules portés par >= 2 répertoires de tests "
                f"découverts : {len(dupes)}"
            )
            for name, dirs in dupes.items():
                print(f"  {'FAIL' if strict and args.baseline is None else 'INFO'} {name} — {', '.join(dirs)}")
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
                print(f"  {'FAIL' if strict and args.baseline is None else 'INFO'} {t}")
        elif args.verbose:
            print("[ok] toutes les cibles-dossier CI sont dans les testpaths")
        # T4 (#25366) : ratchet — dette connue tolérée, nouveau refusé.
        if write_mode:
            write_inventory_baseline(
                args.write_baseline,
                inventory,
                dupes,
                [f["path"] for f in unplayed],
            )
            print(f"[ok] baseline ratchet écrite : {args.write_baseline}")
            return 0
        if args.baseline is not None:
            baseline_failures = judge_inventory_against_baseline(
                inventory,
                dupes,
                [f["path"] for f in unplayed],
                load_inventory_baseline(args.baseline),
            )

    # Verdict des sens d'inventaire : rouges en strict (T0), SAUF en mode
    # baseline (T4) où seuls les findings NOUVEAUX rougissent — la dette
    # enregistrée est tolérée jusqu'à résorption T1/T2. Le sens de
    # convergence (critère 1) reste refusé sans tolérance dans tous les
    # modes stricts : il est mesuré à zéro sur main.
    if args.baseline is not None:
        # Mode ratchet : seuls les findings NOUVEAUX rougissent (le
        # juge couvre dossiers, dupes ET fichiers non collectés), la
        # convergence reste refusée sans tolérance (zéro sur main).
        inventory_red = bool(baseline_failures) or (
            strict and bool(convergence)
        )
    else:
        inventory_red = strict and bool(
            inventory or dupes or convergence
        ) or (file_strict and bool(unplayed))

    return 1 if (
        uncovered
        or problems
        or uncovered_disk
        or missing
        or namespace_problems
        or inventory_red
        or ratchet
        or plan_issues
    ) else 0


if __name__ == "__main__":
    sys.exit(main())
