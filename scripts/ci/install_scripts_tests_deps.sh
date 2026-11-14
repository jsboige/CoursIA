#!/usr/bin/env bash
# Installation de l'environnement de la suite `scripts-tests`.
#
# SOURCE UNIQUE : ce fichier est appele par deux jambes.
#
#   1. `.github/workflows/scripts-tests.yml`, etape `Install dependencies` --
#      la jambe `Scripts Tests` elle-meme.
#   2. `.github/workflows/slow-lane.yml`, job `lot` -- le lot quotidien en
#      ombre de la voie lente (P3 du plan « CI a deux etages », #25510).
#
# Pourquoi un fichier et non une liste recopiee : le lot en ombre mesure la
# duree de la suite qu'on veut deplacer. Une liste de dependances minimale
# donne des durees qu'on ne peut comparer a rien (une dependance manquante
# rend la PR « non mesurable » au lieu de la faire echouer). Un seul script,
# appele par les deux jambes, rend les durees comparables par construction --
# et supprime la derive entre l'environnement mesure et l'environnement reellement
# employe par la suite.
#
# Le bloc ci-dessous est celui de `scripts-tests.yml`, extrait verbatim le
# 2026-11-09 (PR #25521). Toute modification de l'un doit etre portee dans
# l'autre : c'est la raison d'etre du fichier.
set -eo pipefail
python -m pip install --upgrade pip
# Core test deps imported across scripts/ + notebook_tools/ suites.
# Mirror the ML job's scientific stack where suites reuse it, and add
# the lightweight deps the scripts/ suites import that the ML job omits
# (requests, bcrypt, jupyter_client — see #2871 root-cause list).
# pyarrow >= 26 (#21764) : sous 26, le noyau ipykernel meurt
# (Unhandled SIGSEGV) au chargement de pyarrow, sur la chaine
# torch -> dask -> xarray -> pandas -> pyarrow. Mesure : 24.0.0
# crash, 26.0.0 OK ; l'image CI portait 25.0.1, non mesure. Sans
# plancher, `pip install pyarrow` est satisfait par la version
# deja presente dans l'image (25.0.1) et n'echange rien.
pip install numpy pandas scipy "pyarrow>=26" pytest
pip install requests bcrypt jupyter_client
# ipykernel (#18279) : ce job n'enregistrait AUCUN kernelspec
# `python3`, si bien que les deux tests d'integration de
# scripts/tests/test_papermill_meta_strip.py se SAUTAIENT en silence
# (skipif sur la presence du kernelspec). La panne « kernel mort au
# spawn » n'existait alors plus que sur les runners qui avaient le
# kernel : machine-specifique en apparence, FILTREE en realite -- et
# c'est ce filtrage qui a fait suivre pendant dix jours un axe de
# diagnostic .NET alors qu'aucun noyau .NET n'etait lance. Regle F :
# un environnement se repare, il ne se contourne pas par un skip.
# Le test de visibilite ajoute dans le meme commit rougit si ce
# kernelspec disparait a nouveau.
pip install ipykernel
pip install pyyaml tomli
# python-dotenv: scripts/notebook_tools/whisper_int8_comparison.py (and several
# genai-stack modules) import `dotenv` at top level.
pip install python-dotenv
# matplotlib: MyIA.AI.Notebooks/GameTheory/trust_simulation/visualization.py
# imports it at module top level. Without it, pytest bails on
# collection errors for test_trust_simulation.py and skips the
# entire suite, masking every other test result. See #4937.
pip install matplotlib
# scikit-learn : DEPENDANCE HERITEE DU TOOLCACHE, desormais declaree.
# scripts/tests/test_golden_quantitative_claims.py l'importe deja, et
# scripts/tests/test_ws_probes_margin.py ajoute par #24073 l'importe
# via scripts/repro/ws_probes_margin.py. La suite ne collectait que
# parce que le pool `coursia-linux` porte scikit-learn en residu d'un
# job ML -- une dependance qui n'est declaree nulle part est une
# panne en attente (le jour ou le toolcache change, la collecte rend
# une erreur bruyante sur une PR innocente). Meme motif que
# `qc-mcp-lite` / `ModuleNotFoundError: mcp`. Regle F : l'environnement
# se repare, il ne se contourne pas par un skip.
pip install scikit-learn
# papermill + nbformat: genai-stack/commands/notebooks.py imports
# papermill at top level, so test_genai_notebooks.py needs it at
# collection time. Both are declared deps of genai-stack
# (scripts/genai-stack/requirements.txt). Lets us re-include the
# genai test suites that were excluded as missing-dep (#2871 part 2).
pip install papermill nbformat
# huggingface_hub: declare par le requirements du genai-stack
# (scripts/genai-stack/requirements.txt, `huggingface_hub>=0.20.0`) mais
# absent de l'environnement du runner. Le test
# scripts/genai-stack/tests/test_genai_stack_round4.py
# ::TestDownloadQwenDockerScratch::test_scratch_is_anchored_on_repo_root
# echoue la dessus sur TOUTE PR : son
# `patch("huggingface_hub.hf_hub_download")` est une cible CHAINEE, donc
# `mock.patch` resout `huggingface_hub` par import -- l'absence du
# paquet suffit a lever ModuleNotFoundError, avant meme le corps du
# test. commands/models.py n'importe le module qu'a l'interieur de ses
# fonctions (lignes 166/204/285/333) : la cible du patch doit
# pouvoir resoudre le paquet, l'import tardif du code ne la dispense
# pas. Meme motif que `python-sat` / `opentelemetry` plus bas : une
# dependance declaree et non installee est une panne en attente.
# Regle F : l'environnement se repare, il ne se contourne pas par un skip.
pip install "huggingface_hub>=0.20.0"
# Version RESOLUE de pyarrow (#21764) : l'acceptance demande que le
# log affiche la version installee, pas seulement la contrainte.
# Un plancher non affiche est un plancher non prouve.
python -c "import pyarrow; print('pyarrow resolu:', pyarrow.__version__)"
# nbconvert: scripts/notebook_tools/render_oversized_nbconvert.py +
# scripts/tests/test_render_oversized_nbconvert.py (#10969). The
# fail_non_notebook test asserts the real nbformat NotJSONError text,
# so the env must have nbconvert installed (rule F, not a skipif).
pip install nbconvert
# pyjwt[crypto]: scripts/secrets/github_app_token.py signe le JWT d'App
# GitHub avec PyJWT, et ses deux controles positifs le verifient avec la
# cle publique (#17437). Declare ici plutot qu'un skip : sans lui, ces
# tests ne rendent jamais leur verdict dans l'organe qui les execute.
pip install "pyjwt[crypto]"
# torch (CPU) is needed at collection time by the Sudoku/RRN test
# modules under scripts/tests/ (they `import torch` at top level and
# skip themselves at runtime when CUDA is absent). Without it those
# modules fail to import = collection errors. Same index as ml-tests.yml.
pip install torch --index-url https://download.pytorch.org/whl/cpu
# arch (GARCH) for the scripts/tests/ml GARCH-baseline suite, which has
# no other CI home: ml-tests.yml is scoped to ML-Training-Pipeline
# (#2872), so without arch here those 9 tests are missing-dep failures.
# Pulls statsmodels/patsy — still CPU-light.
pip install arch
# rapidfuzz + unidecode + openpyxl: dotnet/GradeBookApp/gradebook.py imports
# all three at module top level, so test_fuzzy_match_group.py needs
# them at collection time (famille 5 de #14615). The test guards with
# importorskip, but wiring it into this run means running it for real.
pip install rapidfuzz unidecode openpyxl
# pypdf: scripts/tests/test_check_bibliography_pdf_integrity.py
# builds a valid PDF with PdfWriter to feed the organ (#17980).
# Without it the 6 tests fail on ModuleNotFoundError instead of
# exercising the script.
pip install pypdf
# RDF catalog export: test_generate_curriculum_rdf imports rdflib
# at collection time and validates the produced graph with pyshacl.
# The test is included by scripts/notebook_tools/tests below, so
# these are job dependencies, not optional notebook extras.
# Match the SemanticWeb series' supported RDF stack.
pip install "rdflib>=7.0.0,<8.0.0" "pyshacl>=0.27.0"
# open_spiel: coeur du service Kernel Gateway CFR (GameTheory/gateway,
# #21104 / pli 0 de l'Epic #19571). La roue 2.0.2 manylinux_2_27
# x86_64 existe pour le python 3.11 de ce job ; sans le paquet, la
# cible pytest ci-dessous est une erreur de collecte au lieu
# d'exercer le service pour de vrai.
pip install open_spiel
# ortools: GameTheory/tests collecte aussi amd_synthesis.py (#22381),
# qui importe CP-SAT au niveau module. Reprendre le plancher declare
# dans GameTheory/requirements.txt pour eviter une erreur de collecte.
pip install "ortools>=9.11"
# z3-solver: MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/gateway/
# test_z3_sudoku_core.py imports z3 at module level (#21100, pli 0
# Origami). Without it the suite fails on ModuleNotFoundError
# instead of exercising the service core.
pip install z3-solver
# python-sat (PySAT): ArgumentAnalysis/argumentation_lib/sat_handler.py
# branche l'entailement propositionnel sur l'organe du depot
# (SymbolicAI/ext_tools/sat_solver.py), qui importe `pysat` et pose
# PYSAT_AVAILABLE. Sans le paquet, l'organe retombe puis
# `_solve_with_pysat` leve ModuleNotFoundError : les 12 tests de
# tests/test_sat_handler.py echouent au lieu d'exercer le moteur
# (mesure du rouge : run 41002293693, job 123889255619, 2026-10-30).
# Regle F : on installe la dependance, on ne la saute pas -- un
# skipif aurait rendu la suite verte en n'executant rien.
# Plancher : `python-sat>=1.8.dev13`, la forme deja utilisee par
# Search/requirements.txt. TOUTES les publications PyPI de
# python-sat sont des pre-releases : un specifier qui nomme une
# pre-release (ici 1.8.dev13) est sans ambiguite pour pip, alors
# qu'une borne stable (>=0.1.8, forme de GameTheory/requirements.txt)
# n'en nomme aucune et reste ambigue. Le solveur
# 'cadical195' (defaut de sat_solver.solve_sat) est present dans
# les roues resolues, verifie sur 1.8.dev19 (cp311/manylinux) et
# 1.9.dev17.
pip install "python-sat>=1.8.dev13"
python -c "import pysat; from importlib.metadata import version; print('python-sat resolu:', version('python-sat'))"
# jupyter_kernel_gateway: son module s'importe `kernel_gateway` et
# `run_gateway.py` le sonde au preflight (#22439). Sans le paquet,
# test_run_gateway.py signalerait une dependance manquante au lieu
# d'exercer le lanceur.
pip install jupyter_kernel_gateway
# opentelemetry-sdk + pydantic + openai : trois paquets que ce job
# consomme a l'import mais n'installait pas -- il ne passait que sur
# les slots au toolcache chaud (residu d'installations d'autres
# jobs). Mesure du cas rouge : run 40182043367, job 121134940940,
# runner myia-po-2027-linux-docker-4 (toolcache neuf, 2026-10-25) :
# 157 x ModuleNotFoundError 'opentelemetry' (COLLECTE de
# test_provider_gate_18709.py -- provers.py:48 -> otel_setup.py:31
# `from opentelemetry.sdk.trace.export import ...` ; l'erreur de
# collecte n'est JAMAIS reclassee SKIP par le conftest #21331, qui
# ne voit que les tests collectes), 60 x 'pydantic' (suites Audio
# v4 : schemas.py:10 importe pydantic au niveau module, le job ADK
# qui l'epingle est un AUTRE job), 2 x 'openai' (config.py:401
# `from openai import AsyncOpenAI`, atteint dans la fenetre de stub
# #18709 ou agent_framework passe mais pas ses deps). Le plancher
# >=1.20.0 reprend agent_tests/requirements.txt l.26 -- le sdk
# n'arrive jamais transitivement via agent-framework. Pins pydantic
# et openai alignees sur le job ADK ci-dessous (2.12.5 / 2.24.0) :
# les versions mesurees vertes sur slot chaud. Contre-teste en venv
# vierge : sans les trois, "1 error during collection" sur
# opentelemetry ; avec, 36 passed + 1 skipped (le skip = coordinator
# reclasifie, comportement #21331).
pip install "opentelemetry-sdk>=1.20.0" "pydantic==2.12.5" "openai==2.24.0"
# nashpy: MyIA.AI.Notebooks/GameTheory/tests/test_bayesian_equilibria.py
# (#22382) imports it at module level. `gametheory-tests.yml` l'installe,
# mais CE job collecte aussi MyIA.AI.Notebooks/GameTheory/tests : sans
# le paquet, une seule erreur de collecte fait echouer les 21098 tests
# verts du run (mesure du 2026-10-27, run 40489527870 :
# "1 error in 750.75s" -> Scripts Tests rouge -> PR gate rouge).
pip install nashpy
# pytest-xdist: this job's 13 suites run in parallel (-n 4) below.
# Not a speed nicety -- the sequential run is what makes this job
# unschedulable on half the pool. Over 68 `Scripts Tests (CPU)` jobs,
# the `myia-po-2024-linux-docker-*` runner class concluded 3 of 40
# (37 cancelled, 18.3 min average) while `myia-ai-01-wsl-*` concluded
# 24 of 25 (9.9 min average). A slower runner class against a
# sequential suite sitting near the cap is a scheduling lottery, not
# a timeout that wants raising. See #14598 / #15574.
# pytest >= 8 : l'option ini `consider_namespace_packages`, qui
# desambiguise les noms de modules pytest, n'existe pas avant 8.0.
# Sur un pytest plus ancien elle serait ignoree SANS BRUIT (simple
# `PytestConfigWarning`) et la collision `tests.conftest`
# reviendrait. Le runner porte 9.1.1 (mesure sur le log du run
# 40409945388) : ce pin est une garantie de non-regression, pas un
# upgrade.
pip install "pytest>=8" pytest-xdist
