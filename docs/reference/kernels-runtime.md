# Kernels & Runtime — Cluster CoursIA

Document de référence détaillant l'inventaire kernels obligatoire sur toute machine du cluster (cf CLAUDE.md règle H.2).

**Regle user 2026-05-07** : toute machine du cluster (ai-01, po-2023, po-2024, po-2025, po-2026) doit pouvoir executer n'importe quel notebook du depot. Reparation env > contournement (regle F, cf [env-python-reparation.md](env-python-reparation.md)).

## Setup macOS / Linux (poste contributeur)

Ce document est centré cluster Windows. Pour le setup d'un poste contributeur **macOS / Linux** (équivalents `brew`/`apt` des commandes `winget`/`choco`, `elan` Lean sans WSL, backend MPS sur Apple Silicon), cf [setup-linux-macos.md](setup-linux-macos.md). Les kernels .NET Interactive, Python et Lean 4 sont cross-OS ; les notebooks s'exécutent à l'identique modulo le backend GPU.

## .NET Interactive (C# notebooks)

Notebooks dans `SymbolicAI/SemanticWeb/`, `SymbolicAI/SmartContract/`, `Search/`, `Sudoku/`, `ML/`, `Probas/`.

| Prerequis | Version | Verification |
|-----------|---------|-------------|
| .NET SDK | 8.0 + 9.0 (10.0 optionnel) | `dotnet --list-sdks` |
| dotnet-interactive | **1.0.617701** (verifie sur ai-01, cf ci-dessous) | `dotnet interactive --version` |
| Jupyter kernels `.net-csharp`, `.net-fsharp`, `.net-powershell` | auto-installes | `jupyter kernelspec list` |

Installation : `dotnet tool install --global Microsoft.dotnet-interactive --version 1.0.617701` puis `dotnet interactive jupyter install`. **Preciser la version** : une installation sans `--version` prend le dernier build publie, aujourd'hui 1.0.712001, qui casse `#!import` (cf tableau ci-dessous).

**Execution** : `python scripts/notebook_tools/notebook_tools.py execute <notebook>` — qui pilote Papermill avec `--kernel .net-csharp`. Le kernel preserve l'etat entre cellules, `#!import` compris.

Ce document affirmait « Papermill ne supporte pas .NET Interactive » et renvoyait vers l'execution cell-by-cell par MCP Jupyter. **C'est faux**, et la consequence etait couteuse : le chemin MCP hang (#835), donc des notebooks .NET etaient committes sans re-execution (violation C.2/H.3, cf l'anti-pattern PR #1591 cite en CLAUDE.md regle F). Verifie firsthand sur ai-01 le 2026-07-25 (dni 1.0.617701) — Papermill execute bien un notebook `.net-csharp` de bout en bout, `execution_count` et sorties reelles a l'appui, y compris a travers un `#!import`.

La **seule** limite reelle est l'**injection de parametres** : Papermill n'a pas de traducteur C#, donc une cellule taguee `parameters` avec `-p` produit `Translator for 'C#' language does not support parameter introspection.` — l'avertissement est emis, l'injection est ignoree, **et le notebook s'execute quand meme**. Les notebooks .NET du depot ne prennent pas de parametres Papermill ; `BATCH_MODE` passe par variable d'environnement, pas par `-p`, et reste donc disponible.

Deux limites voisines, **distinctes** de celle-ci, restent vraies : le restore `#r "nuget:"` est bloque cluster-wide en Papermill headless (cf [dotnet-plotly-zero-restore.md](dotnet-plotly-zero-restore.md)), et la **CI** ne peut pas re-executer ces notebooks faute de kernel installe sur le runner — d'ou l'exigence d'execution **locale** avant commit ([pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md) §D).

**Borne du blocage nuget** (mesure firsthand po-2026 le 2026-08-08 sur `origin/main` `f153cf0c8`, logique de detection = `notebook_tools.py` L375-389 ; l'issue #10024 rapportait 237/129/108/3 mesurés par ai-01 le meme jour, ecart ~7 = evolution du repo + heuristique de classification legerement plus large) :

```
230 notebooks .NET dans MyIA.AI.Notebooks/
  127  SANS aucun #r "nuget:"   -> executables headless MAINTENANT
  103  avec #r "nuget:"          -> le blocage #r nuget peut s'appliquer
    2  avec >=1 code cell exec_count=None  (dont 1 QC, exempt)
```

Cette borne **n'etablit pas** que le blocage `#r "nuget:"` est faux pour les 103 qui en contiennent. Elle etablit qu'il a ete invoque comme dispense generale (PR #10021, `RECOVERABLE-MACHINE` + outputs transplantes hors-depot) pour un notebook qui **n'en contenait aucun** — la forme meme d'une preuve d'execution falsifiee. Le reflexe avant d'invoquer un blocage .NET :

```bash
grep -c '#r "nuget:' <notebook>     # 0  ->  RECOVERABLE-LOCAL : executer pour de vrai
```

### Version : 1.0.617701, pas « >= 1.0.700 »

| Version | Etat | Preuve |
|---------|------|--------|
| 1.0.522904 | a eviter | bug Roslyn |
| 1.0.552801 | ancien pin — **ne plus viser** : hote net8.0-only, bloque les notebooks qui referencent des DLL `net9.0` | [`Search/Part4-Metaheuristics/README.md`](../../MyIA.AI.Notebooks/Search/Part4-Metaheuristics/README.md) (MGS-6 a MGS-9, `MetaGeneticSharp.Extensions`) |
| **1.0.617701** | **cible** — cellule C# et `#!import` OK | verifie firsthand sur ai-01 le 2026-07-25 : `notebook_tools.py execute` sur un notebook `.net-csharp` (SUCCESS 4,4 s, `execution_count: 1`) et sur une paire `#!import helper.ipynb` + appel de la methode importee (SUCCESS 3,8 s, cellule 2 imprime le resultat) |
| 1.0.712001 | a eviter | `#!import` casse (`ArgumentNullException`) — bloque la re-execution de `Sudoku-15-Infer-Csharp` (#8485, #8525) et le pivot d'env #8369 |

Une contrainte `>= 1.0.700` figurait ici : elle est **fausse et nuisible** — elle exclut le pin qu'elle citait dans la meme ligne (552801 < 700) et n'admet, aujourd'hui, que la version cassee. Un `#!import` en echec est un **defaut d'environnement reparable en une commande** (regle F), jamais un blocage utilisateur :

```bash
dotnet tool update --global Microsoft.dotnet-interactive --version 1.0.617701
dotnet interactive jupyter install
```

### Consequence du pin : plafond Roslyn 4.12.0.0 sur les packages NuGet

Le pin n'est pas gratuit. `1.0.617701` **embarque Roslyn 4.12.0.0** (`Microsoft.CodeAnalysis.CSharp.dll`, FileVersion `4.1200.24.57207`, mesure firsthand sur ai-01 le 2026-08-16 dans `.dotnet/tools/.store/.../tools/net9.0/any/`). Tout package reference par `#r "nuget: ..."` qui **exige** une version superieure echoue au chargement :

```
System.IO.FileNotFoundException: Could not load file or assembly
'Microsoft.CodeAnalysis.CSharp, Version=4.13.0.0, ...'
```

**Un `#r "nuget: Microsoft.CodeAnalysis.CSharp, 4.13.0"` ne repare PAS ce cas** : le kernel a deja charge son propre Roslyn dans l'ALC au demarrage, et `#r` ne substitue pas une assembly deja resolue. Le correctif est donc **toujours cote package**, jamais cote kernel — remonter le kernel casserait `#!import` sur tout le depot (tableau ci-dessus).

Instance mesuree (#11104, ML-3 AutoML) :

| Package | Dependance `Microsoft.CodeAnalysis.CSharp` | Sur le kernel pinne |
|---|---|---|
| `Microsoft.ML.AutoML` **0.23.0** | `[4.13.0, )` | **echoue** — `FileNotFoundException` |
| `Microsoft.ML.AutoML` **0.22.3** | `[4.9.2, )` | **OK** — satisfait par 4.12.0.0 |

`0.22.3` prend `Microsoft.ML [4.0.3, )`, borne **ouverte** : le pin `Microsoft.ML, 5.0.0` du notebook reste valide. Mesure de bout en bout apres bascule : **10/10 cellules, 0 erreur, 86,1 s**.

Verifier la dependance d'un package avant d'incriminer le kernel :

```bash
grep -o 'id="Microsoft.CodeAnalysis[^"]*" version="[^"]*"' \
  ~/.nuget/packages/<pkg>/<version>/<pkg>.nuspec
```

**Piege de diagnostic adjacent** : sur cet hote (32 threads), un notebook .NET non borne en threads OpenMP part en timeouts de cellule qui *ressemblent* a un blocage kernel. `OMP_NUM_THREADS=4` a ramene ce meme notebook de **6 380,9 s (7 cellules en timeout a 900 s)** a **14,8 s** — facteur **x431**. Borner les threads **avant** de conclure a un hang.

## Python 3.10+ (notebooks Python)

Notebooks dans `GenAI/`, `QuantConnect/`, `GameTheory/`, `IIT/`, `SymbolicAI/SemanticWeb/` (Python).

### Envs Conda dédiés (ai-01, référence)

| Env | Python | Path | Usage principal |
|-----|--------|------|-----------------|
| **coursia-ml-training** | 3.11.15 | `C:\Users\MYIA\miniconda3\envs\coursia-ml-training` | ML training (PyTorch CUDA 12.6 RTX 4090, sklearn, scipy, hmmlearn, pyarrow) |
| **coursia-sae** | 3.12.13 | `C:\Users\MYIA\miniconda3\envs\coursia-sae` | Traces SAE / substrat LLM série ICT (ICT-21+, #5643) : torch 2.12 CUDA 12.6, transformers 5.x. Extraction GPU = `CUDA_VISIBLE_DEVICES=2` obligatoire (cf Quick Reference GPU) |
| `mcp-jupyter` | 3.10+ | `C:\Users\MYIA\miniconda3\envs\mcp-jupyter` | MCP Jupyter server (kernels Python du MCP) |
| `epita_symbolic_ai` | 3.10+ | `C:\Users\MYIA\.conda\envs\epita_symbolic_ai` | EPITA SymbolicAI : `rdflib`, `owlready2`, `reasonable`, `pyshacl` |
| `epita_symbolic_ai_sherlock` | 3.10+ | `C:\Users\MYIA\.conda\envs\epita_symbolic_ai_sherlock` | Variante Sherlock |
| `llmcompressor` | 3.10+ | `C:\Users\MYIA\miniconda3\envs\llmcompressor` | LLM quantization tooling |
| `e2e_test_env` | 3.10+ | `C:\Users\MYIA\miniconda3\envs\e2e_test_env` | E2E tests |
| `base` | 3.10+ | `C:\Users\MYIA\miniconda3` | Conda base — NE PAS modifier |

### Stack ML training (coursia-ml-training, vérifié 2026-05-06)

- Python 3.11.15
- PyTorch 2.11.0+cu126 (CUDA 12.6 active sur RTX 4090)
- sklearn 1.8.0, scipy 1.17.1, pandas 3.0.2
- hmmlearn (regime detection)
- pyarrow (parquet cache)

### Usage (ai-01)

**Direct execution** (recommande pour scripts long-running) :

```powershell
& "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe" train_moe.py --symbol SPY --regime-method hmm --n-folds 5 --seed 42
```

**Activation interactive** :

```powershell
conda activate coursia-ml-training
python train_moe.py ...
```

**Background avec log** :

```bash
nohup "C:/Users/MYIA/miniconda3/envs/coursia-ml-training/python.exe" train_moe.py ... > run.log 2>&1 &
```

### Pourquoi un env Conda dédié ?

Sur ai-01, le Python 3.14 système est instable : scipy DLL corruption récurrente, conflits pip Python 3.12 vs 3.14, `~cipy/` résidus après force-reinstall ratés. L'env Conda `coursia-ml-training` est l'env de référence stable pour le training ML, configuré expressément avec PyTorch CUDA pour la RTX 4090.

Incident 2026-05-06 : training MoE tenté directement sur Python 3.14 système : `scipy DLL load failed` → `sklearn force-reinstall denied`. Résolution : utiliser l'env Conda dédié. D'où la règle F (cf [env-python-reparation.md](env-python-reparation.md)).

**Réflexe coordinateur** : avant tout dispatch ML training local, vérifier que le script utilise `coursia-ml-training`. Si un agent rapporte un `ImportError` ML (sklearn, scipy, torch), premier debug = "tu as utilisé l'env Conda `coursia-ml-training` ?".

### po-2025 (inventaire complet, 2026-05-23)

**Machine**: MSI GE76 Raider, RTX 3080 Ti Laptop 16GB, **CPU-only strict** (11 crashes GPU). Windows 11 Pro Build 26200.

#### Python PATH piège

`python` sur PATH = MS Store Python 3.13 (`C:\Users\jsboi\AppData\Local\Microsoft\WindowsApps\...\python.exe`). Le kernel Jupyter `python3` = conda base (`C:\ProgramData\miniconda3\python.exe`). Pour papermill : utiliser **toujours** le chemin complet du binaire cible.

#### Conda environments

| Env | Python | Path | Usage |
|-----|--------|------|-------|
| base (ProgramData) | - | `C:\ProgramData\miniconda3` | Conda système |
| base (user) | - | `C:\Users\jsboi\miniconda3` | Conda user |
| coursia-ml-training | 3.12 | `C:\Users\jsboi\.conda\envs\...` | ML training (torch CPU-only) |
| epita_symbolic_ai | 3.12 | `C:\Users\jsboi\.conda\envs\...` | SemanticWeb Python (rdflib, owlready2, pyshacl) |
| mcp-jupyter | 3.10 | `C:\Users\jsboi\.conda\envs\...` | MCP Jupyter server |
| mcp-jupyter-py310 | 3.10 | `C:\Users\jsboi\.conda\envs\...` | Papermill execution (Tweety, SW Python, Lean Python, GT) |
| mcp-markitdown | - | `C:\Users\jsboi\.conda\envs\...` | Document conversion |
| mcp-powerpoint | - | `C:\Users\jsboi\.conda\envs\...` | PPTX handling |
| projet-is-roo-new | - | `C:\Users\jsboi\.conda\envs\...` | Roo dev |

#### .NET

- SDKs : 8.0.x, 9.0.x, 10.0.x
- dotnet-interactive : **1.0.617701** (installe, verifie 2026-07-25 — cf [tableau des versions](#version--10617701-pas--100700))
- Kernels : `.net-csharp`, `.net-fsharp`, `.net-powershell`

#### Jupyter kernels (10 registered)

| Kernel | Type | Executable via |
|--------|------|----------------|
| python3 | Python (conda base) | Papermill |
| .net-csharp | .NET 9.0 | Papermill (`notebook_tools.py execute --kernel .net-csharp`) |
| .net-fsharp | .NET | Papermill (`notebook_tools.py execute --kernel .net-fsharp`) |
| .net-powershell | .NET | Papermill (`notebook_tools.py execute --kernel .net-powershell`) |
| conda-torch | Python (torch) | Papermill |
| lean4 | Lean 4 (v4.29.1 Windows) | `notebook_tools.py execute` (in-process Papermill, translator Python enregistre) |
| lean4-wsl | Lean 4 (v4.11.0 WSL) | `notebook_tools.py execute` (non re-mesure c.10024 ; laisser en l'etat si doute) |
| python3-wsl | Python (WSL 3.12) | wsl_papermill.py |
| smartcontracts | Python | Papermill |

**Écart de compte non résolu** : l'intitulé annonce « 10 registered », la table en liste **9**. Non re-mesurable en l'état — po-2025 est **CONFIRMÉ non joignable** firsthand (#9976 : `HTTP 000` + 100 % de perte ping, LAN physiquement disjoint). Ni le 10 ni le 9 ne sont corrigés ici : un relevé `jupyter kernelspec list` tranchera au retour de la machine. Ne pas citer l'un des deux comme mesuré.

**Note** : la colonne *Executable via* disait « MCP Jupyter cell-by-cell » pour les kernels `.net-*` et `lean4*`. C'etait faux pour `.NET` (Papermill execute `.net-csharp` firsthand, cf L19-21 et la mesure nuget ci-dessus) et **ne s'applique pas** au chemin recommande : le MCP `jupyter-papermill` hang (#835) et ignore `kernel_name` (#5211) — il ne doit **jamais** etre le chemin de re-exec cite dans cette table. Pour `lean4`/`lean4-wsl`, le chemin `notebook_tools.py execute` (Papermill in-process avec translator enregistre, `notebook_tools.py` L1139-1179) est le mecanisme reel ; non re-mesure ce cycle, ne pas affirmer sans mesure.

#### Papermill : env de reference

```bash
# Python notebooks : mcp-jupyter-py310
/c/Users/jsboi/.conda/envs/mcp-jupyter-py310/python.exe -m papermill <nb> <out>

# WSL notebooks : wsl_papermill.py
python scripts/notebook_tools/wsl_papermill.py execute <nb>

# .NET : Papermill via l'outil du depot (cf L19-21 — Papermill execute bien .net-csharp)
python scripts/notebook_tools/notebook_tools.py execute <nb> --cell-by-cell --kernel .net-csharp

# Lean (Windows) : notebook_tools (in-process Papermill)
python scripts/notebook_tools/notebook_tools.py execute <nb>
```

#### MCP jupyter-papermill HANG (bug #835) : bascule directe timeout-wrappée, JAMAIS bloquer (HARD)

**Il existe DEUX chemins d'exécution notebook** : (1) le MCP `jupyter-papermill` (cell-by-cell), (2) **papermill/nbconvert en direct** via `notebook_tools` / les binaires ci-dessus. En theorie interchangeables ; en pratique le chemin (2) direct est **le seul recommande** — le MCP (1) hang (#835) et ignore `kernel_name` (#5211), cf regle ci-dessous.

**Le MCP est un piège (bug #835, CLOSED mais reproductible 2026-07-01)** : `mcp__jupyter-papermill__*` peut **bloquer 6 h+ sur un appel `execute`/`manage_kernel` et tuer la session** (root cause = **stdout buffering** qui bloque le spawn Claude Code — ce n'est PAS un serveur mort, donc **un restart ne corrige rien**). Le tracker « PR #660 » cité par erreur dans des cycles antérieurs = GPU-training checkpoints, **sans rapport**.

**Règle (mandat user 2026-07-01)** :
1. **NE JAMAIS appeler naïvement `mcp__jupyter-papermill__*`.** Pour (re-)exécuter un notebook, un agent **bascule IMMÉDIATEMENT** sur `nbconvert --execute` / `python -m papermill` / `notebook_tools`, **wrappé dans un `timeout`** (child process contrôlable, contrairement au pipe MCP qui peut hang). Il **NE bloque JAMAIS** en attendant le MCP.
2. **Preuve que le direct suffit** : Infer-24 (#4710) + Search-13 (#4713) exécutés `nbconvert --execute` exit 0 alors que le MCP était HS.

```bash
# Fallback direct timeout-wrappé (kernel .net-csharp ou python3) — JAMAIS le MCP :
timeout 600 jupyter nbconvert --to notebook --execute --inplace --ExecutePreprocessor.kernel_name=.net-csharp <nb>
timeout 600 /c/Users/jsboi/.conda/envs/mcp-jupyter-py310/python.exe -m papermill <nb> <out>   # python3
```

**Correctif config #835 (par machine worker, dans `.mcp.json`)** : forcer stdout non-bufferisé — `python -u` + `PYTHONUNBUFFERED=1` (+ `--offline`) sur le serveur MCP. Action **user-hand / par-machine** (ai-01 ne configure pas le `.mcp.json` des workers) ; le correctif **définitif** upstream vit dans `roo-extensions` (cross-team). En attendant, la bascule `nbconvert` timeout-wrappée est **obligatoire**, pas optionnelle.

Un worker **oisif une demi-journée** parce que « le MCP hang » = **échec coordinateur** (coordinator-discipline Règle 4/5 : une lane ne s'arrête jamais), jamais un état worker acceptable.

#### MCP execute_notebook async ignore kernel_name (bug #5211) : nbconvert CLI explicite = chemin canonique

**Le MCP `execute_notebook` mode async IGNORE le paramètre `kernel_name`** et utilise le kernelspec stocké dans le notebook (typiquement `python3` = `WindowsApps\Python313`, qui n'a **pas pymc/pyphi/dowhy**) → `NameError` silencieux car la cellule d'import avale l'`ImportError`. Le mode sync honore `kernel_name` mais bloque ~10 min (risque crash session). Les deux modes MCP sont donc **inutilisables** pour forcer un kernel env-spécifique.

**Décision ai-01 (msg-g5awy3, 2026-07-03) — chemin canonique de re-exec kernel-spécifique** : `jupyter nbconvert --execute --inplace --ExecutePreprocessor.kernel_name=<k>` en background (`run_in_background:true`), **JAMAIS le MCP** pour les notebooks nécessitant un env précis (coursia-ml-training, pyphi, lean4-wsl, .net-csharp). Validé firsthand sur 10 notebooks #3436 ce cycle (PyMC/IIT/Probas/GenAI/ML, 0 NameError).

```bash
# Kernel env-spécifique (force le kernel, indépendant du kernelspec stocké) :
jupyter nbconvert --execute --to notebook --inplace \
  --ExecutePreprocessor.kernel_name=coursia-ml-training \
  --ExecutePreprocessor.timeout=900 <nb>.ipynb
```

**Gotcha subprocess CLI (découvert PT_07 #5245, 2026-07-03)** : si le notebook appelle un **CLI empaqueté dans l'env** via `subprocess.run(["<cli>", ...])` (ex `rewardspy`, `dot`, `lean`), le bare `jupyter nbconvert` hérite d'un PATH **sans** le `Scripts\` de l'env → `FileNotFoundError [WinError 2]`. Fix = wrapper avec **`conda run -n <env> jupyter nbconvert ...`** (active l'env = PATH complet avec `Scripts\`). Sans ça, la cellule subprocess fail même si le notebook tournait en interactif Jupyter.

#### SmartContracts (8/14 groups, maj 2026-05-23)

Packages installes dans mcp-jupyter-py310 : web3, py-solc-x, pycryptodome, py_ecc, phe, tenseal, mpyc, xrpl-py, python-bitcoinlib, vyper, tabulate.

**Groupes EXECUTABLES** (8/14) : SC-0, SC-11, SC-15, SC-16-17, SC-19, SC-20, SC-21-23, SC-25.

**Groupes BLOQUES** (6/14) : SC-1 (Foundry/forge), SC-2-10 (anvil), SC-12-14 (Foundry testing), SC-18 (Vyper+anvil), SC-24 (sepolia .env), SC-26 (anvil+phe).

Installation : `python SymbolicAI/SmartContracts/setup_env.py`.

#### Install scripts dans le repo

| Script | Usage |
|--------|-------|
| `SymbolicAI/SmartContracts/setup_env.py` | Installe deps SmartContracts (phases 0-6), setup WSL Foundry |
| `SymbolicAI/Lean/scripts/validate_lean_setup.py` | Valide env Lean (elan, lean4-jupyter, kernel, openai) |
| `SymbolicAI/Lean/scripts/setup_wsl_python.sh` | Setup WSL Python pour lean4-wsl kernel |

### po-2023 (inventaire kernels, 2026-08-10)

**Machine** : hôte des services GenAI Image/Audio/Video (8 services Docker), RTX 3080 + eGPU RTX 3090, 40 GB VRAM (16 + 24) — cf [cluster-agents.md](cluster-agents.md) L10. **po-2023 n'est PAS CPU-only** : la mention « CPU-only strict » de ce fichier (L114) appartient à **po-2025** (MSI GE76 Raider, 11 crashes GPU), et c'est la seule machine du cluster ainsi caractérisée. Ne pas router par famille sur cette base.

#### Jupyter kernels (12 registered)

Relevé `jupyter kernelspec list` firsthand sur po-2023, 2026-08-10.

| Kernel | Type | Usage |
|--------|------|-------|
| `.net-csharp` | .NET Interactive | notebooks C# (ML, Sudoku, Probas, SymbolicAI .NET) |
| `.net-fsharp` | .NET Interactive | notebooks F# |
| `.net-powershell` | .NET Interactive | notebooks PowerShell |
| `python3` | Python (Windows) | notebooks Python natifs |
| `python3-wsl` | Python (WSL) | notebooks Python côté WSL |
| `lean4-wsl` | Lean 4 (WSL) | `SymbolicAI/Lean` |
| `gametheory-wsl` | Python (WSL + OpenSpiel) | `GameTheory` |
| `mcp-jupyter-py310` | Python 3.10 | exécution Papermill (env de référence) |
| `acestep-venv` | Python (venv) | GenAI Audio — ACE-Step |
| `dia-tts` | Python (venv) | GenAI Audio — Dia TTS |
| `bonsai-gpu` | Python (GPU) | notebooks GPU |
| `cleanenv-k` | Python (env propre) | tests d'isolation de dépendances |

**Couverture des trois kernels installables partout** (règle F / H.2) : .NET Interactive **OK**, Python **OK**, Lean 4 **OK** (via WSL). Aucun contournement « kernel not available locally » n'est recevable sur cette lane.

### Autres machines (po-2024/26)

Inventaire kernels non encore relevé. Vérifier aussi l'env Conda dédié ou son venv équivalent : la mémoire est spécifique ai-01 mais le pattern (env dédié ML) est cluster-wide. Relever via `conda env list` **et** `jupyter kernelspec list` sur chaque machine.

### GenAI GPU stack : triton-windows + bitsandbytes

Les notebooks GenAI GPU (ex. [Video/02-5-LTX2-Audiovisual](../../MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-5-LTX2-Audiovisual.ipynb), #2891) utilisent `triton` (JIT de kernels) et `bitsandbytes` (quantization INT4/NF4). `torch` embarque son runtime CUDA (`torch.cuda.is_available()=True` marche SANS le Toolkit), mais triton/bnb ont besoin de plus :

| Besoin | Fourni par |
|--------|-----------|
| Detection CUDA par triton (`ptxas` + `cuda.h` + `cuda.lib`) | pip wheels `nvidia-cuda-nvcc-cu12` + `nvidia-cuda-runtime-cu12` |
| Compilateur C hote pour le JIT triton (`driver.c`) + bnb | `CC` env ; triton-windows embarque un TinyCC (`triton/runtime/tcc/tcc.exe`) |

**Piège Windows** : si Python et ses paquets sont en **user site-packages** (`%APPDATA%\Python\PythonXX\site-packages` — cas quand `C:\PythonXX\Lib\site-packages` exige admin), `sysconfig['platlib']` pointe sur la base. L'auto-detection de triton (`find_cuda_pip`) et de son TinyCC (`get_cc`) ratent alors. Symptomes : `RuntimeError: Failed to find CUDA` (triton) et `Failed to find C compiler. Please specify via CC` (triton + bnb).

**Fix sans UAC** (canonical triton-windows, prefere a un system Toolkit install) : un `usercustomize.py` en user site-packages injecte `CUDA_HOME` + `CC` au demarrage de chaque interpreteur Python. Exemple (po-2023, 2026-06-16, pour #2891) :

```python
# %APPDATA%\Python\Python313\site-packages\usercustomize.py
import os, site
base = site.getusersitepackages()
if os.path.isdir(os.path.join(base, "nvidia")):
    os.environ.setdefault("CUDA_HOME", os.path.join(base, "nvidia"))
if os.path.isfile(os.path.join(base, "triton", "runtime", "tcc", "tcc.exe")):
    os.environ.setdefault("CC", os.path.join(base, "triton", "runtime", "tcc", "tcc.exe"))
```

`setdefault` => n'ecrase jamais une valeur explicite ; n'affecte que les processus Python (pas de risque global `CC` pour les builds non-Python) ; no-op sur les machines sans les wheels. Test froid (G.2) : vider `~/.triton/cache` puis executer un kernel triton -> `max err = 0` vs torch sur le GPU.

## WSL kernels (Lean / GameTheory / OpenSpiel)

Notebooks dans `GameTheory/` et `SymbolicAI/Lean/` requierent un kernel WSL spécifique :

- `Python (GameTheory WSL + OpenSpiel)` pour GameTheory
- `Python 3 (WSL)` ou `Lean 4 (WSL)` pour SymbolicAI/Lean

Pièges : backslashes consommés par WSL shell, paths sans séparateurs, kernel timeout 60s cold start, heredoc variables interpolées. Wrapper bash obligatoire (Python wrapper ne marche PAS).

Detail diagnostic + workarounds : [.claude/rules/wsl-kernels.md](../../.claude/rules/wsl-kernels.md) + [docs/wsl-kernels-detail.md](wsl-kernels-detail.md).

## Lean prover LLM endpoints

Le multi-agent Lean prover (`MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/`) consomme des endpoints OpenAI-compatible. Cles et URLs stockees dans `MyIA.AI.Notebooks/SymbolicAI/Lean/.env` (gitignored).

| Provider type | Comportement attendu | Quand utiliser |
|---------------|----------------------|----------------|
| **Powerful reasoning** (e.g. GLM-5.1) | Heavy thinking : ~99% des completion_tokens en `reasoning_content`. Necessite `max_tokens >= 8192` et `timeout >= 300s` par call. | Multi-step proof discovery, theoremes non-triviaux |
| **Fast/modest** (e.g. Qwen3.6 local 35B-A3B) | Moins de thinking, plus rapide (~5s/293 tokens). | Validation lemma, sorry guard, étapes routine |
| **Openrouter** (Sonnet/Gemma fallback) | Free tier rate-limited. | Backup powerful quand endpoint principal down |
| **Anthropic direct** | Reserve si on ajoute un client natif (le framework actuel = `OpenAIChatCompletionClient` seul). | A activer ulterieurement |

Mapping avec `prover/config.py PROVIDERS` :

- `provider="zai"` : powerful reasoning
- `provider="local"` : fast/modest
- `provider="openrouter"` : backup
- `director_provider` peut differer du `provider` worker

**Pièges connus** :

1. Modèles powerful reasoning separent `content` et `reasoning_content` dans la reponse JSON. Le framework `agent_framework_openai` gere via `Content.from_text_reasoning()`.
2. `finish_reason: "length"` arrive vite si `max_tokens <= 2048` sur les modèles reasoning (toute la fenetre passe en reasoning).
3. Vérifier le nom exact du modèle côté endpoint (changements silencieux possibles).
4. Ports vLLM locaux 5001/5002 sur ai-01 = surveiller dispo (escalations Cycle 20). Preferer endpoint stable si flaky.

## Training checkpoints & thermal backoff (ai-01)

Librairie canonique de training BG long-running avec checkpoints + reprise + thermal backoff. **Reutiliser systematiquement pour toute training BG sur ai-01** (pas creer de wrapper concurrent).

**Path canonique** : `MyIA.AI.Notebooks/QuantConnect/shared/gpu_training.py` (lib Python, import direct).

> **Note** : la documentation précedemment citait un wrapper outer-supervisor `scripts/training/train_with_checkpoints.py` qui n'a jamais ete cree (`ls scripts/training/` = `No such file or directory`, `git log --grep "train_with_checkpoints"` = 0 commit). Le pattern reel est l'import direct de `gpu_training.py` ci-dessous.

### Pattern d'usage (import direct)

```python
from shared.gpu_training import TrainingCheckpoint

ckpt = TrainingCheckpoint(
    checkpoint_path='results/run_<TS>/checkpoint.pt',
    model_save_path='results/run_<TS>/final_model.pt',
    max_temp=80,    # defaut
    cool_sleep=60,  # defaut training BG long
)

start_epoch, history = ckpt.resume(model, optimizer, scheduler, grad_scaler)

for epoch in range(start_epoch, EPOCHS):
    ckpt.thermal_check()                       # watchdog inter-epoch
    train_metrics = train_epoch(model, ...)    # batch_thermal_check intra-epoch
    val_metrics = evaluate(model, ...)
    ckpt.update(epoch, val_metrics['loss'], history, model, optimizer, scheduler, grad_scaler)

ckpt.finalize(model)
```

### Sortie ecrite dans `<output_dir>/`

- `checkpoint.pt` : state dict complet model + optimizer + scheduler + grad_scaler + epoch + history (reprenable via `ckpt.resume`)
- `final_model.pt` : modele final after `ckpt.finalize()`
- `train.log` : stdout+stderr unbuffered du notebook appelant

### Thermal backoff

Librairie source : `MyIA.AI.Notebooks/QuantConnect/shared/gpu_training.py` (`get_gpu_temp`, `thermal_check`, `batch_thermal_check`, `TrainingCheckpoint`). 18 tests PR #7454, fixes GPU-thermal #7335/#7454/#7456. Defauts : `max_temp=80`, `cool_sleep=15` ; surclasser en `cool_sleep=60` pour training BG long-running sur ai-01 (defaut kernel).

### Contraintes hard

- **GPU 2 only** sur ai-01 (protection vLLM tournant sur GPU 0/1). Le notebook appelant doit cibler explicitement `cuda:2` (`model.to('cuda:2')`).
- Pre-flight check : GPU 2 mem < 1GB ET temp < `max_temp` via `thermal_check()` avant lancement.
- Reprise : `ckpt.resume(...)` recharge automatiquement `checkpoint.pt` si present, sinon demarre depuis le debut. Le monitoring de la croissance `history` (loss/val_loss par epoch) detecte le pattern "fake success" (entrainement termine sans progression).

### Monitoring

```bash
# Temperature GPU live (defaut kernel)
watch -n 5 'nvidia-smi -i 2 --query-gpu=temperature.gpu,memory.used,utilization.gpu --format=csv,noheader'

# Suivi progression entrainement (dans le notebook)
ckpt.update(epoch, val_metrics['loss'], history, ...)  # ajoute une entree history
print(history.tail(10))                                # log rapide cross-epoch

# Detection "fake success"
python -c "import json; h=json.load(open('<output_dir>/history.json')); \
  losses=[e['val_loss'] for e in h['epochs']]; \
  print('val_loss progression:', losses[-10:]); \
  print('FAKE_SUCCESS' if abs(losses[-1]-losses[0]) < 1e-6 else 'OK')"
```

## Verification rapide (toute machine)

```bash
# .NET
dotnet --list-sdks
dotnet interactive --version
jupyter kernelspec list | grep ".net"

# Python
python --version
conda env list

# WSL
wsl -l -v
```

## Si un kernel manque

Cf règle F (CLAUDE.md) : réparer plutôt que contourner. Installer le kernel manquant, ne pas déléguer. Pour kernels privilégiés (UAC), demander au user.
