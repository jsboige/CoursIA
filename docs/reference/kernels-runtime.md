# Kernels & Runtime — Cluster CoursIA

Document de référence détaillant l'inventaire kernels obligatoire sur toute machine du cluster (cf CLAUDE.md règle H.2).

**Regle user 2026-05-07** : toute machine du cluster (ai-01, po-2023, po-2024, po-2025, po-2026) doit pouvoir executer n'importe quel notebook du depot. Reparation env > contournement (regle F, cf [env-python-reparation.md](env-python-reparation.md)).

## .NET Interactive (C# notebooks)

Notebooks dans `SymbolicAI/SemanticWeb/`, `SymbolicAI/SmartContract/`, `Search/`, `Sudoku/`, `ML/`, `Probas/`.

| Prerequis | Version | Verification |
|-----------|---------|-------------|
| .NET SDK | 8.0 + 9.0 (10.0 optionnel) | `dotnet --list-sdks` |
| dotnet-interactive | >= 1.0.700 (PIN 1.0.552801 sur ai-01) | `dotnet interactive --version` |
| Jupyter kernels `.net-csharp`, `.net-fsharp`, `.net-powershell` | auto-installes | `jupyter kernelspec list` |

Installation : `dotnet tool install --global Microsoft.dotnet-interactive` puis `dotnet interactive jupyter install`.

**Execution** : toujours cell-by-cell via MCP Jupyter (Papermill ne supporte pas .NET Interactive). Le kernel `.net-csharp` preserve l'etat entre cellules.

**Versions a EVITER** : 1.0.522904 (Roslyn bug), 1.0.712001 (`#!import` bug). PIN sur 1.0.552801 si possible.

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
- dotnet-interactive : **1.0.552801** (PINNED)
- Kernels : `.net-csharp`, `.net-fsharp`, `.net-powershell`

#### Jupyter kernels (10 registered)

| Kernel | Type | Executable via |
|--------|------|----------------|
| python3 | Python (conda base) | Papermill |
| .net-csharp | .NET 9.0 | MCP Jupyter cell-by-cell |
| .net-fsharp | .NET | MCP Jupyter cell-by-cell |
| .net-powershell | .NET | MCP Jupyter cell-by-cell |
| conda-torch | Python (torch) | Papermill |
| lean4 | Lean 4 (v4.29.1 Windows) | MCP Jupyter cell-by-cell |
| lean4-wsl | Lean 4 (v4.11.0 WSL) | MCP Jupyter cell-by-cell |
| python3-wsl | Python (WSL 3.12) | wsl_papermill.py |
| smartcontracts | Python | Papermill |

#### Papermill : env de reference

```bash
# Python notebooks : mcp-jupyter-py310
/c/Users/jsboi/.conda/envs/mcp-jupyter-py310/python.exe -m papermill <nb> <out>

# WSL notebooks : wsl_papermill.py
python scripts/notebook_tools/wsl_papermill.py execute <nb>

# .NET / Lean : cell-by-cell MCP Jupyter (Papermill ne marche PAS)
```

#### MCP jupyter-papermill HANG (bug #835) : bascule directe timeout-wrappée, JAMAIS bloquer (HARD)

**Il existe DEUX chemins d'exécution notebook** : (1) le MCP `jupyter-papermill` (cell-by-cell), (2) **papermill/nbconvert en direct** via `notebook_tools` / les binaires ci-dessus. Ils sont **interchangeables** pour l'exécution.

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

### Autres machines (po-2023/24/26)

Vérifier qu'elles ont aussi un env Conda dédié ou un venv local équivalent. La mémoire est spécifique ai-01 mais le pattern (env dédié ML) est cluster-wide. Inventorier via `conda env list` sur chaque machine.

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

## Training wrapper checkpoints (ai-01)

Wrapper outer-supervisor reutilisable pour training BG long-running avec checkpoints + reprise + thermal backoff. **Reutiliser systematiquement pour toute training BG sur ai-01** (pas creer de wrapper concurrent).

**Path canonique** : `scripts/training/train_with_checkpoints.py`

### Pattern d'usage

```bash
python scripts/training/train_with_checkpoints.py \
  --script <path_to_train_xxx.py> \
  --config <yaml_or_args> \
  --output-dir results/<run_name>_<TIMESTAMP> \
  --gpu-index 2 \
  --max-temp 80 \
  --cool-sleep 60 \
  --heartbeat 30 \
  --max-restarts 5
```

### Sortie ecrite dans `<output_dir>/`

- `train.log` : stdout+stderr unbuffered du subprocess
- `wrapper_status.json` : etat actualise chaque heartbeat
- `train.pid` (child) + `wrapper.pid` (outer)
- `checkpoint.jsonl` : combos completes (monitor growth pour detecter "fake success")

### Thermal backoff

Source reutilisee : `MyIA.AI.Notebooks/QuantConnect/shared/gpu_training.py` (`get_gpu_temp`, `thermal_check`, `batch_thermal_check`, `TrainingCheckpoint`). Defauts : `max_temp=80`, `cool_sleep=15`.

### Contraintes hard

- **GPU 2 only** sur ai-01. Le wrapper refuse `--gpu-index 0|1` (protection vLLM tournant sur GPU 0/1).
- Pre-flight check : GPU 2 mem < 1GB ET temp < `max_temp` avant lancement.
- Auto-restart jusqu'a 5 sur non-zero exit. Risque "fake success" (code 0 sans atteindre la fin) : surveiller via `checkpoint.jsonl` growth.

### Monitoring

```bash
tail -f <output_dir>/train.log
cat <output_dir>/wrapper_status.json
wc -l <output_dir>/checkpoint.jsonl
nvidia-smi -i 2 --query-gpu=temperature.gpu,memory.used,utilization.gpu --format=csv,noheader
grep -E "VERDICT|SKIPPED|exited with code" <output_dir>/train.log
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
