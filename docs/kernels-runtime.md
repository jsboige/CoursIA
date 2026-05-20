# Kernels & Runtime — Cluster CoursIA

Document de reference detaillant l'inventaire kernels obligatoire sur toute machine du cluster (cf CLAUDE.md regle H.2).

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

### Envs Conda dedies (ai-01, reference)

| Env | Python | Path | Usage principal |
|-----|--------|------|-----------------|
| **coursia-ml-training** | 3.11.15 | `C:\Users\MYIA\miniconda3\envs\coursia-ml-training` | ML training (PyTorch CUDA 12.6 RTX 4090, sklearn, scipy, hmmlearn, pyarrow) |
| `mcp-jupyter` | 3.10+ | `C:\Users\MYIA\miniconda3\envs\mcp-jupyter` | MCP Jupyter server (kernels Python du MCP) |
| `epita_symbolic_ai` | 3.10+ | `C:\Users\MYIA\.conda\envs\epita_symbolic_ai` | EPITA SymbolicAI : `rdflib`, `owlready2`, `reasonable`, `pyshacl` |
| `epita_symbolic_ai_sherlock` | 3.10+ | `C:\Users\MYIA\.conda\envs\epita_symbolic_ai_sherlock` | Variante Sherlock |
| `llmcompressor` | 3.10+ | `C:\Users\MYIA\miniconda3\envs\llmcompressor` | LLM quantization tooling |
| `e2e_test_env` | 3.10+ | `C:\Users\MYIA\miniconda3\envs\e2e_test_env` | E2E tests |
| `base` | 3.10+ | `C:\Users\MYIA\miniconda3` | Conda base — NE PAS modifier |

### Stack ML training (coursia-ml-training, verifie 2026-05-06)

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

### Pourquoi un env Conda dedie ?

Sur ai-01, le Python 3.14 systeme est instable : scipy DLL corruption recurrente, conflits pip Python 3.12 vs 3.14, `~cipy/` residus apres force-reinstall rates. L'env Conda `coursia-ml-training` est l'env de reference stable pour le training ML, configure expressement avec PyTorch CUDA pour la RTX 4090.

Incident 2026-05-06 : training MoE tente directement sur Python 3.14 systeme : `scipy DLL load failed` → `sklearn force-reinstall denied`. Resolution : utiliser l'env Conda dedie. D'ou la regle F (cf [env-python-reparation.md](env-python-reparation.md)).

**Reflexe coordinateur** : avant tout dispatch ML training local, verifier que le script utilise `coursia-ml-training`. Si un agent rapporte un `ImportError` ML (sklearn, scipy, torch), premier debug = "tu as utilise l'env Conda `coursia-ml-training` ?".

### Autres machines (po-2023/24/25/26)

Verifier qu'elles ont aussi un env Conda dedie ou un venv local equivalent. La memoire est specifique ai-01 mais le pattern (env dedie ML) est cluster-wide. Inventorier via `conda env list` sur chaque machine.

## WSL kernels (Lean / GameTheory / OpenSpiel)

Notebooks dans `GameTheory/` et `SymbolicAI/Lean/` requierent un kernel WSL specifique :

- `Python (GameTheory WSL + OpenSpiel)` pour GameTheory
- `Python 3 (WSL)` ou `Lean 4 (WSL)` pour SymbolicAI/Lean

Pieges : backslashes consommes par WSL shell, paths sans separateurs, kernel timeout 60s cold start, heredoc variables interpolees. Wrapper bash obligatoire (Python wrapper ne marche PAS).

Detail diagnostic + workarounds : [.claude/rules/wsl-kernels.md](../.claude/rules/wsl-kernels.md) + [docs/wsl-kernels-detail.md](wsl-kernels-detail.md).

## Lean prover LLM endpoints

Le multi-agent Lean prover (`MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/`) consomme des endpoints OpenAI-compatible. Cles et URLs stockees dans `MyIA.AI.Notebooks/SymbolicAI/Lean/.env` (gitignored).

| Provider type | Comportement attendu | Quand utiliser |
|---------------|----------------------|----------------|
| **Powerful reasoning** (e.g. GLM-5.1) | Heavy thinking : ~99% des completion_tokens en `reasoning_content`. Necessite `max_tokens >= 8192` et `timeout >= 300s` par call. | Multi-step proof discovery, theoremes non-triviaux |
| **Fast/modest** (e.g. Qwen3.6 local 35B-A3B) | Moins de thinking, plus rapide (~5s/293 tokens). | Validation lemma, sorry guard, etapes routine |
| **Openrouter** (Sonnet/Gemma fallback) | Free tier rate-limited. | Backup powerful quand endpoint principal down |
| **Anthropic direct** | Reserve si on ajoute un client natif (le framework actuel = `OpenAIChatCompletionClient` seul). | A activer ulterieurement |

Mapping avec `prover/config.py PROVIDERS` :

- `provider="zai"` : powerful reasoning
- `provider="local"` : fast/modest
- `provider="openrouter"` : backup
- `director_provider` peut differer du `provider` worker

**Pieges connus** :

1. Modeles powerful reasoning separent `content` et `reasoning_content` dans la reponse JSON. Le framework `agent_framework_openai` gere via `Content.from_text_reasoning()`.
2. `finish_reason: "length"` arrive vite si `max_tokens <= 2048` sur les modeles reasoning (toute la fenetre passe en reasoning).
3. Verifier le nom exact du modele cote endpoint (changements silencieux possibles).
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

Cf regle F (CLAUDE.md) : reparer plutot que contourner. Installer le kernel manquant, ne pas deleguer. Pour kernels privilegies (UAC), demander au user.
