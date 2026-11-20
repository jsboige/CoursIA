# H.7 P3 Notebook Runner

Multi-kernel Docker runner for CoursIA notebook execution.
Supports Python 3.11 (system) + kernel global-3.13, .NET 10.0 Interactive (C#), and Lean 4 kernels.

## Quick Start

```bash
# Build the image (first time, ~10 min)
docker-compose build

# Check environment (kernels, tools)
docker-compose run notebook-runner --check-env

# Execute a single notebook
docker-compose run notebook-runner /notebooks/GameTheory/GameTheory-01-Setup-Python.ipynb

# Batch execute all notebooks in a directory
docker-compose run notebook-runner --batch /notebooks/ML/

# Custom timeout per cell (default: 300s)
docker-compose run notebook-runner -e EXECUTION_TIMEOUT=600 /notebooks/path/to/nb.ipynb
```

## Kernel Detection

The runner auto-detects the kernel from notebook metadata:

| Kernel name | Executor | Notes |
|-------------|----------|-------|
| `python3` | Papermill | Standard Python notebooks |
| `python3` (QuantConnect) | nbconvert `--allow-errors` | Detects `QuantBook` in source |
| `global-3.13` | Papermill (kernelspec natif) | Python 3.13 (env conda-forge) — notebooks serie Lean (#16262) |
| `.net-csharp` | nbconvert via .NET Interactive | C# notebooks |
| `.net-fsharp` | nbconvert via .NET Interactive | F# notebooks |
| `lean4` / `lean4-wsl` | elan + lake | Lean 4 formal verification |

## Architecture

```
notebook-runner/
├── Dockerfile              # Multi-stage: .NET 10.0 + Python 3.11 + global-3.13 + Lean 4
├── Dockerfile.jupyterlab   # Thin JupyterLab learning image (FROM the base, #27545)
├── docker-compose.yml      # Volume mounts + resource limits
├── h7_p3_notebook_runner.sh  # Unified kernel dispatch script
└── README.md
```

## JupyterLab learning image (Pli 1.2, #27545)

`Dockerfile.jupyterlab` derives an interactive image from the batch runner
above: it `FROM`s the already-built `coursia/notebook-runner:base` and adds
only JupyterLab — it does **not** re-run the multi-stage build. The canonical
kernels the base already carries (`python3`, `global-3.13`, `.net-csharp`,
`.net-fsharp`, `.net-powershell`) are inherited as-is.

```bash
# Build (after the base image exists)
docker build -t coursia/notebook-jupyterlab:latest -f Dockerfile.jupyterlab .

# Run with the notebook tree mounted
docker run -p 8888:8888 \
  -v "$PWD/../../MyIA.AI.Notebooks:/notebooks" \
  coursia/notebook-jupyterlab:latest
# -> http://localhost:8888/lab
```

This increment does not yet carry the Lean 4 (`lean4-jupyter`) and Rust
(`evcxr`) kernels — they are absent from the base image; a dedicated stage
adds them without duplication (next step, tracked in the PR body).

## Volume Mounts

| Host path | Container path | Purpose |
|-----------|---------------|---------|
| `../../MyIA.AI.Notebooks` | `/notebooks` | All notebooks (read-write) |
| `../../scripts` | `/scripts-repo` | Execution scripts (read-only) |
| `../../MyIA.AI.Notebooks/QuantConnect/data` | `/Lean/Data` | QC market data |

## GitHub Actions Integration

The runner is designed for CI/CD:

```yaml
- name: Execute notebooks
  run: |
    docker-compose -f docker-configurations/notebook-runner/docker-compose.yml \
      run -e QC_API_USER_ID=${{ secrets.QC_USER_ID }} \
          -e QC_API_ACCESS_TOKEN=${{ secrets.QC_API_TOKEN }} \
      notebook-runner --batch /notebooks/QuantConnect/
```

## Known Limitations

- **QuantConnect notebooks**: Only 5 tickers have data locally (SPY, QQQ, AAPL, GOOGL, IWM).
  Crypto and sector ETF notebooks will fail with empty data errors.
  Full data requires QC Cloud backend (see `docs/qc/quantconnect.md`).
- **Lean 4 notebooks**: Require `lean4` kernel installed in the image. WSL-specific notebooks
  (kernel `lean4-wsl`) may need path adjustments.
- **GPU notebooks**: No GPU support in this runner. GenAI notebooks requiring GPU
  (ComfyUI, Qwen) will skip API-dependent cells.
