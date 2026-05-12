# H.7 P3 Notebook Runner

Multi-kernel Docker runner for CoursIA notebook execution.
Supports Python 3.12, .NET 9.0 Interactive (C#), and Lean 4 kernels.

## Quick Start

```bash
# Build the image (first time, ~10 min)
docker-compose build

# Check environment (kernels, tools)
docker-compose run notebook-runner --check-env

# Execute a single notebook
docker-compose run notebook-runner /notebooks/GameTheory/GameTheory-1-Setup.ipynb

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
| `.net-csharp` | nbconvert via .NET Interactive | C# notebooks |
| `.net-fsharp` | nbconvert via .NET Interactive | F# notebooks |
| `lean4` / `lean4-wsl` | elan + lake | Lean 4 formal verification |

## Architecture

```
notebook-runner/
├── Dockerfile          # Multi-stage: .NET 9.0 + Python 3.12 + Lean 4
├── docker-compose.yml  # Volume mounts + resource limits
├── h7_p3_notebook_runner.sh  # Unified kernel dispatch script
└── README.md
```

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
  Full data requires QC Cloud backend (see `docs/H7_P2_DOCKER_ERROR_CATALOG.md`).
- **Lean 4 notebooks**: Require `lean4` kernel installed in the image. WSL-specific notebooks
  (kernel `lean4-wsl`) may need path adjustments.
- **GPU notebooks**: No GPU support in this runner. GenAI notebooks requiring GPU
  (ComfyUI, Qwen) will skip API-dependent cells.
