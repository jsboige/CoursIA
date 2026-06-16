# Scripts for Infer.NET Notebooks

This directory contains setup and testing scripts for the Infer.NET probabilistic programming notebook series.

## Prerequisites

- .NET SDK 6.0 or higher
- Python 3.8 or higher
- pip (Python package manager)

## Quick Setup

### Windows (PowerShell)

```powershell
# Run the setup script
.\setup_environment.ps1

# Or with options
.\setup_environment.ps1 -Verbose
.\setup_environment.ps1 -SkipPapermill  # If you don't need papermill
```

### Manual Setup

1. **Install .NET Interactive tool:**
   ```bash
   dotnet tool install -g Microsoft.dotnet-interactive
   dotnet interactive jupyter install
   ```

2. **Install Python dependencies:**
   ```bash
   pip install -r requirements.txt
   ```

3. **Verify kernels:**
   ```bash
   jupyter kernelspec list
   ```
   You should see `.net-csharp`, `.net-fsharp`, `.net-powershell`

## Testing Notebooks

### Run all tests

```bash
python test_notebooks.py
```

### Test a specific notebook

```bash
python test_notebooks.py -n Infer-1-Setup.ipynb -v
```

### Options

| Option | Description |
|--------|-------------|
| `-n, --notebook` | Test a specific notebook |
| `-t, --timeout` | Timeout per notebook (default: 600s) |
| `-v, --verbose` | Verbose output |
| `-l, --list` | List available notebooks |

### Output

- Executed notebooks are saved in `MyIA.AI.Notebooks/Probas/Infer/test_outputs/`
- Test results summary is saved to `test_outputs/test_results.json`

## Troubleshooting

### Kernel not found

If `.net-csharp` kernel is not found:

```bash
dotnet interactive jupyter install
```

### NuGet restore issues

The notebooks automatically restore NuGet packages. If you encounter issues:

```bash
dotnet nuget locals all --clear
```

### Timeout issues

Some notebooks (especially those with many inference operations) may take longer. Increase the timeout:

```bash
python test_notebooks.py -t 1200  # 20 minutes
```

## Files

| File | Description |
|------|-------------|
| `setup_environment.ps1` | PowerShell setup script |
| `test_notebooks.py` | Python test runner |
| `requirements.txt` | Python dependencies |
| `README.md` | This file |
