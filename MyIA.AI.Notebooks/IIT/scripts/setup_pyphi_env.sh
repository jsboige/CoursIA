#!/usr/bin/env bash
# Setup script for PyPhi conda environment (Python 3.9) — Linux/macOS twin
# of setup_pyphi_env.ps1
# PyPhi 1.2.0 requires Python <=3.9 (collections.Iterable removed in 3.10)
#
# Usage: bash scripts/setup_pyphi_env.sh
#
# Creates:
#   - conda env 'pyphi' with Python 3.9
#   - Jupyter kernel 'pyphi' (Python 3 - PyPhi/IIT)
#
# Prerequisites: conda (miniconda3 or anaconda)
#
# NOTE conda-forge : le script utilise -c conda-forge --override-channels
# partout. Raison (mesure firsthand 2026-08-25, Windows + PyPI) :
#   1. les canaux defaults Anaconda exigent l'acceptation des ToS
#      (CondaToSNonInteractiveError en non-interactif) ;
#   2. PyPI ne publie AUCUN wheel cp39 de pyemd 0.5.1 (seul 1.0.0 en a),
#      donc `pip install pyemd==0.5.1` compile une sdist — contre numpy 2.x
#      au build, puis echoue a l'import ("numpy.dtype size changed"), et
#      exige MSVC/gcc si aucun compilateur n'est present ;
#   3. conda-forge fournit pyemd 0.5.1 en binaire prebuilt lie a numpy 1.x :
#      c'est le seul chemin sans compilateur.

set -euo pipefail

ENV_NAME="${1:-pyphi}"
PYTHON_VERSION="3.9"

echo "=== Setup PyPhi Environment ==="
echo "Env name: $ENV_NAME"
echo "Python version: $PYTHON_VERSION"
echo ""

# 1. Check conda is available
CONDA_EXE="$(command -v conda || true)"
if [ -z "$CONDA_EXE" ]; then
    for p in "$HOME/miniconda3/bin/conda" "$HOME/anaconda3/bin/conda" \
             "/opt/miniconda3/bin/conda" "/opt/anaconda3/bin/conda" \
             "/usr/local/miniconda3/bin/conda"; do
        if [ -x "$p" ]; then
            CONDA_EXE="$p"
            break
        fi
    done
fi

if [ -z "$CONDA_EXE" ]; then
    echo "ERROR: conda not found. Install miniconda3 first." >&2
    echo "  https://docs.conda.io/en/latest/miniconda.html" >&2
    exit 1
fi

echo "[1/4] Using conda: $CONDA_EXE"

# 2. Create conda env (conda-forge, cf. NOTE en tete de script)
if "$CONDA_EXE" env list | grep -qE "^${ENV_NAME}\s"; then
    echo "[2/4] Conda env '$ENV_NAME' already exists, reusing..."
else
    echo "[2/4] Creating conda env '$ENV_NAME' with Python $PYTHON_VERSION (conda-forge)..."
    "$CONDA_EXE" create -n "$ENV_NAME" -c conda-forge --override-channels \
        "python=$PYTHON_VERSION" -y
fi

# 3. Install packages : pyemd via conda-forge (binaire prebuilt, numpy 1.x),
#    le reste via pip
echo "[3/4] Installing packages..."

"$CONDA_EXE" install -n "$ENV_NAME" -c conda-forge --override-channels \
    "pyemd=0.5.1" -y
"$CONDA_EXE" run -n "$ENV_NAME" pip install --quiet "pyphi==1.2.0" "numpy<2" scipy ipykernel matplotlib

# 4. Register Jupyter kernel
echo "[4/4] Registering Jupyter kernel..."
"$CONDA_EXE" run -n "$ENV_NAME" python -m ipykernel install --user \
    --name pyphi --display-name "Python 3 (PyPhi/IIT)"

# 5. Verify
echo ""
echo "=== Verification ==="

if "$CONDA_EXE" run -n "$ENV_NAME" python -c "import pyphi" 2>/dev/null; then
    PYVER="$("$CONDA_EXE" run -n "$ENV_NAME" python -c 'import pyphi; print(pyphi.__version__)')"
    echo "  PyPhi version: $PYVER"
else
    echo "  PyPhi: IMPORT FAILED" >&2
    exit 1
fi

if jupyter kernelspec list 2>/dev/null | grep -q "pyphi"; then
    echo "  Kernel 'pyphi': registered"
else
    echo "  Kernel 'pyphi': NOT FOUND" >&2
fi

echo ""
echo "Setup complete. Activate with: conda activate $ENV_NAME"
echo "Use kernel 'Python 3 (PyPhi/IIT)' in Jupyter notebooks."
