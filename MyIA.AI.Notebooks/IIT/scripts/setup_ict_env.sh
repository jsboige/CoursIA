#!/usr/bin/env bash
# Setup script for the DEDICATED ICT execution environment (Python 3.9) —
# Linux/macOS twin of setup_ict_env.ps1.
#
# L'env `ict-py39` est l'environnement d'execution dedie de la serie IIT/ICT
# (MyIA.AI.Notebooks/IIT/ICT-Series). Il unifie, dans UN SEUL env, les trois
# exigences qui ne tiennent pas ensemble dans l'env py3.13 partage de la flotte :
#   - numpy < 2.0          (pyemd / pyphi exigent numpy 1.x)
#   - torch (CPU)          (strates LLM/SAE : ICT-21/22/24, ICT-SAE-JLens, ICT-40a)
#   - le package local `ict` (simulations, F/Lens, bridges -- `from ict import ...`)
#
# Usage: bash scripts/setup_ict_env.sh
#
# Creates:
#   - conda env 'ict-py39' (cloné de l'env 'pyphi' de base)
#   - le package local `ict` installe en editable (pip install -e ICT-Series)
#   - torch (build CPU) + transformers (strates LLM/SAE)
#   - Jupyter kernel 'ict-py39' (Python 3 (ICT 3.9 dedicated))
#
# Prerequisites:
#   - l'env de base 'pyphi' DOIT exister (creé par setup_pyphi_env.sh) :
#     ce script le CLONE pour heriter de pyemd 0.5.1 binaire prebuilt.
#   - conda (miniconda3 ou anaconda)
#
# NOTE pourquoi on CLONE pyphi plutot qu'on cree l'env a zero :
# PyPI ne publie AUCUN wheel cp39 de pyemd 0.5.1, et conda-forge ne fournit
# pas de gcc utilisable (c-compiler / m2w64-gcc ne livrent pas de compilateur
# fonctionnel sur Windows, mesure firsthand 2026-11-08). Compiler la sdist de
# pyemd est un impasse ; l'env 'pyphi' de base porte deja pyemd 0.5.1 binaire
# (lie numpy 1.x) + pyphi 1.2.0 + numpy<2 + scipy. Le cloner herite de tout ca
# pour free, puis on n'ajoute que le package local `ict` + torch/transformers.

set -euo pipefail

ENV_NAME="${1:-ict-py39}"
BASE_ENV="pyphi"

echo "=== Setup ICT (IIT/ICT-Series) Environment ==="
echo "Env name: $ENV_NAME"
echo "Base env (cloned): $BASE_ENV"
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

echo "[1/5] Using conda: $CONDA_EXE"

# 2. Clone the base 'pyphi' env (inherits prebuilt pyemd 0.5.1 + pyphi + numpy<2)
#    cf. NOTE en tete : c'est le chemin sans compilateur.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if ! "$CONDA_EXE" env list | grep -qE "^${BASE_ENV}\s"; then
    echo "ERROR: base conda env '$BASE_ENV' absent. Creer d'abord l'env de base" >&2
    echo "  via : bash scripts/setup_pyphi_env.sh   (puis relancer ce script)" >&2
    exit 1
fi
if "$CONDA_EXE" env list | grep -qE "^${ENV_NAME}\s"; then
    echo "[2/5] Conda env '$ENV_NAME' already exists, reusing..."
else
    echo "[2/5] Cloning conda env '$BASE_ENV' -> '$ENV_NAME' (heritage pyemd prebuilt)..."
    "$CONDA_EXE" create -n "$ENV_NAME" --clone "$BASE_ENV" -y
fi

# 3. Install the local `ict` package (editable) + its declared core deps.
#    Les pins durs (pyphi==1.2.0, numpy<2) sont deja satisfaits par le clone,
#    le resolver ne les touche pas ; pip complete seulement ce qui manque
#    (antropy, pandas, cryptography -- tous en wheel, sans compilation).
echo "[3/5] Installing local package 'ict' (editable)..."
ICT_SERIES_DIR="$SCRIPT_DIR/../ICT-Series"
if [ ! -d "$ICT_SERIES_DIR" ]; then
    echo "ERROR: ICT-Series dir not found at $ICT_SERIES_DIR" >&2
    exit 1
fi
"$CONDA_EXE" run -n "$ENV_NAME" pip install --quiet -e "$ICT_SERIES_DIR"

# 4. torch (build CPU) + transformers pour les strates LLM/SAE
echo "[4/5] Installing torch (CPU) + transformers..."
"$CONDA_EXE" run -n "$ENV_NAME" pip install --quiet torch \
    --index-url https://download.pytorch.org/whl/cpu
"$CONDA_EXE" run -n "$ENV_NAME" pip install --quiet transformers

# 5. Register Jupyter kernel
echo "[5/5] Registering Jupyter kernel..."
"$CONDA_EXE" run -n "$ENV_NAME" python -m ipykernel install --user \
    --name "$ENV_NAME" --display-name "Python 3 (ICT 3.9 dedicated)"

# Verify
echo ""
echo "=== Verification ==="

if "$CONDA_EXE" run -n "$ENV_NAME" python -c \
    "import numpy, pyphi, ict, torch, transformers; \
     print('numpy', numpy.__version__); \
     print('pyphi', pyphi.__version__); \
     print('torch', torch.__version__); \
     print('transformers', transformers.__version__); \
     print('ict', ict.__file__)" 2>/dev/null; then
    echo "  ICT stack: OK"
else
    echo "  ICT stack: IMPORT FAILED" >&2
    exit 1
fi

if jupyter kernelspec list 2>/dev/null | grep -q "$ENV_NAME"; then
    echo "  Kernel '$ENV_NAME': registered"
else
    echo "  Kernel '$ENV_NAME': NOT FOUND" >&2
fi

echo ""
echo "Setup complete. Activate with: conda activate $ENV_NAME"
echo "Use kernel 'Python 3 (ICT 3.9 dedicated)' for the IIT/ICT notebooks."
