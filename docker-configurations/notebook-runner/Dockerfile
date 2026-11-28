# H.7 P3 Notebook Runner — multi-kernel Docker image
# Supports: Python 3.11 (system, bookworm) + kernel global-3.13, .NET 10.0 Interactive (C#), Lean 4 (elan)
# Usage: docker-compose run notebook-runner /scripts/h7_p3_notebook_runner.sh <notebook.ipynb>

# Stage 1: Base image with .NET 10.0 SDK
# SDK 10 requis depuis le canon dotnet-interactive 1.0.712001 (decision #18766,
# hote net10.0) : sous SDK 9, l'install du tool echoue avec "Settings file
# 'DotnetToolSettings.xml' was not found in the package" (mesure 2026-10-06,
# probe sur sdk:9.0 -> echec, sdk:10.0 -> INSTALL_RC=0).
FROM mcr.microsoft.com/dotnet/sdk:10.0 AS base

# Install system dependencies
# Python = le python3 SYSTEME du tag 10.0.
# - Le socle n'est PAS Debian bookworm : le tag `dotnet/sdk:10.0` est base sur
#   Ubuntu 24.04.5 LTS (mesure dans l'image construite le 2026-11-20 :
#   `cat /etc/os-release` -> Ubuntu 24.04.5 LTS, `python3 --version` -> 3.12.3,
#   `which python3` -> /usr/bin/python3). Le commentaire anterieur annoncait
#   bookworm/3.11 : c'etait faux, et l'ecart etait invisible parce que la
#   borne `numpy<2` du manifeste tient sur 3.11 comme sur 3.12.
# - Le Dockerfile d'origine demandait python3.12 via apt, qui n'existe dans
#   AUCUN repo Debian (bookworm = 3.11) -- image inconstructible depuis main
#   (mesure 2026-10-06 : "E: Unable to locate package python3.12"). Sur Ubuntu
#   24.04 le python3 du systeme EST deja 3.12 : rien a installer pour lui.
# - 3.12 est le dernier interpreteur ou la borne `numpy>=1.24,<2.0` du
#   manifeste tient (numpy 1.26.x ne publie pas de roue cp313).
RUN apt-get update && apt-get install -y --no-install-recommends \
    python3 python3-venv python3-pip \
    wget curl git ca-certificates \
    # .NET Interactive prerequisites
    libicu-dev \
    # Lean 4 (elan) prerequisites
    cmake g++ gcc libc6-dev \
    && rm -rf /var/lib/apt/lists/*

# Stage 2: Python environment
FROM base AS python-env

RUN python3 -m pip install --break-system-packages --no-cache-dir \
    jupyter nbconvert nbformat papermill \
    jupyter_client ipykernel \
    numpy pandas scipy scikit-learn matplotlib \
    # QuantConnect research
    quantconnect-stubs \
    # GenAI notebooks
    requests pillow \
    # Game theory -- open_spiel : nom canon PyPI (le repo installe ce nom,
    # cf GameTheory/scripts/setup_wsl_openspiel.sh ; "openspiel" sans
    # separateur est un projet PyPI homonyme disparu, matrice python
    # incompatible -- mesure 2026-10-06 : 404 sur le simple index)
    nashpy open_spiel \
    # SemanticWeb
    rdflib owlready2 pyshacl \
    # SmartContracts SC-11 (LLM-Assisted) : backend EthereumTester local --
    # web3 pour EthereumTesterProvider, eth-tester[py-evm] pour le backend
    web3 "eth-tester[py-evm]" \
    && python3 -m ipykernel install --name python3 --user

# Stage 2b: kernel Python 3.13 "global-3.13" (notebooks serie Lean, #16262)
# Lean-08-Agentic-Proving-Python.ipynb et ses siblings portent le kernelspec
# `global-3.13` (cf scripts/notebook_tools/check_kernel_suffix_canon.py,
# PYTHON_ENV_NAMES). Env construite via miniforge (conda-forge), meme canal
# que les env des machines de la flotte, puis enregistree en kernelspec.
FROM python-env AS global-313

RUN wget -q https://github.com/conda-forge/miniforge/releases/latest/download/Miniforge3-Linux-x86_64.sh -O /tmp/miniforge.sh \
    && bash /tmp/miniforge.sh -b -p /opt/miniforge \
    && /opt/miniforge/bin/conda create -y -n global-3.13 python=3.13 ipykernel \
    && /opt/miniforge/envs/global-3.13/bin/python -m ipykernel install --name global-3.13 --user \
    && rm /tmp/miniforge.sh

# Stage 3: .NET Interactive
FROM global-313 AS dotnet-interactive

# Pin canon 1.0.712001 (decision #18766, docs/reference/kernels-runtime.md) :
# sans --version, l'install prend le dernier build publie, actuellement casse
# ("Settings file 'DotnetToolSettings.xml' was not found in the package",
# mesure 2026-10-06) -- image inconstructible.
RUN dotnet tool install --global Microsoft.dotnet-interactive --version 1.0.712001 \
    && ~/.dotnet/tools/dotnet-interactive jupyter install

# Stage 4: Lean 4 toolchain (elan)
FROM dotnet-interactive AS lean-env

RUN curl -sL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain stable \
    && echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc

# Set environment
ENV PATH="/root/.dotnet/tools:/root/.elan/bin:${PATH}" \
    PYTHONUNBUFFERED=1 \
    DOTNET_INTERACTIVE_DEFAULT_TOOLCHAIN=net9.0 \
    LANG=C.UTF-8

# Copy runner script
COPY h7_p3_notebook_runner.sh /scripts/h7_p3_notebook_runner.sh
RUN chmod +x /scripts/h7_p3_notebook_runner.sh

# Working directory for notebooks
WORKDIR /notebooks

ENTRYPOINT ["/scripts/h7_p3_notebook_runner.sh"]

# =============================================================================
# Stage 5: image d'APPRENTISSAGE (pli 1.2 de l'Epic #27543, #27545)
# =============================================================================
# Une image unique qui demarre JupyterLab avec les noyaux canoniques de
# docs/reference/kernels-runtime.md : `python3`, `global-3.13`, `.net-csharp`,
# `.net-fsharp`, `.net-powershell`, `lean4` et `rust` (evcxr).
#
# Les etages precedents sont HERITES, pas dupliques : `learning` part de
# `lean-env`, qui part de `dotnet-interactive`, etc. Le cout de l'image
# d'apprentissage est donc celui de l'image d'execution + JupyterLab + les
# paquets du manifeste -- c'est ce que la decision de forme (image unique vs
# variantes par famille) doit arbitrer.
#
# Les paquets Python ne sont PAS ecrits a la main ici : ils sont la projection
# du manifeste consolide du pli 1.1 (#27544), produite par
# scripts/notebook_tools/emit_learning_requirements.py a partir de
# docs/curriculum/manifeste-dependances.json. Le fichier `requirements` est
# versionne dans le depot et verifie par `--check`.
FROM lean-env AS learning

# Versions epinglees (cf docs/reference/kernels-runtime.md) :
# - evcxr_jupyter 0.22.0 (publication 2025-08-18) ;
# - Lean : la toolchain des lakes du depot (v4.33.0, lue dans
#   MyIA.AI.Notebooks/GameTheory/game_theory_lean/lean-toolchain) ;
# - lean4_jupyter : la fourche durable du depot, tag v0.0.3-launch-errors
#   (cf scripts/lean/setup_native_lean4_import.py, FORK_TAG).
ARG EVCXR_VERSION=0.22.0
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.33.0
ARG LEAN4_JUPYTER_SPEC=lean4_jupyter @ git+https://github.com/jsboige/lean4_jupyter.git@v0.0.3-launch-errors

# --- 1) JupyterLab + paquets du manifeste 1.1 -------------------------------
# L'image installe le VERROU (`requirements-learning.lock.txt`) : versions
# exactes et empreintes, aucune resolution a l'execution. Le verrou est la
# resolution de `requirements-learning.txt`, qui est la projection du
# manifeste consolide du pli 1.1.
#
# L'index CPU de PyTorch : la famille GPU est exclue du manifeste, mais
# `torchlens` (groupe inclus) declare `torch>=2.0`. La roue PyPI de torch
# embarque les bibliotheques CUDA (plusieurs Go) ; la roue `+cpu` de l'index
# PyTorch porte la MEME version et PEP 440 la classe au-dessus de la version
# nue, donc le resolveur la retient (verrou : torch==2.15.0+cpu). Motif et
# source : politique versionnee `learning_image_policy.json` (`pip_options`).
#
# `python-constraint` est installe par pip et non par uv : son sdist PyPI
# porte un nom non PEP 625, que uv refuse de resoudre. Motif et source :
# meme politique (`pip_installed`).
COPY requirements-learning.txt requirements-learning.lock.txt /tmp/
RUN set -eux; \
    python3 -m pip install --break-system-packages --no-cache-dir uv; \
    python3 -m pip wheel --no-cache-dir --wheel-dir /tmp/wheels "python-constraint>=1.4.0"; \
    python3 -m pip install --break-system-packages --no-cache-dir --no-deps /tmp/wheels/python_constraint-*.whl; \
    uv pip install --system --break-system-packages \
        --index-strategy unsafe-best-match \
        --extra-index-url https://download.pytorch.org/whl/cpu \
        --requirement /tmp/requirements-learning.lock.txt; \
    rm -rf /tmp/wheels /tmp/requirements-learning.lock.txt /tmp/requirements-learning.txt


# --- 2) Rust / evcxr (noyau `rust`) -----------------------------------------
# Binaire de la publication officielle, version epinglee : pas de compilation
# dans l'image (le compilateur `rustc` reste disponible via rustup pour les
# notebooks, et `rust-src` est requis par evcxr pour compiler incrementally).
RUN set -eux; \
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
        | sh -s -- -y --profile minimal --default-toolchain stable --no-modify-path; \
    . "$HOME/.cargo/env"; \
    rustup component add rust-src; \
    curl -sSfL -o /tmp/evcxr.tar.gz \
        "https://github.com/evcxr/evcxr/releases/download/v${EVCXR_VERSION}/evcxr_jupyter-v${EVCXR_VERSION}-x86_64-unknown-linux-gnu.tar.gz"; \
    mkdir -p /tmp/evcxr && tar -xzf /tmp/evcxr.tar.gz -C /tmp/evcxr --strip-components=1; \
    install -m 0755 /tmp/evcxr/evcxr_jupyter /usr/local/bin/evcxr_jupyter; \
    evcxr_jupyter --install; \
    rm -rf /tmp/evcxr /tmp/evcxr.tar.gz

# --- 3) Noyau Lean 4 (`lean4`) ----------------------------------------------
# Chemin canonique du depot (scripts/lean/setup_native_lean4_import.py +
# MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/lean4-kernel-wrapper.py) :
# toolchain epinglee, REPL compile CONTRE cette toolchain, fourche
# lean4_jupyter, wrapper canonique. Le wrapper refuse de demarrer si le REPL
# n'est pas apparie a la toolchain : c'est la garde #18511, pas une commodite.
#
# Le wrapper vient du depot via un contexte de build nomme (`lean_scripts`) :
# il n'est ni recopie ni reecrit ici. Sans ce contexte, la construction
# echoue (fail-closed) plutot que de partir sur un wrapper bricole.
#
# ANCRAGE (`/opt/lean4-anchor`) -- mesure 2026-11-20, image mesuree :
# le wrapper REFUSE de demarrer quand aucun `lean-toolchain` n'est trouvable
# en remontant depuis le repertoire d'execution (regle #16181 : aucun repli
# vers un projet etranger). Dans un conteneur, le repertoire d'execution est
# celui du carnet (`/notebooks`, `/witness`, ...) : il ne porte aucun
# `lean-toolchain`, et le noyau mourait donc avant `kernel_info`
# (`RuntimeError: Kernel died before replying to kernel_info`, mesure sur le
# temoin Lean, rc=1 en 7,6 s ; les 6 autres familles de noyaux passaient).
# L'image fournit donc SON PROPRE ancrage : `/opt/lean4-anchor/lean-toolchain`
# = la toolchain epinglee de l'image, celle contre laquelle le REPL a ete
# compile -- c'est exactement l'appariement que le wrapper exige (sortie 3
# sur divergence). Le lanceur `/opt/lean4-kernel-launch.sh` entre dans
# l'ancrage puis exec le wrapper ; le carnet reste libre de se trouver
# ailleurs. Verifie : avec l'ancrage, le noyau demarre et `#eval 2 + 2`
# rend `4` (journal : `toolchain pinned: leanprover/lean4:v4.33.0 ;
# REPL: /root/.elan/bin/repl (Lean 4.33.0)`).
COPY --from=lean_scripts lean4-kernel-wrapper.py /opt/lean4-kernel-wrapper.py
RUN set -eux; \
    . "$HOME/.elan/env"; \
    elan toolchain install "${LEAN_TOOLCHAIN}"; \
    python3 -m venv /opt/lean4-venv; \
    /opt/lean4-venv/bin/pip install --upgrade pip; \
    /opt/lean4-venv/bin/pip install ipykernel pyyaml "${LEAN4_JUPYTER_SPEC}"; \
    git clone --depth 1 --branch v4.33.0 https://github.com/leanprover-community/repl.git /opt/repl; \
    cd /opt/repl; \
    elan override set "${LEAN_TOOLCHAIN}"; \
    lake build; \
    install -m 0755 /opt/repl/.lake/build/bin/repl "$HOME/.elan/bin/repl"; \
    rm -rf /opt/repl; \
    mkdir -p /opt/lean4-anchor; \
    printf '%s\n' "${LEAN_TOOLCHAIN}" > /opt/lean4-anchor/lean-toolchain; \
    printf '%s\n' \
        '#!/bin/sh' \
        'cd /opt/lean4-anchor' \
        'exec /opt/lean4-venv/bin/python3 /opt/lean4-kernel-wrapper.py "$@"' \
        > /opt/lean4-kernel-launch.sh; \
    chmod +x /opt/lean4-kernel-launch.sh; \
    mkdir -p /tmp/lean4-kernelspec; \
    printf '%s\n' \
        '{' \
        '  "argv": [' \
        '    "/opt/lean4-kernel-launch.sh",' \
        '    "-f", "{connection_file}"' \
        '  ],' \
        '  "env": {' \
        '    "ELAN_HOME": "/root/.elan",' \
        '    "LEAN4_VENV": "/opt/lean4-venv"' \
        '  },' \
        '  "display_name": "Lean 4",' \
        '  "language": "lean4"' \
        '}' > /tmp/lean4-kernelspec/kernel.json; \
    jupyter kernelspec install --user --name lean4 /tmp/lean4-kernelspec; \
    rm -rf /tmp/lean4-kernelspec

# --- 4) Point d'entree de l'image d'apprentissage ---------------------------
# L'ENTRYPOINT du runner est neutralise : l'image d'apprentissage demarre
# JupyterLab, elle n'execute pas un carnet en lot.
#
# Le CMD nomme l'executable TEL QU'IL EST INSTALLE : `jupyterlab` n'existe pas
# dans le PATH de l'image (le script installe par pip est `jupyter-lab`), si
# bien que `docker run ghcr.io/jsboige/coursia-learning:latest` echouait
# immediatement sur `exec: "jupyterlab": executable file not found in $PATH`
# et que le repli local documente ne demarrait rien (#27547). Le workflow
# `learning-image-ghcr` demarre desormais l'image avec sa commande par defaut
# et exige une reponse HTTP sur le port 8888 : le defaut ne peut pas revenir.
ENV PATH="/root/.elan/bin:/root/.cargo/bin:/root/.dotnet/tools:${PATH}" \
    LEAN_TOOLCHAIN="${LEAN_TOOLCHAIN}"
WORKDIR /notebooks
EXPOSE 8888
ENTRYPOINT []
CMD ["jupyter-lab", "--ip=0.0.0.0", "--port=8888", "--no-browser", "--allow-root"]

