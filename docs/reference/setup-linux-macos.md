# Setup macOS / Linux — équivalents cross-OS du cluster CoursIA

Le dépôt CoursIA a été développé sous Windows (WSL pour Lean/GameTheory). Un contributeur macOS ou Linux peut exécuter la majorité des notebooks sans modification — les kernels .NET Interactive, Python et Lean 4 sont cross-OS. Ce document donne les **équivalents Mac/Linux** des instructions d'installation Windows (`winget`/`choco`/`Set-ExecutionPolicy`) référencées dans [kernels-runtime.md](kernels-runtime.md), [env-python-reparation.md](env-python-reparation.md) et les READMEs de séries.

Pour les commandes spécifiques aux machines du cluster (paths `C:\Users\MYIA\...`, envs Conda dédiés, GPU topology), cf [kernels-runtime.md](kernels-runtime.md) — ce document-ci couvre le **setup d'un poste contributeur Mac/Linux**.

> **Règle FR-first** : ce document est en français (documentation primaire du dépôt). Le contenu d'installation original Windows est préservé dans les READMEs et `kernels-runtime.md`.

## .NET 9.0 + .NET Interactive (notebooks C#/F#)

Le SDK .NET et `dotnet-interactive` sont cross-OS : les notebooks `.net-csharp` s'exécutent à l'identique.

```bash
# Linux (Ubuntu/Debian) : dépôt Microsoft
sudo apt update && sudo apt install -y dotnet-sdk-9.0
# macOS : Homebrew Cask
brew install --cask dotnet-sdk

# dotnet-interactive (même commande que Windows, cross-OS)
dotnet tool install --global Microsoft.dotnet-interactive --version 1.0.617701
dotnet interactive jupyter install

# Vérification
dotnet interactive --version   # 1.0.617701 (pin, cf kernels-runtime.md)
jupyter kernelspec list | grep ".net"   # .net-csharp, .net-fsharp
```

Le pin de version **1.0.617701** s'applique cross-OS (1.0.712001 casse `#!import` partout, pas seulement Windows).

## Python 3.10+ + Conda

```bash
# macOS (Intel/Apple Silicon) et Linux : Miniforge (Conda + conda-forge par défaut)
curl -L -o miniforge.sh https://github.com/conda-forge/miniforge/releases/latest/download/Miniforge3-$(uname)-$(uname -m).sh
bash miniforge.sh -b -p $HOME/miniforge3
eval "$($HOME/miniforge3/bin/conda shell.bash hook)"

# Création d'un env dédié (équivalent de coursia-ml-training sur ai-01)
conda create -n coursia python=3.11 -y
conda activate coursia
pip install numpy scipy pandas scikit-learn matplotlib papermill
```

Sur Mac, préférer **Miniforge** à Miniconda : les wheels conda-forge sont natives Apple Silicon (`arm64`), évitant les traductions Rosetta.

## Lean 4 (notebooks SymbolicAI/Lean)

Lean 4 s'installe via `elan` (cross-OS), équivalent de `rustup` pour Lean. **Pas besoin de WSL sur Mac/Linux** (WSL n'est qu'un contournement Windows).

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source $HOME/.cargo/env   # ou relancer le shell

elan toolchain install stable
lean --version

# Kernel Jupyter Lean 4
pip install lean4-jupyter
python -m lean4_jupyter.kernel install
```

## Packages système courants

Les READMEs de séries donnent parfois l'installation Windows-only (`winget`/`choco`). Équivalents :

| Package | Windows | macOS | Linux (Debian/Ubuntu) |
|---------|---------|-------|-----------------------|
| **FFmpeg** | `winget install FFmpeg` | `brew install ffmpeg` | `sudo apt install ffmpeg` |
| **Graphviz** | `choco install graphviz` | `brew install graphviz` | `sudo apt install graphviz` |
| **JDK 11+** (HermiT/OWLReady2) | `winget install EclipseAdoptium.Temurin.11.JDK` | `brew install --cask temurin@11` | `sudo apt install openjdk-17-jdk` |
| **SWI-Prolog** | `winget install SWI-Prolog` | `brew install swi-prolog` | `sudo apt install swi-prolog` |

Vérifier la disponibilité d'un formula : `brew info <pkg>` (Mac), `apt-cache show <pkg>` (Linux).

## PowerShell vs Bash

Le dépôt fournit des compagnons `.sh` à côté des `.ps1` pour les scripts d'environnement et de tooling :

- `scripts/environment/setup_environment.{ps1,sh}` — setup complet (cf [#10644](https://github.com/jsboige/CoursIA/issues/10644))
- `scripts/environment/audit_environment.{ps1,sh}` — diagnostic env
- `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/launchers/launch_*.{ps1,sh}` — launchers training GPU (cf [#10647](https://github.com/jsboige/CoursIA/issues/10647))

Sur Mac/Linux, utiliser le `.sh`. Les scripts `.ps1` peuvent aussi s'exécuter via PowerShell Core (`pwsh`, installable `brew install --cask powershell`), mais le `.sh` natif est préféré (pas de prérequis `pwsh`).

Les instructions `Set-ExecutionPolicy` des READMEs Windows n'ont **pas d'équivalent** sur Mac/Linux (pas de politique d'exécution de scripts) — un contributeur Mac/Linux les ignore.

## GPU / CUDA (notebooks training & GenAI)

- **Linux NVIDIA** : installer le CUDA Toolkit (12.x) via le dépôt NVIDIA ou le runfile officiel. `nvidia-smi` et `torch.cuda.is_available()` fonctionnent comme sous Windows.
- **macOS Apple Silicon** : pas de CUDA. PyTorch utilise le backend **MPS** (`device="mps"`). Les notebooks training assume généralement `cuda` ; un contributeur Mac doit adapter `model.to("cuda")` → `model.to("mps")` et certains kernels CUDA-specific (triton, bitsandbytes) ne sont pas disponibles — ces notebooks sont `[GPU-Linux/Windows]` uniquement.
- Les launchers `.sh` (cf [#10647](https://github.com/jsboige/CoursIA/issues/10647)) gèrent la détection `nvidia-smi` cross-OS.

## Réparation d'env Python

Les modes d'échec Python diffèrent de Windows (pas de DLL locking, pas d'UAC, pas de Defender quarantine). Cf [env-python-reparation.md](env-python-reparation.md) pour les symptômes Windows ; sur Mac/Linux :

```bash
# Processus lockant un fichier (au lieu de Get-Process)
lsof +D ~/.local/lib/python3.11/site-packages/<pkg>

# Python réellement invoqué (au lieu de where.exe python)
which -a python python3
python -c "import sys; print(sys.executable)"

# Multi-Python confusion : toujours pip via le binaire explicite
python3 -m pip install --force-reinstall <pkg>
```

## Vérification rapide (Mac/Linux)

```bash
dotnet --list-sdks
dotnet interactive --version
jupyter kernelspec list   # .net-csharp, python3, lean4
lean --version
python3 --version
conda env list
```

## Voir aussi

- [kernels-runtime.md](kernels-runtime.md) — Inventaire kernels par machine du cluster (Windows-centric)
- [env-python-reparation.md](env-python-reparation.md) — Réparation env Python (Windows-centric)
- EPIC [#10643](https://github.com/jsboige/CoursIA/issues/10643) — Support multiplateforme Linux/macOS
