# H.7 P3 Notebook Runner

Multi-kernel Docker runner for CoursIA notebook execution.
Supporte Python 3.12 (systeme, Ubuntu 24.04), Python 3.13 (`global-3.13`),
.NET 10 Interactive (C#, F#, PowerShell) et les noyaux Lean 4.

> **Alignement des versions (pli 1.2 de l'Epic #27543, #27545).** Ce README
> annoncait *Python 3.12 / .NET 9* — ni l'un ni l'autre ne decrivait l'image.
> L'image embarque le **Python systeme 3.12.3** et le **SDK .NET 10**
> (`dotnet/sdk:10.0`, requis par dotnet-interactive 1.0.712001). Le tableau
> ci-dessous est desormais la realite mesuree, et les epingles viennent de
> [`docs/reference/kernels-runtime.md`](../../docs/reference/kernels-runtime.md).
>
> **Correction (2026-11-20, mesure dans l'image construite).** La base est
> `dotnet/sdk:10.0`, basee sur **Ubuntu 24.04.5 LTS** — et non sur Debian
> bookworm, comme l'annoncaient une version anterieure de ce fichier et du
> Dockerfile. D'ou l'interpreteur systeme **3.12.3**, et non 3.11
> (`python3 --version` dans l'image construite). L'image est desormais
> construite et mesuree : les versions ci-dessous sont lues dans le
> conteneur, elles ne sont pas deduites.

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

## Image d'apprentissage (JupyterLab, tous les noyaux canoniques)

Une seconde cible du meme `Dockerfile` construit l'**image d'apprentissage** :
une image unique qui demarre JupyterLab avec tous les noyaux canoniques du
depot. Elle REBUILT les etages du runner (`base` → `python-env` →
`global-313` → `dotnet-interactive` → `lean-env`) au lieu de les dupliquer.

```bash
# Compose (l'entree `additional_contexts` fournit le wrapper Lean canonique)
docker compose -f docker-configurations/notebook-runner/docker-compose.yml build learning
docker compose -f docker-configurations/notebook-runner/docker-compose.yml up learning
# -> http://localhost:8888

# Ou en buildx direct : le contexte nomme est REQUIS, la construction echoue sans lui
docker buildx build \
  --build-context lean_scripts=../../MyIA.AI.Notebooks/SymbolicAI/Lean/scripts \
  --target learning -t coursia/learning:latest \
  docker-configurations/notebook-runner
```

Le contexte nomme `lean_scripts` fournit
`MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/lean4-kernel-wrapper.py` — le
wrapper canonique du noyau Lean — directement depuis le depot. Il n'est ni
recopie ni reecrit dans le contexte Docker ; sans lui, la construction echoue
(fail-closed) au lieu de livrer un wrapper bricole.

### L'image publiee : une seule commande, sans construire

Le workflow [`learning-image-ghcr`](../../.github/workflows/learning-image-ghcr.yml)
(publie par #27546) reconstruit l'image quand le `Dockerfile`, les exigences,
les temoins ou le manifeste du pli 1.1 changent, execute un carnet temoin par
famille de noyau (7 sur 7 exigees), puis publie sur GHCR avec une etiquette
versionnee et `latest`. Une fois le paquet public, l'apprenant n'a **rien a
construire** :

```bash
docker run -p 8888:8888 ghcr.io/jsboige/coursia-learning:latest
# -> http://localhost:8888 — JupyterLab, les 7 noyaux canoniques
```

L'image **demarre seule** : sa commande par defaut est JupyterLab, aucune
commande n'est a ajouter. Le workflow `learning-image-ghcr` le verifie a chaque
construction — il lance l'image sans surcharge de commande et exige une
reponse HTTP sur le port 8888 ; c'est le temoin de la commande par defaut
(#27547).

**Le jeton** : JupyterLab en demande un, tire au hasard a chaque demarrage et
affiche dans le journal du conteneur (`docker logs <conteneur>`) ; sans lui,
`/lab` redirige vers la page de connexion. Le jeton n'est ni fixe ni desactive
dans l'image : la posture d'authentification d'un paquet public est une
decision du mainteneur, pas un effet de bord de ce pli.

Mesure relevee sur la machine de l'auteur (4 vCPU, 16 Go, `hostRequirements`
du devcontainer) : **4,3 s** entre le lancement du conteneur et la reponse de
JupyterLab, puis **8,1 s** pour le carnet temoin Python et **10,1 s** pour le
carnet temoin C# (`witness-net-csharp`). Ces trois durees dependent de la
machine hote ; le workflow en releve une a chaque build.

La premiere publication et la visibilite publique du paquet dependent du
reglage du paquet GHCR cote mainteneur ; les etiquettes datees
(`20261120-1930`) et `sha-<commit>` restent disponibles pour figer une
version de cours. Le cache de couches vit dans l'etiquette `buildcache` du
paquet : la reconstruction apres un changement ne recompile que les etages
touches.

Les paquets Python de l'image d'apprentissage ne sont **pas** ecrits a la
main : ils sont la projection du manifeste consolide du pli 1.1
(`docs/curriculum/manifeste-dependances.json`), produite par

```bash
python scripts/notebook_tools/emit_learning_requirements.py --write   # emettre
python scripts/notebook_tools/emit_learning_requirements.py --check   # verifier
```

`requirements-learning.txt` est versionne dans le depot, et les exclusions
declarees (chacune avec un motif et une source) vivent dans
[`learning_image_policy.json`](learning_image_policy.json).

## Kernel Detection

The runner auto-detects the kernel from notebook metadata:

| Kernel name | Executor | Notes |
|-------------|----------|-------|
| `python3` | Papermill | Carnets Python standard (Python systeme 3.12.3) |
| `python3` (QuantConnect) | nbconvert `--allow-errors` | Detects `QuantBook` in source |
| `global-3.13` | Papermill (kernelspec natif) | Python 3.13 (env conda-forge) — notebooks serie Lean (#16262) |
| `.net-csharp` | nbconvert via .NET Interactive | C# notebooks |
| `.net-fsharp` | nbconvert via .NET Interactive | F# notebooks |
| `.net-powershell` | nbconvert via .NET Interactive | Carnets PowerShell |
| `lean4` / `lean4-wsl` | elan + lake | Verification formelle Lean 4 |
| `rust` | evcxr | Carnets Rust (jumeaux Sudoku) |

L'**image d'apprentissage** enregistre en plus : `rust` (evcxr 0.22.0) et
`lean4` (wrapper canonique + REPL apparie a la toolchain epinglee).

## Architecture

```text
notebook-runner/
├── Dockerfile          # Multi-etapes : .NET 10 + Python 3.12/3.13 + Lean 4 (+ cible `learning`)
├── docker-compose.yml  # Montages de volumes + limites de ressources (+ service `learning`)
├── h7_p3_notebook_runner.sh  # Script de dispatch unifie des noyaux
├── learning_image_policy.json     # Exclusions declarees (motif + source) de l'image d'apprentissage
├── requirements-learning.txt      # Paquets de l'image d'apprentissage, generes depuis le manifeste
├── witness/                        # Un carnet temoin par famille de noyau
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
  Full data requires QC Cloud backend (see `docs/qc/quantconnect.md`).
- **Lean 4 notebooks**: Require `lean4` kernel installed in the image. WSL-specific notebooks
  (kernel `lean4-wsl`) may need path adjustments.
- **GPU notebooks**: No GPU support in this runner. GenAI notebooks requiring GPU
  (ComfyUI, Qwen) will skip API-dependent cells.
- **Image d'apprentissage, noyau `lean4`** : le wrapper canonique refuse de
  demarrer si aucun ancrage `lean-toolchain` n'est atteignable depuis le
  repertoire d'execution (garde #18511). L'image fournit son propre ancrage
  (`/opt/lean4-anchor/lean-toolchain`, la toolchain epinglee de l'image, celle
  contre laquelle le REPL a ete compile) et un lanceur qui y entre : un carnet
  Lean s'execute donc depuis n'importe quel repertoire du conteneur. Sans cet
  ancrage, le noyau mourait avant `kernel_info` — mesure du 2026-11-20
  (temoin Lean : rc=1 en 7,6 s avant correction, `#eval 2 + 2` -> `4` apres).
- **Image d'apprentissage, paquets Python** : ils sont installes sous le
  Python systeme 3.12.3, pas sous `global-3.13`. La borne
  `numpy>=1.24,<2.0` du manifeste et son association canonique
  `python3 → 3.13` ne peuvent pas tenir ensemble (numpy 1.26.x ne publie
  aucune roue cp313). Le noyau `global-3.13` est donc enregistre **sans** les
  paquets du manifeste.
