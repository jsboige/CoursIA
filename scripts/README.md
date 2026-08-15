# Scripts - Outils Utilitaires

Scripts de gestion, validation et execution pour l'ecosysteme CoursIA.

## Structure

```text
scripts/
├── notebook_tools/              # Outils manipulation notebooks
│   ├── notebook_tools.py        # CLI (skeleton, validate, analyze, execute)
│   ├── notebook_helpers.py      # Helpers manipulation programmatique
│   ├── extract_notebook_skeleton.py  # Extraction structure pour README
│   └── fix_audio_dependencies.py     # Fix dependances audio
│
├── genai-stack/                 # CLI GenAI (Docker, validation, modeles)
│   └── genai.py                 # Point d'entree unifie
│
├── kernels/                     # Configurations kernels Jupyter
│   └── lean4-wsl/               # Kernel Lean4 via WSL
│
├── mcp-maintenance/             # Troubleshooting MCP/NuGet
│   ├── docs/                    # Documentation resolution problemes
│   ├── scripts/                 # Scripts de diagnostic
│   └── config/                  # Variables critiques
│
├── environment/                 # Scripts environnement (jumeaux .ps1/.sh)
│   ├── setup_environment.{ps1,sh}    # Setup de base (Python, .NET, kernels)
│   ├── audit_environment.{ps1,sh}    # Diagnostic de l'environnement
│   ├── automata-build-deploy.{ps1,sh}  # Build/déploiement des automates
│   ├── install-ffmpeg.{ps1,sh}       # Installation FFmpeg
│   ├── z3-build-deploy.{ps1,sh}      # Build du wrapper Z3.Linq forké
│   └── README.md                # Équivalences Linux/macOS (#10644)
│
├── translation/                 # Synchro traduction multilingue (#4957 / #1650)
│   └── extract_cells_to_csv.py  # Extraction cellules -> CSV (drift-detection)
│
├── tests/                       # Tests unitaires
│
└── validate_lean11.py           # Validation Lean11
```

## Scripts Principaux

### notebook_tools.py

CLI multi-fonction pour la gestion des notebooks.

```bash
# Extraire la structure
python scripts/notebook_tools/notebook_tools.py skeleton MyIA.AI.Notebooks/Sudoku --output markdown

# Valider (structure uniquement)
python scripts/notebook_tools/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku --quick

# Analyser le contenu
python scripts/notebook_tools/notebook_tools.py analyze MyIA.AI.Notebooks/Sudoku

# Executer
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/GenAI --timeout 300
```

### notebook_helpers.py

Fonctions utilitaires pour manipulation programmatique.

```bash
python scripts/notebook_tools/notebook_helpers.py list notebook.ipynb
python scripts/notebook_tools/notebook_helpers.py analyze notebook.ipynb
python scripts/notebook_tools/notebook_helpers.py get-source notebook.ipynb 5
```

### genai.py (CLI GenAI)

```bash
# Statut services Docker
python scripts/genai-stack/genai.py docker status

# Validation complete
python scripts/genai-stack/genai.py validate --full

# Verification GPU
python scripts/genai-stack/genai.py gpu
```

Voir [genai-stack/README.md](genai-stack/README.md) pour la documentation complete.

### extract_cells_to_csv.py (Synchro traduction)

Extrait les cellules d'un notebook ou d'une série vers le CSV de synchro traduction
(`translations/<famille>/<série>.csv`), source de vérité de l'alignement multilingue.
Schéma ratified #4957 §1 : `notebook, cell_id, cell_type, src_lang, src_hash, text_<lang>, hash_<lang>`
(8 langues EN/FR/ES/AR/FA/ZH/RU/PT). Les hashes bidirectionnels rendent la désynchronisation
détectable mécaniquement (source modifiée sans retraduction, ou traduction éditée à la main).

```bash
# Extraire le CSV initial d'une série (langue pivot fr, #1650 Phase 0.5)
python scripts/translation/extract_cells_to_csv.py MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/ \
    -o translations/symbolicai/argument_analysis.csv

# Un seul notebook (POC / schema review)
python scripts/translation/extract_cells_to_csv.py notebook.ipynb -o poc.csv
```

Le script est la couche T1 de l'infrastructure #4957 ; le drift-detection CI (T2) et la
resync par le moteur Argumentum (T3, gated #1650 Phase 1) viennent dans les tranches suivantes.

## Installation

```bash
# Windows (PowerShell) — FFmpeg + audit + setup de base
./scripts/environment/install-ffmpeg.ps1
./scripts/environment/audit_environment.ps1
./scripts/environment/setup_environment.ps1

# Linux / macOS (bash) — jumeaux équivalents
./scripts/environment/install-ffmpeg.sh
./scripts/environment/audit_environment.sh
./scripts/environment/setup_environment.sh --auto-fix
```

Chaque script PowerShell possède un jumeau bash de comportement équivalent
(`scripts/environment/README.md` documente les différences de port). Le seul
script Windows-only du dépôt est `scripts/genai-stack/Configure-IISAuthentication.ps1`
(IIS n'existe pas sur Mac/Linux) — pas de jumeau bash prévu.

## Validation Lean

```bash
# Valider Lean11
python scripts/kernels/validate_lean11.py
```

## Tests

```bash
python -m pytest scripts/tests/
```

## Hygiene disque — worktrees, stash, object-store

Recette periodique (cf #8924). Une lane livre par l'API GitHub des que son
disk-fill empeche `git fetch` ; ces preventifs gardent le depot exploitable.

### Avant/apres publie (recette reproductible, etalon ai-01)

| Mesure | Avant | Apres | Source |
| --- | --- | --- | --- |
| Worktrees enregistres | 192 | 188 | `git worktree list --porcelain` |
| Worktrees disposable (HEAD∈main, dirty=0) | 9 | 5 | merge-base + status |
| Object store | 2 389 MB | 1 234 MB | `du -sh .git/objects` |
| Stash global (16 entrees) | preserve | preserve | inventaire ci-dessous |

Cycle execute sur `myia-po-2023` (2026-07-30) : 4 worktrees retires (~3.6 GB),
`git gc --prune=now --aggressive` (4min41), gain net ~1.15 GB sur l'object-store.

### Recette, du moins risque au plus risque

```bash
# 1. Lister les worktrees + reperer ceux dont le HEAD est deja dans origin/main
git worktree list --porcelain
# Pour chaque candidat, verifier :
git merge-base --is-ancestor <HEAD> origin/main
git -C <path> status --porcelain    # doit etre vide (hors untracked)
# Si les deux sont VRAI -> git worktree remove <path>

# 2. Compacter l'object store (gain le plus gros, perte nulle)
git gc --prune=now --aggressive     # plusieurs minutes sur gros depots

# 3. Seulement si un fetch casse encore : nettoyer les packs temporaires
ls .git/objects/pack/tmp_pack_*     # residus d'index-pack interrompu
```

**A NE PAS faire** :

- `git stash clear` : les entrees sont du travail non-commite, sans proprietaire
  automatiquement identifiable (29+ sur ai-01). Inventorier d'abord
  (`git stash list --date=iso` + `git stash show --stat <n>` par entree) et
  decider par entree (rejouer / abandonner / promouvoir en branche).
- `git worktree remove -f` sur un arbre dirty : c'est precisement la ou du
  travail non-pousse vit.
- `git gc --aggressive` regulierement sur un workflow actif : chaque appel
  recompacte tout. Une fois par cycle / une fois par semaine suffit.

### Stash global vs stash-par-worktree (piege classique)

`git stash list` est **global au depot**, pas par worktree : un stash pose dans
un worktree survit a la suppression de ce worktree. Lire 29 entrees depuis 5
worktrees **n'en fait pas 145** : c'est 29, point. La liste retournee depuis
n'importe quel worktree est la meme.

### Documentation source

- Issue **#8924** (recette, mesure, cycle par machine)
- Lane proprietaire : `myia-po-2023:CoursIA-2` pour le cycle de reference ; a
  tour de role par cycle parmi `myia-ai-01`, `myia-po-2023`, `myia-po-2024`,
  `myia-po-2025`, `myia-po-2026`.
