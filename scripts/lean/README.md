# Scripts Lean

Outils pour le cycle de vie des projets Lean 4 du dépôt.

| Script | Rôle |
|--------|------|
| `setup_lean4_all.py` | Installation initiale des toolchains Lean via `elan` pour tous les projets |
| `setup_native_lean4_import.py` | Kernel `lean4-wsl` natif (jupyter-WSL bridge, sans `wsl()` subprocess) |
| `setup_shared_mathlib.ps1` | Mutualisation des checkouts Mathlib via junctions NTFS (voir ci-dessous) |
| `lean_kernel_check.py` | Diagnostic kernel Lean (toolchain, oleans, env Python) |
| `smoke_test_epita_is.py` | Smoke tests du parcours EPITA-IS (notebooks + preuves) |

Tests unitaires dans `tests/`.

---

## `setup_shared_mathlib.ps1` — mutualisation Mathlib (issue #4363, outillage #2611)

### Problème

~12-15 projets Lake du dépôt (`MyIA.AI.Notebooks/**/`) embarquent chacun leur
propre checkout Mathlib. Sans mutualisation : **~61 GB dupliqués** sur disque,
un checkout complet (`lake exe cache get` ≈ 8000 oleans, ~40 s) par projet
lors de chaque migration de rev.

### Solution : junctions NTFS

Les projets partageant **exactement** le même `lake-manifest.json` (toutes deps
transitives, pas seulement `mathlib`) + le même `lean-toolchain` peuvent
partager le même checkout Mathlib via une **jonction NTFS** (reparse-point,
ne nécessite pas d'élévation admin) pointant vers un cache central :

```
<racine-du-depot>\.mathlib-cache\<toolchain>-<rev8>\mathlib\
```

**La racine dépend de la machine** — `C:\dev\CoursIA\` sur les workers, `D:\CoursIA\`
sur ai-01. Ne pas traiter un chemin absolu de cette doc comme canonique : une
recherche large sur la mauvaise racine renvoie `0 olean` et se lit à tort comme
« cache purgé » (cause n°1 de l'incident du 2026-07-29, cf caveat de mesure
plus bas). Résoudre la racine avec `git rev-parse --show-toplevel`.

Le script `setup_shared_mathlib.ps1` automatise cette mutualisation et persiste
l'état dans `.mathlib-cache/<toolchain>-<rev8>/share-state.json`.

### Modes

```powershell
# Scan : inventaire des groupes mutualisables (lecture seule)
pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan

# Apply : crée le cache partagé + junctions pour les groupes éligibles.
#   -Build            : lance lake build dans chaque projet (vérifie replay
#                       pur : 0 recompilation attendue).
#   -RemoveBackups    : après build SUCCESS, supprime les checkouts physiques
#                       d'origine (libère l'espace disque). Requiert -Build.
#   -Group <key>      : restreint à un groupe (ex: 'd568c8c0' = rev Mathlib).
pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Apply -Build -RemoveBackups

# Rollback : retire les junctions et restaure les checkouts physiques depuis
# les backups .bak-2611 (lit share-state.json).
pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Rollback
```

### État actuel sur ce dépôt (2026-07-03)

Une seule cohorte mutualisée est active à ce jour :

| Groupe (toolchain-rev8) | Mathlib | Membres | Cache (GB) |
|-------------------------|---------|---------|------------|
| `leanprover_lean4_v4.31.0-rc1-d568c8c0` | `d568c8c09630de097a046763c17b9ea99f95f950` | **19 lakes** | ~7 |

Liste exhaustive des 19 lakes junctionnés (extrait de `share-state.json`) :

```
GameTheory/cooperative_games_lean
GameTheory/minimax_lean
GameTheory/repeated_games_lean
GameTheory/social_choice_lean
GameTheory/stable_marriage_lean
ML/learning_theory_lean
Probas/decision_theory_lean
QuantConnect/kelly_lean
Search/search_lean
Sudoku/sudoku_lean
SymbolicAI/Lean/calibration_lean
SymbolicAI/Lean/conway_lean
SymbolicAI/Lean/grothendieck_lean
SymbolicAI/Lean/knot_lean
SymbolicAI/Lean/mathlib_examples
SymbolicAI/Lean/sensitivity_lean
SymbolicAI/Planners/planning_lean
SymbolicAI/SmartContracts/erc20_lean
SymbolicAI/Tweety/argumentation_lean
```

**Vérification** : un `cmd /c fsutil reparsepoint query <lake>\.lake\packages\mathlib`
doit afficher un `Nom substitut` pointant vers
`<racine-du-depot>\.mathlib-cache\leanprover_lean4_v4.31.0-rc1-d568c8c0\mathlib`
(`C:\dev\CoursIA\...` sur les workers, `D:\CoursIA\...` sur ai-01).

**Preuve de replay** (cf issue #4363, commentaires du 2026-07-02) :
`lake build` à travers la junction = **0 recompilation** (Build completed
successfully sur 2954-3327 jobs selon le projet). Aucun projet junctionné ne
nécessite `lake update`.

### Groupes orphelins (rev unique, non mutualisables)

| Groupe | Mathlib | Cause |
|--------|---------|-------|
| `leanprover_lean4_v4.27.0-rc1-8cb93191` | `8cb93191` | `social_choice_lean_peters` seul (API-port wall, INTRINSIC) |
| `leanprover_lean4_v4.25.0-1ccd71f8` | `1ccd71f8` | Snapshot prover reference interne uniquement |
| `leanprover_lean4_v4.30.0-rc2-54f98fd6` | `54f98fd6` | Cache d'archives rc2 (plus de projets rc2 sur main post #4364) |

### Caveats opérationnels

- **NE PAS lancer `lake update` dans un projet junctionné** : cela muterait le
  checkout partagé pour TOUS les membres du groupe. Mettre à jour = `Rollback`
  d'abord, `lake update`, puis re-`Apply`.
- **Avant `rm -rf` d'un lake**, retirer la junction via `cmd /c rmdir
  <lake>\.lake\packages\mathlib` (supprime le reparse-point seul, jamais la
  cible du cache partagé). Un `rm` Git-Bash peut traverser la junction et
  supprimer le cache.
- **`.mathlib-cache/`** est gitignored (artefact local, jamais commité).
- **Race condition partagée** (cf `lean-rc1-convergence-method.md`) : ne pas
  paralléliser `lake build` sur 2+ lakes partageant la même junction cache.
  Séquentialiser.
- **Ne jamais compter les oleans à la main pour conclure « cache purgé »** :
  `find <lake>/.lake/packages/mathlib -name '*.olean'` renvoie **0** sur un cache
  sain de 8124 oleans (Git-Bash `find` ne traverse pas les junctions), et
  `os.path.islink()` renvoie **False** dessus — rien ne signale qu'on mesure un
  lien. Noter l'asymétrie avec le caveat `rm` ci-dessus : `rm` traverse la
  junction (et peut détruire le cache), `find` ne la traverse pas (et le déclare
  vide). Utiliser `py scripts/lean/check_mathlib_cache.py`, qui résout chaque
  `realpath`, compte via `os.walk`, affiche si le chemin est une junction et
  dédoublonne les lakes partageant un même cache physique. Un `lake build` sur
  une cible connue reste la preuve décisive (~2 min à chaud vs 30+ min à froid).
  Incident fondateur : 5 cycles de lane Lean perdus sur un cache intact
  (DM `msg-20260729T055956-n3f4ap`) — c'est le second mécanisme de faux-absent,
  distinct de celui documenté dans
  [`docs/lean/coordinator-workflow.md`](../../docs/lean/coordinator-workflow.md)
  (oleans cherchés dans le répertoire source au lieu de `.lake/build/lib/lean/`).

### Histoire des issues

- **#2611** — outillage initial, alignement des manifests (fermé).
- **#4362 EPIC** — Lean harmonisation : Mathlib unifié, mutualisation, regroupement
  de lakes cohésifs (tracker parent).
- **#4364** — convergence rc2 → v4.31.0-rc1 (10+ tranches livrées, comment
  du 2026-07-02 dans #4363 documente le replay + extension).
- **#4363** — cette mutualisation (19/19 lakes actifs).
- **#4365** — regroupement des lakes cohésifs post-convergence (Phase 4 de
  #4362, OPTIONNEL après convergence complète).

Voir aussi : `lean-wdac-olean-wholesale-copy.md`, `lean-knot-build-windows-cache.md`,
`lean-rc1-convergence-method.md` dans `~/.claude/projects/c--dev-CoursIA-2/memory/`.
