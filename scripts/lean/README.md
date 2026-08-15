# Scripts Lean

Outils pour le cycle de vie des projets Lean 4 du dépôt.

| Script | Rôle |
|--------|------|
| `setup_lean4_all.py` | Installation initiale des toolchains Lean via `elan` pour tous les projets |
| `setup_native_lean4_import.py` | Kernel `lean4-wsl` natif (jupyter-WSL bridge, sans `wsl()` subprocess) |
| `setup_shared_mathlib.ps1` | Mutualisation des checkouts Mathlib via junctions NTFS (Windows, voir ci-dessous) |
| `setup_shared_mathlib.sh` | Jumeau Linux/macOS du `.ps1` (mode Scan portable ; Apply/Rollback = `RECOVERABLE-USER-HAND`, voir ci-dessous) |
| `setup_shared_mathlib_scan.py` | Helper Python du `.sh` (discovery TSV cross-OS, évite les pièges `os.path.join` MSYS) |
| `lean_kernel_check.py` | Diagnostic kernel Lean (toolchain, oleans, env Python) |
| `smoke_test_epita_is.py` | Smoke tests du parcours EPITA-IS (notebooks + preuves) |
| `check_public_anchor.py` | Detecte les `sorry` qu'aucune declaration publique n'atteint — l'angle mort residuel du gate `proof-integrity` (voir ci-dessous) |
| `count_code_sorry.py` | Compte les `sorry` **hors commentaires** (la vraie dette) et liste les theoremes vacuous (`: True`) — ce que `grep -c sorry` surestime de ~11x (voir ci-dessous) |

Tests unitaires dans `tests/`.

---

## `check_public_anchor.py` — les `sorry` hors de portee du gate (issue #8782)

### Problème

Le gate `proof-integrity` (`lean-axiom.yml`) mesure les axiomes via `#print axioms`
sur les declarations **publiques** d'un module. `_enumerate_module_declarations`
(`agent_tests/lean_server.py`) saute les declarations `private`, a raison : Lean 4
les mangle en `_private.<Module>.<hash>.<name>`, donc `#print axioms` repondrait
`unknown constant` et ferait tomber le verdict du module entier (#8722). La
justification ecrite dans ce code est que rien n'est perdu, *car un lemme prive
n'atteint le kernel qu'a travers les theoremes publics qui l'utilisent, et ceux-la
sont enumeres*.

C'est vrai **quand un theoreme public consomme effectivement la chaine**. Quand ce
n'est pas le cas — chaine privee sur toute sa longueur, ou lemme prive que personne
ne cite — le `sorryAx` n'apparait dans la cloture d'**aucune** declaration enumeree.
Le module est alors correctement cible, correctement enumere, et rapporte propre
alors qu'il porte un `sorry`. Le garde `enumerated=0` ne couvre pas ce cas : il ne
se declenche que si le module **entier** enumere vide, pas pour une declaration
privee orpheline dans un module par ailleurs sain.

Cet outil verifie mecaniquement cette hypothese, module par module.

### Pourquoi une analyse statique suffit — et est complete

En Lean 4, `private` est de portee **module** : une declaration privee n'est pas
referencable depuis un autre module. La cloture arriere d'une declaration privee est
donc entierement contenue dans son propre fichier, ce qui rend l'analyse mono-fichier
*complete* pour cette question, pas approximative. Aucun kernel, aucun Mathlib
construit : l'outil tourne sur n'importe quelle machine.

### Biais assume : jamais de fausse alarme, silences possibles

Le graphe de references est bati sur les noms — un token identique a un nom de
declaration compte comme une reference. C'est une **sur**-approximation des aretes
(une variable locale homonyme en cree une qui n'existe pas), et l'effet va toujours
dans le meme sens : plus d'aretes = plus de chances de trouver un ancrage =
**moins** de verdicts `unanchored`. L'outil peut donc taire un angle mort reel, il
ne peut pas en inventer un. C'est le bon biais pour un advisory.

Les commentaires sont retires avant l'analyse (via `strip_comments` de
`check_i18n_siblings.py`), sans quoi une mention en prose compterait comme une
citation : c'est exactement ce qui distingue ce detecteur d'un `grep -c`.

### Usage

```bash
python scripts/lean/check_public_anchor.py <fichier.lean> [...]
python scripts/lean/check_public_anchor.py --lake MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean
python scripts/lean/check_public_anchor.py --lake <dir> --json
python scripts/lean/check_public_anchor.py --lake <dir> --fail-on-unanchored
```

Advisory (exit 0) par defaut : l'outil rend visible, il ne decide pas.
`--fail-on-unanchored` est opt-in. Une cible vide ou absente est une **erreur**, pas
un rapport propre — un detecteur d'angle mort ne doit jamais se taire parce qu'il
n'a rien regarde (meme raison d'etre que les classifications `EMPTY_*` de #8940).

### Verdicts

| Verdict | Sens |
|---------|------|
| `anchored_public` | le porteur du `sorry` est lui-meme public — le gate le voit |
| `anchored_transitive` | porteur prive, mais une declaration publique le rejoint — vu transitivement |
| `unanchored` | porteur prive qu'aucune declaration publique ne rejoint — **invisible du gate** |
| `anonymous` | `example` : sans nom, jamais enumerable |
| `orphan_sorry` | `sorry` hors de toute declaration |

---

## `count_code_sorry.py` — la vraie dette de preuve vs `grep`, et les theoremes vides (issue #10188)

### Problème : deux angles morts composes

**1. `grep -c sorry` surevalue la dette d'un facteur ~11x a l'echelle du depot.**
Le compteur naif inclut le mot `sorry` dans les docstrings (`/- ... sorry ... -/`),
les commentaires ligne (`-- ... sorry`) et les chaines. Un body de PR qui cite un
avant/apres tire de `grep` cite donc un nombre sans rapport avec la dette reelle,
et un coordinateur qui dispatch du travail « fermer le sorry #N » depuis ce compte
envoie un worker sur une veine tarie (cas conway_lean : `grep` = 152, code reel = 2
distincts).

**2. Les theoremes vacuous passent TOUS nos gates.** Un enonce dont la conclusion
est `True` (`theorem foo : True := by trivial`, ou `∃ μ, True`) est entierement
verifie et entierement vide : `grep` ne le voit pas (pas de `sorry`, ou un `sorry`
sur un but trivial), `lake build` est vert, `#print axioms` est vert, et les scans
`sorryAx` / `Classical.choice` sont verts car `trivial` n'utilise aucun axiome
interdit. Fermer un tel `sorry` en une ligne produit un « sorry 41 -> 40 »
parfaitement authentique au compteur — avec **zero mathematique**. C'est la fausse
progression que G.2 interdit, sauf qu'ici toutes les preuves demandees par le
harnais seraient fournies.

### Solution : un organe d'analyse statique (sans Lean ni Mathlib)

Comme `check_public_anchor.py`, l'analyse est **mono-fichier et complete** pour la
question posee : on stripe les commentaires (blocs `/- -/` **imbriques** + lignes
`--`, en preservant les positions pour les rapports `file:line`), puis on compte
les tokens `sorry` reels et on les attribue a la declaration englobante. Les
siblings i18n `_en` (miroirs byte-identiques, convention #4980) sont rapportes
separement pour ne pas gonfler le compte *distinct*.

La detection vacuous cible la **fin du type** avant `:=`, avec un motif ancre :
`:\s*True$` (type = `True`) ou `,\s*True$` (conclusion d'un existentiel/universel).
Cela ne flaggue **pas** `a = True` (equation, le caractere avant `True` est `=`) ni
`True -> True` (fonction) — ces enonces sont triviaux mais disent quelque chose.

### Usage

```bash
# Depot entier : table par lake + liste advisory des vacuous (exit 0)
python scripts/lean/count_code_sorry.py

# Un seul lake
python scripts/lean/count_code_sorry.py --lake MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean

# JSON machine (CI / generation de body PR)
python scripts/lean/count_code_sorry.py --json

# Strict : exit 1 si un theoreme vacuous NON-marker reste (gate post-triage)
python scripts/lean/count_code_sorry.py --strict
```

Advisory (exit 0) par defaut : l'outil rend visible, il ne decide pas. Les
marqueurs assumes (`theorem *_prerequisites` du `MathlibPrerequisites.lean` de
knot_lean) sont taggues `is_marker` et ignores par `--strict` — ils sont la
dette explicite d'un port, pas des faux verts. Hors perimetre (statu quo i18n
#4980) : `.lake/packages/`, `_peters/`, `reference_docs/`, libs vendored.

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

### Jumeau Linux/macOS — `setup_shared_mathlib.sh` (PR #10664+)

L'EPIC #10643 (Support multiplateforme) introduit un jumeau bash pour les
workers Mac/Linux. Différences structurelles vs le `.ps1` :

| Aspect | Windows (NTFS junction) | Linux/macOS |
|--------|-------------------------|-------------|
| Lien vers le cache partagé | NTFS junction (`mklink /J`) | `ln -s` (mode Scan) ou bind mount (`mount --bind`, sudo) |
| Suppression du lien seul | `cmd /c rmdir` | `rm <symlink>` (le cache survit) |
| Suppression longue-path | `robocopy /MIR` depuis un dossier vide | `rm -rf` (FS Unix gère nativement) |
| Mode Scan (lecture seule) | OK | OK, 100% portable |
| Mode Apply | OK, sans élévation | **`RECOVERABLE-USER-HAND`** : bind mount requiert sudo, symlink absolu macOS risque avec outils natifs Xcode |
| Mode Rollback | Lit `share-state.json`, restore depuis `.bak-2611` | TODO partiel — `--rollback-via-restore-from-backup` exigé |

**Verdict SOTA-OK sur le mode Scan** : le scan énumère les lakes, groupe par
(toolchain, transitive deps), affiche l'économie potentielle. Aucune écriture,
aucun sudo. Le seul couplage OS est `os.path.islink()` (POSIX) pour détecter
les symlinks existants.

**Verdict RECOVERABLE-USER-HAND sur les modes Apply/Rollback** : par défaut,
le script sort en code 2 avec un message explicite si `--allow-bind-mount-with-sudo`
(Linux) ou `--allow-abs-symlink` (macOS) manque. Le user prend la décision.

```
./scripts/lean/setup_shared_mathlib.sh --scan
./scripts/lean/setup_shared_mathlib.sh --apply --allow-bind-mount-with-sudo --build
./scripts/lean/setup_shared_mathlib.sh --rollback --rollback-via-restore-from-backup
```

**Helper Python** : `setup_shared_mathlib_scan.py` est invoqué par le `.sh`
pour énumérer les lakes. Il utilise un `pj()` POSIX manuel (concaténation
avec `/`) au lieu de `os.path.join` car Git Bash MSYS détecte `os.sep = '\\'`
mais reçoit des paths POSIX-style en entrée (`REPO_ROOT=/c/...`). Bug mesuré :
`os.path.join('/c/repo', 'a/b')` produit `/c/repo\\a/b` qui n'existe pas.

### Histoire des issues

- **#2611** — outillage initial, alignement des manifests (fermé).
- **#4362 EPIC** — Lean harmonisation : Mathlib unifié, mutualisation, regroupement
  de lakes cohésifs (tracker parent).
- **#4364** — convergence rc2 → v4.31.0-rc1 (10+ tranches livrées, comment
  du 2026-07-02 dans #4363 documente le replay + extension).
- **#4363** — cette mutualisation (19/19 lakes actifs).
- **#4365** — regroupement des lakes cohésifs post-convergence (Phase 4 de
  #4362, OPTIONNEL après convergence complète).
- **#10643 EPIC** — Support multiplateforme Linux/macOS (sub-issue #10644 :
  scripts d'environnement + tooling `scripts/`, livrable #10664+).

Voir aussi : `lean-wdac-olean-wholesale-copy.md`, `lean-knot-build-windows-cache.md`,
`lean-rc1-convergence-method.md` dans `~/.claude/projects/c--dev-CoursIA-2/memory/`.
