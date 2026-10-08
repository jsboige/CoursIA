# Junctions Mathlib — scan po-2025 : 18 jonctions vivantes, **aucune utilisable**

**Date** : 2026-10-08
**Lane** : `myia-po-2025:CoursIA`
**Issue parente** : #13962 — Appliquer les junctions NTFS sur le cluster Mathlib `520045ab`
**Mode** : `Scan` (lecture seule, aucune modification) + organe dédié `check_mathlib_cache.py` + mesure résolue des cibles
**Commandes exécutées** :
- `pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` depuis `D:\dev\CoursIA` (worktree **principal**)
- `python scripts/lean/check_mathlib_cache.py`
- mesure résolue des cibles de jonction (`fsutil reparsepoint query`, énumération chemin `\\?\`)

Voir aussi :
- `docs/lean/junctions-scan-po-2024.md` — **le pair méthodologique** (22 jonctions vers un store vide) ; §4 « Angle mort de l'instrument » est le protocole repris ici
- `docs/lean/junctions-scan-po-2027-CoursIA2.md` — même angle mort de classement (cible réelle ≠ groupe déclaré)
- `docs/lean/junctions-scan-po-2026.md` · `docs/lean/junctions-scan-po-2023.md` · `docs/lean/junctions-scan-po-2027.md` · `docs/lean/cluster-junctions-c857.md`

## Résumé

Le tirage de cycle a rendu #13962 et le rapport po-2025 manquait à la série (les pairs po-2023, po-2024, po-2026, po-2027, po-2027-CoursIA2 existaient, pas po-2025). Ce rapport le solde.

Le verdict est **plus fort** qu'un rafraîchissement : po-2025 n'est ni une machine « sans travail » ni une machine « sans donneur ». C'est un **cluster appliqué dont les 18 jonctions sont inutilisables** — 14 vers une cible qui **n'existe pas**, 4 vers un store **vide** appartenant à une **autre toolchain**. Le Scan rend pourtant `Economie totale potentielle : 0 GB`, c'est-à-dire la signature exacte d'une machine sans travail.

| Métrique | po-2025 (ce rapport, 2026-10-08) |
|---|---:|
| Projets Lake portant `mathlib` (manifest scanné) | **30** |
| Lacs **`JUNCTIONED`** | **18** |
| … dont la jonction est **utilisable** | **0** |
| … dont la cible **n'existe pas** (`v4.33.0-db584cd6`) | **14** |
| … dont la cible est **vide** et d'une **autre toolchain** (`v4.32.1-520045ab`) | **4** |
| Checkouts physiques réels | **1** (`formal_logic_lean`, 0,77 GB) |
| **Oleans Mathlib atteignables** (`check_mathlib_cache.py`) | **0 / 36** |
| Sauvegardes `.bak-2611` disponibles pour un Rollback | **0** |
| Économie « potentielle » rendue par le Scan | **0 GB** (métrique aveugle ici) |

## 1. Sortie verbatim du Scan (2026-10-08)

```
=== Projets Lake avec dependance mathlib (30) ===

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [MUTUALISABLE] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/GameTheory/assignment_lean                           JUNCTIONED
  MyIA.AI.Notebooks/GameTheory/game_theory_lean                          JUNCTIONED
  MyIA.AI.Notebooks/GameTheory/minimax_lean                              JUNCTIONED
  MyIA.AI.Notebooks/ML/learning_theory_lean                              JUNCTIONED
  MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean     JUNCTIONED
  MyIA.AI.Notebooks/Probas/DecisionTheory/decision_theory_lean           pas de checkout local
  MyIA.AI.Notebooks/QuantConnect/kelly_lean                              JUNCTIONED
  MyIA.AI.Notebooks/Search/search_lean                                   JUNCTIONED
  MyIA.AI.Notebooks/Sudoku/sudoku_lean                                   JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/geometry_lean               pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean               pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean                     JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean                          pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/formal_groups_lean                   JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/galois_lean                          JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean                    pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean                           JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean                            JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples                     JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean                     JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean                    JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean                 JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean                 JUNCTIONED

--- Groupe leanprover_lean4_v4.25.0-1ccd71f8 [isole] : toolchain=leanprover/lean4:v4.25.0 mathlib=1ccd71f8 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/session_state/reference_docs/stable_marriage/upstream pas de checkout local

--- Groupe leanprover_lean4_v4.32.1-520045ab [isole] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_lean_peters    pas de checkout local

--- Groupe leanprover_lean4_v4.33.0-rc1-5eec30bc [isole] : toolchain=leanprover/lean4:v4.33.0-rc1 mathlib=5eec30bc ---
  MyIA.AI.Notebooks/GameTheory/conway_cgt_lean                           pas de checkout local

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [isole] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/Search/discrepancy_lean                              pas de checkout local

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [isole] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean                            pas de checkout local

--- Groupe leanprover_lean4_v4.33.1-0df444a3 [isole] : toolchain=leanprover/lean4:v4.33.1 mathlib=0df444a3 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean                    checkout physique (0.77 GB)

--- Groupe leanprover_lean4_v4.33.1-0df444a3 [isole] : toolchain=leanprover/lean4:v4.33.1 mathlib=0df444a3 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean                    pas de checkout local

=== Economie totale potentielle (groupes en l'etat) : 0 GB ===
Note : l'alignement des manifests (#2611 etape 2) peut elargir les groupes.
```

## 2. « JUNCTIONED » ne dit rien de la cible

Le Scan rapporte **18 `JUNCTIONED`** — et il a raison sur un point : ces 18 chemins **sont** des jonctions NTFS. Ce qu'il ne mesure pas, c'est **où elles pointent**. Or c'est là que se joue l'usabilité :

- le Scan **ne résout pas la cible** : une jonction pendante et une jonction saine s'affichent identiquement ;
- le Scan **groupe le lac par son propre `lean-toolchain`**, pas par la cible de sa jonction — `game_theory_lean`, `percolation_lean`, `knot_lean` et `argumentation_lean` sont listés **sous le groupe `v4.33.0-db584cd6`** alors que leur jonction pointe le cache `v4.32.1-520045ab`.

Ce second angle mort est **déjà documenté** sur une autre machine de la série : `junctions-scan-po-2027-CoursIA2.md` relève que le Scan range `kelly_lean` sous `v4.33.0-db584cd6` « parce que son manifest declare v4.33.0 » alors que la cible réelle mesurée est `v4.32.1-520045ab`. po-2025 en est une seconde occurrence, à quatre lacs.

## 3. Mesure résolue — 18/18 inutilisables

Mesure des 18 cibles, par résolution du lien (même protocole que `junctions-scan-po-2024.md` §4) :

| Classe | Compte | Cible | Constat |
|---|---:|---|---|
| **Jonction pendante** | **14** | `D:\dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib` | **la cible n'existe pas** — le groupe `v4.33.0-db584cd6` est un répertoire **vide**, sans même une entrée `mathlib/` |
| **Jonction vivante sur store vide, toolchain dérivée** | **4** | `D:\dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.32.1-520045ab\mathlib` | la cible existe mais porte **0 entrée**, pas de `.git`, **0 MB** ; et le lac est en **v4.33.0** contre un groupe **v4.32.1** |

Les 14 pendantes : `assignment_lean`, `minimax_lean`, `learning_theory_lean`, `kelly_lean`, `search_lean`, `sudoku_lean`, `calibration_lean`, `formal_groups_lean`, `galois_lean`, `hecke_lean`, `mathlib_examples`, `sensitivity_lean`, `planning_lean`, `erc20_lean`.

Les 4 dérivées : `game_theory_lean`, `percolation_lean`, `knot_lean`, `argumentation_lean`.

Ces deux classes sont **distinctes** de l'état décrit sur po-2024 (« 22 jonctions vivantes vers un store vide », dont 11 dérivées) : po-2024 n'avait pas de **cible inexistante**. Une jonction pendante n'est pas une jonction froide — c'est un lien dont le support a disparu.

## 4. Instrument de confirmation

Les deux classes ont été confirmées sur un cas-type chacune, avec l'instrument de `junctions-scan-po-2024.md` §4 (résolution **et** énumération à travers le lien, pour écarter le piège « un `0` rendu par `find`/`islink` sur une jonction saine ne prouve rien ») :

| # | Ce qui est mesuré | Instrument | Résultat |
|---|---|---|---|
| 1 | Le chemin est bien une jonction NTFS | `fsutil reparsepoint query` | balise `0xa0000003` (« Substitut de nom / Point de montage ») — **cas A et cas B** |
| 2 | …et pas une jonction déguisée | `Test-Path` sur le chemin résolu | cas A : cible **absente** (`False`) · cas B : cible présente (`True`) |
| 3 | Le contenu est absent **à travers** le lien | énumération chemin `\\?\` | cas B : **0 entrée**, `lakefile.lean` = False, `.git` = False |
| 4 | La dérive de toolchain est réelle | `lean-toolchain` du lac vs groupe | lac `v4.33.0` contre groupe `v4.32.1` (`share-state.json`) |

Le point 3 est celui qui écarte le faux négatif : le `0` est mesuré **à travers** la jonction, pas sur le chemin du lien.

## 5. Le compte de membres de `share-state.json`

Le seul groupe disposant d'un état est `leanprover_lean4_v4.32.1-520045ab` :

```json
{ "groupId": "leanprover_lean4_v4.32.1-520045ab",
  "toolchain": "leanprover/lean4:v4.32.1",
  "mathlibRev": "520045ab14e26149ee970e2e617ca04b09bde5d6",
  "createdAt": "2026-09-25T05:24:36.2033464+02:00", "members": [ 7 ] }
```

| Membre déclaré | État mesuré aujourd'hui |
|---|---|
| `game_theory_lean` (lac v4.33.0) | jonction **vivante sur store vide** |
| `repeated_games_lean` | **absent** de l'inventaire des lacs (non tracké) |
| `percolation_lean` (lac v4.33.0) | jonction **vivante sur store vide** |
| `decision_theory_lean` | **aucun checkout** |
| `conway_lean` — **donneur** (`isDonor: true`) | **aucun checkout** |
| `knot_lean` (lac v4.33.0) | jonction **vivante sur store vide** |
| `argumentation_lean` (lac v4.33.0) | jonction **vivante sur store vide** |

Deux faits en découlent :

1. **Le donneur ne porte rien.** `conway_lean` est déclaré donneur du groupe ; il n'a aujourd'hui **aucun** checkout Mathlib — son `.lake/packages` a **entièrement disparu**, pas seulement `mathlib`. La copie physique qui devait alimenter les six autres n'est plus là.
2. **Aucune sauvegarde n'existe.** Les 7 membres portent tous `hadBackup: false`, et **aucun `.bak-2611`** n'existe dans l'arbre (recherche à **toute profondeur** sous `MyIA.AI.Notebooks`, pas seulement aux niveaux superficiels — la sauvegarde attendue est à `.lake/packages/mathlib.bak-2611`, soit 7 niveaux sous la racine). `-Mode Rollback` (« restaure les checkouts physiques depuis les backups ») **n'a donc rien à restaurer** pour aucun des sept.

La forme appliquée est en revanche conforme à l'intention du script, et c'est ce qui rend le diagnostic non trivial : sur `game_theory_lean`, les **huit autres paquets** (`aesop`, `batteries`, `Cli`, `importGraph`, `LeanSearchClient`, `plausible`, `proofwidgets`, `Qq`) sont des répertoires **réels**, et **seul `mathlib`** est une jonction. Un `ls` sur `.lake/packages` y montre donc une arborescence Lake normale — le seul élément cassé est précisément celui qu'on partage.

La chronologie des migrations de toolchain situe l'origine : `knot_lean` est passé en v4.33.0 le **2026-09-19** (`3eb6db5f71`), `percolation_lean` et `argumentation_lean` le **2026-09-24** (`a6c8ac71c2`), `game_theory_lean` le **2026-09-25** (`69ac7ea0a3`) — soit *avant ou le jour même* de la création du groupe (2026-09-25T05:24:36+02:00). Trois des quatre lacs étaient donc déjà migrés au moment du groupement.

## 6. Ce que le « 0 GB » de l'organe veut dire, et ce qu'il ne dit pas

`Economie totale potentielle : 0 GB` est **exact et trompeur** : l'organe calcule l'économie à partir des checkouts **physiques** (il n'en voit qu'un, `formal_logic_lean`, isolé en v4.33.1). Une jonction n'étant pas un checkout physique, elle n'entre dans aucun calcul.

La conséquence est que la machine portant **le plus de jonctions cassées de la série après po-2024** reçoit la même ligne que les machines sans travail (`po-2023`, `po-2026`, `po-2027`, ai-01 : « large réservoir, amorçage quasi nul »). Le `0 GB` ne dit pas « rien à faire » ; il dit « aucune économie *supplémentaire* à tirer » — sur un état déjà appliqué.

## 7. Position dans la flotte

| Machine | Jonctions | Store | État |
|---|---:|---|---|
| ai-01 | 0 | — | réservoir large, amorçage nul |
| po-2023 | 0 | — | 3 checkouts physiques (1,28 GB), 0,64 GB récupérables — Apply non justifié |
| po-2024 | **22** | **vide** | **appliqué le 2026-08-30**, store vidé depuis, 11 dérivées |
| **po-2025** | **18** | **vide + 1 cible inexistante** | **appliqué**, 0 utilisable, 4 dérivées, 0 sauvegarde — **(ce rapport)** |
| po-2026 | 1 | — | 15 checkouts physiques, 4,09 GB récupérables |
| po-2027 | 0 / 9 | vide | deux mesures selon le worktree (faux négatif de portée) |

po-2025 est la **deuxième machine de la série dont le cluster est appliqué et cassé**, et la première à porter une **cible de jonction inexistante**.

## 8. Recommandation

**Aucun `Apply` n'est lancé, ni proposé, par ce rapport.** Sur l'état mesuré, un Apply serait au mieux inopérant et au pire aggravant :

1. **Il n'y a pas de donneur.** Le donneur déclaré (`conway_lean`) n'a plus de checkout, et le seul checkout physique de la machine (`formal_logic_lean`, 0,77 GB) est dans un groupe **isolé** (`v4.33.1`) — il ne peut pas alimenter le groupe `db584cd6`. Le script lui-même « skip le groupe AVANT toute jonction » sans donneur (docstring, durcissement #18584).
2. **Il n'y a pas de filet.** `hadBackup: false` sur les 7 membres, aucun `.bak-2611` dans l'arbre : un Apply qui échoue laisserait le même état, sans retour possible.
3. **Le geste utile est l'inverse d'un Apply** : retirer les 18 jonctions pour que chaque lac redevienne un lac ordinaire, et laisser `lake exe cache get` repeupler là où un build est réellement demandé. C'est un **geste disque** — il attend un **GO nominatif** (déjà consigné au registre des vérifications en attente de la lane).

**Angle mort à dispatcher** (repris de `junctions-scan-po-2024.md` §4, non traité depuis) : tant que `Scan` affiche `JUNCTIONED` sans résoudre la cible, **aucune** des machines de la série ne peut alerter sur une jonction pendante ou dérivée. Une seconde cécité, propre à l'organe dédié, est mesurée au §9.

## 9. Angle mort de `check_mathlib_cache.py` (mesuré)

L'organe dédié **corrige** le piège de `islink` — et tombe dans un piège voisin. Sur les 14 jonctions pendantes, il rend `absent` **et** `reel` :

```
  absent    assignment_lean                   0 olean  reel
  cold      game_theory_lean                  0 olean  junction
```

La cause est un **retour anticipé** avant la détection de jonction :

| Ligne | Code | Effet sur une jonction **pendante** |
|---|---|---|
| 88 | `if not mathlib.exists(): → status = "absent"; return` | `exists()` suit le lien vers une cible absente → **`False`** → sortie **avant** la l. 93-96 |
| 93-96 | `real = os.path.realpath(mathlib)` puis `junction = …` | **jamais atteint** — la clé `junction` reste absente |
| 158 | `flag = "junction" if r.get("junction") else "reel    "` | affiche **`reel`** : l'exact contraire de la vérité |

Mesure de la divergence, sur le même chemin :

```
os.path.islink  : False      Path.is_symlink() : False
os.path.exists  : False      Path.is_junction(): True      <- la seule API qui voit juste
os.path.isdir   : False      Path.resolve()    : <la cible, correctement résolue>
```

`Path.is_junction()` (Python ≥ 3.12 ; po-2025 porte 3.13.14) **voit** la jonction pendante — `resolve()` la résout correctement aussi. C'est l'ordre des tests qui perd l'information, pas l'API.

Le fichier porte pourtant l'avertissement exact, à sa dernière ligne : « un comptage a 0 via `find` ou `islink` ne prouve rien sur une junction ». L'organe qui écrit cet avertissement classe 14 jonctions comme des répertoires réels.

**Portée du chiffre.** Le verdict global `mathlib ok: 0 / 36` reste **juste** — aucune des deux cécités ne fabrique un faux « ok ». Elles faussent le **diagnostic** (quelle classe de panne, sur quel lac), pas le verdict d'atteignabilité.

```
Lakes: 36 | mathlib ok: 0 | froid: 4 | partiel: 1 | non installe: 27 | caches physiques distincts: 2
```

## Conclusion opérationnelle

1. **po-2025 ne peut pas être réparée par un Apply** : ni donneur, ni sauvegarde. La décision n'est pas « appliquer ou pas », elle est « retirer les 18 jonctions » — geste **coordinateur + GO user**.
2. **Les deux organes de la série ne distinguent pas** `JUNCTION-COLD` de `JUNCTION-DANGLING`, ni la cible réelle du groupe déclaré. C'est la proposition §4 de po-2024, restée ouverte ; po-2025 en fournit la seconde occurrence.
3. **Aucune modification n'a été faite** par ce rapport : `Scan` et les organes de mesure sont en lecture seule.

## Fichier source de la mesure

Sortie verbatim du Scan et mesures résolues conservées dans le scratchpad du worker po-2025 pour traçabilité : `scratchpad/scan-po2025-ter.txt`, `scratchpad/meas_junctions.ps1`, `scratchpad/confirm_reparse.ps1`.

## Voir aussi

- #13962 — issue parente (mesure ai-01 : 110 Go d'empreinte, 0 jonction active)
- #2611 — outillage `setup_shared_mathlib.ps1` (CLOSED) · #18584 — durcissement validation du cache
- #4362 — EPIC parent · #4363, #4364, #4365 — phases 1-2-3 (CLOSED sans application)
- `docs/lean/junctions-scan-po-2024.md` — pair méthodologique (22 jonctions, store vide)
- `docs/lean/junctions-scan-po-2026.md` · `junctions-scan-po-2023.md` · `junctions-scan-po-2027.md` · `junctions-scan-po-2027-CoursIA2.md`
- `docs/lean/cluster-junctions-c857.md` — référence cluster
- `scripts/lean/check_mathlib_cache.py` — organe d'atteignabilité des oleans
