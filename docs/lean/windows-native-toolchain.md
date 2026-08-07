# Lean 4 Windows-native toolchain — UNBLOCK Lake build depuis MSYS

> **Statut (2026-08-07)** : procédure validée firsthand sur la machine
> `po-2023` (Windows 11 Pro 10.0.26200, elan toolchain
> `c:\Users\jsboi\.elan\toolchains\leanprover--lean4---v4.31.0-rc1\`).
> Concerne tout agent `po-*` ou worker ad-hoc qui doit valider un lake Lean
> sans sortir de Windows (i.e. sans passer par WSL).
>
> **Pré-requis** : avoir installé le toolchain via `elan` (typiquement
> `elan toolchain install v4.31.0-rc1` + `elan default v4.31.0-rc1`).
> Pour ce repo, le `lean-toolchain` du lake pointe
> `leanprover/lean4:v4.31.0-rc1` — `elan` lit ce fichier et bascule
> automatiquement dessus.

## TL;DR — 3 commandes

```bash
# depuis un worktree du repo (bash MSYS Git Bash, cwd = racine lake) :
lake build                                # exit 0 si tout passe
echo $?                                   # 0
ls .lake/build/lib/Conway/Life/*.olean   # artifacts attendus
```

Si `lake build` retourne `exit 143` (SIGTERM) ou reste bloqué sur
`Mathlib.*` modules 6000+/8498 : c'est **OOM ou parallelism kill**, pas
un mismatch de toolchain. Voir §3 ci-dessous.

## 1. Pourquoi cette note existe

Le toolchain Lean 4 est officiellement portable Windows-native
(`elan install` produit un binaire `lean.exe` Windows). Pendant longtemps,
la pratique officieuse du cluster CoursIA a été de **basculer en WSL pour
les `lake build`**, sous l'hypothèse que la traversée Mathlib (~8500 modules
à compiler depuis zéro) était instable en Windows natif.

L'investigation **c.9713-bis** (refutée par **C9714-L1**) avait conclu
« WSL seul viable pour Mathlib », basée sur l'observation que
`git worktree add` côté WSL ne lisait pas le `.git` file pointant vers
`D:/Dev/...`. C'était un **problème de worktree-gitdir path translation**,
**pas** un problème de toolchain.

**C.9713-bis-L1 (90) — REFUTÉE** : la conclusion « Windows-native lake
build impossible sur ce worktree » était **trop pessimiste**. Le `.git`
file contenant `D:/Dev/CoursIA-...` est invisible à `git worktree` WSL,
mais le toolchain `lean.exe` Windows lit le `lean-toolchain` file
directement et résout `lake build` côté natif. Les deux opérations
(WSL git, Windows lake) peuvent coexister sur le même worktree.

## 2. Procédure validée (c.9714, machine `po-2023`)

### 2.1 Préparation

```bash
# Vérifier le toolchain actif
elan toolchain list
# Attendu : leanprover/lean4:v4.31.0-rc1 (active)

# Vérifier le binaire
ls "c:/Users/jsboi/.elan/toolchains/leanprover--lean4---v4.31.0-rc1/bin/lean.exe"
# Attendu : fichier présent

# Vérifier `lake` accessible
which lake
# Attendu : c:/Users/jsboi/.elan/toolchains/leanprover--lean4---v4.31.0-rc1/bin/lake
```

### 2.2 Build

```bash
cd <racine_lake>           # contient lakefile.toml + lean-toolchain
lake build                  # par défaut : LAKE_JOBS = nb CPUs
```

### 2.3 Variantes de parallelism (si build instable)

```bash
LAKE_JOBS=2 lake build     # parallèle modéré
LAKE_JOBS=1 lake build     # sérial — utile pour isoler un module fautif
```

### 2.4 Vérification de succès (CRITIQUE — voir §4)

```bash
ls .lake/build/lib/Conway/Life/HashlifeCorrectness.olean
# Attendu : fichier présent (artifact compilé)

# OU : recompile incrémental d'un fichier seul
lake env lean Conway/Life/HashlifeCorrectness.lean
# exit 0 si compile clean
```

## 3. Quand `lake build` SIGTERM-ise (`Lean exited 143`)

**Symptôme** : `lake build` atteint les modules Mathlib `[6000-8500/8498]`
puis s'arrête brutalement avec `Lean exited with code 143` (SIGTERM).
Plusieurs SIGTERMs à des modules différents = OOM ou kill par Windows
job-object (RAM peak > limite worker).

**Pas un mismatch toolchain.** Le toolchain fonctionne — ce sont les
ressources machines qui craquent. `UInt.ir` (souvent cité en erreur) existe
dans **les deux** toolchains `v4.31.0` et `v4.31.0-rc1`.

**Diagnostic** :

```bash
# Vérifier RAM dispo
free -h                                # sous WSL — PAS représentatif
wmic OS get FreePhysicalMemory,TotalVisibleMemorySize /VALUE   # Windows natif

# Vérifier le job object
Get-Process | Sort-Object WS -Descending | Select-Object -First 10  # PowerShell
```

**Remèdes** (par ordre de préférence) :

1. **`LAKE_JOBS=1` (série)** : élimine la pression mémoire parallèle.
   Temps de build ~2-3× plus long, mais passe sur les machines 16-32 GB.
2. **`LAKE_JOBS=2`** : compromis si la machine a 32 GB+.
3. **Machines 16 GB ou moins** : envisager `LAKE_JOBS=1` **ET** laisser
   le build **rouler la nuit** ; ne pas saturer la RAM avec d'autres
   processus pendant le build.
4. **CI Linux** (`lean-conway.yml` sur PR-land) : c'est le **gate canonique**.
   Le build local Windows-native sert de pré-flight worker — s'il
   échoue par OOM, ne pas **régénérer une PR de fix**, juste laisser
   la CI Linux trancher (les runners CI ont 64 GB+).

## 4. Le `TaskOutput` exit 0 ≠ Lake build SUCCESS (C9714-L4 ★★)

**Piège** (incident fondateur c.9714) : un build Lake lancé en
background (`run_in_background: true`) peut produire un
`TaskOutput exit 0` **sans avoir effectivement écrit le `.olean` cible**.
Les SIGTERMs de Windows-native (§3) peuvent laisser le worker en
état « process exited cleanly but artifacts missing ».

**Règle absolue** : avant de déclarer « Lake build SUCCESS » sur
dashboard / MEMORY / body PR, **vérifier l'artifact** :

```bash
test -f .lake/build/lib/<Module_path>/<file>.olean && echo "ARTIFACT_PRESENT" || echo "ARTIFACT_MISSING_BUILD_FAILED"
```

**Variante pour recompile single-file** :

```bash
lake env lean <file>.lean 2>&1 | tail -5
# exit 0 + zéro warning `declaration uses 'sorry'` non-attendu = SUCCESS
```

Sans cette vérification, un `exit 0` apparent peut masquer un Lake
qui n'a jamais atteint la phase de compilation du fichier cible.

## 5. Anti-patterns à NE PAS faire

- **NE PAS** déduire « toolchain mismatch » d'un SIGTERM en milieu de
  Mathlib. C'est OOM/parallelism, pas un bug Lean.
- **NE PAS** brûler 2-3 cycles à essayer `v4.31.0` (sans `-rc1`) comme
  « fix ». `UInt.ir` est présent dans les deux toolchains ; la cause
  est ailleurs.
- **NE PAS** déclarer « Lake build SUCCESS » sur la foi d'un
  `TaskOutput exit 0` seul (§4).
- **NE PAS** régénérer un clean Mathlib build à chaque cycle. Le
  `.lake/build/` est **persistent** entre les `lake build` (sauf
  `lake clean`). La traversée initiale (cold) est coûteuse (~30 min
  sur 16 cores), les incréments suivants sont rapides.

## 6. Quand utiliser WSL quand même

WSL reste utile pour **git worktree operations** sur des worktrees
multi-OS (un `.git` file Windows n'est pas lisible par git WSL —
incident fondateur c.9713-bis). En pratique :

| Opération | Windows natif | WSL | Note |
|---|---|---|---|
| `lake build` | ✅ (recommandé) | ✅ (si toolchain WSL) | Préférer Windows natif si dispo |
| `lake env lean <file>.lean` | ✅ | ✅ | Plus rapide que full build |
| `git worktree add <path> WSL-style` | ✅ (Windows paths) | ❌ (lit `.git` file mais ne le suit pas correctement) | WSL `git worktree add` sur worktree Windows = OK si on lit juste l'arbre, KO si on manipule le `.git` file |
| Lean prover (BG iters) | ✅ | ✅ | Indifférent |
| Proof-integrity CI | N/A | N/A | CI Linux = gate canonique |

## 7. Cross-references

- **PR #9840** (jsboige, lane `myia-ai-01:CoursIA`, OPEN MERGEABLE) :
  preuve complète des murs SW+SE via restatement fenêtré — utilise
  ce toolchain pour la validation Lake firsthand.
- **PR #9833** (lane `myia-po-2023:CoursIA-2`, OPEN avec `[COORD HOLD]`
  par ai-01) : tentait un verdict INTRINSIC sur les murs SW+SE,
  contredit par #9840 — le contenu UNBLOCK de cette note est extrait
  ici, le reste du PR est mis en attente.
- **EPIC #6724** : `Conway/Life/HashlifeCorrectness` murs quadrants.
- **C9714-L1 ★★** (91) : cette note est l'ancrage durable de la leçon
  (originellement dans le body de PR #9833 d2ba4dd45, maintenant
  promu en doc pérenne `docs/`).
- **C9714-L3 ★★** (91) : `Lean exited 143` = OOM/parallelism kill.
- **C9714-L4 ★★** (91) : BG `TaskOutput` exit 0 ≠ Lake build SUCCESS.
- **C9713-bis-L1 ★★** (90) : WSL↔Windows worktree-gitdir path
  translation — REFUTÉE pour le toolchain, conserve sa valeur pour
  les opérations `git worktree` multi-OS.

## 8. Voir aussi

- [`ab-methodology.md`](ab-methodology.md) — méthodologie
  abductive pour itérer sur les preuves.
- [`prover_iteration_history.md`](prover_iteration_history.md) —
  historique des cycles du prover BG.
- [`coordinator-workflow.md`](coordinator-workflow.md) — workflow
  coordinateur (merge gate, lake build).
- [`../../CLAUDE.md` §F](../../CLAUDE.md) — règle env/kernel :
  réparer, jamais contourner.
