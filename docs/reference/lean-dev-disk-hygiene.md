# Lean dev-machine disk hygiene

> REFERENCE — vivante — dernière révision 2026-11-11

Structural note (perennial). Source: #8924 cluster disk-hygiene grain, measured
2026-08-05 on `myia-po-2026`. Records the *normal* Lean disk footprint on a dev
machine, the experiment-worktree accumulation pattern, and the safe-removal
protocol — so agents do not (a) chase a false "disk full" premise, (b) destroy
production build cache, or (c) remove another workspace's worktrees.

## The normal footprint (not waste)

A CoursIA dev machine carrying the Lean fleet legitimately holds **~34–51 GB of
`.lake` build cache**. This is the compiled Mathlib + per-lake olean set. It is:

- **Needed** for cycles — `lake build` on a warm cache is seconds/minutes; a cold
  rebuild is hours. Deleting `.lake` to "free space" trades disk for every
  downstream cycle.
- **Mutualized via junctions** (#4363): a central Mathlib clone is junctioned
  into each lake's `.lake/packages/mathlib`. The junction is **fragile** — a
  `lake build` on the wrong tree can wipe it (lesson
  `lake-build-shared-tree-mathlib-update-wipe.md`). Do NOT hand-edit `.lake`.
- **Lives in the main shared tree** (`c:\dev\CoursIA\...\<lake>\.lake`), not in
  worktrees. The worktrees themselves are small; the cache is central.

If a measurement says "C: is near full", the `.lake` cache is almost certainly
the largest line item — and it is the *wrong* target. Verify the premise before
acting (see "Measure first" below).

## Experiment-worktree accumulation

The genuinely reclaimable disk is **orphaned Lean experiment worktrees**, each of
which carries its own `.lake` build (5–13 GB). These accumulate across cycles
(`-nw` native-decide probes, P4 quadrant experiments, knot/axiom scratch). A
typical stale set on this machine:

```
CoursIA-c6724-c31-p4nw   13.0 GB   (Lean experiment, .lake build)
hashlife-l2536-nw          8.2 GB   (Lean experiment, .lake build)
CoursIA-c488-nw-lemma      7.7 GB   (Lean experiment, .lake build)
CoursIA-c710-hashlife-s3   5.3 GB   (Lean experiment, .lake build)
```

These are safe to remove **only** when all of: branch merged-or-abandoned,
`git status` clean, no unpushed commits, AND the worktree belongs to your
workspace (see below).

## Cross-workspace coexistence — NEVER remove another workspace's worktree

`c:\dev` holds **two** CoursIA clones side by side: `CoursIA` (this workspace)
and `CoursIA-2` (the sibling workspace). Each clone administers its own
worktrees, but the worktree *directories* all live under `c:\dev\CoursIA-*` and
are visually indistinguishable. **Ownership is determined by the worktree's
`.git` pointer**, not by directory name.

```bash
cat C:/dev/<worktree>/.git
# gitdir: C:/dev/CoursIA-2/.git/worktrees/<name>   → belongs to CoursIA-2, DO NOT TOUCH from CoursIA
# gitdir: C:/dev/CoursIA/.git/worktrees/<name>     → belongs to CoursIA, yours to manage
```

Removing another workspace's worktree violates "Stay in YOUR workspace"
(global CLAUDE.md) and #1502, and can destroy in-flight work the other lane has
not pushed. **Always read the `.git` pointer before removing any worktree.**

## Safe-removal protocol (4 gates, no `-f`)

A worktree may be removed only after all four gates pass:

1. **Ownership** — `.git` pointer resolves to YOUR clone (`CoursIA/.git`).
2. **No uncommitted work** — `git -C <wt> status --porcelain` is empty (`dirty=0`).
3. **No unpushed commits** — `git -C <wt> log --oneline origin/<branch>..HEAD` is
   empty. (If `<branch>` is not on `origin`, *all* its commits are local-only;
   `git worktree remove` still preserves the branch in `.git`, so commits are not
   lost — but confirm you intend to keep only the branch, not the checkout.)
4. **No force** — `git worktree remove <wt>` (never `-f`). The refusal under
   `-f`-less removal when dirty is the guardrail (lesson
   `worktree-triage-squash-merge-merged-pr-xref.md`).

Preserving the branch (default) honors "Consolider != Archiver": the work
survives in `.git` even after the checkout is gone. Remote branches are never
deleted by this protocol.

## Measure first (G.1)

Before any recovery, measure the actual disk state — prior reports go stale fast
(other machines recover, pruning frees space). 2026-08-05 baseline on this
machine:

```
C:  721.9 / 952.9 GB used  (75.8%)   ← "99%" reported elsewhere was stale
```

If your measurement contradicts the premise that sent you, **report the
measurement and follow it** rather than acting on the stale figure. The
acceptance criterion for a disk grain is: measure-before → recover-preserving →
measure-after → perennial-note (this file).

## Mutualisation Mathlib — la clé de groupe et la portée du scan

*(Section ajoutée en français, règle `readme-french-first` — le reste du fichier est en anglais.)*

`scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` groupe les lacs par **identité de
manifest**, pas par rev Mathlib : la clé est le `toolchain` plus la liste triée des
couples `(name, rev)` de **toutes** les dépendances transitives. Cette borne est
délibérée — un replay Lake exige l'identité du graphe de packages entier, pas
seulement celle de Mathlib (précondition durcie le 2026-06-10, commentée dans le
script). Des lacs qui partagent exactement `toolchain + rev Mathlib` restent donc
**isolés dès que leurs dépendances transitives diffèrent** : c'est le contrôle de
discrimination de l'instrument, pas un défaut de mesure.

Deux conséquences de portée, à vérifier avant d'interpréter un chiffre :

1. **Le scanner est worktree-local, pas machine-global.** Il lit les fichiers suivis
   de la racine courante, donc un checkout vivant dans un autre worktree lui est
   structurellement invisible. Un « 0 » obtenu depuis un worktree frais n'est pas une
   absence, c'est un **artefact de portée** : c'est ainsi qu'un scan a conclu à zéro
   économie sur un groupe entièrement mutualisable, alors que des jonctions NTFS
   vivantes existaient dans le worktree principal (mesure rejouée dans
   [`../lean/junctions-scan-po-2024.md`](../lean/junctions-scan-po-2024.md)).
2. **L'économie calculée n'est matérialisée que par les membres qui portent un
   checkout.** Le calcul d'économie agrège les tailles des `MathlibDir` des membres
   `HasCheckout` ; si aucun n'en a, la somme est vide et le gain vaut zéro — sans que
   cela dise quoi que ce soit du potentiel du groupe.

Un `Apply` réel exige donc trois prérequis, tous nécessaires : **(a)** au moins un
membre du groupe porte un checkout initial (le donneur) ; **(b)** les autres membres
sont configurés en jonctions vers ce donneur ; **(c)** les manifests de tous les
membres sont alignés — ce que le regroupement par identité de manifest garantit par
construction. L'alignement des manifests (#2611 étape 2) est la voie pour faire
entrer dans un groupe des lacs qui n'en partagent que la rev Mathlib ; ce n'est jamais
un raccourci vers un `Apply` bâclé.

Scan daté, composition du groupe et bornes du grain : rapport figé
[`2026-09-02-cluster-junctions-c857.md`](../transients/2026-09-02-cluster-junctions-c857.md).

## See also

- #4363 — Mathlib mutualization (central clone + per-lake junctions)
- #8924 — cluster disk-hygiene grain (source of this note)
- `lake-build-shared-tree-mathlib-update-wipe.md` (memory) — junction fragility
- `worktree-triage-squash-merge-merged-pr-xref.md` (memory) — no-`-f` guardrail
- [procedures-recurrentes.md](procedures-recurrentes.md) — "Consolider != Archiver"
