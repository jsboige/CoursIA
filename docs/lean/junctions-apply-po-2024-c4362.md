# Mathlib checkouts mutualisés — Apply po-2024 (CoursIA-2, c.4362)

Issue : [#4362](https://github.com/jsboige/CoursIA/issues/4362) — Lean : harmoniser Mathlib, mutualiser les checkouts, regrouper les lakes (anti-prolifération).
Scan préalable de cette lane : [junctions-scan-po-2024.md](junctions-scan-po-2024.md).

**Lane** : `myia-po-2024:CoursIA-2`.
**Date** : 2026-11-21.
**Périmètre** : machine MYIA-PO-2024 — (a) WSL Ubuntu `/home/jesse` (les workspaces de build manuels des lakes), (b) côté NTFS le clone principal `D:/Dev/CoursIA-2` (2 checkouts matérialisés). La CI self-hosted tourne dans son propre checkout et ne touche pas ces répertoires.
**Statut** : **Apply exécuté — 24 symlinks WSL + 2 junctions NTFS posés, 133,5 Go de checkouts dupliqués neutralisés** ; rollback intégral disponible dans `/home/jesse/.trash/mathlib-swap-20261121/` (WSL) et `D:/Dev/CoursIA-2/.tmp/trash/` (NTFS) ; purge différée (la poubelle n'est pas une purge).

## Topologie réelle mesurée avant Apply

Scan `setup_shared_mathlib_scan.py` (côté NTFS) + inventaire `find /home/jesse -name mathlib -path "*/.lake/packages/*"` (côté WSL) : **31 checkouts matérialisés en WSL** + **2 en NTFS**, groupés par rev :

| Rev Mathlib | Checkouts WSL | Taille cumulée | Traitement |
|---|---|---|---|
| `db584cd6` (v4.33.0, rev flotte) | 17 | ~112 Go | 1 donateur + 16 symlinks |
| `520045ab` (v4.32.1) | 8 | ~52 Go | 1 donateur + 7 symlinks |
| `0df444a3` (v4.33.1) | 2 | ~8,5 Go | 1 donateur + 1 symlink |
| autres revs (5e932f97, 5eec30bc, 81a5d257, c55e6e78) | 4 | ~28 Go | **exclus** — un membre par groupe, pas de duplication à tuer |

Côté NTFS : `calibration_lean` (checkout physique 1,04 Go, rev `db584cd6` conforme) et `mimo_lean` (checkout physique 0,51 Go, rev `81a5d257` **stale** vs manifest `db584cd6` — divergence de type kelly_lean documentée au fil de l'EPIC).

## Choix des donateurs (complétude mesurée, pas la taille)

| Groupe | Donateur | Preuve de complétude |
|---|---|---|
| `db584cd6` | `lean-projects/conway_lean` (13,1 Go) | git clean, rev exact, **8852 oleans**, `Mathlib.lean` présent |
| `520045ab` | `lakes/planning_lean` (11,1 Go) | git clean, rev exact, **8795 oleans**, `Mathlib.lean` présent |
| `0df444a3` | `ffl-foundation-pilot` (7,2 Go) | rev exact, **8852 oleans** |

Les victimes incluent des checkouts **partiels** (3,4–4,7 Go, clone interrompu) : les brancher sur le donateur complet les répare au passage — un checkout partiel ne peut servir aucun build complet.

## Garde pré-geste

- Aucun process `lake`/`lean` actif (garde par `comm` via `pgrep -x`, pas par arguments — leçon po-2028 n°2).
- mtimes des checkouts : tous antérieurs de ≥ 6 jours au geste (le plus récent : 2026-11-15) — **aucun acteur concurrent** en setup (leçon po-2028 n°3).
- Triple prédicat par victime avant mutation : `.lake/packages` n'est pas lui-même un lien · `mathlib` est un vrai répertoire · rev du checkout = rev du groupe (leçon po-2028 n°1). Aucun SKIP n'a déclenché : 24/24 victimes ont passé la garde.

## Apply exécuté

**WSL (24 symlinks)** — par victime : `mv <mathlib> /home/jesse/.trash/mathlib-swap-20261121/<projet>-mathlib/` puis `ln -s <donateur> <mathlib>`. Un seul lien `mathlib` par projet — jamais le `packages/` entier, dont les autres dépendances peuvent diverger.

- 16 symlinks → `lean-projects/conway_lean/.lake/packages/mathlib` (`db584cd6`) : knot_build_c615_194826, lean16650, coursia-builds/formal_groups_lean, sd-build, mle433, planning433, cal433, gtbuild, sc25262, erc20433, lakes/grothendieck_lean, lakes/social_choice_core_lean, knot_build_20261019_192638, knot_build_c615_192845, conway13483, conway17465.
- 7 symlinks → `lakes/planning_lean/.lake/packages/mathlib` (`520045ab`) : grbump, lakes/social_choice_lean_peters, knotbuild, kellybuild, aslbuild, gflow13106, lean-projects/learning_theory_lean.
- 1 symlink → `ffl-foundation-pilot/.lake/packages/mathlib` (`0df444a3`) : modallogic-17522.

**NTFS (2 junctions + 1 store)** — `D:/Dev/CoursIA-2/.mathlib-cache/leanprover_lean4_v4.33.0-db584cd6/` reçoit le checkout de `calibration_lean` (move, pas copie) ; `mimo_lean` est pointé sur le même store (son checkout stale `81a5d257` est parqué dans `.tmp/trash/mimo-mathlib-81a5d257-20261121/` — régénérable par `lake update`, la divergence manifest/checkout est levée).

## Vérification (post-mutation)

- **24/24 liens WSL** résolvent : `readlink -f` → donateur du groupe, `Mathlib.lean` accessible à travers chaque lien.
- **2/2 junctions NTFS** : reparse point présent, `Mathlib.lean` accessible, `git rev-parse HEAD` à travers la junction = `db584cd6d46c…` exact.
- **Build de contrôle** : `lake build Mathlib` dans `lakes/grothendieck_lean` — projet branché sur le donateur **par le nouveau symlink**, scope-bounded (`systemd-run --scope -p MemoryMax=18G`), lancé à l'apply. Résultat : **à ajouter au cycle suivant** (build complet Mathlib, cache froid du projet) — ce rapport est honnête sur ce point, il ne l'anticipe pas.
- **`distinct_code_sorry`** : structurellement inchangé — le geste ne touche que des checkouts de dépendance (gitignores), jamais une source du dépôt ; les revs de dépendance sont identiques avant/après par construction (garde du triple prédicat).

## Rollback et purge

- **Rollback** (un par victime) : `rm` du lien puis `mv /home/jesse/.trash/mathlib-swap-20261121/<projet>-mathlib <projet>/.lake/packages/mathlib`. NTFS : supprimer la junction (`rmdir`), restaurer par move inverse.
- **Purge différée** : poubelle WSL **133 Go** + NTFS 0,51 Go. Les copies sont prouvées redondantes (même rev, donateur complet), mais la purge reste un geste séparé et explicite.

## Économie réelle

| Poste | Valeur |
|---|---|
| Checkouts dupliqués neutralisés (en poubelle, récupérables) | **133,5 Go** (133 Go WSL + 0,51 Go NTFS) |
| Magasins restants | 3 donateurs WSL (1 par rev du groupe muté) + 1 store NTFS |
| Réparation au passage | 1 checkout stale (`mimo_lean` NTFS, `81a5d257` vs manifest `db584cd6`) + les checkouts partiels branchés sur un magasin complet |

**Rapprochement des tailles (point du CR 22/11).** La somme des tailles par groupe de la table « Topologie réelle » (~112 + ~52 + ~8,5 Go, moins les 3 donateurs conservés ~13,1 + ~11,1 + ~7,2 Go) donne ~141 Go de victimes estimées ; ces valeurs sont des **estimations arrondies** par groupe. La valeur faisant foi est la **mesure directe** de la poubelle après l'apply : `du -sh /home/jesse/.trash/mathlib-swap-20261121/` = **133 Go**. C'est cette mesure (133 Go WSL + 0,51 Go NTFS = 133,5 Go) qui est annoncée, pas la somme de la table.

## Leçons (pour les Apply suivants)

1. **Le scan NTFS seul sous-voit la machine** : le clone `D:/Dev/CoursIA-2` n'avait que 2 checkouts, le WSL en portait 31 — l'inventaire doit couvrir les deux côtés du paravirtuel avant de décider l'économie.
2. **`git rev-parse --short` ment par la longueur** : le même rev s'affiche `db584cd6d4` (10) dans un projet et `db584cd6d46` (11) dans un autre (désambiguïsation contextuelle) — grouper par short-10 a failli créer un faux groupe ; regrouper sur le rev complet.
3. **Le contrôle de complétude est `find -name '*.lean' | wc -l` + git clean + rev exact**, pas la taille : deux checkouts de 7,2 Go peuvent ne pas être équivalents (complet vs clone interrompu rattrapé).
