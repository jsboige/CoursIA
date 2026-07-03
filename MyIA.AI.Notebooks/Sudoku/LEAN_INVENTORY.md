# Inventaire des projets Lean 4 — `Sudoku`

Inventaire transverse des projets de formalisation Lean 4 sous `Sudoku/`, sur le modèle de
[`GameTheory/LEAN_INVENTORY.md`](../GameTheory/LEAN_INVENTORY.md) et
[`SymbolicAI/Lean/LEAN_INVENTORY.md`](../SymbolicAI/Lean/LEAN_INVENTORY.md). Source de
vérité : corps de l'Epic
[#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification `firsthand`. Colonne
*Sorry (production)* = métrique CI `standalone-tactic` (les mentions prose « 0 sorry »
n'entrent pas dans ce compte ; cf.
`lean-ci-sorry-filter`).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `sudoku_lean` | v4.31.0-rc1 | 0 | 3 | 0¹ | PEDA/REF | #4055, #4038 |
| **Total** | — | **0** | **3** | — | — | — |

¹ Aucun notebook Lean dédié. Companion conceptuel = le notebook **Sudoku-1** (résolution
par contraintes .NET C# — convention sibling-lake).

---

## Par lake

### sudoku_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : **cohérence (soundness) des règles de propagation** du Sudoku — naked single
et hidden single. Premier lake Lean de la série Sudoku (roadmap #4038 Tier 3, #4055). Modèle
abstrait de contraintes (grille 9×9 = instance, pas un cas spécial).

- **Toolchain** : v4.31.0-rc1 · **Dépendance** : Mathlib4
- **lib** : `Sudoku` (`globs := #[.submodules \`Sudoku]`)
- **Modules** : `Sudoku/Basic.lean`, `Sudoku/Propagation.lean` + umbrella `Sudoku.lean`
- **sorry (production)** : **0**. `lake build Sudoku` SUCCESS (8495 jobs, 0 error 0 warning).

#### Théorèmes prouvés (0 sorry)

- **`peer_excludes_value`** (keystone) : une cellule qui contient la valeur `v` exclut `v`
  de toutes ses pairs (même ligne/colonne/bloc).
- **`naked_single_sound`** : si une cellule n'a qu'un seul candidat possible, l'y placer
  préserve la validité de la grille.
- **`hidden_single_sound`** : si une valeur ne peut aller que dans une seule cellule d'une
  unité, l'y placer préserve la validité.

#### Honnêteté du périmètre (G.3/G.9)

La **cohérence des règles de propagation** est prouvée 0 sorry (par `by_contra` + keystone
`peer_excludes_value`). Ce qui reste **OPEN (non sorry-backed)**, documenté honnêtement :

- **Réduction au problème de couverture exacte** (exact cover, Knuth DLX) — la réduction
  Sudoku ⟺ couverture exacte.
- **Complétude de l'ensemble de règles** (les trois règles suffisent-elles à résoudre toute
  grille soluble ?).

Axiomes `[propext, Quot.sound]` (Mathlib standard, **pas de `Classical.choice`** — pur
Prop/Fintype ; **pas de `sorryAx`**).

## Notes transverses

- **Coordination #2978** : vérifié sans chevauchement avec la série finitude/derivatives
  (pas de conflit de symbols/namespaces).
- **WDAC workaround** (RECOVERABLE-LOCAL) : `lake exe cache get` bloqué → copie wholesale
  `cp -r sibling/.lake` + `lake-manifest.json` d'un lake frère compatible. Cf.
  `lean-wdac-olean-wholesale-copy`.
- CI : `.github/workflows/lean-sudoku.yml` (`sorry-filter-mode: standalone-tactic`,
  baseline `"0"`).
