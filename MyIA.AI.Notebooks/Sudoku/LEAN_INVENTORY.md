# Inventaire des projets Lean 4 — `Sudoku`

Inventaire transverse des projets de formalisation Lean 4 sous `Sudoku/`, sur le modèle de
[`GameTheory/LEAN_INVENTORY.md`](../GameTheory/LEAN_INVENTORY.md) et
[`SymbolicAI/Lean/LEAN_INVENTORY.md`](../SymbolicAI/Lean/LEAN_INVENTORY.md). Source de
vérité : corps de l'Epic
[#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification `firsthand`. Colonne
*Sorry (production)* = métrique CI `real` (commentaires strippés, `\bsorry\b`, fichiers FR
hors `_en` ; bascule #11688 — historiquement `standalone-tactic` ; les mentions prose
« 0 sorry » n'entrent pas dans ce compte).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `sudoku_lean` | v4.32.1 | 0 | 4 | 1¹ | PEDA/REF | #4055, #4038 |
| **Total** | — | **0** | **4** | **1** | — | — |

¹ Notebook câblé : **Sudoku-19-Lean-Propagation.ipynb** (propagation des règles en
cellules Lean). Companion conceptuel = le notebook **Sudoku-1** (résolution
par contraintes .NET C# — convention sibling-lake).

---

## Par lake

### sudoku_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : **cohérence (soundness) des règles de propagation** du Sudoku — naked single
et hidden single. Premier lake Lean de la série Sudoku (roadmap #4038 Tier 3, #4055). Modèle
abstrait de contraintes (grille 9×9 = instance, pas un cas spécial).

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **lib** : `Sudoku` (`globs := #[.submodules \`Sudoku]`)
- **Modules** : `Sudoku/Basic.lean`, `Sudoku/Propagation.lean`, `Sudoku/ExactCover.lean` +
  umbrella `Sudoku.lean`
- **sorry (production)** : **0** (real-mode). CI verte sur main
  (`lean-sudoku.yml`, dernier run 2026-08-18).

#### Théorèmes prouvés (0 sorry)

- **`peer_excludes_value`** (keystone) : une cellule qui contient la valeur `v` exclut `v`
  de toutes ses pairs (même ligne/colonne/bloc).
- **`naked_single_sound`** : si une cellule n'a qu'un seul candidat possible, l'y placer
  préserve la validité de la grille.
- **`hidden_single_sound`** : si une valeur ne peut aller que dans une seule cellule d'une
  unité, l'y placer préserve la validité.
- **`ExactCover.lean`** (réduction Sudoku ⟺ couverture exacte, les deux sens) :
  `solution_imp_exact_cover` (une solution Sudoku est une couverture exacte de ses
  contraintes), `toSelection_fromSelection` + `fromSelection_mem`/`mem_fromSelection_iff`
  (sens retour : une couverture exacte sélectionne une solution),
  `toSelection_cell_unique`/`toSelection_scopeVal_unique` (unicité de la sélection).

#### Honnêteté du périmètre (G.3/G.9)

La **cohérence des règles de propagation** est prouvée 0 sorry (par `by_contra` + keystone
`peer_excludes_value`), et la **réduction à la couverture exacte** (historiquement OPEN)
est désormais **livrée dans les deux sens** (`ExactCover.lean`). Ce qui reste
**OPEN (non sorry-backed)**, documenté honnêtement :

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
- CI : `.github/workflows/lean-sudoku.yml` (`sorry-filter-mode: real`, baseline `"0"` ;
  bascule mode #11688).
