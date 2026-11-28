# gkdim_lean — Dimension de Gelfand-Kirillov

Lake Lean 4.33 / Mathlib 4.33 (pin `db584cd`, même ancrage que les lacs voisins de
l'îlot Grothendieck) portant le **premier jalon formel** du parcours sur la dimension
de Gelfand-Kirillov : les deux bornes de croissance qui caractérisent un exposant, et
la croissance exactement linéaire de l'anneau polynomial à une variable.

Ce lac **ne formalise pas** le théorème du trou de Smoktunowicz. La bibliothèque de
maths de Lean ne sait pas encore définir la dimension de Gelfand-Kirillov, ni graduer
un anneau par `N`, ni localiser d'Ore : le lac se place **en deçà** de cette
frontière, et le dit dans le carnet qui l'accompagne.

## Modules

| Module | Contenu | Twin EN |
|---|---|---|
| `GKdim/Core.lean` | fonction de Hilbert de `K[X]`, bornes `growthAtMost` / `growthAtLeast`, lemmes de croissance linéaire | `Core_en.lean` |

Les racines `GKdim.lean` et `GKdim_en.lean` sont les agrégateurs FR et EN
(convention i18n EPIC #4980) : la racine FR n'importe **que** le module FR, les
siblings `_en` restant découverts par les
`globs := #[.submodules \`GKdim, \`GKdim, \`GKdim_en]` du `lakefile.lean`.

## Déclarations

| Déclaration | Énoncé |
|---|---|
| `hilbert_poly1` | fonction de Hilbert de `K[X]` : `n + 1` monômes de degré au plus `n` |
| `hilbert_poly1_space_equiv` | l'espace `K[X]_{< n + 1}` est `K`-isomorphe à `Fin (n+1) → K` (identification de Mathlib) |
| `hilbert_poly1_eq_finrank` | `hilbert_poly1 n` est le rang fini de `K[X]_{< n + 1}` — le lien formel entre la suite et l'espace qu'elle mesure |
| `growthAtMost G d` | ∃ `C`, `n₀` : `G n ≤ C * n ^ d` pour tout `n ≥ n₀` |
| `growthAtLeast G d` | ∃ `c > 0`, `n₀` : `G n ≥ c * n ^ d` pour tout `n ≥ n₀` |
| `poly1_growthAtMost` | la croissance de `K[X]` est majorée par un multiple de `n` |
| `poly1_growthAtLeast` | la croissance de `K[X]` est minorée par `n` |
| `poly1_gkdim_is_one` | les deux bornes réunies : la croissance est exactement linéaire, donc `GKdim K[X] = 1` |

## Carnets

- [GROTH-07 — la capacité et le trou de Smoktunowicz](../GROTH-07-Capacity-Python.ipynb)
  (kernel Python 3) : la narration, la mesure de l'exposant, les exclusions successives,
  et le modèle fini de la capacité.
- [GROTH-07b — compagnon natif](../GROTH-07-Capacity-Lean.ipynb)
  (kernel `lean4-wsl`) : les mêmes énoncés compilés, `#print axioms` et `#eval` in-kernel.

## Build

```bash
lake build   # depuis ce dossier (lean-toolchain v4.33.0)
```

## CI

Ce lac est servi par la matrice `lean-ci-matrix.yml` (entrée `gkdim` de
`scripts/lean/ci_lakes.json`) : build (baseline `sorry = 0`, mode `real`) et gate
`proof-integrity` (`fail-on-sorry: true`, `target-modules: "*"`). Aucun `sorry`, aucun
`native_decide.*`. Les **trois lemmes de croissance** sont des consequences
d'arithmétique sur les naturels (`omega`) : leurs certificats `#print axioms` se
réduisent à `propext` et `Quot.sound`, sans `Classical.choice`. Les **deux declarations
de lien** (`hilbert_poly1_space_equiv`, `hilbert_poly1_eq_finrank`) mobilisent en
revanche `Classical.choice` — c'est inherent : `Module.finrank` est `noncomputable`.
`Classical.choice` fait partie de l'allow-list par defaut de la porte d'axiomes, la
gate reste donc verte ; le carnet `GROTH-07-Capacity-Lean.ipynb` ne cite que les trois
lemmes de croissance, dont les certificats restent inchanges.

## Conventions

- Docstrings **françaises** par défaut, jumeau `_en` **byte-identique hors commentaires**
  ([lean-i18n.md](../../../../../.claude/rules/lean-i18n.md)).
- `lakefile.lean` + `lake-manifest.json` (épinglé) + `lean-toolchain` : les trois fichiers
  sont **committés**, `.lake/` est ignoré.
- `globs := #[.submodules \`GKdim, \`GKdim, \`GKdim_en]` : `.submodules` couvre les
  sous-modules (FR **et** siblings `_en`), les deux racines (FR et EN) sont globbees
  explicitement — la forme bare ne matche que les sous-modules.
