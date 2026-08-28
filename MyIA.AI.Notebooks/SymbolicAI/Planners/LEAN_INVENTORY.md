# Inventaire des projets Lean 4 — `SymbolicAI/Planners`

Inventaire transverse des projets de formalisation Lean 4 sous `SymbolicAI/Planners/`, sur
le modèle de [`GameTheory/LEAN_INVENTORY.md`](../../GameTheory/LEAN_INVENTORY.md) et
[`SymbolicAI/Lean/LEAN_INVENTORY.md`](../Lean/LEAN_INVENTORY.md). Source de vérité : corps
de l'Epic [#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification
`firsthand`. Colonne *Sorry (production)* = métrique CI `real` (commentaires strippés [ligne
`--` et bloc `/- -/`] puis `\bsorry\b` — les mentions prose « 0 sorry » n'entrent pas dans
ce compte ; cf. `lean-ci-sorry-filter`).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `planning_lean` | v4.32.1 | 0 | 3 | 1 | PEDA/REF | #4053, #4038 |
| **Total** | — | **0** | **3** | — | — | — |

¹ Notebook Lean câblé = `SymbolicAI/Planners/02-Classical/Planners-5b-Lean-Relaxation.ipynb`
(kernel `lean4-wsl`, importe `Planning.*`). Companion conceptuel = la série **Planners**.
Premier lake Lean de la série Planning (roadmap #4038 Tier 2, #4053) — admissibilité de la
relaxation sans-delete (h⁺).

---

## Par lake

### planning_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : **admissibilité de la relaxation sans-delete (h⁺)** en planification STRIPS —
le coût du plan relaxé optimal `h⁺` n'excède jamais le coût réel optimal `h*`. Justifie
formellement les heuristiques de relaxation `h_max`/`h_add`/`FF` (roadmap #4038 Tier 2,
#4053). Premier lake Lean de la série Planning.

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **lib** : `Planning` (`globs := #[.submodules \`Planning]`), package `planning_lean`
- **Modules** : `Planning/Strips.lean`, `Planning/Relaxation.lean`,
  `Planning/Admissibility.lean` (FR ; jumeaux `_en` exclus, i18n #4980)
- **sorry (production)** : **0** (métrique CI `real`, baseline `"0"`).

#### Théorèmes prouvés (0 sorry)

- **`relaxed_plan_admissible`** (flagship) : `h⁺ ≤ h*` — tout plan réel est un plan relaxé
  (la relaxation ignore les effets de delete, l'état relaxé ne fait que croître).
- **`relaxed_plan_witness`** : témoin du plan relaxé optimal.
- **`run_subset_runR`** / **`runR_mono`** : lemmas de support — inclusion et monotonie de la
  relation de transition relaxée.
- **`step_subset_stepR`** / **`step_mono`** : lemmas locaux sur l'étape relaxée.
- Définitions : `Action`, `applicable`, `goalSatisfied`, `reaches`, `reachesR`, `run`, `runR`.

#### Honnêteté du périmètre (G.3/G.9)

L'**admissibilité de `h⁺`** est prouvée 0 sorry. Ce qui reste **OPEN (non sorry-backed)**,
documenté honnêtement :

- **Complétude des heuristiques** `h_max`/`h_add`/`FF` : le lake prouve l'admissibilité de
  `h⁺`, pas leur complétude ni leur dominance mutuelle.
- **Extraction de plan** et **recherche arrière** (backward search) — non formalisées.

## Notes transverses

- **CI** : `.github/workflows/lean-planning.yml` (`project-path: …/planning_lean`,
  `sorry-filter-mode: real`, baseline `"0"`), caller de `lean-build.yml@main`. `real` =
  awk canonique (lean-build.yml) — rattrape `exact sorry`, `:= by sorry`, `<;> sorry`,
  `def f : T := sorry`, pas les mentions prose.
- **i18n (#4980)** : jumeaux `Planning/Strips_en.lean` etc. — les comptes sorries et le
  décompte de modules portent sur les fichiers FR.
