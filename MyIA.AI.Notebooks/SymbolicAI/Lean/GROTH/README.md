# Îlot GROTH — théorie des catégories et topos en Mathlib

Îlot de la série [SymbolicAI/Lean](../README.md) né de la carte cible de la série
([#17545](https://github.com/jsboige/CoursIA/issues/17545), phase 1) : les digestions EGA/SGA
de la racine supposaient catégories, foncteurs et adjonctions « jamais préparés ». L'îlot
accueille la **marche manquante** puis les descentes correspondantes.

| Carnet | Statut | Rôle |
|---|---|---|
| [GROTH-01-Categories-Mathlib-Lean.ipynb](GROTH-01-Categories-Mathlib-Lean.ipynb) | présent | La marche manquante : catégories, foncteurs, transformations naturelles et adjonctions **exécutés nativement** (kernel `lean4-wsl`), depuis une catégorie à deux objets construite à la main jusqu'aux énoncés du lake `grothendieck_lean` |
| GROTH-02 (tribut) | à venir | Migration du carnet d'hommage [Lean-15](../Lean-15-Grothendieck-Tribute.ipynb) — attend la clôture des PRs vivantes sur le lake |
| GROTH-03 (atelier) | à venir | Migration de l'atelier texte [Lean-15b](../Lean-15b-Lean-Grothendieck.ipynb) |
| GROTH-04 (companion) | à venir | Migration du companion [Lean-15c](../Lean-15c-Lean-Grothendieck-Companion.ipynb) |

Les migrations 02-04 suivent la contrainte de séquençage de la carte (§8 : pas de
renommage sous une PR vivante) — les PRs [#21223](https://github.com/jsboige/CoursIA/pull/21223),
[#21235](https://github.com/jsboige/CoursIA/pull/21235), [#21337](https://github.com/jsboige/CoursIA/pull/21337),
[#21407](https://github.com/jsboige/CoursIA/pull/21407) et [#21413](https://github.com/jsboige/CoursIA/pull/21413)
touchent actuellement le lake ou les carnets concernés.

Le companion complet du parcours (adjonctions, topologies, cribles) vit dans le lake
[`grothendieck_lean/`](../grothendieck_lean/README.md) — modules `Grothendieck/CategoryAndSites.lean`
et `Grothendieck/Adjunction.lean`.
