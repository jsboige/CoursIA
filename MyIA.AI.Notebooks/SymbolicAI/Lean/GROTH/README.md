# Îlot GROTH — théorie des catégories et topos en Mathlib

Îlot de la série [SymbolicAI/Lean](../README.md) né de la carte cible de la série
([#17545](https://github.com/jsboige/CoursIA/issues/17545), phase 1) : les digestions EGA/SGA
de la racine supposaient catégories, foncteurs et adjonctions « jamais préparés ». L'îlot
accueille la **marche manquante** puis les descentes correspondantes.

| Carnet | Statut | Rôle |
|---|---|---|
| [GROTH-01-Categories-Mathlib-Lean.ipynb](GROTH-01-Categories-Mathlib-Lean.ipynb) | présent | La marche manquante : catégories, foncteurs, transformations naturelles et adjonctions **exécutés nativement** (kernel `lean4-wsl`), depuis une catégorie à deux objets construite à la main jusqu'aux énoncés du lake `grothendieck_lean` |
| [GROTH-02-Tribut-Python.ipynb](GROTH-02-Tribut-Python.ipynb) | présent | Hommage à Alexandre Grothendieck : le langage grothendieckien dans Mathlib 4 (catégories/foncteurs, cribles et topologies, faisceaux, site de Zariski) — kernel Python 3 (extraits Mathlib via `subprocess` → WSL `lean`) - Epic #1646 |
| [GROTH-03-Atelier-Python.ipynb](GROTH-03-Atelier-Python.ipynb) | présent | Atelier pratique : cribles, topologies et faisceaux en exercices sur les sources du lake `grothendieck_lean` — kernel Python 3 (snippets via `subprocess` WSL) - Epic #1646 |
| [GROTH-04-Companion-Lean.ipynb](GROTH-04-Companion-Lean.ipynb) | présent | Companion formel natif : les modules du lake visités par leurs énoncés qui compilent (Yoneda, Čech, Mayer-Vietoris, Zariski), 0 sorry attesté par `#print axioms` — kernel `lean4-wsl` - Epic #11703 |
| [GROTH-05-MvPowerSeries-Lean.ipynb](GROTH-05-MvPowerSeries-Lean.ipynb) | présent | La seconde marche « à écrire dans tous les cas » de la carte : séries formelles multivariées `MvPowerSeries` **exécutées nativement** (kernel `lean4-wsl`, pur Mathlib au pin de `formal_groups_lean`) — lecture par coefficients, produit de Cauchy, idéal d'augmentation, substitution, inversion, et l'axiome d'identité d'une loi de groupe formel refermé — le vocabulaire que consomme [Lean-30](../Lean-30-FormalGroups-Native.ipynb) |

Les carnets Lean-15 / 15b / 15c sont descendus depuis la racine de la série en
GROTH-02 / 03 / 04 (tranche T3 de la carte, [#17545](https://github.com/jsboige/CoursIA/issues/17545)),
une fois la contrainte de séquençage (§8 : pas de renommage sous une PR vivante) levée
par la clôture des PRs [#21223](https://github.com/jsboige/CoursIA/pull/21223), [#21235](https://github.com/jsboige/CoursIA/pull/21235), [#21337](https://github.com/jsboige/CoursIA/pull/21337), [#21407](https://github.com/jsboige/CoursIA/pull/21407) et [#21413](https://github.com/jsboige/CoursIA/pull/21413).

Le companion complet du parcours (adjonctions, topologies, cribles) vit dans le lake
[`grothendieck_lean/`](grothendieck_lean/README.md) — modules `Grothendieck/CategoryAndSites.lean`
et `Grothendieck/Adjunction.lean`.
