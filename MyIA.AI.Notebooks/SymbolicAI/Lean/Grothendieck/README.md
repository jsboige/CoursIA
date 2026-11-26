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
| [GROTH-05-MvPowerSeries-Lean.ipynb](GROTH-05-MvPowerSeries-Lean.ipynb) | présent | La seconde marche « à écrire dans tous les cas » de la carte : séries formelles multivariées `MvPowerSeries` **exécutées nativement** (kernel `lean4-wsl`, pur Mathlib au pin de `formal_groups_lean`) — lecture par coefficients, produit de Cauchy, idéal d'augmentation, substitution, inversion, et l'axiome d'identité d'une loi de groupe formel refermé — le vocabulaire que consomme [GROTH-06](GROTH-06-FormalGroups-Lean.ipynb) |
| [GROTH-06-FormalGroups-Lean.ipynb](GROTH-06-FormalGroups-Lean.ipynb) | présent | Compagnon **natif** (kernel `lean4-wsl`) du lake [`formal_groups_lean`](formal_groups_lean/README.md) : les groupes formels multivariés à travers les modules `Basic`/`Hom`/`Additive`/`Iterates` — structure `MvFormalGroup`, morphismes et changement d'anneau, loi additive, itérés — `#check`/`#print axioms` in-kernel, 0 `sorry` |
| [GROTH-07-Capacity-Python.ipynb](GROTH-07-Capacity-Python.ipynb) | présent | **Capacité** : le mécanisme de la preuve formelle du trou de Smoktunowicz, modélisé sur un cas fini — l'exposant de croissance de la fonction de Hilbert (suite de Hilbert, pente log-log), les exclusions successives de l'intervalle ]1, 2[, puis le défaut de croissance `dim(S·U) - dim(U)` minimisé sur les sous-espaces plus grands, et sa monotonie vérifiée exhaustivement — kernel Python 3 - Epic #27589 |
| [GROTH-07-Capacity-Lean.ipynb](GROTH-07-Capacity-Lean.ipynb) | présent | Compagnon **natif** (kernel `lean4-wsl`) du lake [`gkdim_lean`](gkdim_lean/README.md) : les deux bornes de croissance (`growthAtMost` / `growthAtLeast`) qui caractérisent un exposant, et la croissance exactement linéaire de `K[X]`, donc une dimension de Gelfand-Kirillov égale à `1` — `#check`/`#print axioms` in-kernel, 0 `sorry` |

Les carnets Lean-15 / 15b / 15c sont descendus depuis la racine de la série en
GROTH-02 / 03 / 04 (tranche T3 de la carte, [#17545](https://github.com/jsboige/CoursIA/issues/17545)),
une fois la contrainte de séquençage (§8 : pas de renommage sous une PR vivante) levée
par la clôture des PRs [#21223](https://github.com/jsboige/CoursIA/pull/21223), [#21235](https://github.com/jsboige/CoursIA/pull/21235), [#21337](https://github.com/jsboige/CoursIA/pull/21337), [#21407](https://github.com/jsboige/CoursIA/pull/21407) et [#21413](https://github.com/jsboige/CoursIA/pull/21413).
Le carnet Lean-30 et son lake `formal_groups_lean` sont descendus en GROTH-06
(tranche T8-30 de la même carte), une fois la marche préparatoire GROTH-05 livrée.

Le companion complet du parcours (adjonctions, topologies, cribles) vit dans le lake
[`grothendieck_lean/`](grothendieck_lean/README.md) — modules `Grothendieck/CategoryAndSites.lean`
et `Grothendieck/Adjunction.lean`. Le lake [`formal_groups_lean/`](formal_groups_lean/README.md)
(port de `anthropics/fermats-last-theorem`, Apache-2.0) porte les groupes formels multivariés
consommés par GROTH-06. Le lake [`gkdim_lean/`](gkdim_lean/README.md) porte le premier jalon
formel de la dimension de Gelfand-Kirillov, consommé par GROTH-07.
