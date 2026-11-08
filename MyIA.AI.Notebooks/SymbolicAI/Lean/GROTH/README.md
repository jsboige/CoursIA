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
| [GROTH-05-MvPowerSeries-Lean.ipynb](GROTH-05-MvPowerSeries-Lean.ipynb) | présent | La seconde marche « à écrire dans tous les cas » de la carte : séries formelles multivariées `MvPowerSeries` **exécutées nativement** (kernel `lean4-wsl`, pur Mathlib au pin de `formal_groups_lean`) — lecture par coefficients, produit de Cauchy, idéal d'augmentation, substitution, inversion, et l'axiome d'identité d'une loi de groupe formel refermé — le vocabulaire que consomme [Lean-30](../Lean-30-FormalGroups-Native.ipynb) |

Les migrations 02-04 suivent la contrainte de séquençage de la carte (§8 : pas de
renommage sous une PR vivante) — les PRs [#21223](https://github.com/jsboige/CoursIA/pull/21223),
[#21235](https://github.com/jsboige/CoursIA/pull/21235), [#21337](https://github.com/jsboige/CoursIA/pull/21337),
[#21407](https://github.com/jsboige/CoursIA/pull/21407) et [#21413](https://github.com/jsboige/CoursIA/pull/21413)
touchent actuellement le lake ou les carnets concernés.

Le companion complet du parcours (adjonctions, topologies, cribles) vit dans le lake
[`grothendieck_lean/`](grothendieck_lean/README.md) — modules `Grothendieck/CategoryAndSites.lean`
et `Grothendieck/Adjunction.lean`.

## Deux repères de provenance Stacks

Ces lignes relient deux tags présents dans le code Axiom à des déclarations déjà
présentes dans le module GROTH sur les adjonctions. Elles documentent une
provenance déclarative ; elles ne prétendent pas établir une égalité formelle
entre les énoncés. La source Axiom est épinglée au commit
`5ed82d14634e8d9576bb844c7bd4e3da66d450e7` (lecture du 2026-11-08), fichier
[`StacksCore/CategoryTheory/AdjointFunctors.lean`](https://github.com/AxiomMath/Stacks/blob/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/StacksCore/CategoryTheory/AdjointFunctors.lean#L16).
Le petit extrait parseable est conservé dans
[`scripts/lean/fixtures/stacks_adjoint_tags_excerpt.txt`](../../../../scripts/lean/fixtures/stacks_adjoint_tags_excerpt.txt) ;
il provient du dépôt sous licence Apache-2.0
([texte de licence](https://github.com/AxiomMath/Stacks/blob/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/LICENSE)).

| Tag Stacks | Déclaration taguée chez Axiom | Déclaration GROTH existante | Portée du rapprochement |
|---|---|---|---|
| 0037 | [`Adjunction.mkOfHomEquiv`](https://github.com/AxiomMath/Stacks/blob/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/StacksCore/CategoryTheory/AdjointFunctors.lean#L16) | [`Grothendieck/Adjunction.lean`](grothendieck_lean/Grothendieck/Adjunction.lean) : `homEquiv_family` | Le commentaire Axiom décrit le constructeur à partir de l'isomorphisme Hom ; GROTH expose la famille des équivalences Hom portée par `Adjunction`. |
| 0039 | [`Adjunction.leftAdjoint_preservesColimits`](https://github.com/AxiomMath/Stacks/blob/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/StacksCore/CategoryTheory/AdjointFunctors.lean#L51) et [`Adjunction.rightAdjoint_preservesLimits`](https://github.com/AxiomMath/Stacks/blob/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/StacksCore/CategoryTheory/AdjointFunctors.lean#L53) | [`Grothendieck/Adjunction.lean`](grothendieck_lean/Grothendieck/Adjunction.lean) : `leftAdjoint_preserves_colimits` et `rightAdjoint_preserves_limits` | Axiom rattache ces déclarations au tag 0039 et précise les cas de préservation finie ; GROTH expose les formes générales de préservation. |

Le contrôle réutilise le parseur de déclarations Lean de
`scripts/lean/lean_material_map.py` et vérifie les deux témoins depuis ce README,
l'extrait amont et les fichiers réellement suivis dans le lake. Il ne lance aucun
build d'AxiomMath/Stacks et ne change pas le périmètre du lake GROTH.
