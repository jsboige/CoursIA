# `differential_lean` — enveloppe de visite de `qinz1yang/differential-geometry`

Lake d'enveloppe de l'EPIC **#18205** (« origami » : géométrie différentielle en Lean —
conjecture de Poincaré et flot de Ricci). Pli 1, sub-grain 1.

## Ce que ce lake est — et ce qu'il n'est pas

Ce lake ne **recopie aucune source** de l'amont, ne **forke rien**, et n'ouvre **aucune PR**
chez l'amont : il déclare `qinz1yang/differential-geometry` comme **dépendance Lake**
épinglée sur un tag de release. C'est exactement la forme du précédent
[`GameTheory/social_choice_lean_peters/`](../../../GameTheory/SocialChoice/social_choice_lean_peters/)
(Peters, MIT), dont `lakefile.lean` et le fichier de visite sont repris.

| | |
|---|---|
| Dépôt amont | [`qinz1yang/differential-geometry`](https://github.com/qinz1yang/differential-geometry) |
| Tag épinglé | **`v0.1.3`** — commit `7a48598d35109aa99d1cc678e2724c213cdf4ff3` |
| Licence amont | **Apache-2.0** |
| `lean-toolchain` amont | `leanprover/lean4:v4.33.1` |
| Mathlib amont | `leanprover-community/mathlib4` @ `v4.33.1` |

## L'exception de toolchain, assumée

Ce lake reste en **Lean `v4.33.1`** alors que le parc CoursIA est en `v4.33.0`. C'est une
**exception documentée**, de même nature que celle de Peters : l'amont déclare lui-même
`leanprover/lean4:v4.33.1` dans son `lean-toolchain`, et un lake d'enveloppe qui ne suit pas
la toolchain de sa dépendance ne s'élabore pas. L'exception est portée par le fichier
`lean-toolchain` de ce répertoire, pas par une option de build.

## Ce que la visite mesure

`DifferentialTour.lean` (et son jumeau anglais `DifferentialTour_en.lean`, convention
i18n #4980) importe trois modules de l'amont et demande au noyau Lean, par `#print
axioms`, la liste des axiomes dont dépend un théorème-tête de chacune des trois **petites
fermetures** citées par l'EPIC :

| Fermeture | Module importé | Théorème-tête |
|---|---|---|
| Lemme de Morse | `DifferentialGeometry.Topology.Morse.ExtremumChart` | `exists_quadratic_chart_of_isLocalMin` |
| Cohomologie de de Rham | `DifferentialGeometry.Tensor.Exterior.Cochain` | `pullbackCohomologyMap_id` |
| Bonnet–Myers | `DifferentialGeometry.Geometry.Comparison.BonnetMyers.Diameter` | `bonnet_myers_diameter_le_of_complete_metric` |

La sortie de `#print axioms` est le **témoin** : l'amont annonce n'utiliser que `propext`,
`Classical.choice` et `Quot.sound`. Ce lake **mesure** cette annonce sur trois points
d'entrée ; il ne la reprend pas sur parole, et il ne réécrit aucune preuve.

## Construire

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean
lake update                 # récupère l'amont épinglé et Mathlib v4.33.1
lake exe cache get          # oleans Mathlib précompilés
lake build                  # élabore DifferentialTour + DifferentialTour_en
```

`lake build` n'est **pas** branché sur la CI du dépôt : la fermeture de Poincaré dépasse le
budget des jobs Lean (cf. #18100), et l'amont est compilé depuis ses sources par sa propre
CI. Le build est donc un **geste de visite reproductible**, exécuté hors CI et journalisé
dans la PR.

## Mesures relevées

<!-- MESURES:START -->
Exécutées le **2026-10-07** sur `myia-po-2025`, **hors CI**, sur cette branche. Mathlib
v4.33.1 était déjà présent dans le cache de la machine (`lake exe cache get` ne
télécharge rien) — le temps de la visite est donc celui de l'élaboration, pas d'un
téléchargement.

| Étape | rc | Temps | Pic RSS `lean.exe` |
|---|---:|---:|---:|
| `lake update` | 0 | 491 s | — |
| `lake exe cache get` | 0 | 33 s | — |
| `lake build DifferentialGeometry.Tensor.Exterior.Cochain` | 0 | 285 s | — |
| `lake build DifferentialGeometry.Topology.Morse.ExtremumChart` | 0 | 215 s | 2 805 Mo |
| `lake build …Geometry.Comparison.BonnetMyers.Diameter` | 0 | **1 859 s** | 2 526 Mo |
| `lake build` (défaut : `DifferentialTour` + `_en`) | 0 | 70 s | 1 854 Mo |

**Total ≈ 2 953 s (49 min)** pour la visite complète ; le build des trois fermetures à
lui seul ≈ 2 359 s (39 min), **dominé par Bonnet–Myers** (détail des fermetures dans
la table ci-dessous).

### Fermetures d'imports (modules `DifferentialGeometry.*`, Mathlib exclu)

| Fermeture | Modules | Lignes |
|---|---:|---:|
| `Tensor/Exterior/Cochain` (de Rham) | 33 | 13 432 |
| `Topology/Morse/ExtremumChart` (Morse) | 47 | 23 522 |
| `Geometry/Comparison/BonnetMyers/Diameter` | 383 | 181 252 |

### Le témoin `#print axioms`

Les trois théorèmes-têtes, interrogés **dans les deux siblings**, ne dépendent que de
**`propext`, `Classical.choice`, `Quot.sound`** — aucun `sorryAx`, aucun `native_decide.*` :

```text
info: DifferentialTour.lean:31:0: '…Topology.Morse.exists_quadratic_chart_of_isLocalMin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: DifferentialTour.lean:34:0: '…DifferentialForm.pullbackCohomologyMap_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: DifferentialTour.lean:37:0: '…Riemannian.BonnetMyers.bonnet_myers_diameter_le_of_complete_metric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

L'annonce de l'amont est donc **mesurée sur trois points d'entrée**, pas reprise sur parole.
<!-- MESURES:END -->

## Voir aussi

- [#18205](https://github.com/jsboige/CoursIA/issues/18205) — EPIC origami géométrie différentielle
- [`docs/lean/origami-reconnaissance.md`](../../../../docs/lean/origami-reconnaissance.md) —
  Pli 1, sub-grains 3 (sources tierces) et 4 (emplacement), livrés par #18978
- [`social_choice_lean_peters/`](../../../GameTheory/SocialChoice/social_choice_lean_peters/) — précédent
  de la forme « enveloppe par dépendance, jamais par copie »
