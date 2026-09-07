# formal_groups_lean — Groupes formels multivariés

Lake Lean 4.33 / Mathlib 4.33 (pin `db584cd`, ancrage #14773) portant la
théorie des **groupes formels multivariés** : structure `MvFormalGroup`,
commutativité, morphismes (identité, composition, changement de base), loi
additive de référence, et itérés de la loi (partie linéaire, hauteur finie).

Provenance : port de `Definitions/Def_MvFormalGroup_BasicV2.lean` du dépôt
[anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem)
(Apache-2.0, commit `aa2d8b34`) — voir `NOTICE.md`. Énoncés et preuves sont
repris de l'amont ; le découpage en modules progressifs et les docstrings
FR/EN sont l'apport CoursIA (issue #14785, sur-grain de #14771).

## Modules

| Module | Contenu | Twin EN |
|---|---|---|
| `FormalGroups/Basic.lean` | structure `MvFormalGroup` (neutre, partie linéaire, associativité), `IsComm`, substituabilité | `Basic_en.lean` |
| `FormalGroups/Hom.lean` | morphismes `Hom`, `Hom.id`, `Hom.comp`, `End`, changement d'anneau `map` | `Hom_en.lean` |
| `FormalGroups/Additive.lean` | la loi additive `addMv` + instance `IsComm` + exemples bornés | `Additive_en.lean` |
| `FormalGroups/Iterates.lean` | itérés `nthSeries`, partie linéaire `linearPart`, hauteur finie `FiniteHeight` | `Iterates_en.lean` |

Hors scope (cf. #14785) : vecteurs de Witt, théorème de Cartier,
Artin–Hasse, applications arithmétiques avancées.

## Build

```bash
lake build   # depuis ce dossier (lean-toolchain v4.33.0)
```

## CI

Workflow `lean-formal-groups.yml` (dispatcher fin vers les workflows
réutilisables, même forme que `hecke_lean`) : build (baseline `sorry = 0`,
mode `real`) et gate `proof-integrity` (`fail-on-sorry: true`,
`target-modules: "*"`, axiomes interdits `native_decide.*`/`sorryAx`).
