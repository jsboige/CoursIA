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
| `FormalGroups/Growth.lean` | lemmes de comptage de la dimension de Gelfand–Kirillov : `hilbertCumule`, `hilbertCouche`, `motsLibres`, sous-multiplicativité `sous_multiplicative_le_pow`, comparaison polynomiale / exponentielle `hilbertCumule_deux_lt_motsLibres_deux` (issue #27589) | `Growth_en.lean` |

Hors scope (cf. #14785) : vecteurs de Witt, théorème de Cartier,
Artin–Hasse, applications arithmétiques avancées.

`Growth.lean` est un ajout CoursIA hors du port Apache-2.0 : il tient les
faits de comptage que le carnet `GROTH-05b-GelfandKirillov-Python.ipynb`
mesure numériquement (croissance polynomiale `C(n+d, d)`, croissance
exponentielle `2^(n+1) - 1` de l'algèbre libre), et compare les deux : dès le
rang `2`, la fonction de Hilbert cumulée de `k[x, y]` passe sous le compte des
mots de l'algèbre libre `k⟨x, y⟩` (l'une ajoute une couche, l'autre double),
les deux comptes coïncidant aux rangs `0` et `1`. Il **ne définit pas** la
dimension de Gelfand–Kirillov elle-même — Mathlib ne la porte pas — et ne
prouve ni le théorème du trou de Smoktunowicz ni l'asymptotique
`log(dim A_n) / log n` : la frontière est dite dans la docstring du module.

## Build

```bash
lake build   # depuis ce dossier (lean-toolchain v4.33.0)
```

## CI

Ce lake est servi par la matrice `lean-ci-matrix.yml` (entrée
`formal_groups` de `scripts/lean/ci_lakes.json`, #13751) : build (baseline
`sorry = 0`, mode `real`) et gate `proof-integrity` (`fail-on-sorry: true`,
`target-modules: "*"`, axiomes interdits `native_decide.*`/`sorryAx`). Le
dispatcher dédié `lean-formal-groups.yml` a été retiré dans la même
migration — deux déclencheurs simultanés produiraient un double build.
