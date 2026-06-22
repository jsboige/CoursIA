# Hommage à Grothendieck — Visite de Mathlib

Alexandre Grothendieck (1928-2014).

## Objectif

Ce workspace est un **hommage pédagogique** montrant comment le langage
mathématique de Grothendieck vit déjà dans Mathlib 4. Ce n'est **pas** une
tentative de formaliser EGA/SGA.

Le but est d'offrir aux apprenants un point d'entrée curaté vers :
- Catégories, cribles (sieves) et topologies de Grothendieck
- Faisceaux (sheaves), prefaisceaux séparés, topologies sous-canoniques
- Génération de recouvrements (coverage) et caractérisation des faisceaux
- La topologie canonique et les sites sous-canoniques
- Schémas (espaces annelés en anneaux locaux localement Spec R)
- Le site de Zariski
- Ce que Mathlib possède et ce qu'il n'a pas (encore)

## Structure

La formalisation couvre **23 modules (Parties 1-23, 3182 lignes, 0 sorry)**,
importés dans l'ordre par le parapluie `Grothendieck.lean`. Chaque module se
numérote lui-même via son en-tête (`Grothendieck tribute — Part N`).

| Partie | Fichier | Contenu | Lignes |
|--------|---------|---------|--------|
| 1 | `Grothendieck/CategoryAndSites.lean` | Cribles, topologies de Grothendieck (triviale/discrète/dense), trois axiomes | 106 |
| 2 | `Grothendieck/SchemesTour.lean` | Type des schémas, foncteur Spec, Γ, `homeoOfIso`, pleinement fidèle | 79 |
| 3 | `Grothendieck/ZariskiSite.lean` | Prétopologie de Zariski, théorème-pont `zariskiTopology_eq`, sous-canonique | 84 |
| 4 | `Grothendieck/MathlibMap.lean` | Index `#check` des définitions Mathlib liées à Grothendieck | 90 |
| 5 | `Grothendieck/Calibration.lean` | 4 cibles de micro-preuve pour le harnais du prouveur (Epic #1453) | 80 |
| 6 | `Grothendieck/SieveLattice.lean` | Identités de pullback de cribles : `pullback_id`, `pullback_pullback`, `pullback_bot`, `pullback_monotone` | 88 |
| 7 | `Grothendieck/SheafBasics.lean` | Bases faisceau/préfaisceau séparé, transfert de faisceau le long de J₁ ≤ J₂ | 128 |
| 8 | `Grothendieck/SieveOps.lean` | Ordre sur les topologies, clôture de recouvrement, composition de cribles | 124 |
| 9 | `Grothendieck/CoverageGen.lean` | Coverage-vers-topologie, caractérisation des faisceaux, sup de coverages | 148 |
| 10 | `Grothendieck/CanonicalProps.lean` | Topologie canonique, sous-canoïcité, faisceaux représentables | 133 |
| 11 | `Grothendieck/SieveGenerate.lean` | Identités de génération de cribles | 128 |
| 12 | `Grothendieck/DenseTopology.lean` | La topologie dense | 131 |
| 13 | `Grothendieck/Sheafification.lean` | Faisceautisation (le foncteur faisceau associé) | 175 |
| 14 | `Grothendieck/LeftExact.lean` | Exactitude à gauche de la faisceautisation | 133 |
| 15 | `Grothendieck/SitePoints.lean` | Points d'un site (foncteurs fibres) | 220 |
| 16 | `Grothendieck/Subcanonical.lean` | Topologies de Grothendieck sous-canoniques | 88 |
| 17 | `Grothendieck/SheafHom.lean` | Hom interne des faisceaux | 140 |
| 18 | `Grothendieck/ConstantSheaf.lean` | Le foncteur faisceau constant (ponte vers `CategoryTheory.Sites.ConstantSheaf` de Mathlib) | 185 |
| 19 | `Grothendieck/Conservative.lean` | Familles conservatrices de points | 226 |
| 20 | `Grothendieck/SheafCohomology/Basic.lean` | Cohomologie des faisceaux (basée sur Ext) | 214 |
| 21 | `Grothendieck/MayerVietorisSquare.lean` | Carrés de Mayer-Vietoris | 195 |
| 22 | `Grothendieck/SheafCohomology/MayerVietoris.lean` | Suite exacte longue de Mayer-Vietoris | 164 |
| 23 | `Grothendieck/SheafCohomology/Cech.lean` | Cohomologie de Čech | 123 |

L'extension (Parties 6-23) a été développée sous l'Issue #2159 / Epic #1646 et
est **complète** : tous les 23 modules mergés, 0 `sorry`, 0 axiome ajouté.

## Build

```bash
# Depuis ce répertoire (WSL requis)
lake build Grothendieck
# Compile les 23 modules (3182 lignes)
```

## Compte de sorry

**0 sorry, 0 axiome** — tous les 23 modules sont complets à la création
(Parties 1-23 mergées).

## Toolchain

Alignée avec les autres projets SymbolicAI/Lean : `leanprover/lean4:v4.30.0-rc2`

## References

The language toured here — Grothendieck topologies, sites, sheaves, and schemes — originates in Grothendieck's algebraic geometry. These are the canonical entry points. This workspace is a pedagogical tour indexed against Mathlib, **not** a formalization of EGA/SGA.

- **Mac Lane, S.; Moerdijk, I.** *Sheaves in Geometry and Logic: A First Introduction to Topos Theory*. Springer Universitext, 1992. — Standard reference for Grothendieck topologies, sieves, sites, and sheaves (Parts 1, 6-8, 10, 13-14).
- **Artin, M.; Grothendieck, A.; Verdier, J. L.**, eds. *Theorie des topos et cohomologie etale des schemas* (SGA 4). Springer Lecture Notes in Mathematics 269, 270, 305, 1972-1973. — Origin of sites, Grothendieck topologies, and points of a topos (Parts 1, 15, 19).
- **Grothendieck, A.; Dieudonne, J.** *Elements de geometrie algebrique* (EGA). Publications Mathematiques de l'IHES, 1960-1967. — Origin of schemes and the Zariski site (Parts 2-3).
- **Vakil, R.** *The Rising Sea: Foundations of Algebraic Geometry*. — Widely used pedagogical notes in the Grothendieckian spirit.
- **The Stacks Project.** [stacks.math.columbia.edu](https://stacks.math.columbia.edu) — Reference for schemes, sheafification, and sheaf cohomology (Parts 13, 20-23).
- **The Mathlib Community.** *Mathlib4, Category Theory and Sites*. [mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/) — The library this tour indexes (Part 4); see de Moura & Ullrich, "The Lean 4 Theorem Prover" (2021).
- **nLab.** [ncatlab.org](https://ncatlab.org) — Entries on Grothendieck topology, sieve, site, sheaf, and sheafification.

## Voir aussi

- Epic #1646 (hommage à Grothendieck)
- Issue #2159 (profondeur de formalisation Grothendieck)
- PR #2675 (Phases 4-6 : SieveOps + CoverageGen + CanonicalProps)
- Epic #1453 (calibration du harnais prouveur)
- Workspace hommage Conway (`../conway_lean/`)
- Série de notebooks Lean (`../README.md`)

## Conclusion

Cet hommage est une **visite pédagogique complète** (23 modules, 3182 lignes,
0 `sorry`, 0 axiome ajouté) montrant comment le langage de Grothendieck — sites,
faisceaux, faisceautisation, points, cohomologie — vit déjà dans Mathlib 4. Ce
n'est délibérément **pas** une formalisation d'EGA/SGA ; c'est un index curaté
qui laisse les apprenants voir la bibliothèque à travers des yeux grothendieckiens.

### La trajectoire

Les modules tracent un chemin cohérent : **sites et cribles** (Parties 1, 6, 8,
11, 12, 16) → **faisceaux, séparation et transfert** (7, 9, 10, 17) →
**faisceautisation et son exactitude à gauche** (13, 14) → **points et familles
conservatrices** (15, 19) → **cohomologie des faisceaux, Mayer-Vietoris et Čech**
(20-23), avec **schémas et site de Zariski** (2, 3) et une **carte Mathlib** (4)
ancrant la visite à la bibliothèque qu'elle indexe.

### Le périmètre, honnêtement

Selon la section `## Compte de sorry` ci-dessus, la visite est à **0 `sorry`,
0 axiome ajouté** — chaque résultat est pleinement prouvé. L'index `#check` de la
Partie 4 est explicite sur ce que Mathlib possède et ce qu'il n'a pas (encore) ;
la visite documente cette frontière au lieu de la maquiller. Le module compagnon
`Calibration.lean` (Partie 5) alimente le harnais du prouveur (Epic #1453),
reliant cette formalisation à l'effort de preuve plus large.

### Où aller ensuite

- **Profondeur** : l'Issue #2159 / l'Epic #1646 suivent la formalisation
  ultérieure — cette visite est le socle, pas le plafond.
- **Compagnons** : `conway_lean/` (mathématiques de Conway), la série de
  notebooks Lean.
- **Références** : Mac Lane–Moerdijk et SGA 4 pour le cœur topos-théorique ;
  Vakil et le Stacks Project pour les schémas et la cohomologie.
