# Hommage à Grothendieck — Visite de Mathlib

Alexandre Grothendieck (1928-2014).

## État

- **Toolchain** : `leanprover/lean4:v4.31.0-rc1`
- **Sorry** : **0 sorry, 0 axiome** — les 43 modules leaf sont complets à la création
- **Build** : `lake build Grothendieck` — compile 43 modules leaf + 1 umbrella bilingue (re-audité 2026-08-16)
- **Dépendances** : Mathlib 4 (via `lakefile.lean`)
- **Couverture i18n (EPIC #4980 ratifiée 2026-07-04)** : couverture bilingue FR/EN complète — **44 fichiers FR** (1 umbrella `Grothendieck.lean` bilingue inline FR+EN + **43 modules leaf** FR canonique, dont `ExceptionalDirect.lean` Partie 34 ajouté via #10357 le 2026-08-11 et les Parties 35-43 via les vagues Phase 5 de #2159 le 2026-08-14..16) + **43 siblings `_en.lean`** sur `main` (les 43 modules leaf uniquement ; l'umbrella est bilingue inline). Conformément à la convention ratifiée (Option A : `Foo.lean` FR canonique + `Foo_en.lean` miroir EN pour les leafs), **tous les 43 modules leaf** sont déjà bilingues au pattern A (namespaces `_en` anti-collision, contenu non-docstring byte-identique détectable par CI). L'umbrella `Grothendieck.lean` est bilingue inline (FR canonique d'abord, EN en miroir, cf doctring final du fichier) — c'est *by design*, pas un gap i18n. **`README.en.md`** présent (miroir EN du présent fichier). Hors-scope : `.lake/packages/`, libs vendored.

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

La formalisation couvre **43 modules leaf (0 sorry)** + **3 sous-modules
SheafCohomology/** (Basic + MayerVietoris + Cech, déjà comptés dans la Partie
20-22), importés dans l'ordre par le parapluie `Grothendieck.lean` (qui est
lui-même bilingue inline FR/EN, pas de sibling `_en` pour l'umbrella). La Partie
34 (`ExceptionalDirect.lean`) a été ajoutée par **PR #10357 (MERGED 2026-08-11)** —
extension Phase 2 de l'Epic #2159 qui formalise l'image directe exceptionnelle
`f_!` au niveau préfaisceau et son adjonction `f_! ⊣ f^*` (extension de Kan
à gauche de `f^*` le long de `f`). Les **Parties 35-43** (formes flèche et
bundlée de la couverture, lois du foncteur pullback et de l'ordre/treillis des
topologies — CoversArrow, Cover, PullbackFunctor, PullbackFunctorLaws,
TopologyLattice, CoversPullback, CoversOrder, PullbackCoversLaws, CoversLattice)
ont été ajoutées par les vagues **Phase 5 de l'Epic #2159** (mergées
2026-08-14..16).

*La trajectoire pédagogique des 43 modules leaf — des sites et cribles jusqu'à la cohomologie, avec schémas/Zariski et carte Mathlib en ancrage :*

```mermaid
flowchart LR
    T1["<b>Sites & cribles</b><br/><i>Parties 1·6·8·11·12·16</i><br/>topologies de Grothendieck<br/>pullback_id · pullback_monotone"]
    T2["<b>Faisceaux & séparation</b><br/><i>7·9·10·17</i><br/>préfaisceau séparé<br/>transfert le long de J₁ ≤ J₂"]
    T3["<b>Faisceautisation</b><br/><i>13·14</i><br/>foncteur faisceau associé<br/>exactitude à gauche (LeftExact)"]
    T4["<b>Points & conservateurs</b><br/><i>15·19</i><br/>foncteurs fibres<br/>familles conservatrices"]
    T5["<b>Cohomologie</b><br/><i>20·21·22·23</i><br/>Ext · Mayer-Vietoris · Čech"]
    T1 --> T2 --> T3 --> T4 --> T5
    S["<b>Schémas & site de Zariski</b><br/><i>Parties 2·3</i><br/>foncteur Spec<br/>zariski_topology_eq"] -.->|"ancre géométrique"| T1
    MM["<b>Carte Mathlib</b><br/><i>Partie 4</i><br/>index #check"] -.->|"ancre bibliothèque"| T3
```

| Partie | Fichier | `_en` | Contenu | Lignes |
|--------|---------|-------|---------|--------|
| racine | `Grothendieck.lean` | (bilingue inline) | **Racine umbrella** (imports-only des 43 leaf + doctring bilingue FR/EN) ; pas de sibling `_en` (le contenu EN vit dans le même fichier en miroir) | 217 |
| 1 | `Grothendieck/CategoryAndSites.lean` | `CategoryAndSites_en.lean` | Cribles, topologies de Grothendieck (triviale/discrète/dense), trois axiomes | 243 |
| 2 | `Grothendieck/SchemesTour.lean` | `SchemesTour_en.lean` | Type des schémas, foncteur Spec, Γ, `homeoOfIso`, pleinement fidèle | 196 |
| 3 | `Grothendieck/ZariskiSite.lean` | `ZariskiSite_en.lean` | Prétopologie de Zariski, théorème-pont `zariskiTopology_eq`, sous-canonique | 139 |
| 4 | `Grothendieck/MathlibMap.lean` | `MathlibMap_en.lean` | Index `#check` des définitions Mathlib liées à Grothendieck | 124 |
| 5 | `Grothendieck/Calibration.lean` | `Calibration_en.lean` | 4 cibles de micro-preuve pour le harnais du prouveur (Epic #1453) | 95 |
| 6 | `Grothendieck/SieveLattice.lean` | `SieveLattice_en.lean` | Identités de pullback de cribles (7) : `pullback_id`, `pullback_pullback`, `pullback_bot`, `pullback_monotone`, `pullback_union` (#7895), `pullback_ofObjects`, `mem_iff_pullback_eq_top` | 253 |
| 7 | `Grothendieck/SheafBasics.lean` | `SheafBasics_en.lean` | Bases faisceau/préfaisceau séparé, transfert de faisceau le long de J₁ ≤ J₂ | 231 |
| 8 | `Grothendieck/SieveOps.lean` | `SieveOps_en.lean` | Ordre sur les topologies, clôture de recouvrement, composition de cribles | 208 |
| 9 | `Grothendieck/CoverageGen.lean` | `CoverageGen_en.lean` | Coverage-vers-topologie, caractérisation des faisceaux, sup de coverages | 233 |
| 10 | `Grothendieck/CanonicalProps.lean` | `CanonicalProps_en.lean` | Topologie canonique, sous-canoïcité, faisceaux représentables | 155 |
| 11 | `Grothendieck/SieveGenerate.lean` | `SieveGenerate_en.lean` | Identités de génération de cribles | 243 |
| 12 | `Grothendieck/DenseTopology.lean` | `DenseTopology_en.lean` | La topologie dense | 218 |
| 13 | `Grothendieck/Sheafification.lean` | `Sheafification_en.lean` | Faisceautisation (le foncteur faisceau associé) | 259 |
| 14 | `Grothendieck/LeftExact.lean` | `LeftExact_en.lean` | Exactitude à gauche de la faisceautisation | 219 |
| 15 | `Grothendieck/SitePoints.lean` | `SitePoints_en.lean` | Points d'un site (foncteurs fibres) | 411 |
| 16 | `Grothendieck/Subcanonical.lean` | `Subcanonical_en.lean` | Topologies de Grothendieck sous-canoniques | 232 |
| 17 | `Grothendieck/SheafHom.lean` | `SheafHom_en.lean` | Hom interne des faisceaux | 273 |
| 18 | `Grothendieck/ConstantSheaf.lean` | `ConstantSheaf_en.lean` | Le foncteur faisceau constant (ponte vers `CategoryTheory.Sites.ConstantSheaf` de Mathlib) | 252 |
| 19 | `Grothendieck/Conservative.lean` | `Conservative_en.lean` | Familles conservatrices de points | 501 |
| 20 | `Grothendieck/SheafCohomology/Basic.lean` | `SheafCohomology/Basic_en.lean` | Cohomologie des faisceaux (basée sur Ext) | 336 |
| 21 | `Grothendieck/MayerVietorisSquare.lean` | `MayerVietorisSquare_en.lean` | Carrés de Mayer-Vietoris | 338 |
| 22 | `Grothendieck/SheafCohomology/MayerVietoris.lean` | `SheafCohomology/MayerVietoris_en.lean` | Suite exacte longue de Mayer-Vietoris | 235 |
| 23 | `Grothendieck/SheafCohomology/Cech.lean` | `SheafCohomology/Cech_en.lean` | Cohomologie de Čech | 203 |
| 24 | `Grothendieck/YonedaLemma.lean` | `YonedaLemma_en.lean` | Le lemme de Yoneda (plongement, équivalence, naturalité, pleinement fidèle, coyoneda) | 275 |
| 25 | `Grothendieck/Adjunction.lean` | `Adjunction_en.lean` | Adjonction de foncteurs, unité/co-unit, lemme de la tortue (turtle), adjoints à droite/gauche | 335 |
| 26 | `Grothendieck/Monads.lean` | `Monads_en.lean` | Monades en théorie des catégories, unité, multiplication, loi d'association | 253 |
| 27 | `Grothendieck/Comma.lean` | `Comma_en.lean` | Catégorie comma, projections, fonctorialité | 239 |
| 28 | `Grothendieck/Limits.lean` | `Limits_en.lean` | Limites et colimites | 421 |
| 29 | `Grothendieck/Equivalences.lean` | `Equivalences_en.lean` | Équivalences de catégories, foncteurs pleinement fidèles, essentiellement surjectifs | 338 |
| 30 | `Grothendieck/Construction.lean` | `Construction_en.lean` | Constructions catégorielles de base | 256 |
| 31 | `Grothendieck/KanExtensions.lean` | `KanExtensions_en.lean` | Extensions de Kan (limites/colimites généralisées) | 481 |
| 32 | `Grothendieck/MonoidalCategories.lean` | `MonoidalCategories_en.lean` | Catégories monoïdales, tenseur, unité, associateur | 397 |
| 33 | `Grothendieck/DirectImage.lean` | `DirectImage_en.lean` | Index `#check` (8) de l'adjonction `f^* ⊣ f_*` — image directe / réciproque des faisceaux de modules (#8882) | 325 |
| 34 | `Grothendieck/ExceptionalDirect.lean` | `ExceptionalDirect_en.lean` | Image directe exceptionnelle `f_!` au niveau préfaisceau et son adjonction `f_! ⊣ f^*` — extension de Kan à gauche de `f^*` le long de `f` (#10357, Phase 2 de #2159) | 202 |
| 35 | `Grothendieck/CoversArrow.lean` | `CoversArrow_en.lean` | Forme flèche de la couverture : `covers_monotone`, `covers_union`, `covers_inf`, équivalence `covers_comp_iff` (#10879, Phase 5 de #2159) | 199 |
| 36 | `Grothendieck/Cover.lean` | `Cover_en.lean` | Couverture bundlée `J.Cover X` : coe-injective, lois pullback/top/inf, `bind_mem_iff`, condition de base (#10912, Phase 5 de #2159) | 284 |
| 37 | `Grothendieck/PullbackFunctor.lean` | `PullbackFunctor_en.lean` | Lois de cohérence du pseudofoncteur pullback sur `J.Cover` : `pullback_triple`, `pullbackComp_assoc`, unités gauche/droite (#11023, Phase 5 de #2159) | 149 |
| 38 | `Grothendieck/PullbackFunctorLaws.lean` | `PullbackFunctorLaws_en.lean` | Lois de foncteur du pullback : `pullback_functor_id`, `pullback_functor_comp(_assoc)`, `covers_pullback_comp` (#11035, Phase 5 de #2159) | 141 |
| 39 | `Grothendieck/TopologyLattice.lean` | `TopologyLattice_en.lean` | Lois de treillis des topologies de Grothendieck : `inf/sup_covering`, `sSup_covering`, `le_covers` (#11038, Phase 5 de #2159) | 211 |
| 40 | `Grothendieck/CoversPullback.lean` | `CoversPullback_en.lean` | Lois de la forme flèche sous pullback : `covers_pullback_comp`, `covers_bind`, `covers_iso_covering/cancel`, `covers_mono` (#11057, Phase 5 de #2159) | 202 |
| 41 | `Grothendieck/CoversOrder.lean` | `CoversOrder_en.lean` | Lois d'ordre de la forme flèche `J.Covers` : `covers_top/bot_iff`, `covers_inter_iff`, `covers_of_covering`, `covers_generate_sieve` (#11068, Phase 5 de #2159) | 164 |
| 42 | `Grothendieck/PullbackCoversLaws.lean` | `PullbackCoversLaws_en.lean` | Lois de la forme flèche sous pullback itéré : `covers_pullback_assoc`, `covers_pullback_id`, `covers_pullback_generate` (#11217, Phase 5 de #2159) | 160 |
| 43 | `Grothendieck/CoversLattice.lean` | `CoversLattice_en.lean` | Lois de treillis indexées de la forme flèche : `sInf/sSup_covering`, `sInf/sSup_covers` (#11231, Phase 5 de #2159) | 106 |

*La colonne `Lignes` compte le **fichier FR seul** ; le total FR+EN est le double approximatif.*

L'extension a été développée sous l'Issue #2159 / Epic #1646 : les **43 modules leaf**
sont mergés + 1 umbrella bilingue, 0 `sorry`, 0 axiome ajouté. **Phase 2** (Partie 34
`f_! ⊣ f^*`) livrée par PR #10357 (MERGED 2026-08-11) ; **Phase 5** (Parties 35-43,
formes flèche/bundlée de la couverture et lois du pullback) livrée par vagues
(2026-08-14..16 : #10879, #10912, #11023, #11035, #11038, #11057, #11068, #11217,
#11231) ; **Phase 1** (Parties 1-33) précédemment shippée par vagues de PRs
(#2675, #8882, etc.).

## Build

```bash
# Depuis ce répertoire (WSL requis)
lake build Grothendieck
# Compile les 43 modules leaf + 1 umbrella bilingue
# Dernier build vérifié : 2026-08-12, « Build completed successfully » (compteurs re-audités 2026-08-16)
```

## Compte de sorry

**0 sorry, 0 axiome** — tous les 43 modules leaf sont complets à la création
(l'umbrella `Grothendieck.lean` est imports-only sans déclaration). La Partie 34
`ExceptionalDirect.lean` (#10357) cite `sorry` deux fois en prose docstring
(marque de la formalisation bornée) mais ne contient **aucun sorry tactic**.

## Toolchain

Alignée avec les autres projets SymbolicAI/Lean : `leanprover/lean4:v4.31.0-rc1`

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
- Issue #2159 (profondeur de formalisation Grothendieck — Phase 1 shippée, **Phase 2** livrée par #10357 le 2026-08-11 : `f_! ⊣ f^*` au niveau préfaisceau = Partie 34 `ExceptionalDirect.lean`)
- PR #2675 (Phases 4-6 : SieveOps + CoverageGen + CanonicalProps)
- **PR #10357** (Phase 2 #2159 : exceptional direct image `f_! ⊣ f^*` au niveau préfaisceau, formalisation bornée du chaînon manquant entre `f^*` et `f_*`)
- Epic #1453 (calibration du harnais prouveur)
- Workspace hommage Conway (`../conway_lean/`)
- **EPIC #4980** — convention i18n Lean (Option A sibling pair post-2026-07-04 ; 43 siblings `_en.lean` sur `main` dans cette lake + 1 umbrella bilingue inline)
- Issue #8960 (réconciliation des deux numérotations `Partie`)
- **[`README.en.md`](./README.en.md)** — miroir EN du présent fichier
- Série de notebooks Lean (`../README.md`)

## Conclusion

Cet hommage est une **visite pédagogique complète** (43 modules leaf + 1 umbrella bilingue, 0
`sorry`, 0 axiome ajouté) montrant comment le langage de Grothendieck — sites,
faisceaux, faisceautisation, points, cohomologie, Yoneda, images directes,
image directe exceptionnelle `f_!`, formes flèche/bundlée de la couverture — vit
déjà dans Mathlib 4. Ce n'est
délibérément **pas** une formalisation d'EGA/SGA ; c'est un index curaté
qui laisse les apprenants voir la bibliothèque à travers des yeux grothendieckiens.

### La trajectoire

Les modules tracent un chemin cohérent : **sites et cribles** (Parties 1, 6, 8,
11, 12, 16) → **faisceaux, séparation et transfert** (7, 9, 10, 17) →
**faisceautisation et son exactitude à gauche** (13, 14) → **points et familles
conservatrices** (15, 19) → **cohomologie des faisceaux, Mayer-Vietoris et Čech**
(20-23), avec **schémas et site de Zariski** (2, 3), une **carte Mathlib** (4)
et le **lemme de Yoneda** (24) ancrant la visite à la bibliothèque qu'elle indexe. Les bases catégorielles (Adjonction, Équivalences, Monades) aux Parties 25, 29, 26 soutiennent toute la formalisation. `DirectImage.lean` (Partie 33) indexe l'adjonction `f^* ⊣ f_*` — l'instance la plus simple des « six opérations », qui transporte les faisceaux le long des morphismes de schémas. `ExceptionalDirect.lean` (Partie 34, #10357) franchit un échelon en formalisant `f_! ⊣ f^*` au niveau préfaisceau — l'image directe *à support propre* comme extension de Kan à gauche de `f^*`, chaînon manquant entre `f^*` (inverse-image) et `f_*` (image directe). Les Parties 35-43 prolongent le versant *couverture* : formes flèche et bundlée de `J.Cover`, lois du foncteur pullback et de l'ordre/treillis des topologies (CoversArrow, Cover, PullbackFunctor, PullbackFunctorLaws, TopologyLattice, CoversPullback, CoversOrder, PullbackCoversLaws, CoversLattice, Phase 5 de #2159).

*La construction verticale « faisceau » — chaque couche bâtie sur la précédente, de la donnée du site jusqu'à la cohomologie :*

```mermaid
flowchart TD
    SITE["<b>Site</b><br/><i>catégorie + topologie de Grothendieck</i><br/>(Partie 1)"]
    PSH["<b>Préfaisceau</b><br/><i>objets Cᵒᵖ → Type*</i>"]
    SEP["<b>Préfaisceau séparé</b><br/>unicité du recollement"]
    SH["<b>Faisceau</b><br/>existence + unicité du recollement"]
    SHIF["<b>Faisceautisation</b><br/><i>foncteur faisceau associé</i><br/>Partie 13 — exactitude à gauche (Partie 14)"]
    COH["<b>Cohomologie des faisceaux</b><br/>Parties 20-23<br/>Ext · Mayer-Vietoris · Čech"]
    SITE --> PSH --> SEP --> SH
    SHIF -.->|"produit un faisceau<br/>depuis un préfaisceau"| SH
    SH --> COH
    TR["<b>Transfert de faisceau</b><br/>le long de J₁ ≤ J₂<br/>(Partie 7)"] -.-> SH
```

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
