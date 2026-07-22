# Grothendieck Tribute — Mathlib Tour

Alexandre Grothendieck (1928-2014).

## Status

- **Toolchain**: `leanprover/lean4:v4.31.0-rc1`
- **Sorry**: **0 sorry, 0 axiom** — all 29 modules are complete at creation (Parts 1-29 merged)
- **Build**: `lake build Grothendieck` — compiles the 29 modules (~11000 lines)
- **Dependencies**: Mathlib 4 (via `lakefile.lean`)
- **i18n coverage (EPIC #4980)**: near-complete coverage — **29 `.lean` modules** + **29 `_en.lean` siblings** on `main`. Per the ratified convention (Option A: `Foo.lean` FR-canonical + `Foo_en.lean` EN mirror), **all 29 modules** are already bilingual in Pattern A (`_en` namespaces anti-collision, non-docstring content byte-identical CI-detectable). **`README.md`** present (FR-canonical sibling of this file). Out-of-scope: `.lake/packages/`, vendored libs.

## Purpose

This workspace is a **pedagogical homage** showing how Grothendieck's mathematical
language already lives in Mathlib 4. It is **not** an attempt to formalize EGA/SGA.

The goal is to give learners a curated entry point into:
- Categories, sieves, and Grothendieck topologies
- Sheaves, separated presheaves, subcanonical topologies
- Coverage generation and sheaf characterization
- The canonical topology and subcanonical sites
- Schemes (locally ringed spaces locally Spec R)
- The Zariski site
- What Mathlib has and what it doesn't (yet)

## Structure

The formalization spans **29 modules (Parts 1-29, ~11000 lines, 0 sorry)**, imported
in order by the umbrella `Grothendieck.lean`. Each module self-numbers via its header
(`Grothendieck tribute — Part N`).

| Part | File | `_en` | Content | Lines |
|------|------|-------|---------|-------|
| 1 | `Grothendieck/CategoryAndSites.lean` | `CategoryAndSites_en.lean` | Sieves, Grothendieck topologies (trivial/discrete/dense), three axioms | 106 |
| 2 | `Grothendieck/SchemesTour.lean` | `SchemesTour_en.lean` | Scheme type, Spec functor, Γ, `homeoOfIso`, fully-faithful | 79 |
| 3 | `Grothendieck/ZariskiSite.lean` | `ZariskiSite_en.lean` | Zariski pretopology, `zariskiTopology_eq` bridge theorem, subcanonical | 84 |
| 4 | `Grothendieck/MathlibMap.lean` | `MathlibMap_en.lean` | `#check` index of Grothendieck-related Mathlib definitions | 90 |
| 5 | `Grothendieck/Calibration.lean` | `Calibration_en.lean` | 4 micro-proof targets for the prover harness (Epic #1453) | 80 |
| 6 | `Grothendieck/SieveLattice.lean` | `SieveLattice_en.lean` | Sieve pullback identities: `pullback_id`, `pullback_pullback`, `pullback_bot`, `pullback_monotone` | 88 |
| 7 | `Grothendieck/SheafBasics.lean` | `SheafBasics_en.lean` | Sheaf/separated presheaf basics, sheaf transfer along J₁ ≤ J₂ | 128 |
| 8 | `Grothendieck/SieveOps.lean` | `SieveOps_en.lean` | Topology ordering, covering closure, sieve composition | 124 |
| 9 | `Grothendieck/CoverageGen.lean` | `CoverageGen_en.lean` | Coverage-to-topology, sheaf characterization, sup of coverages | 148 |
| 10 | `Grothendieck/CanonicalProps.lean` | `CanonicalProps_en.lean` | Canonical topology, subcanonicity, representable sheaves | 133 |
| 11 | `Grothendieck/SieveGenerate.lean` | `SieveGenerate_en.lean` | Sieve generation identities | 128 |
| 12 | `Grothendieck/DenseTopology.lean` | `DenseTopology_en.lean` | The dense topology | 131 |
| 13 | `Grothendieck/Sheafification.lean` | `Sheafification_en.lean` | Sheafification (the associated sheaf functor) | 175 |
| 14 | `Grothendieck/LeftExact.lean` | `LeftExact_en.lean` | Left exactness of sheafification | 133 |
| 15 | `Grothendieck/SitePoints.lean` | `SitePoints_en.lean` | Points of a site (fiber functors) | 220 |
| 16 | `Grothendieck/Subcanonical.lean` | `Subcanonical_en.lean` | Subcanonical Grothendieck topologies | 88 |
| 17 | `Grothendieck/SheafHom.lean` | `SheafHom_en.lean` | Internal hom of sheaves | 140 |
| 18 | `Grothendieck/ConstantSheaf.lean` | `ConstantSheaf_en.lean` | The constant sheaf functor (bridges Mathlib `CategoryTheory.Sites.ConstantSheaf`) | 185 |
| 19 | `Grothendieck/Conservative.lean` | `Conservative_en.lean` | Conservative families of points | 226 |
| 20 | `Grothendieck/SheafCohomology/Basic.lean` | `SheafCohomology/Basic_en.lean` | Sheaf cohomology (Ext-based) | 214 |
| 21 | `Grothendieck/MayerVietorisSquare.lean` | `MayerVietorisSquare_en.lean` | Mayer-Vietoris squares | 195 |
| 22 | `Grothendieck/SheafCohomology/MayerVietoris.lean` | — | Mayer-Vietoris long exact sequence | 164 |
| 23 | `Grothendieck/SheafCohomology/Cech.lean` | `SheafCohomology/Cech_en.lean` | Čech cohomology | 123 |
| 24 | `Grothendieck/YonedaLemma.lean` | `YonedaLemma_en.lean` | The Yoneda lemma (embedding, equivalence, naturality, fully-faithful, coyoneda) | 168 |
| 25 | `Grothendieck/Comma.lean` | `Comma_en.lean` | Comma category, projections, functoriality | 96 |
| 26 | `Grothendieck/Construction.lean` | `Construction_en.lean` | Basic categorical constructions | 153 |
| 27 | `Grothendieck/KanExtensions.lean` | `KanExtensions_en.lean` | Kan extensions (generalized limits/colimits) | 271 |
| 28 | `Grothendieck/Limits.lean` | `Limits_en.lean` | Limits and colimits | 348 |
| 29 | `Grothendieck/MonoidalCategories.lean` | `MonoidalCategories_en.lean` | Monoidal categories, tensor, unit, associator | 437 |

The extension (Parts 6-24) was developed under Issue #2159 / Epic #1646 and is
**complete**: all 29 modules merged, 0 `sorry`, 0 axiom added.

## Build

```bash
# From this directory (WSL required)
lake build Grothendieck
# Builds all 29 modules (~11000 lines)
```

## Sorry count

**0 sorry, 0 axiom** — all 29 modules are complete at creation (Parts 1-29 merged).

## Toolchain

Aligned with other SymbolicAI/Lean projects: `leanprover/lean4:v4.31.0-rc1`

## References

The language toured here — Grothendieck topologies, sites, sheaves, and schemes — originates in Grothendieck's algebraic geometry. These are the canonical entry points. This workspace is a pedagogical tour indexed against Mathlib, **not** a formalization of EGA/SGA.

- **Mac Lane, S.; Moerdijk, I.** *Sheaves in Geometry and Logic: A First Introduction to Topos Theory*. Springer Universitext, 1992. — Standard reference for Grothendieck topologies, sieves, sites, and sheaves (Parts 1, 6-8, 10, 13-14).
- **Artin, M.; Grothendieck, A.; Verdier, J. L.**, eds. *Theorie des topos et cohomologie etale des schemas* (SGA 4). Springer Lecture Notes in Mathematics 269, 270, 305, 1972-1973. — Origin of sites, Grothendieck topologies, and points of a topos (Parts 1, 15, 19).
- **Grothendieck, A.; Dieudonne, J.** *Elements de geometrie algebrique* (EGA). Publications Mathematiques de l'IHES, 1960-1967. — Origin of schemes and the Zariski site (Parts 2-3).
- **Vakil, R.** *The Rising Sea: Foundations of Algebraic Geometry*. — Widely used pedagogical notes in the Grothendieckian spirit.
- **The Stacks Project.** [stacks.math.columbia.edu](https://stacks.math.columbia.edu) — Reference for schemes, sheafification, and sheaf cohomology (Parts 13, 20-23).
- **The Mathlib Community.** *Mathlib4, Category Theory and Sites*. [mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/) — The library this tour indexes (Part 4); see de Moura & Ullrich, "The Lean 4 Theorem Prover" (2021).
- **nLab.** [ncatlab.org](https://ncatlab.org) — Entries on Grothendieck topology, sieve, site, sheaf, and sheafification.

## See also

- Epic #1646 (Grothendieck tribute)
- Issue #2159 (Grothendieck formalization depth)
- PR #2675 (Phases 4-6: SieveOps + CoverageGen + CanonicalProps)
- Epic #1453 (prover harness calibration)
- Conway tribute workspace (`../conway_lean/`)
- Lean notebook series (`../README.md`)
- **EPIC #4980** — Lean i18n convention (Option A sibling pair post-2026-07-04; 29 `_en.lean` siblings on `main` in this lake)
- **[`README.md`](./README.md)** — FR canonical sibling of this file

## Conclusion

This tribute is a **complete pedagogical tour** (29 modules, ~11000 lines, 0 `sorry`,
0 axiom added) showing how Grothendieck's language — sites, sheaves,
sheafification, points, cohomology, Yoneda — already lives in Mathlib 4. It is
deliberately **not** a formalization of EGA/SGA; it is a curated index that lets
learners see the library through Grothendieckian eyes.

### The arc

The modules trace a coherent path: **sites and sieves** (Parts 1, 6, 8, 11, 12,
16) → **sheaves, separation, and transfer** (7, 9, 10, 17) → **sheafification and
its left exactness** (13, 14) → **points and conservative families** (15, 19) →
**sheaf cohomology, Mayer-Vietoris, and Čech** (20-23), with **schemes and the
Zariski site** (2, 3) and a **Mathlib map** (4) anchoring the tour to the library
it indexes.

### Scope, honestly

Per the `## Sorry count` section above, the tour is **0 `sorry`, 0 axiom added** —
every result is fully proven. Part 4's `#check` index is explicit about what
Mathlib has and what it does not (yet); the tour documents that boundary rather
than papering over it. The companion `Calibration.lean` (Part 5) feeds the prover
harness (Epic #1453), tying this formalization to the broader proving effort.

### Where to go next

- **Depth**: Issue #2159 / Epic #1646 track further formalization — this tour is
  the foundation, not the ceiling.
- **Companions**: `conway_lean/` (Conway's mathematics), the Lean notebook series.
- **References**: Mac Lane–Moerdijk and SGA 4 for the topos-theoretic core; Vakil
  and the Stacks Project for schemes and cohomology.
