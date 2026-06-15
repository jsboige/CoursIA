# Grothendieck Tribute — Mathlib Tour

Alexandre Grothendieck (1928-2014).

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

The formalization spans **23 modules (Parts 1-23, 3182 lines, 0 sorry)**, imported
in order by the umbrella `Grothendieck.lean`. Each module self-numbers via its header
(`Grothendieck tribute — Part N`).

| Part | File | Content | Lines |
|------|------|---------|-------|
| 1 | `Grothendieck/CategoryAndSites.lean` | Sieves, Grothendieck topologies (trivial/discrete/dense), three axioms | 106 |
| 2 | `Grothendieck/SchemesTour.lean` | Scheme type, Spec functor, Γ, `homeoOfIso`, fully-faithful | 79 |
| 3 | `Grothendieck/ZariskiSite.lean` | Zariski pretopology, `zariskiTopology_eq` bridge theorem, subcanonical | 84 |
| 4 | `Grothendieck/MathlibMap.lean` | `#check` index of Grothendieck-related Mathlib definitions | 90 |
| 5 | `Grothendieck/Calibration.lean` | 4 micro-proof targets for the prover harness (Epic #1453) | 80 |
| 6 | `Grothendieck/SieveLattice.lean` | Sieve pullback identities: `pullback_id`, `pullback_pullback`, `pullback_bot`, `pullback_monotone` | 88 |
| 7 | `Grothendieck/SheafBasics.lean` | Sheaf/separated presheaf basics, sheaf transfer along J₁ ≤ J₂ | 128 |
| 8 | `Grothendieck/SieveOps.lean` | Topology ordering, covering closure, sieve composition | 124 |
| 9 | `Grothendieck/CoverageGen.lean` | Coverage-to-topology, sheaf characterization, sup of coverages | 148 |
| 10 | `Grothendieck/CanonicalProps.lean` | Canonical topology, subcanonicity, representable sheaves | 133 |
| 11 | `Grothendieck/SieveGenerate.lean` | Sieve generation identities | 128 |
| 12 | `Grothendieck/DenseTopology.lean` | The dense topology | 131 |
| 13 | `Grothendieck/Sheafification.lean` | Sheafification (the associated sheaf functor) | 175 |
| 14 | `Grothendieck/LeftExact.lean` | Left exactness of sheafification | 133 |
| 15 | `Grothendieck/SitePoints.lean` | Points of a site (fiber functors) | 220 |
| 16 | `Grothendieck/Subcanonical.lean` | Subcanonical Grothendieck topologies | 88 |
| 17 | `Grothendieck/SheafHom.lean` | Internal hom of sheaves | 140 |
| 18 | `Grothendieck/ConstantSheaf.lean` | The constant sheaf functor (bridges Mathlib `CategoryTheory.Sites.ConstantSheaf`) | 185 |
| 19 | `Grothendieck/Conservative.lean` | Conservative families of points | 226 |
| 20 | `Grothendieck/SheafCohomology/Basic.lean` | Sheaf cohomology (Ext-based) | 214 |
| 21 | `Grothendieck/MayerVietorisSquare.lean` | Mayer-Vietoris squares | 195 |
| 22 | `Grothendieck/SheafCohomology/MayerVietoris.lean` | Mayer-Vietoris long exact sequence | 164 |
| 23 | `Grothendieck/SheafCohomology/Cech.lean` | Čech cohomology | 123 |

The extension (Parts 6-23) was developed under Issue #2159 / Epic #1646 and is
**complete**: all 23 modules merged, 0 `sorry`, 0 axiom added.

## Build

```bash
# From this directory (WSL required)
lake build Grothendieck
# Builds all 23 modules (3182 lines)
```

## Sorry count

**0 sorry, 0 axiom** — all 23 modules are complete at creation (Parts 1-23 merged).

## Toolchain

Aligned with other SymbolicAI/Lean projects: `leanprover/lean4:v4.30.0-rc2`

## See also

- Epic #1646 (Grothendieck tribute)
- Issue #2159 (Grothendieck formalization depth)
- PR #2675 (Phases 4-6: SieveOps + CoverageGen + CanonicalProps)
- Epic #1453 (prover harness calibration)
- Conway tribute workspace (`../conway_lean/`)
- Lean notebook series (`../README.md`)
