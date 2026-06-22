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

## Conclusion

This tribute is a **complete pedagogical tour** (23 modules, 3182 lines, 0 `sorry`,
0 axiom added) showing how Grothendieck's language — sites, sheaves,
sheafification, points, cohomology — already lives in Mathlib 4. It is
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
