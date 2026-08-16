# Grothendieck Tribute — Mathlib Tour

Alexandre Grothendieck (1928-2014).

## Status

- **Toolchain**: `leanprover/lean4:v4.31.0-rc1`
- **Sorry**: **0 sorry, 0 axiom** — all 43 leaf modules are complete at creation
- **Build**: `lake build Grothendieck` — compiles the 43 leaf modules (20,988 FR+EN lines, + 217 for the umbrella = **21,205 total**, measured 2026-08-16)
- **Dependencies**: Mathlib 4 (via `lakefile.lean`)
- **i18n coverage (EPIC #4980, ratified 2026-07-04)**: complete bilingual FR/EN coverage — **44 FR files** (1 umbrella `Grothendieck.lean` bilingual inline FR+EN + **43 leaf modules** FR canonical, incl. Part 34 `ExceptionalDirect.lean` via #10357 on 2026-08-11 and Parts 35-43 via the Phase 5 waves of #2159 on 2026-08-14..16) + **43 `_en.lean` siblings** on `main` (leaf modules only; the umbrella is bilingual inline). Per the ratified convention (Option A: `Foo.lean` FR canonical + `Foo_en.lean` EN mirror for leaves), **all 43 leaf modules** are bilingual in Pattern A (`_en` namespaces anti-collision, non-docstring content byte-identical CI-detectable). The umbrella `Grothendieck.lean` is bilingual inline (FR canonical first, EN mirror, see final doctring in the file) — *by design*, not an i18n gap. **`README.md`** present (FR canonical sibling of this file). Out-of-scope: `.lake/packages/`, vendored libs.

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

The formalization spans **43 leaf modules (20,988 FR+EN lines, 0 sorry)**, imported
in order by the umbrella `Grothendieck.lean` (which is itself bilingual inline FR/EN; no `_en` sibling for the umbrella).

| Part | File | `_en` | Content | Lines |
|------|------|-------|---------|-------|
| root | `Grothendieck.lean` | (bilingual inline) | **Umbrella root** (imports-only of the 43 leaves + bilingual FR/EN doctring); no `_en` sibling (the EN content lives in the same file as a mirror) | 217 |
| 1 | `Grothendieck/CategoryAndSites.lean` | `CategoryAndSites_en.lean` | Sieves, Grothendieck topologies (trivial/discrete/dense), three axioms | 243 |
| 2 | `Grothendieck/SchemesTour.lean` | `SchemesTour_en.lean` | Scheme type, Spec functor, Γ, `homeoOfIso`, fully-faithful | 196 |
| 3 | `Grothendieck/ZariskiSite.lean` | `ZariskiSite_en.lean` | Zariski pretopology, `zariskiTopology_eq` bridge theorem, subcanonical | 139 |
| 4 | `Grothendieck/MathlibMap.lean` | `MathlibMap_en.lean` | `#check` index of Grothendieck-related Mathlib definitions | 124 |
| 5 | `Grothendieck/Calibration.lean` | `Calibration_en.lean` | 4 micro-proof targets for the prover harness (Epic #1453) | 95 |
| 6 | `Grothendieck/SieveLattice.lean` | `SieveLattice_en.lean` | Sieve pullback identities (7): `pullback_id`, `pullback_pullback`, `pullback_bot`, `pullback_monotone`, `pullback_union` (#7895), `pullback_ofObjects`, `mem_iff_pullback_eq_top` | 253 |
| 7 | `Grothendieck/SheafBasics.lean` | `SheafBasics_en.lean` | Sheaf/separated presheaf basics, sheaf transfer along J₁ ≤ J₂ | 231 |
| 8 | `Grothendieck/SieveOps.lean` | `SieveOps_en.lean` | Topology ordering, covering closure, sieve composition | 208 |
| 9 | `Grothendieck/CoverageGen.lean` | `CoverageGen_en.lean` | Coverage-to-topology, sheaf characterization, sup of coverages | 233 |
| 10 | `Grothendieck/CanonicalProps.lean` | `CanonicalProps_en.lean` | Canonical topology, subcanonicity, representable sheaves | 155 |
| 11 | `Grothendieck/SieveGenerate.lean` | `SieveGenerate_en.lean` | Sieve generation identities | 243 |
| 12 | `Grothendieck/DenseTopology.lean` | `DenseTopology_en.lean` | The dense topology | 218 |
| 13 | `Grothendieck/Sheafification.lean` | `Sheafification_en.lean` | Sheafification (the associated sheaf functor) | 259 |
| 14 | `Grothendieck/LeftExact.lean` | `LeftExact_en.lean` | Left exactness of sheafification | 219 |
| 15 | `Grothendieck/SitePoints.lean` | `SitePoints_en.lean` | Points of a site (fiber functors) | 411 |
| 16 | `Grothendieck/Subcanonical.lean` | `Subcanonical_en.lean` | Subcanonical Grothendieck topologies | 232 |
| 17 | `Grothendieck/SheafHom.lean` | `SheafHom_en.lean` | Internal hom of sheaves | 273 |
| 18 | `Grothendieck/ConstantSheaf.lean` | `ConstantSheaf_en.lean` | The constant sheaf functor (bridges Mathlib `CategoryTheory.Sites.ConstantSheaf`) | 252 |
| 19 | `Grothendieck/Conservative.lean` | `Conservative_en.lean` | Conservative families of points | 501 |
| 20 | `Grothendieck/SheafCohomology/Basic.lean` | `SheafCohomology/Basic_en.lean` | Sheaf cohomology (Ext-based) | 336 |
| 21 | `Grothendieck/MayerVietorisSquare.lean` | `MayerVietorisSquare_en.lean` | Mayer-Vietoris squares | 338 |
| 22 | `Grothendieck/SheafCohomology/MayerVietoris.lean` | `SheafCohomology/MayerVietoris_en.lean` | Mayer-Vietoris long exact sequence | 235 |
| 23 | `Grothendieck/SheafCohomology/Cech.lean` | `SheafCohomology/Cech_en.lean` | Čech cohomology | 203 |
| 24 | `Grothendieck/YonedaLemma.lean` | `YonedaLemma_en.lean` | The Yoneda lemma (embedding, equivalence, naturality, fully-faithful, coyoneda) | 275 |
| 25 | `Grothendieck/Adjunction.lean` | `Adjunction_en.lean` | Adjunction of functors, unit/counit, turtle lemma, left/right adjoints | 335 |
| 26 | `Grothendieck/Monads.lean` | `Monads_en.lean` | Monads in category theory, unit, multiplication, associativity law | 253 |
| 27 | `Grothendieck/Comma.lean` | `Comma_en.lean` | Comma category, projections, functoriality | 239 |
| 28 | `Grothendieck/Limits.lean` | `Limits_en.lean` | Limits and colimits | 421 |
| 29 | `Grothendieck/Equivalences.lean` | `Equivalences_en.lean` | Equivalences of categories, fully-faithful functors, essentially surjective | 338 |
| 30 | `Grothendieck/Construction.lean` | `Construction_en.lean` | Basic categorical constructions | 256 |
| 31 | `Grothendieck/KanExtensions.lean` | `KanExtensions_en.lean` | Kan extensions (generalized limits/colimits) | 481 |
| 32 | `Grothendieck/MonoidalCategories.lean` | `MonoidalCategories_en.lean` | Monoidal categories, tensor, unit, associator | 397 |
| 33 | `Grothendieck/DirectImage.lean` | `DirectImage_en.lean` | `#check` index (8) of the `f^* ⊣ f_*` adjunction — direct/inverse image of module sheaves (#8882) | 325 |
| 34 | `Grothendieck/ExceptionalDirect.lean` | `ExceptionalDirect_en.lean` | Exceptional direct image `f_!` at the presheaf level and its adjunction `f_! ⊣ f^*` — left Kan extension of `f^*` along `f` (#10357, Phase 2 of #2159) | 202 |
| 35 | `Grothendieck/CoversArrow.lean` | `CoversArrow_en.lean` | Arrow form of the covering: `covers_monotone`, `covers_union`, `covers_inf`, `covers_comp_iff` equivalence (#10879, Phase 5 of #2159) | 199 |
| 36 | `Grothendieck/Cover.lean` | `Cover_en.lean` | Bundled covering `J.Cover X`: coe-injective, pullback/top/inf laws, `bind_mem_iff`, base condition (#10912, Phase 5 of #2159) | 284 |
| 37 | `Grothendieck/PullbackFunctor.lean` | `PullbackFunctor_en.lean` | Coherence laws of the pullback pseudofunctor on `J.Cover`: `pullback_triple`, `pullbackComp_assoc`, left/right units (#11023, Phase 5 of #2159) | 149 |
| 38 | `Grothendieck/PullbackFunctorLaws.lean` | `PullbackFunctorLaws_en.lean` | Pullback functor laws: `pullback_functor_id`, `pullback_functor_comp(_assoc)`, `covers_pullback_comp` (#11035, Phase 5 of #2159) | 141 |
| 39 | `Grothendieck/TopologyLattice.lean` | `TopologyLattice_en.lean` | Lattice laws of Grothendieck topologies: `inf/sup_covering`, `sSup_covering`, `le_covers` (#11038, Phase 5 of #2159) | 211 |
| 40 | `Grothendieck/CoversPullback.lean` | `CoversPullback_en.lean` | Arrow-form laws under pullback: `covers_pullback_comp`, `covers_bind`, `covers_iso_covering/cancel`, `covers_mono` (#11057, Phase 5 of #2159) | 202 |
| 41 | `Grothendieck/CoversOrder.lean` | `CoversOrder_en.lean` | Order laws of the arrow form `J.Covers`: `covers_top/bot_iff`, `covers_inter_iff`, `covers_of_covering`, `covers_generate_sieve` (#11068, Phase 5 of #2159) | 164 |
| 42 | `Grothendieck/PullbackCoversLaws.lean` | `PullbackCoversLaws_en.lean` | Arrow-form laws under iterated pullback: `covers_pullback_assoc`, `covers_pullback_id`, `covers_pullback_generate` (#11217, Phase 5 of #2159) | 160 |
| 43 | `Grothendieck/CoversLattice.lean` | `CoversLattice_en.lean` | Indexed lattice laws of the arrow form: `sInf/sSup_covering`, `sInf/sSup_covers` (#11231, Phase 5 of #2159) | 106 |

*The `Lines` column counts the **FR file alone**; the FR+EN total is roughly double.*

The extension was developed under Issue #2159 / Epic #1646: the 43 leaf modules
are merged + 1 bilingual umbrella, 0 `sorry`, 0 axiom added. Phase 2 (Part 34
`f_! ⊣ f^*`) shipped by PR #10357 (MERGED 2026-08-11); Phase 5 (Parts 35-43,
arrow/bundled forms of the covering and pullback laws) shipped by waves
(2026-08-14..16: #10879, #10912, #11023, #11035, #11038, #11057, #11068, #11217,
#11231); Phase 1 (Parts 1-33) previously shipped by PR waves (#2675, #8882, etc.).

## Build

```bash
# From this directory (WSL required)
lake build Grothendieck
# Builds the 43 leaf modules + 1 bilingual umbrella (21,205 FR+EN lines total)
# Last verified build: 2026-07-30, "Build completed successfully (2821 jobs)" (counters re-audited 2026-08-16)
```

## Sorry count

**0 sorry, 0 axiom** — all 43 leaf modules are complete at creation
(the umbrella `Grothendieck.lean` is imports-only without declarations).

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
- **EPIC #4980** — Lean i18n convention (Option A sibling pair post-2026-07-04; 43 `_en.lean` siblings on `main` in this lake + 1 bilingual inline umbrella)
- Issue #8960 (reconciling the two `Part` numberings)
- **[`README.md`](./README.md)** — FR canonical sibling of this file

## Conclusion

This tribute is a **complete pedagogical tour** (43 leaf modules + 1 bilingual umbrella, 21,205 FR+EN lines, 0 `sorry`,
0 axiom added) showing how Grothendieck's language — sites, sheaves,
sheafification, points, cohomology, Yoneda, direct images, covering forms —
already lives in Mathlib 4. It is
deliberately **not** a formalization of EGA/SGA; it is a curated index that lets
learners see the library through Grothendieckian eyes.

### The arc

The modules trace a coherent path: **sites and sieves** (Parts 1, 6, 8, 11, 12,
16) → **sheaves, separation, and transfer** (7, 9, 10, 17) → **sheafification and
its left exactness** (13, 14) → **points and conservative families** (15, 19) →
**sheaf cohomology, Mayer-Vietoris, and Čech** (20-23), with **schemes and the
Zariski site** (2, 3), a **Mathlib map** (4), and the **Yoneda lemma** (24)
anchoring the tour to the library it indexes. The categorical foundations
(Adjunction, Equivalences, Monads) at Parts 25, 29, 26 underpin the whole
formalization. `DirectImage.lean` indexes the `f^* ⊣ f_*` adjunction — the
simplest instance of the "six operations", transporting sheaves along morphisms
of schemes. `ExceptionalDirect.lean` (Part 34, #10357) climbs a rung by
formalizing `f_! ⊣ f^*` at the presheaf level — the *proper-support* direct
image as a left Kan extension of `f^*`, the missing link between `f^*`
(inverse image) and `f_*` (direct image). Parts 35-43 extend the *covering*
side: arrow and bundled forms of `J.Cover`, pullback functor and topology
order/lattice laws (CoversArrow, Cover, PullbackFunctor, PullbackFunctorLaws,
TopologyLattice, CoversPullback, CoversOrder, PullbackCoversLaws, CoversLattice,
Phase 5 of #2159).

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
