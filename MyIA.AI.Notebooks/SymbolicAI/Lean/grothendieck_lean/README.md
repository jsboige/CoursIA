# Grothendieck Tribute — Mathlib Tour

Alexandre Grothendieck (1928-2014).

## Purpose

This workspace is a **pedagogical homage** showing how Grothendieck's mathematical
language already lives in Mathlib 4. It is **not** an attempt to formalize EGA/SGA.

The goal is to give learners a curated entry point into:
- Categories, sieves, and Grothendieck topologies
- Schemes (locally ringed spaces locally Spec R)
- The Zariski site
- What Mathlib has and what it doesn't (yet)

## Structure

### Phase 1 (Tour) — `0 sorry`

| File | Content | Lines |
|------|---------|-------|
| `Grothendieck/CategoryAndSites.lean` | Sieves, Grothendieck topologies (trivial/discrete/dense), three axioms | ~110 |
| `Grothendieck/SchemesTour.lean` | Scheme type, Spec functor, Γ, homeoOfIso, fully-faithful | ~70 |
| `Grothendieck/ZariskiSite.lean` | Zariski pretopology, zariskiTopology_eq bridge theorem, subcanonical | ~60 |
| `Grothendieck/MathlibMap.lean` | `#check` index of all Grothendieck-related Mathlib definitions | ~70 |
| `Grothendieck/Calibration.lean` | 4 micro-proof targets for prover harness (Epic #1453) | ~60 |

### Phase 2 (Extension) — `0 sorry` (Issue #2159, Epic #2162)

| File | Content | Lines |
|------|---------|-------|
| `Grothendieck/SieveLattice.lean` | Sieve pullback identities: `pullback_id`, `pullback_pullback` (contravariant composition), `pullback_bot`, `pullback_monotone` | ~90 |

### Phase 3 (Sheaf Basics) — `0 sorry` (Issue #2159, Epic #2162)

| File | Content | Lines |
|------|---------|-------|
| `Grothendieck/SheafBasics.lean` | Sheaf/separated basics, subcanonical topologies, sheaf transfer along J₁ ≤ J₂ | ~128 |

## Build

```bash
# From this directory (WSL required)
lake build Grothendieck
```

## Sorry count

**0 production sorry** — all proofs are complete at creation.

## Toolchain

Aligned with other SymbolicAI/Lean projects: `leanprover/lean4:v4.30.0-rc2`

## See also

- Epic #1646 (Grothendieck tribute)
- Epic #1453 (prover harness calibration)
- Conway tribute workspace (`../conway_lean/`)
- Lean notebook series (`../README.md`)
