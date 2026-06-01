# Grothendieck's Mathematical Language in Mathlib 4

A living index of what Mathlib 4 provides from Grothendieck's mathematical language,
as of May 2026 (toolchain v4.30.0-rc2).

This document accompanies the `grothendieck_lean/` workspace (Epic #1646).

## Exploitable in Mathlib 4 (pedagogically useful)

### Category Theory Foundations

| Concept | Module | Status |
|---------|--------|--------|
| Categories, functors | `Mathlib.CategoryTheory.Category.Basic` | Complete |
| Natural transformations | `Mathlib.CategoryTheory.NaturalTransformation` | Complete |
| Yoneda lemma | `Mathlib.CategoryTheory.Yoneda` | Complete |
| Limits, colimits | `Mathlib.CategoryTheory.Limits.Shapes` | Complete |
| Adjunctions | `Mathlib.CategoryTheory.Adjunction.Basic` | Complete |
| Abelian categories | `Mathlib.CategoryTheory.Abelian.Basic` | Complete |

### Sites and Grothendieck Topologies

| Concept | Module | Status |
|---------|--------|--------|
| Presieves | `Mathlib.CategoryTheory.Sites.Sieves` | Complete |
| Sieves (subfunctors of Yoneda) | `Mathlib.CategoryTheory.Sites.Sieves` | Complete |
| Grothendieck topology | `Mathlib.CategoryTheory.Sites.Grothendieck` | Complete |
| Trivial topology | `GrothendieckTopology.trivial` (= `⊥`) | Complete |
| Discrete topology | `GrothendieckTopology.discrete` (= `⊤`) | Complete |
| Dense topology | `GrothendieckTopology.dense` | Complete |
| Atomic topology | `GrothendieckTopology.atomic` | Complete |
| Pretopologies | `Mathlib.CategoryTheory.Sites.Pretopology` | Complete |
| Sheaves of types | `Mathlib.CategoryTheory.Sites.SheafOfTypes` | Complete |
| Sheaves (general) | `Mathlib.CategoryTheory.Sites.Sheaf` | Complete |
| Sheafification | `Mathlib.CategoryTheory.Sites.Sheafification` | Complete |
| Coherent topologies | `Mathlib.CategoryTheory.Sites.Coherent.Basic` | Partial |

### Sheaves on Topological Spaces

| Concept | Module | Status |
|---------|--------|--------|
| Presheaves | `Mathlib.Topology.Sheaves.Presheaf` | Complete |
| Sheaf condition | `Mathlib.Topology.Sheaves.Sheaf` | Complete |
| Stalks, germs | `Mathlib.Topology.Sheaves.Stalks` | Complete |
| Sheafification (topological) | `Mathlib.Topology.Sheaves.SheafCondition` | Complete |

### Algebraic Geometry

| Concept | Module | Status |
|---------|--------|--------|
| Prime spectrum Spec R | `Mathlib.AlgebraicGeometry.Spec` | Complete |
| Structure sheaf | `Mathlib.AlgebraicGeometry.StructureSheaf` | Complete |
| Scheme (locally ringed space) | `Mathlib.AlgebraicGeometry.Scheme` | Complete |
| Scheme.Hom | `Mathlib.AlgebraicGeometry.Scheme` | Complete |
| Spec functor | `AlgebraicGeometry.Scheme.Spec` | Complete |
| Global sections Γ | `AlgebraicGeometry.Scheme.Γ` | Complete |
| Open immersions | `Mathlib.AlgebraicGeometry.OpenImmersion` | Complete |
| basicOpen | `Mathlib.RingTheory.Localization.Basic` | Available |

### Zariski Site

| Concept | Module | Status |
|---------|--------|--------|
| Zariski pretopology | `AlgebraicGeometry.Scheme.zariskiPretopology` | Complete |
| Zariski topology | `AlgebraicGeometry.Scheme.zariskiTopology` | Complete |
| zariskiTopology_eq bridge | `Scheme.zariskiTopology_eq` | Complete |
| Subcanonical property | `Scheme.zariskiTopology.Subcanonical` | Complete |
| Forget continuous | `Scheme.forgetToTop.IsContinuous` | Complete |
| Big Zariski site | `Mathlib.AlgebraicGeometry.Sites.BigZariski` | Complete |

### Morphism Properties

| Concept | Module | Status |
|---------|--------|--------|
| Etale morphisms | `Mathlib.AlgebraicGeometry.Etale` | Partial |
| Smooth morphisms | `Mathlib.AlgebraicGeometry.Smooth` | Partial |
| Separated morphisms | `Mathlib.AlgebraicGeometry.Separated` | Partial |
| Finite morphisms | `Mathlib.AlgebraicGeometry.Finite` | Embryonic |
| Proper morphisms | `Mathlib.AlgebraicGeometry.Proper` | Embryonic |

## Partially Available (advanced, usable with care)

| Concept | Module | Notes |
|---------|--------|-------|
| Derived categories | `Mathlib.CategoryTheory.Localization` + Riou 2025 | Advanced, active development |
| Functor homology | Scattered | No unified API |
| Quasi-coherent sheaves | `Mathlib.AlgebraicGeometry.GammaSpec` | Basic structure only |
| Projective spectrum | Not present | Would need new development |

## Absent from Mathlib (research-grade formalization targets)

| Concept | Status | Notes |
|---------|--------|-------|
| Etale cohomology | Absent | Site étale, ℓ-adic, fundamental group |
| Motives | Absent | Pure motives, Voevodsky DM category |
| Six operations | Absent | Grothendieck's formalism (Rf_*, f_!, f^!, etc.) |
| Grothendieck-Riemann-Roch | Absent | Needs K-theory + chern classes |
| Grothendieck duality | Absent | Very deep, requires residues/differential forms |
| Crystalline cohomology | Absent | p-adic Hodge theory context |
| Anabelian geometry | Absent | Section conjecture, etc. |
| Deep EGA results | Absent | Proper base change, semi-continuity, etc. |
| Deep SGA results | Absent | SGA 1-7, most results not formalized |

## Key References

- Grothendieck, A. *Elements de Geometrie Algebrique* (EGA I-IV), 1960-1967.
- Grothendieck, A. *Seminaire de Geometrie Algebrique* (SGA 1-7), 1960-1969.
- The Mathlib Community. *The Mathlib Library*, arXiv:1910.09436 (2020).
- Commelin, J., Massot, P. *Natural number game* and Mathlib scheme formalization efforts.

## Scope Note

This map covers **Grothendieck's language in Mathlib** — what a learner can explore
today through `#check` and micro-proofs. It is NOT a roadmap for future formalization.
Research-grade targets (etale cohomology, motives, etc.) are listed to clarify the
boundary between "pedagogically accessible" and "open research problem".
