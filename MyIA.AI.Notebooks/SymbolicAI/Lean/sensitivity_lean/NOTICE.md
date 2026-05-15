# Sensitivity Theorem — Huang 2019

Formalization of Hao Huang's sensitivity theorem in Lean 4.

## Source

This is a dust-off (re-port) of `mathlib4/Archive/Sensitivity.lean`,
adapted for Mathlib v4.30.0-rc2 with pedagogical decomposition.

Original authors: Reid Barton, Johan Commelin, Jesse Michael Han,
Chris Hughes, Robert Y. Lewis, Patrick Massot.

## License

The original code is released under the Apache 2.0 license
(as part of mathlib4). This port preserves that license.

## Theorem

In the hypercube of dimension n >= 1, if one colors more than half
the vertices then at least one vertex has at least sqrt(n) colored neighbors.

## Structure

| File | Content |
|------|---------|
| `Sensitivity/Hypercube.lean` | Hypercube type Q, adjacency relation |
| `Sensitivity/VectorSpace.lean` | Free vector space V, basis e, dual basis epsilon |
| `Sensitivity/Operator.lean` | Linear operator f, Knuth matrix g |
| `Sensitivity/MainTheorem.lean` | Huang degree theorem (huang_degree_theorem) |
