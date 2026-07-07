# sensitivity_lean — Sensitivity Conjecture (Huang 2019)

> Series: [`SymbolicAI/Lean`](../README.md) · [`sensitivity_lean`](./)

Lean 4 formalization of the **Sensitivity Theorem** from Boolean function
analysis — the degree bound that **resolves the Sensitivity Conjecture** (open
since 1989/1992, settled by Hao Huang in 2019 via a four-page combinatorial
argument).

Complete mini-project: **0 sorry, 0 axiom** beyond Lean core axioms.

## Status

- **Toolchain**: `v4.31.0-rc1`
- **Sorry**: **0** — every proof is closed
- **Build**: `lake build Sensitivity` — SUCCESS
- **Dependencies**: Mathlib4

## What it formalizes

For a Boolean function `f : {0,1}^n → {0,1}`, three complexity measures are
linked by the chain `s(f) ≤ bs(f) ≤ deg(f)`:

- **Sensitivity** `s(f)`: the maximum, over inputs `x`, of the number of
  coordinates `i` whose flip `x ⊕ eᵢ` changes `f(x)`.
- **Block sensitivity** `bs(f)`: the maximum number of *disjoint* blocks of
  coordinates that can each individually flip `f`.
- **Degree** `deg(f)`: the degree of `f` as a real multilinear polynomial.

The **Sensitivity Conjecture** (Nisan–Szegedy 1992, refining Wegener 1989 and
Cook et al. 1986) asked whether `bs(f)` is polynomially bounded in `s(f)`. Huang
(2019) settled it positively by proving the degree theorem: **every induced
subgraph of the `n`-cube on more than half its vertices has a vertex of degree
`≥ √n`** (`huang_degree_theorem`, `MainTheorem.lean` L84). The corollary is the
quadratic bound `deg(f) ≤ s(f)²`, i.e. `bs(f) ≤ s(f)²`.

The proof hinges on a spectral argument (`exists_eigenvalue`, L51): a signed
adjacency matrix `Aₙ` of the hypercube has eigenvalue `√n`, and Cauchy's
interlacing theorem forces a high-degree vertex in any large induced subgraph.

## Modules

| File | Lines | sorry | Content |
|------|------:|------:|---------|
| `Sensitivity.lean` | 1 | 0 | Root import umbrella |
| `Sensitivity/Hypercube.lean` | 124 | 0 | Boolean hypercube `Q n`, vertices, adjacency |
| `Sensitivity/VectorSpace.lean` | 132 | 0 | Real vector space of Boolean functions, `ℝ^{2^n}` basis |
| `Sensitivity/Operator.lean` | 100 | 0 | Sensitivity and block-sensitivity operators |
| `Sensitivity/MainTheorem.lean` | 131 | 0 | `exists_eigenvalue` (L51), `huang_degree_theorem` (L84) |

## Key results

- **`huang_degree_theorem`** (`MainTheorem.lean` L84) — the main result: for
  `H : Set (Q m.succ)` with `Card H ≥ 2^m + 1` (more than half the `2^{m+1}`
  vertices of `Q_{m+1}`), `H` contains a vertex of degree `≥ √(m+1)`.
- **`exists_eigenvalue`** (`MainTheorem.lean` L51) — the spectral lemma feeding
  the degree theorem.
- Complete hypercube + vector-space + operator infrastructure (0 sorry).

## Notes

- The Sensitivity Conjecture was posed by Nisan and Szegedy (1992) and resolved
  by Hao Huang (*Induced subgraphs of hypercubes and a proof of the Sensitivity
  Conjecture*, Annals of Mathematics 190(3), 2019).
- Part of the [`SymbolicAI/Lean`](../README.md) formalization series.

## Build

```bash
# From this directory (WSL recommended for lake on Windows)
lake build Sensitivity
```

## See also

- **[`SymbolicAI/Lean`](../README.md)** — parent series index
- Huang (2019), *Induced subgraphs of hypercubes and a proof of the Sensitivity
  Conjecture*, Ann. Math. 190(3).
- Nisan & Szegedy (1992), *On the degree of Boolean functions as real
  polynomials*, DIMACS.

## Conclusion

This mini-project formalizes in Lean 4 (0 `sorry`, 0 axiom beyond Lean core) the
proof that **resolved the Sensitivity Conjecture** — open since 1989/1992, settled
by Hao Huang in 2019 via a four-page combinatorial argument. The whole chain
`s(f) ≤ bs(f) ≤ deg(f)` and Huang's degree theorem are closed.

### What is proven

The headline `huang_degree_theorem` (`MainTheorem.lean`): every induced subgraph
of the `n`-cube on more than half its vertices has a vertex of degree `≥ √n`. The
corollary is the quadratic bound `deg(f) ≤ s(f)²`, equivalently `bs(f) ≤ s(f)²` —
sensitivity and block sensitivity are polynomially related, as the conjecture
asked. The supporting infrastructure (hypercube `Q n`, the real vector space of
Boolean functions, sensitivity/block-sensitivity operators) is fully built.

### Why it works

The argument is spectral (`exists_eigenvalue`): a signed adjacency matrix of the
hypercube has eigenvalue `√n`, and Cauchy's interlacing theorem forces a
high-degree vertex in any large induced subgraph. The formalization carries that
eigenvalue/interlacing skeleton through Mathlib.

### Where to go next

- **Source**: Huang (2019), *Induced subgraphs of hypercubes and a proof of the
  Sensitivity Conjecture*, Annals of Mathematics 190(3).
- **Context**: Nisan & Szegedy (1992), the conjecture as posed.
- **Series**: the [`SymbolicAI/Lean`](../README.md) formalization index.
