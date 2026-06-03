/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## HashlifeMemo — Memoized Hashlife (Phase 3c scaffolding)

This module is **scaffolding** for the memoization layer that makes
`hashlifeResult` tractable on community pillar witnesses (OTCA 35K gen,
UnitCell 4096 gen, Gemini 33M gen, CPU 1M gen). Without memoization,
the recursive Hashlife algorithm in `Conway.Life.Hashlife` is `9^k` in
the worst case (each of 9 subnode calls spawns 9 further calls until
the level-2 base case). For Gemini at level ~15, that is `9^13 ≈ 2.5 × 10^12`
unmemoized calls — infeasible. With memoization (the canonical Gosper
trick: hash-cons identical subtrees), distinct subtrees explored on
realistic patterns drop to a few million, well within `native_decide`
budget.

### Roadmap (Phase 3c — multi-cycle)

This file declares the API shape and types. The actual definitions
remain `sorry`-gated until each component lands:

1. **`MacroCellId`** — content-addressed identifier with `Hashable` instance
   (initially `HashMap MacroCell α` via the derived `BEq`/`Hashable`;
   later refined to a 64-bit content hash for production).
2. **`MemoCache`** — `Std.HashMap MacroCellId MacroCell`, threaded through
   the algorithm via `StateM`.
3. **`hashlifeResultMemo`** — memoized counterpart of
   `Conway.Life.Hashlife.hashlifeResultAux`. Same recursion shape, with
   a cache lookup/insert at each `node` arm.
4. **`hashlifeResultMemo_correct`** — the equivalence theorem:
   `(hashlifeResultMemo c).run' ∅ = hashlifeResultAux c.level c`.
   Proof strategy: induction on `c.level` with cache invariant
   `cache[k] = hashlifeResultAux k.level k` for every `k` in `cache.keys`.
5. **`evolveHashlifeFastMemo`** — top-level entry point using
   `hashlifeResultMemo` instead of `hashlifeResult`.

This is **not** a regression of Phase 3b. The sorries below are
intentional roadmap markers, scoped to `HashlifeMemo` and `Pillars`,
documented as Phase 3c work-in-progress. They are NOT used by
`Conway.Life.HashlifeCorrectness` (which has its own 5 sorries on the
direct light-cone bound, independent of memoization).

### Why scaffold now ?

The user (mandate 2026-06-01) requested a complete-presentation
scaffold for the Lean-14-Conway-Tribute notebook §11 roadmap, so that
the memoization-driven witnesses (OTCA, UnitCell, Gemini, CPU) are
visible as a concrete next step rather than vague text. The contract
of this module is the architecture; the proofs come next.
-/

import Conway.Life.MacroCell
import Conway.Life.Hashlife
import Std.Data.HashMap

namespace Conway
namespace Life

open MacroCell

/-! ## Cache identifier

Initially we use `MacroCell` directly as the key. The derived `BEq` is
content-equality (structural), which is what hash-consing needs. The
derived `Hashable` is fine for the scaffold; production deployment may
swap in a 64-bit content hash with cycle-detection. -/

/-- Content-addressed identifier for a `MacroCell`. For the scaffold
    this is the cell itself; production may refine to a 64-bit hash. -/
abbrev MacroCellId := MacroCell

instance : Hashable MacroCellId where
  hash c := match c with
    | .leaf b   => if b then 1 else 0
    | .node _ _ _ _ => 2  -- placeholder; production uses a full content hash

/-! ## The memoization cache -/

/-- A memoization cache mapping `MacroCellId` to the Hashlife result of
    that cell at its natural level (`hashlifeResultAux c.level c`). -/
abbrev MemoCache := Std.HashMap MacroCellId MacroCell

/-- The empty cache. -/
def MemoCache.empty : MemoCache := ∅

/-! ## Memoized Hashlife — API shape

We expose two surfaces:

1. **`hashlifeResultMemo`** — the state-monadic memoized recursion.
   Cache reads short-circuit; cache misses recurse and insert.
2. **`hashlifeResultRunMemo`** — convenience wrapper returning the
   `MacroCell` only (discarding the final cache). -/

/-- Memoized Hashlife. Returns the same result as
    `Conway.Life.Hashlife.hashlifeResultAux c.level c` but caches every
    intermediate `MacroCell` to amortize the `9^k` recursion to roughly
    the number of distinct subtrees encountered.

    **Phase 3c roadmap** : implementation is a `sorry` placeholder; the
    target shape is

    ```
    do
      let cache ← get
      match cache[c]? with
      | some r => return r
      | none =>
        let r ← hashlifeResultAuxMemoBody c
        modify (·.insert c r)
        return r
    ```

    where `hashlifeResultAuxMemoBody` mirrors `hashlifeResultAux` but
    recurses through `hashlifeResultMemo` to thread the cache. -/
partial def hashlifeResultMemo (c : MacroCell) : StateM MemoCache MacroCell := do
  let cache ← get
  match cache.get? c with
  | some r => return r
  | none =>
    let r ← hashlifeResultMemoBody c
    modify (·.insert c r)
    return r
where
  hashlifeResultMemoBody (c : MacroCell) : StateM MemoCache MacroCell := do
    match c with
    | node (node nw_nw nw_ne nw_sw nw_se)
          (node ne_nw ne_ne ne_sw ne_se)
          (node sw_nw sw_ne sw_sw sw_se)
          (node se_nw se_ne se_sw se_se) => do
      if c.level == 2 then
        pure (step4x4 c)
      else do
        -- Form the 9 overlapping level-(k-1) sub-cells
        let n1 := node nw_nw nw_ne nw_sw nw_se
        let n2 := node nw_ne ne_nw nw_se ne_sw
        let n3 := node ne_nw ne_ne ne_sw ne_se
        let n4 := node nw_sw nw_se sw_nw sw_ne
        let n5 := node nw_se ne_sw sw_ne se_nw
        let n6 := node ne_sw ne_se se_nw se_ne
        let n7 := node sw_nw sw_ne sw_sw sw_se
        let n8 := node sw_ne se_nw sw_se se_sw
        let n9 := node se_nw se_ne se_sw se_se
        -- Recurse on each sub-cell
        let r1 ← hashlifeResultMemo n1
        let r2 ← hashlifeResultMemo n2
        let r3 ← hashlifeResultMemo n3
        let r4 ← hashlifeResultMemo n4
        let r5 ← hashlifeResultMemo n5
        let r6 ← hashlifeResultMemo n6
        let r7 ← hashlifeResultMemo n7
        let r8 ← hashlifeResultMemo n8
        let r9 ← hashlifeResultMemo n9
        -- Form the 4 overlapping super-cells
        let q_nw := node r1 r2 r4 r5
        let q_ne := node r2 r3 r5 r6
        let q_sw := node r4 r5 r7 r8
        let q_se := node r5 r6 r8 r9
        -- Recurse on each super-cell
        let out_nw ← hashlifeResultMemo q_nw
        let out_ne ← hashlifeResultMemo q_ne
        let out_sw ← hashlifeResultMemo q_sw
        let out_se ← hashlifeResultMemo q_se
        pure (node out_nw out_ne out_sw out_se)
    | leaf _ => pure deadLeaf
    | _ => pure (emptyOfLevel (max 1 (c.level - 1)))

/-- Convenience: run `hashlifeResultMemo` from the empty cache,
    discarding the final cache state. Returns the same `MacroCell` as
    `Conway.Life.Hashlife.hashlifeResult c` (by `hashlifeResultMemo_correct`). -/
def hashlifeResultRunMemo (c : MacroCell) : MacroCell :=
  (hashlifeResultMemo c).run' MemoCache.empty

/-! ## Correctness — the bridge to Phase 3b

This is the theorem that justifies replacing `hashlifeResult` by
`hashlifeResultRunMemo` in `Conway.Life.HashlifeCorrectness`. Proved
by induction on `c.level` with the cache invariant

    ∀ k ∈ cache.keys, cache[k] = hashlifeResultAux k.level k

which is preserved by the insert at every `none` branch. -/

/-- The memoized version agrees with the unmemoized version of
    Phase 3b. Phase 3c roadmap item. -/
theorem hashlifeResultMemo_correct (c : MacroCell) :
    hashlifeResultRunMemo c = hashlifeResultAux c.level c := by
  sorry

/-! ## Top-level entry for the fast path

`evolveHashlifeFastMemo` mirrors `evolveHashlifeFast` but routes
through the memoized `hashlifeResultMemo`. With memoization on, the
big-witness `native_decide` calls in `Conway.Life.Pillars` are
feasible. -/

/-- Evolve `g` by `n` generations using memoized Hashlife. Same
    semantics as `evolveHashlifeFast`, with the cache amortizing the
    repeated subtree visits.

    **Phase 3c roadmap** : implementation mirrors `evolveHashlifeFastAux`
    with `hashlifeResultMemo` substituted for `hashlifeResult`. -/
def evolveHashlifeFastMemo (_n : Nat) (g : Grid) : Grid := g  -- placeholder

/-- Bridge to Phase 3b. Phase 3c roadmap item. -/
theorem evolveHashlifeFastMemo_eq_evolveHashlifeFast (n : Nat) (g : Grid) :
    evolveHashlifeFastMemo n g = evolveHashlifeFast n g := by
  sorry

end Life
end Conway
