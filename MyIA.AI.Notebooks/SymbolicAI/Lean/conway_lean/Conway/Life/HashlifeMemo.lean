/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## HashlifeMemo — Memoized Hashlife, proven correct (Phase 3c)

This module implements the memoization layer that makes `hashlifeResult`
tractable on community pillar witnesses (OTCA 35K gen, UnitCell 4096 gen,
Gemini 33M gen, CPU 1M gen). Without memoization, the recursive Hashlife
algorithm in `Conway.Life.Hashlife` is `9^k` in the worst case (each of
13 subnode calls spawns further calls until the level-2 base case). With
memoization (the canonical Gosper trick: cache results for identical
subtrees), distinct subtrees explored on realistic patterns drop to a few
million, within `native_decide` budget.

### Design

- **Cache**: `Std.HashMap (Nat × MacroCell) MacroCell`, keyed by
  `(fuel, cell)`. The fuel is part of the key because
  `hashlifeResultAux` is genuinely fuel-dependent (its fallback arms
  depend on whether fuel is exhausted), so caching by cell alone would
  be unsound on malformed cells.
- **`Hashable MacroCell`**: a structural 64-bit content hash
  (`MacroCell.contentHash`). `BEq` comes from the derived `DecidableEq`
  (hence lawful), which is what the cache-correctness proofs need.
- **Fused correctness**: instead of defining the memoized function and
  then proving it correct by a separate induction, each function returns
  a subtype packaging the value, the final cache, a proof that the value
  equals the unmemoized reference, and a proof that the cache stays
  correct (`CacheOK`). Every recursive call carries its own proof, so no
  global induction over the 13-call recursion tree is ever needed. The
  proofs are `Prop`-valued and fully erased at runtime.

### Implementation notes

- The well-formed `node`-of-`node`s arm spells out its 16 grandchildren
  (`a1..a4, b1..b4, c1..c4, d1..d4`) **without** a pattern alias
  (`c@(...)`): alias fvars are syntactically opaque to `rw`/`simp`, which
  would break the unfold lemma `hashlifeResultAux_succ_node` below.
- The malformed arms whose `level` computation is stuck (e.g.
  `1 + (1 + w1.level)` with `w1` neutral) return the *verbatim* `ite`
  expression from `hashlifeResultAux`'s fallback arm so that `rfl`
  closes the proof obligation by definitional unfolding.
-/

import Conway.Life.MacroCell
import Conway.Life.Hashlife
import Std.Data.HashMap

namespace Conway
namespace Life

open MacroCell

/-! ## Hashing MacroCells

A structural content hash. Equal cells (by the derived `DecidableEq`,
which induces the `BEq` in scope) get equal hashes by construction, so
`LawfulHashable` is automatic. -/

/-- Structural 64-bit content hash of a `MacroCell`. -/
def MacroCell.contentHash : MacroCell → UInt64
  | .leaf b => if b then 1 else 0
  | .node nw ne sw se =>
    mixHash 2 (mixHash (mixHash nw.contentHash ne.contentHash)
                       (mixHash sw.contentHash se.contentHash))

instance : Hashable MacroCell := ⟨MacroCell.contentHash⟩

/-! ## The memoization cache and its invariant -/

/-- Memoization cache: `(fuel, cell) ↦ hashlifeResultAux fuel cell`. -/
abbrev MemoCache := Std.HashMap (Nat × MacroCell) MacroCell

/-- The empty cache. -/
def MemoCache.empty : MemoCache := ∅

/-- Cache correctness: every binding records the true (unmemoized)
    Hashlife result for its key. -/
def CacheOK (m : MemoCache) : Prop :=
  ∀ fuel c r, m[(fuel, c)]? = some r → r = hashlifeResultAux fuel c

theorem cacheOK_empty : CacheOK MemoCache.empty := by
  intro fuel c r h
  simp [MemoCache.empty] at h

/-- Inserting a correct binding preserves cache correctness. -/
theorem CacheOK.insert {m : MemoCache} (hm : CacheOK m) {fuel : Nat}
    {c r : MacroCell} (hr : r = hashlifeResultAux fuel c) :
    CacheOK (m.insert (fuel, c) r) := by
  intro f d r' h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  next heq =>
    have hkey : ((fuel, c) : Nat × MacroCell) = (f, d) := eq_of_beq heq
    injection hkey with h1 h2
    subst h1; subst h2
    injection h with h'
    exact h'.symm.trans hr
  next _ =>
    exact hm f d r' h

/-! ## Unfold lemma for the well-formed arm

`hashlifeResultAux` uses a pattern alias `c@(node ...)` in its source,
whose alias fvar blocks syntactic rewriting. This lemma restates the
well-formed arm with explicit patterns and zeta-expanded `let`s; it is
true by `rfl` (iota + zeta reduction). Grandchild naming: `a* = nw.*`,
`b* = ne.*`, `c* = sw.*`, `d* = se.*`, each in `nw ne sw se` order. -/

private theorem hashlifeResultAux_succ_node (fuel : Nat)
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell) :
    hashlifeResultAux (fuel + 1)
      (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
            (node c1 c2 c3 c4) (node d1 d2 d3 d4)) =
    if (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).level == 2 then
      step4x4 (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                    (node c1 c2 c3 c4) (node d1 d2 d3 d4))
    else
      node
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a1 a2 a3 a4))
          (hashlifeResultAux fuel (node a2 b1 a4 b3))
          (hashlifeResultAux fuel (node a3 a4 c1 c2))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a2 b1 a4 b3))
          (hashlifeResultAux fuel (node b1 b2 b3 b4))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node b3 b4 d1 d2))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a3 a4 c1 c2))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node c1 c2 c3 c4))
          (hashlifeResultAux fuel (node c2 d1 c4 d3))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node b3 b4 d1 d2))
          (hashlifeResultAux fuel (node c2 d1 c4 d3))
          (hashlifeResultAux fuel (node d1 d2 d3 d4)))) := rfl

/-! ## The memoized recursion, fused with its correctness proof

`hashlifeResultMemoAux fuel c m hm` returns `(value, cache')` together
with proofs that `value = hashlifeResultAux fuel c` and `CacheOK cache'`.
Structural recursion on `fuel`. -/

set_option maxHeartbeats 800000 in
/-- Memoized counterpart of `hashlifeResultAux`, carrying its own
    correctness certificate. The cache is threaded left-to-right through
    the 13 recursive calls of the well-formed arm. -/
def hashlifeResultMemoAux : (fuel : Nat) → (c : MacroCell) →
    (m : MemoCache) → CacheOK m →
    {p : MacroCell × MemoCache //
      p.1 = hashlifeResultAux fuel c ∧ CacheOK p.2}
  | 0, _, m, hm => ⟨(deadLeaf, m), rfl, hm⟩
  | fuel + 1, node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
              (node c1 c2 c3 c4) (node d1 d2 d3 d4), m, hm =>
    match hlook : m[(fuel + 1,
        node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4))]? with
    | some r => ⟨(r, m), hm _ _ _ hlook, hm⟩
    | none =>
      if hl2 : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                     (node c1 c2 c3 c4) (node d1 d2 d3 d4)).level == 2 then
        have hres : step4x4 (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                                  (node c1 c2 c3 c4) (node d1 d2 d3 d4))
            = hashlifeResultAux (fuel + 1)
                (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                      (node c1 c2 c3 c4) (node d1 d2 d3 d4)) := by
          rw [hashlifeResultAux_succ_node, if_pos hl2]
        ⟨(step4x4 (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                        (node c1 c2 c3 c4) (node d1 d2 d3 d4)),
          m.insert (fuel + 1,
              node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                   (node c1 c2 c3 c4) (node d1 d2 d3 d4))
            (step4x4 (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                           (node c1 c2 c3 c4) (node d1 d2 d3 d4)))),
         hres, hm.insert hres⟩
      else
        -- The 9 sub-cells (n1..n9), then the 4 super-cells, threading
        -- the cache (and its `CacheOK` proof) through all 13 calls.
        let p1 := hashlifeResultMemoAux fuel (node a1 a2 a3 a4) m hm
        let p2 := hashlifeResultMemoAux fuel (node a2 b1 a4 b3) p1.1.2 p1.2.2
        let p3 := hashlifeResultMemoAux fuel (node b1 b2 b3 b4) p2.1.2 p2.2.2
        let p4 := hashlifeResultMemoAux fuel (node a3 a4 c1 c2) p3.1.2 p3.2.2
        let p5 := hashlifeResultMemoAux fuel (node a4 b3 c2 d1) p4.1.2 p4.2.2
        let p6 := hashlifeResultMemoAux fuel (node b3 b4 d1 d2) p5.1.2 p5.2.2
        let p7 := hashlifeResultMemoAux fuel (node c1 c2 c3 c4) p6.1.2 p6.2.2
        let p8 := hashlifeResultMemoAux fuel (node c2 d1 c4 d3) p7.1.2 p7.2.2
        let p9 := hashlifeResultMemoAux fuel (node d1 d2 d3 d4) p8.1.2 p8.2.2
        let o1 := hashlifeResultMemoAux fuel
          (node p1.1.1 p2.1.1 p4.1.1 p5.1.1) p9.1.2 p9.2.2
        let o2 := hashlifeResultMemoAux fuel
          (node p2.1.1 p3.1.1 p5.1.1 p6.1.1) o1.1.2 o1.2.2
        let o3 := hashlifeResultMemoAux fuel
          (node p4.1.1 p5.1.1 p7.1.1 p8.1.1) o2.1.2 o2.2.2
        let o4 := hashlifeResultMemoAux fuel
          (node p5.1.1 p6.1.1 p8.1.1 p9.1.1) o3.1.2 o3.2.2
        have hres : node o1.1.1 o2.1.1 o3.1.1 o4.1.1
            = hashlifeResultAux (fuel + 1)
                (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                      (node c1 c2 c3 c4) (node d1 d2 d3 d4)) := by
          rw [hashlifeResultAux_succ_node, if_neg hl2,
              o1.2.1, o2.2.1, o3.2.1, o4.2.1,
              p1.2.1, p2.2.1, p3.2.1, p4.2.1, p5.2.1,
              p6.2.1, p7.2.1, p8.2.1, p9.2.1]
        ⟨(node o1.1.1 o2.1.1 o3.1.1 o4.1.1,
          o4.1.2.insert (fuel + 1,
              node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                   (node c1 c2 c3 c4) (node d1 d2 d3 d4))
            (node o1.1.1 o2.1.1 o3.1.1 o4.1.1)),
         hres, o4.2.2.insert hres⟩
  | fuel + 1, leaf b, m, hm => ⟨(deadLeaf, m), rfl, hm⟩
  | fuel + 1, node (leaf x) q2 q3 q4, m, hm => ⟨(deadLeaf, m), rfl, hm⟩
  -- Malformed cells whose `level` is a stuck term: return the verbatim
  -- fallback `ite` of `hashlifeResultAux` so that `rfl` closes the goal.
  | fuel + 1, node (node w1 w2 w3 w4) (leaf x) q3 q4, m, hm =>
    ⟨(if (node (node w1 w2 w3 w4) (leaf x) q3 q4).level == 0 then deadLeaf
      else emptyOfLevel ((node (node w1 w2 w3 w4) (leaf x) q3 q4).level - 1),
      m), rfl, hm⟩
  | fuel + 1, node (node w1 w2 w3 w4) (node x1 x2 x3 x4) (leaf y) q4, m, hm =>
    ⟨(if (node (node w1 w2 w3 w4) (node x1 x2 x3 x4) (leaf y) q4).level == 0
      then deadLeaf
      else emptyOfLevel
        ((node (node w1 w2 w3 w4) (node x1 x2 x3 x4) (leaf y) q4).level - 1),
      m), rfl, hm⟩
  | fuel + 1, node (node w1 w2 w3 w4) (node x1 x2 x3 x4)
              (node y1 y2 y3 y4) (leaf z), m, hm =>
    ⟨(if (node (node w1 w2 w3 w4) (node x1 x2 x3 x4)
              (node y1 y2 y3 y4) (leaf z)).level == 0
      then deadLeaf
      else emptyOfLevel
        ((node (node w1 w2 w3 w4) (node x1 x2 x3 x4)
               (node y1 y2 y3 y4) (leaf z)).level - 1),
      m), rfl, hm⟩

/-- Memoized Hashlife from the empty cache: same result as
    `hashlifeResult c = hashlifeResultAux c.level c`. -/
def hashlifeResultRunMemo (c : MacroCell) : MacroCell :=
  (hashlifeResultMemoAux c.level c MemoCache.empty cacheOK_empty).1.1

/-- The memoized version agrees with the unmemoized Phase 3b reference.
    Immediate from the fused certificate. -/
theorem hashlifeResultMemo_correct (c : MacroCell) :
    hashlifeResultRunMemo c = hashlifeResultAux c.level c :=
  (hashlifeResultMemoAux c.level c MemoCache.empty cacheOK_empty).2.1

/-! ## Memoized fast evolution

`evolveHashlifeFastMemoAux` mirrors `evolveHashlifeFastAux`, routing the
Hashlife jump through `hashlifeResultMemoAux` and threading the cache
across successive jumps. Same fused-certificate style. -/

/-- Memoized counterpart of `evolveHashlifeFastAux`, carrying its own
    correctness certificate. Structural recursion on `fuel`. -/
def evolveHashlifeFastMemoAux : (fuel n : Nat) → (g : Grid) →
    (m : MemoCache) → CacheOK m →
    {p : Grid × MemoCache //
      p.1 = evolveHashlifeFastAux fuel n g ∧ CacheOK p.2}
  | 0, 0, g, m, hm => ⟨(g, m), rfl, hm⟩
  | fuel + 1, 0, g, m, hm => ⟨(g, m), rfl, hm⟩
  | 0, n + 1, g, m, hm => ⟨(g, m), rfl, hm⟩
  | fuel + 1, n + 1, g, m, hm =>
    have heq : evolveHashlifeFastAux (fuel + 1) (n + 1) g =
        if (gridToMacroCellWithOffset g).2.level >= 2
            && n + 1 >= jumpSize (gridToMacroCellWithOffset g).2.level then
          evolveHashlifeFastAux fuel
            (n + 1 - jumpSize (gridToMacroCellWithOffset g).2.level)
            ((hashlifeJump (gridToMacroCellWithOffset g).2).toGrid
              (jumpResultOff (gridToMacroCellWithOffset g).1
                (gridToMacroCellWithOffset g).2.level))
        else evolve (n + 1) g := rfl
    if hcond : (gridToMacroCellWithOffset g).2.level >= 2
        && n + 1 >= jumpSize (gridToMacroCellWithOffset g).2.level then
      let pc := padCenter2 (gridToMacroCellWithOffset g).2
      let pr := hashlifeResultMemoAux pc.level pc m hm
      let r2 := evolveHashlifeFastMemoAux fuel
        (n + 1 - jumpSize (gridToMacroCellWithOffset g).2.level)
        (pr.1.1.toGrid (jumpResultOff (gridToMacroCellWithOffset g).1
          (gridToMacroCellWithOffset g).2.level))
        pr.1.2 pr.2.2
      ⟨r2.1, by
        rw [heq, if_pos hcond, r2.2.1, pr.2.1]
        -- Residual: `hashlifeResultAux pc.level pc` vs
        -- `hashlifeJump (gridToMacroCellWithOffset g).2` — definitionally
        -- equal after unfolding `hashlifeJump`/`hashlifeResult` and the
        -- local `pc` let.
        rfl, r2.2.2⟩
    else
      ⟨(evolve (n + 1) g, m), by rw [heq, if_neg hcond], hm⟩

/-- Evolve `g` by `n` generations using memoized Hashlife. Same
    semantics as `evolveHashlifeFast` (see the bridge theorem below). -/
def evolveHashlifeFastMemo (n : Nat) (g : Grid) : Grid :=
  (evolveHashlifeFastMemoAux n n g MemoCache.empty cacheOK_empty).1.1

/-- Bridge to Phase 3b: the memoized fast path agrees with the
    unmemoized one. Immediate from the fused certificate. -/
theorem evolveHashlifeFastMemo_eq_evolveHashlifeFast (n : Nat) (g : Grid) :
    evolveHashlifeFastMemo n g = evolveHashlifeFast n g :=
  (evolveHashlifeFastMemoAux n n g MemoCache.empty cacheOK_empty).2.1

/-! ## The empty grid is a fixed point

Needed by `Conway.Life.Pillars` while the pillar patterns are still
placeholder empty grids (RLE loading pending). -/

theorem step_empty : step ([] : Grid) = [] := by
  simp [step, candidates, sortDedup]

theorem evolve_empty (n : Nat) : evolve n ([] : Grid) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [evolve_succ, ih, step_empty]

theorem evolveHashlifeFast_empty (n : Nat) :
    evolveHashlifeFast n ([] : Grid) = [] := by
  cases n with
  | zero => rfl
  | succ n =>
    -- On `[]`, `gridFrame` gives level 0, the jump condition is false,
    -- and the fast path falls back to `evolve`.
    show evolveHashlifeFastAux (n + 1) (n + 1) ([] : Grid) = []
    rw [show evolveHashlifeFastAux (n + 1) (n + 1) ([] : Grid)
        = evolve (n + 1) ([] : Grid) from rfl]
    exact evolve_empty (n + 1)

theorem evolveHashlifeFastMemo_empty (n : Nat) :
    evolveHashlifeFastMemo n ([] : Grid) = [] := by
  rw [evolveHashlifeFastMemo_eq_evolveHashlifeFast]
  exact evolveHashlifeFast_empty n

/-! ## Sanity checks

The memoized functions must agree with their references on the
canonical patterns (these are compiled evaluations, complementing the
kernel-checked theorems above). -/

#eval hashlifeResultRunMemo (gridToMacroCell glider)
        == hashlifeResult (gridToMacroCell glider)          -- expect true
#eval evolveHashlifeFastMemo 8 glider == evolveHashlifeFast 8 glider  -- true
#eval evolveHashlifeFastMemo 4 blinker_h == evolve 4 blinker_h        -- true
#eval evolveHashlifeFastMemo 3 toad == evolve 3 toad                  -- true

end Life
end Conway
