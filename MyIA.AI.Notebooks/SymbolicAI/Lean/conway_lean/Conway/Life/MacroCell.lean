/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## MacroCell — Quadtree representation for Hashlife

A `MacroCell` represents a square region of the Game of Life grid as a
quadtree. Level-0 cells are individual boolean cells. A level-(n+1) cell
is a 2x2 arrangement of level-n cells (named `nw`, `ne`, `sw`, `se` for
north-west, north-east, south-west, south-east).

The key insight of Hashlife (Gosper 1984) is that the step function on
MacroCells can be computed recursively and memoized, giving exponential
speedup on patterns with repetitive structure.

## Layout convention

We use the same coordinate convention as `Conway.Life`:
- Each cell is `(row, col) : Int × Int`.
- Rows increase downward (north -> south).
- Columns increase rightward (west -> east).

So at the top level a node `node nw ne sw se` of level `n+1` covers a
region of size `2^(n+1) x 2^(n+1)` partitioned as:

```
nw | ne
---+---
sw | se
```

where each quadrant is `2^n x 2^n`. If the whole region has its
top-left corner at `(row0, col0)`, then:

- `nw` covers `[row0,            row0 + 2^n)         x [col0,           col0 + 2^n)`
- `ne` covers `[row0,            row0 + 2^n)         x [col0 + 2^n,    col0 + 2^(n+1))`
- `sw` covers `[row0 + 2^n,     row0 + 2^(n+1))      x [col0,           col0 + 2^n)`
- `se` covers `[row0 + 2^n,     row0 + 2^(n+1))      x [col0 + 2^n,    col0 + 2^(n+1))`

This module is fully proven (no gaps). It only provides the data
structure and conversions. The Hashlife algorithm lives in
`Conway.Life.Hashlife`.
-/

import Conway.Life

namespace Conway
namespace Life

/-! ## The quadtree data structure -/

/-- A quadtree cell.
    - `leaf b` is a single cell that is alive (`b = true`) or dead (`b = false`).
    - `node nw ne sw se` is a 2x2 block of subtrees, all required (by convention,
      but not enforced by the type) to have the same level. -/
inductive MacroCell where
  | leaf (alive : Bool)
  | node (nw ne sw se : MacroCell)
  -- `DecidableEq` (rather than a derived `BEq`) so that the `BEq`
  -- instance is lawful (`instLawfulBEq`), which the memoization cache
  -- proofs in `Conway.Life.HashlifeMemo` rely on.
  deriving DecidableEq, Repr, Inhabited

namespace MacroCell

/-- The level of a `MacroCell`: 0 for `leaf`, `1 + nw.level` for `node`.
    By construction, a well-formed `MacroCell` has all four subtrees at the
    same level; we only inspect `nw`. -/
def level : MacroCell -> Nat
  | leaf _      => 0
  | node nw _ _ _ => 1 + nw.level

/-- The side length of the region covered by a `MacroCell`: `2 ^ level`. -/
def size (c : MacroCell) : Nat := 2 ^ c.level

/-- A leaf containing a dead cell. -/
def deadLeaf : MacroCell := leaf false

/-- A leaf containing a live cell. -/
def aliveLeaf : MacroCell := leaf true

/-- Build an "empty" (all-dead) `MacroCell` of level `n`. -/
def emptyOfLevel : Nat -> MacroCell
  | 0     => deadLeaf
  | n + 1 =>
    let sub := emptyOfLevel n
    node sub sub sub sub

/-- Test if a `MacroCell` represents the all-dead region. -/
def isEmpty : MacroCell -> Bool
  | leaf b      => !b
  | node a b c d => a.isEmpty && b.isEmpty && c.isEmpty && d.isEmpty

/-! ## Conversion: MacroCell -> Grid

Given a `MacroCell` and the absolute `(row, col)` offset of its top-left
corner, enumerate the live cells in lexicographic `(row, col)` order.

The recursion walks the quadrants in the order `nw, ne, sw, se`. We
process all of `nw`'s rows before `ne`'s rows is **not** correct in the
lex ordering when rows interleave; however, because `nw` and `ne` cover
the same row range and `nw` has strictly smaller columns, listing all of
`nw` then all of `ne` does produce lex order **only when** each
quadrant's output is itself sorted. The simpler and obviously correct
implementation is to concatenate the four quadrants and then `sortDedup`
at the top level. -/

/-- Internal helper: enumerate the live cells of `c` whose top-left
    corner is at offset `(r0, c0)`. The resulting list is **not** guaranteed
    to be sorted in lex order — the caller should `sortDedup` if needed. -/
def toCellsAux (r0 c0 : Int) : MacroCell -> List (Int × Int)
  | leaf true   => [(r0, c0)]
  | leaf false  => []
  | node nw ne sw se =>
    let n := nw.level
    let half : Int := (2 ^ n : Nat)
    nw.toCellsAux r0 c0
      ++ ne.toCellsAux r0 (c0 + half)
      ++ sw.toCellsAux (r0 + half) c0
      ++ se.toCellsAux (r0 + half) (c0 + half)

/-- Convert a `MacroCell` to a `Grid`, given the offset `(r0, c0)` of its
    top-left corner. The output is sorted lexicographically and deduplicated. -/
def toGrid (offset : Int × Int) (c : MacroCell) : Grid :=
  sortDedup (c.toCellsAux offset.1 offset.2)

end MacroCell

/-! ## Conversion: Grid -> MacroCell

Given a `Grid` (list of live cell coordinates), build a `MacroCell` of the
smallest level whose region, placed at a chosen offset, contains all the
live cells. The offset is returned alongside so that subsequent calls to
`toGrid` round-trip correctly.

The construction is straightforward but a little tedious:
1. Find the bounding box `[rMin, rMax] x [cMin, cMax]` of the live cells
   (using extra padding on each side to allow `step` to spread).
2. Compute the side length needed: `max (rMax - rMin + 1) (cMax - cMin + 1)`,
   rounded up to the next power of 2.
3. Recursively build the quadtree, dispatching each live cell to the
   appropriate quadrant.
-/

namespace MacroCell

/-- Smallest `n` such that `2 ^ n >= k`. -/
def ceilLog2 (k : Nat) : Nat :=
  match k with
  | 0     => 0
  | 1     => 0
  | k + 2 => 1 + ceilLog2 ((k + 2 + 1) / 2)

/-- `ceilLog2 k` is large enough that `2 ^ ceilLog2 k >= k`. This is the
    arithmetic heart of the `gridFrame` containment lemma. -/
theorem ceilLog2_spec (k : Nat) : 2 ^ ceilLog2 k >= k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [ceilLog2]
    | 1 => simp [ceilLog2]
    | m + 2 =>
      simp only [ceilLog2]
      have h : 2 ^ ceilLog2 ((m + 2 + 1) / 2) >= (m + 2 + 1) / 2 :=
        ih ((m + 2 + 1) / 2) (by omega)
      have h2 : 2 * 2 ^ ceilLog2 ((m + 2 + 1) / 2) >= m + 2 := by omega
      rw [Nat.pow_add, Nat.pow_one]
      exact h2

/-- Build a `MacroCell` of level `n` covering the square `[r0, r0 + 2^n) x
    [c0, c0 + 2^n)`, with live cells given by membership test in `g`. -/
def buildFromGrid (g : Grid) (r0 c0 : Int) : Nat -> MacroCell
  | 0     => leaf (g.elem (r0, c0))
  | n + 1 =>
    let half : Int := (2 ^ n : Nat)
    let nw := buildFromGrid g r0          c0          n
    let ne := buildFromGrid g r0          (c0 + half) n
    let sw := buildFromGrid g (r0 + half) c0          n
    let se := buildFromGrid g (r0 + half) (c0 + half) n
    node nw ne sw se

/-- The level of a `MacroCell` built by `buildFromGrid g r0 c0 lvl` is `lvl`. -/
theorem level_buildFromGrid (g : Grid) (r0 c0 : Int) (lvl : Nat) :
    (buildFromGrid g r0 c0 lvl).level = lvl := by
  induction lvl with
  | zero => rfl
  | succ n ih =>
    simp only [buildFromGrid]
    rw [level, ih]
    omega

/-- A cell `p` lies inside the level-`lvl` square anchored at `(r0, c0)`:
    `[r0, r0 + 2^lvl) x [c0, c0 + 2^lvl)`.

    NOTE: `cases`/`rcases`/`rintro` on a disjunction whose branches mention
    `inRegion` (which unfolds to `Int.le`/`Int.lt`) triggers a Lean
    dependent-elimination failure on the Int subtraction match. The proof
    below uses `match` (which elaborates differently and succeeds) to split
    the 4-way quadrant disjunction. -/
def inRegion (p : Int × Int) (r0 c0 : Int) (lvl : Nat) : Prop :=
  r0 ≤ p.1 ∧ p.1 < r0 + (2 ^ lvl : Nat) ∧
    c0 ≤ p.2 ∧ p.2 < c0 + (2 ^ lvl : Nat)

/-- **Round-trip core lemma**: a cell `p` appears in the `toCellsAux`
    enumeration of `buildFromGrid g r0 c0 lvl` iff `p` lies inside the
    covered square AND `p ∈ g`. Proved by induction on `lvl`,
    generalizing the offsets so the IH applies at shifted quadrant origins. -/
theorem mem_toCellsAux_buildFromGrid (g : Grid) (lvl : Nat) (r0 c0 : Int)
    (p : Int × Int) :
    p ∈ (buildFromGrid g r0 c0 lvl).toCellsAux r0 c0 ↔
      inRegion p r0 c0 lvl ∧ p ∈ g := by
  induction lvl generalizing r0 c0 p with
  | zero =>
    cases h : g.elem (r0, c0) with
    | true =>
      unfold inRegion
      simp only [buildFromGrid, toCellsAux, h, pow_zero, Nat.cast_one,
                 List.mem_singleton]
      constructor
      · rintro rfl
        refine ⟨⟨rfl.le, by omega, rfl.le, by omega⟩, ?_⟩
        exact List.elem_iff.mp h
      · rintro ⟨⟨h1, h2, h3, h4⟩, _⟩
        ext <;> omega
    | false =>
      simp only [buildFromGrid, toCellsAux, h, List.not_mem_nil, false_iff]
      rintro ⟨hreg, hpg⟩
      unfold inRegion at hreg
      obtain ⟨h1, h2, h3, h4⟩ := hreg
      have hp : p = (r0, c0) := by ext <;> omega
      subst hp
      have hne : (r0, c0) ∉ g := by
        intro hm
        exact absurd (List.elem_iff.mpr hm) (Bool.eq_false_iff.mp h)
      exact absurd hpg hne
  | succ n ih =>
    simp only [buildFromGrid, toCellsAux, level_buildFromGrid] at *
    simp only [List.mem_append] at *
    have ihn := ih r0 c0 p
    have ihne := ih r0 (c0 + (2 ^ n : Nat)) p
    have ihsw := ih (r0 + (2 ^ n : Nat)) c0 p
    have ihse := ih (r0 + (2 ^ n : Nat)) (c0 + (2 ^ n : Nat)) p
    rw [ihn, ihne, ihsw, ihse]
    constructor
    · -- Forward: `match` (not rcases) splits the Or — rcases/rintro trigger a
      -- Lean dependent-elimination failure on the Int.le in branch types.
      -- Left-nested `((A ∨ B) ∨ C) ∨ D`:
      --   nw = inl (inl (inl _)), ne = inl (inl (inr _)),
      --   sw = inl (inr _),       se = inr _.
      intro h
      match h with
      | Or.inl (Or.inl (Or.inl ⟨hreg, hm⟩)) =>
        unfold inRegion at hreg
        refine ⟨?_, hm⟩
        unfold inRegion; simp only [Nat.pow_succ, Nat.cast_mul]; omega
      | Or.inl (Or.inl (Or.inr ⟨hreg, hm⟩)) =>
        unfold inRegion at hreg
        refine ⟨?_, hm⟩
        unfold inRegion; simp only [Nat.pow_succ, Nat.cast_mul]; omega
      | Or.inl (Or.inr ⟨hreg, hm⟩) =>
        unfold inRegion at hreg
        refine ⟨?_, hm⟩
        unfold inRegion; simp only [Nat.pow_succ, Nat.cast_mul]; omega
      | Or.inr ⟨hreg, hm⟩ =>
        unfold inRegion at hreg
        refine ⟨?_, hm⟩
        unfold inRegion; simp only [Nat.pow_succ, Nat.cast_mul]; omega
    · rintro ⟨hreg, hpg⟩
      unfold inRegion at hreg
      simp only [Nat.pow_succ, Nat.cast_mul] at hreg
      by_cases hr : p.1 < r0 + (2 ^ n : Nat)
      · by_cases hc : p.2 < c0 + (2 ^ n : Nat)
        · left; left; left; unfold inRegion; refine ⟨⟨?_, ?_, ?_, ?_⟩, hpg⟩ <;> omega
        · left; left; right; unfold inRegion; refine ⟨⟨?_, ?_, ?_, ?_⟩, hpg⟩ <;> omega
      · by_cases hc : p.2 < c0 + (2 ^ n : Nat)
        · left; right; unfold inRegion; refine ⟨⟨?_, ?_, ?_, ?_⟩, hpg⟩ <;> omega
        · right; unfold inRegion; refine ⟨⟨?_, ?_, ?_, ?_⟩, hpg⟩ <;> omega

/-- **Offset-shift identity for `toCellsAux`**: enumerating `c`'s live cells
    with the top-left corner anchored at `(r0, c0)` equals the
    origin-anchored enumeration `(c.toCellsAux 0 0)` translated pointwise by
    `(r0, c0)`. Pure structural induction on `MacroCell` — no Hashlife, no
    `evolve`, no light-cone. This is the bookkeeping bridge that will align an
    offset-`(r0, c0)` `toCellsAux` / `toGrid` membership goal with an
    origin-anchored induction hypothesis in the eventual P4
    central-correctness assembly (`hashlifeResult_central_correct`). -/
theorem toCellsAux_shift (c : MacroCell) (r0 c0 : Int) :
    c.toCellsAux r0 c0 =
      (c.toCellsAux 0 0).map (fun p => (p.1 + r0, p.2 + c0)) := by
  induction c generalizing r0 c0 with
  | leaf b =>
    -- `toCellsAux r0 c0 (leaf b)` reduces to `[(r0, c0)]` / `[]`, but
    -- `List.map f [(0, 0)] = [(0 + r0, 0 + c0)]` is NOT defeq to `[(r0, c0)]`
    -- (`Int.add 0 _` does not reduce definitionally), so `rfl` fails — close
    -- by `zero_add` instead.
    cases b
    · simp only [toCellsAux, List.map_nil]
    · simp only [toCellsAux, List.map_singleton, zero_add]
  | node nw ne sw se ihw ine isw ise =>
    simp only [toCellsAux]
    -- Apply the IH to each LHS quadrant, anchoring at the origin:
    rw [ihw r0 c0, ine r0 (c0 + (2 ^ nw.level : Nat)),
        isw (r0 + (2 ^ nw.level : Nat)) c0,
        ise (r0 + (2 ^ nw.level : Nat)) (c0 + (2 ^ nw.level : Nat))]
    -- Distribute the RHS map over the concatenation, then fold the
    -- origin-anchored quadrants back through the IH (forward) so each RHS
    -- segment becomes a composition of two shifts; `map_map` flattens it.
    simp only [List.map_append, zero_add]
    rw [ine 0 (2 ^ nw.level : Nat), isw (2 ^ nw.level : Nat) 0,
        ise (2 ^ nw.level : Nat) (2 ^ nw.level : Nat)]
    simp only [List.map_map, zero_add]
    -- Both sides are now concatenations of `map (shift_i) (toCellsAux 0 0 sub_i)`,
    -- differing only by AC rearrangements of addition; normalise and close.
    simp only [add_zero, add_assoc, add_comm, add_left_comm]
    rfl

/-- **Membership form of the offset-shift identity**: `p` lies in the
    offset-`(r0, c0)` enumeration of `c` iff `p` translated back to the origin
    `(p.1 - r0, p.2 - c0)` lies in the origin-anchored enumeration. This is the
    form directly usable inside membership biconditionals (e.g. the P4
    central-correctness goal `p ∈ (hashlifeResultAux …).toGrid off ↔ …`), where
    the list-equality `toCellsAux_shift` is less convenient. -/
theorem mem_toCellsAux_shift {c : MacroCell} {r0 c0 : Int} {p : Int × Int} :
    p ∈ c.toCellsAux r0 c0 ↔ (p.1 - r0, p.2 - c0) ∈ c.toCellsAux 0 0 := by
  rw [toCellsAux_shift, List.mem_map]
  constructor
  · rintro ⟨q, hqmem, hpq⟩
    -- `q` is a free variable, so we rewrite the membership to speak of `q`
    -- directly (cannot `subst` on `q.1`/`q.2`, which are field accesses).
    have hqeq : q = (p.1 - r0, p.2 - c0) := by
      rw [Prod.ext_iff] at hpq; ext <;> omega
    rw [hqeq] at hqmem
    exact hqmem
  · intro hq
    refine ⟨(p.1 - r0, p.2 - c0), hq, ?_⟩
    ext <;> omega

end MacroCell

/-! ## High-level Grid -> MacroCell

We pick an offset and level large enough to contain `g`. To leave room
for one round of `step` to spread, we add a 2-cell padding on each side
of the bounding box. Empty grids give the all-dead level-0 leaf. -/

/-- The minimum row of a non-empty grid; defaults to 0 on the empty grid. -/
def gridRowMin (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => min m q.1) p.1

/-- The maximum row of a non-empty grid; defaults to 0 on the empty grid. -/
def gridRowMax (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => max m q.1) p.1

/-- The minimum column of a non-empty grid; defaults to 0 on the empty grid. -/
def gridColMin (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => min m q.2) p.2

/-- The maximum column of a non-empty grid; defaults to 0 on the empty grid. -/
def gridColMax (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => max m q.2) p.2

/-! ## Bounding-box membership lemmas

These relate `gridRowMin` / `gridRowMax` / `gridColMin` / `gridColMax` to list
membership: every live cell of `g` lies inside its bounding box. They form the
arithmetic bridge for `gridFrame_contains_g` (P5 correctness, issue #2162,
Gap 2 — the Grid↔MacroCell round trip).

The four bounding-box helpers are `foldl`s over a coordinate projection, so we
factor the reasoning through generic `proj`-parameterised lemmas and
instantiate them for rows (`(·.1)`) and columns (`(·.2)`). We split
`p ∈ head :: tail` via `by_cases` rather than `cases`/`subst` to avoid the
direction-dependent substitution (which side gets eliminated) when both
operands are local variables. -/

/-- Generic helper: a `foldl` of `min` (via a projection `proj`) never exceeds
    its seed accumulator. -/
theorem foldl_proj_min_le_seed (ps : Grid) (proj : Int × Int → Int) (acc : Int) :
    ps.foldl (fun m q => min m (proj q)) acc ≤ acc := by
  induction ps generalizing acc with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    have h := ih (min acc (proj q))
    omega

/-- Generic helper: a `foldl` of `min` (via `proj`) never exceeds the projected
    coordinate of any cell in the list. -/
theorem foldl_proj_min_le_of_mem (ps : Grid) (proj : Int × Int → Int) (acc : Int)
    (p : Int × Int) (hp : p ∈ ps) :
    ps.foldl (fun m q => min m (proj q)) acc ≤ proj p := by
  induction ps generalizing acc p with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    by_cases heq : p = q
    · rw [heq]
      have h := foldl_proj_min_le_seed qs proj (min acc (proj q))
      omega
    · have hps : p ∈ qs := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact ih (min acc (proj q)) p hps

/-- Generic helper: a `foldl` of `max` (via a projection `proj`) is never below
    its seed accumulator. -/
theorem le_foldl_proj_max_seed (ps : Grid) (proj : Int × Int → Int) (acc : Int) :
    acc ≤ ps.foldl (fun m q => max m (proj q)) acc := by
  induction ps generalizing acc with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    have h := ih (max acc (proj q))
    omega

/-- Generic helper: a `foldl` of `max` (via `proj`) is never below the projected
    coordinate of any cell in the list. -/
theorem le_foldl_proj_max_of_mem (ps : Grid) (proj : Int × Int → Int) (acc : Int)
    (p : Int × Int) (hp : p ∈ ps) :
    proj p ≤ ps.foldl (fun m q => max m (proj q)) acc := by
  induction ps generalizing acc p with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    by_cases heq : p = q
    · rw [heq]
      have h := le_foldl_proj_max_seed qs proj (max acc (proj q))
      omega
    · have hps : p ∈ qs := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact ih (max acc (proj q)) p hps

/-- Every cell of `g` has row coordinate at least `gridRowMin g`. -/
theorem gridRowMin_le_of_mem (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    gridRowMin g ≤ p.1 := by
  cases g with
  | nil => simp at hp
  | cons p₀ ps =>
    simp only [gridRowMin]
    by_cases heq : p = p₀
    · rw [heq]
      exact foldl_proj_min_le_seed ps (·.1) p₀.1
    · have hps : p ∈ ps := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact foldl_proj_min_le_of_mem ps (·.1) p₀.1 p hps

/-- Every cell of `g` has row coordinate at most `gridRowMax g`. -/
theorem le_gridRowMax_of_mem (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    p.1 ≤ gridRowMax g := by
  cases g with
  | nil => simp at hp
  | cons p₀ ps =>
    simp only [gridRowMax]
    by_cases heq : p = p₀
    · rw [heq]
      exact le_foldl_proj_max_seed ps (·.1) p₀.1
    · have hps : p ∈ ps := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact le_foldl_proj_max_of_mem ps (·.1) p₀.1 p hps

/-- Every cell of `g` has column coordinate at least `gridColMin g`. -/
theorem gridColMin_le_of_mem (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    gridColMin g ≤ p.2 := by
  cases g with
  | nil => simp at hp
  | cons p₀ ps =>
    simp only [gridColMin]
    by_cases heq : p = p₀
    · rw [heq]
      exact foldl_proj_min_le_seed ps (·.2) p₀.2
    · have hps : p ∈ ps := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact foldl_proj_min_le_of_mem ps (·.2) p₀.2 p hps

/-- Every cell of `g` has column coordinate at most `gridColMax g`. -/
theorem le_gridColMax_of_mem (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    p.2 ≤ gridColMax g := by
  cases g with
  | nil => simp at hp
  | cons p₀ ps =>
    simp only [gridColMax]
    by_cases heq : p = p₀
    · rw [heq]
      exact le_foldl_proj_max_seed ps (·.2) p₀.2
    · have hps : p ∈ ps := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact le_foldl_proj_max_of_mem ps (·.2) p₀.2 p hps

/-- For any non-empty grid, the row bounding box is well-formed:
    `gridRowMin g ≤ gridRowMax g`. -/
theorem gridRowMin_le_gridRowMax (g : Grid) (hg : g ≠ []) :
    gridRowMin g ≤ gridRowMax g := by
  obtain ⟨p₀, ps, rfl⟩ : ∃ p₀ ps, g = p₀ :: ps := by
    cases g with
    | nil => exact absurd rfl hg
    | cons p₀ ps => exact ⟨p₀, ps, rfl⟩
  have hmin : gridRowMin (p₀ :: ps) ≤ p₀.1 :=
    gridRowMin_le_of_mem _ _ (by simp)
  have hmax : p₀.1 ≤ gridRowMax (p₀ :: ps) :=
    le_gridRowMax_of_mem _ _ (by simp)
  omega

/-- For any non-empty grid, the column bounding box is well-formed:
    `gridColMin g ≤ gridColMax g`. -/
theorem gridColMin_le_gridColMax (g : Grid) (hg : g ≠ []) :
    gridColMin g ≤ gridColMax g := by
  obtain ⟨p₀, ps, rfl⟩ : ∃ p₀ ps, g = p₀ :: ps := by
    cases g with
    | nil => exact absurd rfl hg
    | cons p₀ ps => exact ⟨p₀, ps, rfl⟩
  have hmin : gridColMin (p₀ :: ps) ≤ p₀.2 :=
    gridColMin_le_of_mem _ _ (by simp)
  have hmax : p₀.2 ≤ gridColMax (p₀ :: ps) :=
    le_gridColMax_of_mem _ _ (by simp)
  omega

/-- Generic helper: a `foldl` of `min` (via `proj`) is *attained* — the result
    is either the seed `acc` or the projection of some element of the list.
    Companion to `foldl_proj_min_le_seed`/`foldl_proj_min_le_of_mem` (those give
    the `≤` bounds; this one gives the witness). -/
theorem foldl_proj_min_attained (ps : Grid) (proj : Int × Int → Int) (acc : Int) :
    ps.foldl (fun m q => min m (proj q)) acc = acc ∨
      ∃ p ∈ ps, ps.foldl (fun m q => min m (proj q)) acc = proj p := by
  induction ps generalizing acc with
  | nil => left; rfl
  | cons q qs ih =>
    simp only [List.foldl_cons]
    rcases ih (min acc (proj q)) with h | ⟨p, hp, hval⟩
    · rcases le_total acc (proj q) with hle | hle
      · left; rw [h]; omega
      · right; exact ⟨q, by simp, by rw [h]; omega⟩
    · right; exact ⟨p, by simp [hp], hval⟩

/-- The row minimum of a non-empty grid is *attained* by some live cell:
    there is a `p ∈ g` with `p.1 = gridRowMin g`. This is the witness form of
    `gridRowMin_le_of_mem` (needed to extract the topmost live cell, e.g. for
    the structural satisfiability bound on `box_assez_grand`). -/
theorem gridRowMin_mem (g : Grid) (hg : g ≠ []) :
    ∃ p ∈ g, p.1 = gridRowMin g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridRowMin]
    rcases foldl_proj_min_attained ps (·.1) p₀.1 with h | ⟨p, hp, hval⟩
    · exact ⟨p₀, by simp, h.symm⟩
    · exact ⟨p, by simp [hp], hval.symm⟩

/-- Compute a suitable `(offset, level)` so that the square of side
    `2 ^ level` placed at `offset` strictly contains the bounding box of
    `g` plus a 2-cell padding on each side. Returns `((0, 0), 0)` for the
    empty grid. -/
def gridFrame (g : Grid) : (Int × Int) × Nat :=
  match g with
  | []      => ((0, 0), 0)
  | _ :: _ =>
    let rMin := gridRowMin g
    let rMax := gridRowMax g
    let cMin := gridColMin g
    let cMax := gridColMax g
    -- 2-cell padding on each side
    let r0 := rMin - 2
    let c0 := cMin - 2
    let height := (rMax - rMin + 5).toNat   -- +1 for inclusive, +4 for padding
    let width  := (cMax - cMin + 5).toNat
    let side   := max height width
    let lvl    := MacroCell.ceilLog2 side
    ((r0, c0), lvl)

/-- For every live cell `p ∈ g`, the frame chosen by `gridFrame g` contains `p`:
    `inRegion p r0 c0 lvl` where `((r0, c0), lvl) = gridFrame g`. This is the
    containment bridge for the Grid↔MacroCell round trip (issue #2162, Gap 2). -/
theorem gridFrame_contains_g (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    let ((r0, c0), lvl) := gridFrame g
    MacroCell.inRegion p r0 c0 lvl := by
  cases g with
  | nil => simp at hp
  | cons p₀ ps =>
    have hrMin : gridRowMin (p₀ :: ps) ≤ p.1 := gridRowMin_le_of_mem _ _ hp
    have hrMax : p.1 ≤ gridRowMax (p₀ :: ps) := le_gridRowMax_of_mem _ _ hp
    have hcMin : gridColMin (p₀ :: ps) ≤ p.2 := gridColMin_le_of_mem _ _ hp
    have hcMax : p.2 ≤ gridColMax (p₀ :: ps) := le_gridColMax_of_mem _ _ hp
    have hrnn : gridRowMin (p₀ :: ps) ≤ gridRowMax (p₀ :: ps) :=
      gridRowMin_le_gridRowMax _ (List.cons_ne_nil _ _)
    have hcnn : gridColMin (p₀ :: ps) ≤ gridColMax (p₀ :: ps) :=
      gridColMin_le_gridColMax _ (List.cons_ne_nil _ _)
    simp only [gridFrame]
    set rMin := gridRowMin (p₀ :: ps)
    set rMax := gridRowMax (p₀ :: ps)
    set cMin := gridColMin (p₀ :: ps)
    set cMax := gridColMax (p₀ :: ps)
    set height := (rMax - rMin + 5).toNat
    set width := (cMax - cMin + 5).toNat
    set side := max height width
    set lvl := MacroCell.ceilLog2 side
    have hspec : (2 ^ lvl : Nat) ≥ side := MacroCell.ceilLog2_spec side
    have hh : height ≤ side := Nat.le_max_left _ _
    have hw : width ≤ side := Nat.le_max_right _ _
    have hnn_r : 0 ≤ rMax - rMin + 5 := by omega
    have hnn_c : 0 ≤ cMax - cMin + 5 := by omega
    unfold MacroCell.inRegion
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Convert a `Grid` to a `MacroCell`, returning the chosen offset so that
    `MacroCell.toGrid offset (gridToMacroCell g) = g`. -/
def gridToMacroCellWithOffset (g : Grid) : (Int × Int) × MacroCell :=
  let (off, lvl) := gridFrame g
  (off, MacroCell.buildFromGrid g off.1 off.2 lvl)

/-- Convert a `Grid` to a `MacroCell`, discarding the offset (defaulting to
    `(0, 0)` for the round trip). For round-trip purposes, prefer
    `gridToMacroCellWithOffset`. -/
def gridToMacroCell (g : Grid) : MacroCell :=
  (gridToMacroCellWithOffset g).2

/-! ## Sanity checks

We verify that the round trip `Grid -> MacroCell -> Grid` preserves the
small canonical patterns of `Conway.Life`. -/

-- Bounding-box helpers
#eval gridRowMin block
#eval gridRowMax block
#eval gridFrame block

-- The empty grid should give a level-0 dead leaf.
#eval gridToMacroCell ([] : Grid) |>.level
#eval gridToMacroCell ([] : Grid) |>.isEmpty

-- Round trip on the block: the MacroCell, then back to a grid at the
-- chosen offset, should equal `block`.
#eval
  let (off, mc) := gridToMacroCellWithOffset block
  (off, mc.level, mc.toGrid off == block)

#eval
  let (off, mc) := gridToMacroCellWithOffset blinker_h
  (off, mc.level, mc.toGrid off == blinker_h)

#eval
  let (off, mc) := gridToMacroCellWithOffset glider
  (off, mc.level, mc.toGrid off == glider)

#eval
  let (off, mc) := gridToMacroCellWithOffset beehive
  (off, mc.level, mc.toGrid off == beehive)

#eval
  let (off, mc) := gridToMacroCellWithOffset toad
  (off, mc.level, mc.toGrid off == toad)

end Life
end Conway
