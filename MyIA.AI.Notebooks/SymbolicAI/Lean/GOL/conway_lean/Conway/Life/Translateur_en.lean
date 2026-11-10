/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway's Game of Life - Translators: finite families and impossibility certificates

Formal companion of the `GOL-08-Loi-II-Translateur-Life.ipynb` notebook
(GOL-08b): Law II of the Game of Life - "a pattern that translates by `v`
in `p` generations (a translator) cannot exceed the speed of light `c`
(1 cell/generation), nor `c/2` for orthogonal displacement" - is here
instantiated on **explicitly enumerated finite families**, mirroring the
Python synthesizer of the notebook.

The family `family b k` is the (list of) all patterns of 1 to `k` cells
inside the `b x b` box (lower-left corner at the origin). The certificate
`noTranslator b k v p = true` - proved by `decide` - states that **no**
pattern of the family is a translator with vector `v` and period `p`. The
kernel literally evaluates every candidate: this is a formal proof of
exhaustive failure, not a statistical test.

Formal instances (cells `Int × Int`, row/column coordinates of the
`Conway.Life` module, lexicographic order):

- `translator_witness_glider`: the family (3, 5) - 381 patterns of 1 to 5
  cells in the 3x3 box - contains a (1, -1)/4 translator: the glider of
  `Conway.Life`, recovered by enumeration (the kernel stops at the first
  witness, exactly like the notebook's synthesizer).
- `no_translator_two_thirds_c`: in that same family (3, 5), no pattern
  translates by (2, 0) in 3 generations - speed 2/3 c, beyond the
  orthogonal limit c/2. The glider itself is in the family and does not
  escape the verdict.
- `no_small_orthogonal_translator`: the family (3, 3) - 129 patterns of at
  most 3 cells - contains no (0, 2)/4 translator; yet the LWSS spaceship of
  `Conway.Life.Spaceships` (9 cells, outside the family by size alone)
  achieves exactly that displacement (`lwss_spaceship`). The family's
  boundary is size, not the rule.

Honest boundary against the Python notebook: the Python instances enumerate
the 5x5 box up to 5 cells (68,405 candidates); the `decide` kernel
reduction budget bounds us here to the 3x3 box (381 and 129 candidates).
The formal statements are strictly weaker than their Python counterparts,
and remain so until a more generous reduction ceiling is available. No
statement below claims to cover the 5x5 box.

i18n convention (EPIC #4980): this file is the EN mirror of the FR
canonical `Translateur.lean` (consumer twin, cf `Spaceships_en.lean`).
The body signatures, proofs and tactics remain byte-identical between the
two files; only the docstrings and comments differ.

This module is fully proven (no `sorry`).
-/

import Conway.Life

namespace Conway_en
open Conway
namespace Life_en
open Life

/-! ## The box and its family

`boxCells b` enumerates the `b * b` cells of the `b x b` box in
lexicographic order - the same canonical order as the grids of
`Conway.Life`. `family b k` takes its sublists of 1 to `k` cells: each
element is already sorted and duplicate-free (a sublist of a sorted
`Nodup` list), hence canonical without going through `sortDedup`.
-/

/-- The cells of the `b x b` box (origin at the upper-left corner), in
    lexicographic order. By construction the list is sorted and `Nodup`. -/
def boxCells (b : Nat) : List (Int × Int) :=
  (List.range b).flatMap fun i => (List.range b).map fun j => ((i : Int), (j : Int))

/-- The cells of the box lie in `[0, b)`: every point of `boxCells b` has both
    coordinates in the interval. One direction only - the one `family_scope`
    needs; the converse is not stated. -/
theorem mem_boxCells {b : Nat} {p : Int × Int} (hp : p ∈ boxCells b) :
    0 ≤ p.1 ∧ p.1 < b ∧ 0 ≤ p.2 ∧ p.2 < b := by
  obtain ⟨x, y⟩ := p
  simp only [boxCells, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨i, hi, j, hj, hxy⟩ := hp
  -- The `do` block produced by `simp` is a `List.bind`: it has to be unfolded
  -- before `List.mem_range` can apply (measured, not assumed).
  simp only [List.pure_def, List.bind_eq_flatMap, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hi hj
  obtain ⟨a, ha, rfl⟩ := hi
  obtain ⟨c, hc, rfl⟩ := hj
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨hx, hy⟩ := hxy
  subst hx
  subst hy
  omega

/-- The family of patterns of 1 to `k` cells in the `b x b` box: all the
    non-empty sublists of `boxCells b` of length at most `k`. Every element
    is a canonical `Grid` (sorted, `Nodup`). -/
def family (b k : Nat) : List Grid :=
  ((boxCells b).sublists).filter fun g => decide (0 < g.length ∧ g.length ≤ k)

/-- Scope of the family: every covered pattern lives inside the box. This
    lemma is what makes the certificate precise - "no translator **in the
    `b x b` box with at most `k` cells**", no more, no less. -/
theorem family_scope {b k : Nat} {g : Grid} (hg : g ∈ family b k)
    {p : Int × Int} (hp : p ∈ g) :
    0 ≤ p.1 ∧ p.1 < b ∧ 0 ≤ p.2 ∧ p.2 < b := by
  obtain ⟨hg', -⟩ := List.mem_filter.1 hg
  exact mem_boxCells ((List.mem_sublists.1 hg').subset hp)

/-! ## The synthesizer and its certificate

Two boolean predicates, decidable by the kernel, that walk the family
exactly like the `synthetiseur` of notebook GOL-08: `hasTranslator` looks
for a witness (stopping at the first one found), `noTranslator` records
the exhaustive failure. Both are proofs when the kernel reduces them to
`true`.
-/

/-- Impossibility certificate: no pattern of `family b k` is a spaceship
    with vector `v` and period `p`. -/
def noTranslator (b k : Nat) (v : Int × Int) (p : Nat) : Bool :=
  (family b k).all fun g => !isSpaceship g p v

/-- Synthesizer: the family `family b k` contains a spaceship with vector
    `v` and period `p`. -/
def hasTranslator (b k : Nat) (v : Int × Int) (p : Nat) : Bool :=
  (family b k).any fun g => isSpaceship g p v

/-! ## Formal instances

Three `decide`s, each a complete kernel evaluation of the family. Family
sizes: (3, 5) = 381 patterns, (3, 3) = 129 patterns.
-/

/-- The glider of `Conway.Life` is indeed a pattern of the family (3, 5):
    5 cells inside the 3x3 box. The witness of the next `decide` is
    therefore a legitimate element of the enumerated family. -/
theorem glider_mem_family : glider ∈ family 3 5 := by decide

set_option maxHeartbeats 1000000 in
/-- **Witness** - the family (3, 5) contains a (1, -1)/4 translator: it is
    the glider, recovered by kernel enumeration (stopping at the first
    witness). Formal counterpart of the notebook's case (3, 5, 1, 1, 4)
    (Python's downward dy = Lean's negative dy). -/
theorem translator_witness_glider : hasTranslator 3 5 (1, -1) 4 = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- **Impossibility** - in the family (3, 5) - which contains the glider -
    no pattern translates by (2, 0) in 3 generations: speed 2/3 c, beyond
    the orthogonal limit c/2 of Law II. Counterpart of the notebook's case
    (5, 5, 2, 0, 3), bounded here to the 3x3 box. -/
theorem no_translator_two_thirds_c : noTranslator 3 5 (2, 0) 3 = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- **Family boundary** - the family (3, 3) (at most 3 cells) contains no
    (0, 2)/4 translator, while the LWSS - 9 cells, outside the family by
    size alone - achieves exactly that displacement
    (`Conway.Life.Spaceships.lwss_spaceship`). Counterpart of the
    notebook's contrast (5, 5, 2, 0, 4). -/
theorem no_small_orthogonal_translator : noTranslator 3 3 (0, 2) 4 = true := by
  decide

end Life_en
end Conway_en
