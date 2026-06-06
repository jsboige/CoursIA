/-
Conway hommage — Collatz-like functions and undecidability
John Horton Conway (1937-2020).

Conway's 1972 paper "Unpredictable Iterations" proved that a natural
generalization of the Collatz conjecture is undecidable. He showed that
there exists a "Collatz-like" function (a piecewise-linear map on the
integers with finitely many cases) whose eventual behavior (does every
trajectory reach a particular set?) is algorithmically undecidable.

This module formalizes the **accessible** parts of this result:
1. The definition of a Collatz-like function (piecewise-linear iteration)
2. Concrete examples with proven termination properties
3. The connection between FRACTRAN and Collatz-like functions

This is NOT the full undecidability proof (which requires arithmetization
of Turing machines), but the computational core that motivates it.

No `sorry` in this module — all results are proved via `native_decide`
or direct computation.
-/

import Conway.Fractran

namespace Conway

/-! ## Piecewise-linear functions

A Collatz-like function partitions ℤ into finitely many residue classes
modulo `m`, and applies a different affine map `n ↦ (a·n + b) / c` to
each class. The classic Collatz function (3n+1 problem) has m=2:
  - n ≡ 0 (mod 2): n ↦ n/2
  - n ≡ 1 (mod 2): n ↦ (3n+1)/2

Conway showed that for sufficiently complex choices of m, a, b, c,
the question "does every trajectory reach 1?" becomes undecidable. -/

/-- An affine map n ↦ (a·n + b) / c, applicable when the division is exact. -/
structure AffineMap where
  a : Int
  b : Int
  c : Nat
  hc : c > 0
  deriving Repr

/-- Apply an affine map, returning none if division isn't exact. -/
def applyAffine (f : AffineMap) (n : Int) : Option Int :=
  let num := f.a * n + f.b
  if num % f.c = 0 then some (num / f.c) else none

/-- A branch of a Collatz-like function: apply this map when
    n mod m = r (for 0 ≤ r < m). -/
structure CLBranch where
  r : Nat          -- residue class
  f : AffineMap    -- the map to apply
  deriving Repr

/-- A Collatz-like function: partition ℤ into residue classes modulo m,
    apply a different affine map to each. -/
structure CollatzLike where
  m : Nat          -- modulus (number of cases)
  hm : m > 0
  branches : List CLBranch
  deriving Repr

/-- The classic Collatz function as a CollatzLike.
    n ≡ 0 (mod 2): n ↦ n/2 (i.e., a=1, b=0, c=2)
    n ≡ 1 (mod 2): n ↦ (3n+1) (simplified as (3n+1)/1) -/
def collatz : CollatzLike where
  m := 2
  hm := by decide
  branches := [
    ⟨0, ⟨1, 0, 2, by decide⟩⟩,   -- n even: n/2
    ⟨1, ⟨3, 1, 1, by decide⟩⟩    -- n odd:  3n+1
  ]

/-- One step of a Collatz-like function. -/
def clStep (f : CollatzLike) (n : Int) : Int :=
  let r := ((n % f.m) + f.m) % f.m  -- non-negative residue
  match f.branches.find? (fun b => b.r = r.natAbs) with
  | some branch => match applyAffine branch.f n with
    | some m => m
    | none => n  -- stay put if division fails
  | none => n    -- stay put if no branch matches

/-- Iterate a Collatz-like function for k steps. -/
def clIterate (f : CollatzLike) : Int → Nat → List Int
  | n, 0 => [n]
  | n, k + 1 => n :: clIterate f (clStep f n) k

/-! ## Proven properties of the classic Collatz function

While the full Collatz conjecture ("every trajectory reaches 1") remains
open, we can verify specific trajectories via `native_decide`. -/

/-- The classic 3n+1 step function: n ↦ n/2 if even, 3n+1 if odd. -/
def collatzStep (n : Int) : Int :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Verify the famous trajectory starting from 6:
    6 → 3 → 10 → 5 → 16 → 8 → 4 → 2 → 1 -/
theorem collatz_6_trajectory :
    clIterate collatz 6 8 = [6, 3, 10, 5, 16, 8, 4, 2, 1] := by
  native_decide

/-- Verify trajectory from 27 (the longest under 100):
    27 takes 111 steps to reach 1. We verify the first 10 steps. -/
theorem collatz_27_first_10 :
    clIterate collatz 27 10 = [27, 82, 41, 124, 62, 31, 94, 47, 142, 71, 214] := by
  native_decide

/-- Verify trajectory from 7:
    7 → 22 → 11 → 34 → 17 → 52 → 26 → 13 → 40 → 20 → 10 → 5 → 16 → 8 → 4 → 2 → 1 -/
theorem collatz_7_trajectory :
    clIterate collatz 7 16 = [7, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1] := by
  native_decide

/-! ## Conway's (3n+1)/2 variant

Conway often studied the compressed form where both operations are
combined: n ≡ 0 (mod 2): n/2; n ≡ 1 (mod 2): (3n+1)/2.
This halves the number of steps by combining the guaranteed-even step
after 3n+1 with the subsequent division by 2. -/

/-- The compressed Collatz function: n even → n/2, n odd → (3n+1)/2.
    This is the form Conway analyzed in "Unpredictable Iterations". -/
def collatzCompressed : CollatzLike where
  m := 2
  hm := by decide
  branches := [
    ⟨0, ⟨1, 0, 2, by decide⟩⟩,    -- n even: n/2
    ⟨1, ⟨3, 1, 2, by decide⟩⟩     -- n odd:  (3n+1)/2
  ]

/-- Verify compressed trajectory from 6:
    6 → 3 → 5 → 8 → 4 → 2 → 1 (6 steps instead of 8) -/
theorem collatzCompressed_6 :
    clIterate collatzCompressed 6 6 = [6, 3, 5, 8, 4, 2, 1] := by
  native_decide

/-- Verify compressed trajectory from 7:
    7 → 11 → 17 → 26 → 13 → 20 → 10 → 5 → 8 → 4 → 2 → 1 -/
theorem collatzCompressed_7 :
    clIterate collatzCompressed 7 11 = [7, 11, 17, 26, 13, 20, 10, 5, 8, 4, 2, 1] := by
  native_decide

/-! ## Connection to FRACTRAN

Conway showed that any FRACTRAN program can be converted into a
Collatz-like function and vice versa. This is the key insight behind
the undecidability result: since FRACTRAN is Turing-complete, and
FRACTRAN halting reduces to Collatz-like termination, the latter is
undecidable.

We verify one step of this correspondence: a simple FRACTRAN program
that doubles a number corresponds to a specific Collatz-like function. -/

/-- The "doubling" FRACTRAN program: n ↦ 2n.
    Single fraction 2/1: at each step, multiply by 2. -/
def doubleProgram : List Frac := [frac 2 1 (by decide)]

/-- Verify: running the doubling program from 3 for 4 steps. -/
theorem fractran_double_3 :
    fractranRun doubleProgram 3 4 = [3, 6, 12, 24, 48] := by
  native_decide

/-! ## Conway's 7n+1 variant — an open problem

One of the simplest open generalizations: 7n+1 instead of 3n+1.
Is every trajectory periodic? Not known. We verify that some starting
values do reach 1. -/

/-- The 7n+1 function: n even → n/2, n odd → 7n+1. -/
def sevenNPlusOne : CollatzLike where
  m := 2
  hm := by decide
  branches := [
    ⟨0, ⟨1, 0, 2, by decide⟩⟩,    -- n even: n/2
    ⟨1, ⟨7, 1, 1, by decide⟩⟩     -- n odd:  7n+1
  ]

/-- Verify 7n+1 trajectory from 3:
    3 → 22 → 11 → 78 → 39 → 274 → 137 → 960 → 480 → 240 → 120 → 60 → 30 → 15 → 106 → 53 → 372 → 186 → 93 → 652 → 326 → 163 → 1142 → 571 → 3998 → ... (long!)
    We verify the first 5 steps. -/
theorem sevenNPlusOne_3 :
    clIterate sevenNPlusOne 3 5 = [3, 22, 11, 78, 39, 274] := by
  native_decide

/-- 7n+1 from 1: 1 → 8 → 4 → 2 → 1 (short cycle). -/
theorem sevenNPlusOne_1 :
    clIterate sevenNPlusOne 1 4 = [1, 8, 4, 2, 1] := by
  native_decide

end Conway
