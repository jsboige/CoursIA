/-
Conway's Look-and-Say Sequence
John Horton Conway (1937-2020)

The look-and-say sequence starts with "1". Each subsequent term describes the
previous term by reading off consecutive digit groups:
  1 → 11 → 21 → 1211 → 111221 → 312211 → 13112221 → ...

Conway proved remarkable properties:
- The ratio |a(n+1)| / |a(n)| converges to Conway's constant λ ≈ 1.303577...
- λ is the unique positive real root of a degree-71 polynomial
- The sequence splits into exactly 92 "atomic elements" (named after chemical elements)

This file formalizes the sequence generation and verifies the first terms.
-/

import Mathlib.Data.List.Basic

namespace Conway

/-- Split a number into its decimal digits (most significant first).
  1211 → [1, 2, 1, 1]  -/
def natToDigits (n : Nat) : List Nat :=
  if n = 0 then []
  else natToDigits (n / 10) ++ [n % 10]
  termination_by n
  decreasing_by omega

/-- Convert a list of digits (most significant first) to a Nat.
  [1, 2, 1, 1] → 1211 -/
def digitsToNat : List Nat → Nat
  | [] => 0
  | d :: ds => d * 10 ^ ds.length + digitsToNat ds

/-- Run-length encode a list: group consecutive equal elements.
  [1, 1, 2, 2, 2, 1] → [(2, 1), (3, 2), (1, 1)]
  Uses fuel to satisfy the termination checker. -/
def runLengthAux : Nat → List Nat → List (Nat × Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, a :: as =>
    match as.span (· = a) with
    | (eqs, rest) => (eqs.length + 1, a) :: runLengthAux fuel rest

/-- Run-length encode a list (wrapper with sufficient fuel). -/
def runLength (l : List Nat) : List (Nat × Nat) :=
  runLengthAux (l.length + 1) l

/-- Flatten (count, digit) pairs into a digit list: [(2,1), (3,2)] → [2,1,3,2] -/
def flattenPairs : List (Nat × Nat) → List Nat
  | [] => []
  | (count, digit) :: rest =>
    natToDigits count ++ [digit] ++ flattenPairs rest

/-- One step of the look-and-say transformation.
  Read digits left-to-right, output run-length encoding as a number. -/
def lookAndSayStep (n : Nat) : Nat :=
  if n = 0 then 0
  else digitsToNat (flattenPairs (runLength (natToDigits n)))

/-- Generate the n-th look-and-say number (0-indexed, seed = 1) -/
def lookAndSay : Nat → Nat
  | 0 => 1
  | n + 1 => lookAndSayStep (lookAndSay n)

-- Verify the first 6 terms of the look-and-say sequence
#eval! lookAndSay 0  -- 1
#eval! lookAndSay 1  -- 11
#eval! lookAndSay 2  -- 21
#eval! lookAndSay 3  -- 1211
#eval! lookAndSay 4  -- 111221
#eval! lookAndSay 5  -- 312211

end Conway
