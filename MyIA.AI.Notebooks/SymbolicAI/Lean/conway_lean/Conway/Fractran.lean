/-
Conway's FRACTRAN — A Universal Machine
John Horton Conway (1937-2020)

FRACTRAN is arguably the simplest known universal computational model.
A FRACTRAN program is a list of positive fractions. Given an input
integer N, the machine finds the first fraction f such that N*f is
an integer, replaces N with N*f, and repeats. Conway proved FRACTRAN
is Turing-complete.

Example — prime generation (Conway's 14-fraction program):
  Starting from 2, the powers of 2 in the output are exactly 2^p
  for each prime p: 2^2, 2^3, 2^5, 2^7, 2^11, ...
-/

namespace Conway

/-- A FRACTRAN instruction: fraction num/den stored as two Nats.
  den must be positive (ensured by construction). -/
structure Frac where
  num : Nat
  den : Nat
  h : den > 0
  deriving Repr

/-- Create a Frac from two Nats, proving den > 0 via decision -/
def frac (n d : Nat) (h : d > 0) : Frac := ⟨n, d, h⟩

/-- Check if n * (num/den) is a whole number -/
def fracMulNat (n : Nat) (f : Frac) : Bool :=
  n * f.num % f.den == 0

/-- One FRACTRAN step: find first applicable fraction, or halt -/
def fractranStep : List Frac → Nat → Option Nat
  | [], _ => none
  | f :: rest, n =>
    if fracMulNat n f then some (n * f.num / f.den)
    else fractranStep rest n

/-- Run FRACTRAN for k steps (or until halt) -/
def fractranRun (prog : List Frac) (n : Nat) : Nat → List Nat
  | 0 => [n]
  | k + 1 =>
    match fractranStep prog n with
    | some n' => n :: fractranRun prog n' k
    | none => [n]

/-- Helper: list of Nat pairs → list of Frac -/
def mkFracs : List (Nat × Nat) → List Frac
  | [] => []
  | (n, d) :: rest =>
    if h : d > 0 then ⟨n, d, h⟩ :: mkFracs rest
    else mkFracs rest -- skip invalid fractions

/-- Conway's prime-generating FRACTRAN program (14 fractions).
  From n=2, powers of 2 in the output are 2^p for each prime p. -/
def primeProgram : List Frac := mkFracs [
  (17, 91), (78, 85), (19, 51), (23, 38), (29, 33),
  (77, 19), (95, 23), (77, 19), (1, 17), (11, 13),
  (13, 11), (15, 2), (1, 7), (55, 1)]

-- Run a few steps of the prime generator from n=2
#eval fractranRun primeProgram 2 20

end Conway
