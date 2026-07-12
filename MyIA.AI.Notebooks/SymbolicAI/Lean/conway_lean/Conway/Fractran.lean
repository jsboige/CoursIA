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

/-
  `Conway.Fractran` — FRACTRAN, une machine universelle
  ======================================================
  FRACTRAN est sans doute le modèle de calcul universel connu le plus
  simple. Un programme FRACTRAN est une liste de fractions positives.
  Étant donné un entier N en entrée, la machine trouve la première
  fraction f telle que N*f soit un entier, remplace N par N*f, puis
  recommence. Conway a démontré que FRACTRAN est Turing-complet.

  Exemple — génération des nombres premiers (programme de Conway à
  14 fractions) :
    À partir de 2, les puissances de 2 dans la sortie sont exactement
    2^p pour chaque nombre premier p : 2^2, 2^3, 2^5, 2^7, 2^11, ...

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN), variante pragmatique
  c.379 (deux blocs `/` top-level distincts, sans `---` interne, analogue
  c.376/c.377/c.378) : le bloc EN existant est préservé verbatim ci-dessus,
  le bloc FR miroir est ajouté juste après sans séparateur `---`. Convention
  sibling pair (`<Foo>_en.lean` à part) réservée aux modules de substance
  (cf c.374 `Astar_en.lean`) ; pour les modules de formalisation comme
  `Fractran`, l'inline FR+EN est le bon compromis (peu de code, deux langues
  côte à côte).

  Cross-références : c.366 `Conway.lean` racine bilingue (MERGED),
  c.367 Grothendieck hommage (MERGED), c.373 `Knots.lean` racine bilingue,
  c.374 `Astar.lean` sibling pair, c.375 `Knots` sub-modules bilingues,
  c.376 `Knots/Invariant` bilingue 6/6 (saturation locale du lac `knot_lean`),
  c.377 `Conway/MathlibMap` bilingue (premier sous-module rollout
  `conway_lean`, PIVOT L335 strict), c.378 `Conway/LookAndSay` bilingue
  (suite rollout `conway_lean` Phase 1+), **c.379 `Conway/Fractran`
  bilingue (suite rollout `conway_lean` Phase 1+, machine universelle
  Turing-complète)**.
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
