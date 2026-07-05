/-
  Stable Marriage - Definitions
  =============================

  English mirror of `StableMarriage/Definitions.lean` (FR-first canonical).
  Convention i18n Lean ratifiée par ai-01 (2026-07-04, #4980 comment-4881909354) :
  fichiers `.lean` distincts FR + EN siblings dans le même lake, les deux compilent.
  Drift-CI detectable : contenu non-docstring byte-identique entre siblings.
  Namespace sibling : `StableMarriage_en` (le FR canonique reste `StableMarriage`).
  Convention observée dans `GaleShapley_en.lean` / `Lattice_en.lean` :
  les imports intra-lake restent sur les fichiers FR canoniques
  (e.g. `import StableMarriage.Definitions`), seul `namespace StableMarriage`
  est renommé en `namespace StableMarriage_en`.
  Pas une traduction destructive : manual translation FR-first-from-origin
  (pas d'historique EN pré-Option A pour ce fichier) ; code tactique Lean
  byte-identique préservé verbatim, prose (header + sections + docstrings)
  traduite. Pattern identique c.238.2/#5362 (RepeatedGames), c.238.3/#5363
  (Minimax), c.238.4/#5419 (Shapley).

  See #4980. Part of #4208 (axe E).
-/

import Mathlib.Data.Finset.Basic

namespace StableMarriage_en


open Finset Function

variable {n : Nat} [NeZero n]

/-- A man is identified by `Fin n` -/
abbrev Man (n : Nat) := Fin n

/-- A woman is identified by `Fin n` -/
abbrev Woman (n : Nat) := Fin n

/--
Preference profile of a person over the opposite set.
Represented by a function assigning to each candidate its rank (smallest = preferred).
Strict preference means that the ranking function is injective.
-/
structure PrefProfile (n : Nat) [NeZero n] where
  /-- Men's preferences: each man ranks all women -/
  menPref : Fin n → Fin n → Fin n
  /-- Women's preferences: each woman ranks all men -/
  womenPref : Fin n → Fin n → Fin n
  /-- The ranking of each man is a permutation (bijective) -/
  menPref_bijective : ∀ m, Bijective (menPref m)
  /-- The ranking of each woman is a permutation (bijective) -/
  womenPref_bijective : ∀ w, Bijective (womenPref w)

namespace PrefProfile

variable {n : Nat} [NeZero n] (prof : PrefProfile n)

/--
Man `m` prefers woman `w1` to woman `w2` if and only if `w1`
has a smaller rank. Since `menPref m` is a bijection `Fin n → Fin n`,
a smaller rank means more preferred.
-/
def manPrefers (m : Fin n) (w1 w2 : Fin n) : Bool :=
  prof.menPref m w1 < prof.menPref m w2

/--
Woman `w` prefers man `m1` to man `m2` if and only if `m1`
has a smaller rank.
-/
def womanPrefers (w : Fin n) (m1 m2 : Fin n) : Bool :=
  prof.womenPref w m1 < prof.womenPref w m2

/--
Man `m` strictly prefers woman `w1` to woman `w2`.
Prop-valued version for theorem statements.
-/
def ManPrefers (m : Fin n) (w1 w2 : Fin n) : Prop :=
  prof.menPref m w1 < prof.menPref m w2

/--
Woman `w` strictly prefers man `m1` to man `m2`.
-/
def WomanPrefers (w : Fin n) (m1 m2 : Fin n) : Prop :=
  prof.womenPref w m1 < prof.womenPref w m2

end PrefProfile

/--
A matching is a bijection from men to women
(perfect matching).
-/
structure Matching (n : Nat) [NeZero n] where
  /-- Associates each man to his matched woman -/
  spouse : Fin n → Fin n
  /-- The matching is bijective (each woman is matched to exactly one man) -/
  bijective : Bijective spouse

namespace Matching

variable {n : Nat} [NeZero n] (μ : Matching n)

/-- Retrieves the inverse: which man is matched to woman `w` -/
noncomputable def inverse (w : Fin n) : Fin n :=
  (Equiv.ofBijective μ.spouse μ.bijective).symm w

end Matching

/--
Blocking pair for matching `μ` under preference profile `prof`:
a man `m` and a woman `w` who mutually prefer each other to their current
partners.
-/
def IsBlockingPair (prof : PrefProfile n) (μ : Matching n)
    (m : Fin n) (w : Fin n) : Prop :=
  prof.ManPrefers m w (μ.spouse m) ∧
  prof.WomanPrefers w m (μ.inverse w)

/--
A matching is stable if and only if no blocking pair exists.
-/
def IsStable (prof : PrefProfile n) (μ : Matching n) : Prop :=
  ∀ m w, ¬ IsBlockingPair prof μ m w

/--
A matching is man-optimal if and only if each man
gets his best possible partner among all stable matchings.
-/
def IsManOptimal (prof : PrefProfile n) (μ : Matching n) : Prop :=
  IsStable prof μ ∧
  ∀ μ' : Matching n, IsStable prof μ' →
    ∀ m : Fin n, prof.menPref m (μ.spouse m) ≤ prof.menPref m (μ'.spouse m)

end StableMarriage_en
