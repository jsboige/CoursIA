/-
  Mariage stable — Définitions
  =============================

  Types et définitions fondamentaux pour le problème du mariage stable.
  On modélise n hommes et n femmes (tous deux via `Fin n`), chacun muni d'un
  ordre de préférence strict sur l'ensemble opposé.

  Un couplage (matching) est une bijection entre hommes et femmes.
  Un couplage est stable si et seulement si aucune paire bloquante
  (blocking pair) n'existe.

  Convention i18n (cf #4980) : en-têtes et docstrings en français,
  noms de symboles Lean et tactiques préservés en anglais (compatibilité Mathlib).
-/

import Mathlib.Data.Finset.Basic

namespace StableMarriage

open Finset Function

variable {n : Nat} [NeZero n]

/-- Un homme est identifié par `Fin n` -/
abbrev Man (n : Nat) := Fin n

/-- Une femme est identifiée par `Fin n` -/
abbrev Woman (n : Nat) := Fin n

/--
Profil de préférence d'une personne sur l'ensemble opposé.
Représenté par une fonction associant à chaque candidat son rang (plus petit = préféré).
La préférence stricte signifie que la fonction de classement est injective.
-/
structure PrefProfile (n : Nat) [NeZero n] where
  /-- Préférences des hommes : chaque homme classe toutes les femmes -/
  menPref : Fin n → Fin n → Fin n
  /-- Préférences des femmes : chaque femme classe tous les hommes -/
  womenPref : Fin n → Fin n → Fin n
  /-- Le classement de chaque homme est une permutation (bijectif) -/
  menPref_bijective : ∀ m, Bijective (menPref m)
  /-- Le classement de chaque femme est une permutation (bijectif) -/
  womenPref_bijective : ∀ w, Bijective (womenPref w)

namespace PrefProfile

variable {n : Nat} [NeZero n] (prof : PrefProfile n)

/--
L'homme `m` préfère la femme `w1` à la femme `w2` si et seulement si `w1`
a un rang plus petit. Puisque `menPref m` est une bijection `Fin n → Fin n`,
un rang plus petit signifie plus préférée.
-/
def manPrefers (m : Fin n) (w1 w2 : Fin n) : Bool :=
  prof.menPref m w1 < prof.menPref m w2

/--
La femme `w` préfère l'homme `m1` à l'homme `m2` si et seulement si `m1`
a un rang plus petit.
-/
def womanPrefers (w : Fin n) (m1 m2 : Fin n) : Bool :=
  prof.womenPref w m1 < prof.womenPref w m2

/--
L'homme `m` préfère strictement la femme `w1` à la femme `w2`.
Version Prop-valued pour les énoncés de théorèmes.
-/
def ManPrefers (m : Fin n) (w1 w2 : Fin n) : Prop :=
  prof.menPref m w1 < prof.menPref m w2

/--
La femme `w` préfère strictement l'homme `m1` à l'homme `m2`.
-/
def WomanPrefers (w : Fin n) (m1 m2 : Fin n) : Prop :=
  prof.womenPref w m1 < prof.womenPref w m2

end PrefProfile

/--
Un couplage (matching) est une bijection des hommes vers les femmes
(couplage parfait).
-/
structure Matching (n : Nat) [NeZero n] where
  /-- Associe chaque homme à sa femme appariée -/
  spouse : Fin n → Fin n
  /-- Le couplage est bijectif (chaque femme est appariée à exactement un homme) -/
  bijective : Bijective spouse

namespace Matching

variable {n : Nat} [NeZero n] (μ : Matching n)

/-- Récupère l'inverse : quel homme est apparié à la femme `w` -/
noncomputable def inverse (w : Fin n) : Fin n :=
  (Equiv.ofBijective μ.spouse μ.bijective).symm w

end Matching

/--
Paire bloquante pour le couplage `μ` sous le profil de préférence `prof` :
un homme `m` et une femme `w` qui se préfèrent mutuellement à leurs partenaires
actuels.
-/
def IsBlockingPair (prof : PrefProfile n) (μ : Matching n)
    (m : Fin n) (w : Fin n) : Prop :=
  prof.ManPrefers m w (μ.spouse m) ∧
  prof.WomanPrefers w m (μ.inverse w)

/--
Un couplage est stable si et seulement si aucune paire bloquante n'existe.
-/
def IsStable (prof : PrefProfile n) (μ : Matching n) : Prop :=
  ∀ m w, ¬ IsBlockingPair prof μ m w

/--
Un couplage est optimal pour les hommes si et seulement si chaque homme
obtient sa meilleure partenaire possible parmi tous les couplages stables.
-/
def IsManOptimal (prof : PrefProfile n) (μ : Matching n) : Prop :=
  IsStable prof μ ∧
  ∀ μ' : Matching n, IsStable prof μ' →
    ∀ m : Fin n, prof.menPref m (μ.spouse m) ≤ prof.menPref m (μ'.spouse m)

end StableMarriage
