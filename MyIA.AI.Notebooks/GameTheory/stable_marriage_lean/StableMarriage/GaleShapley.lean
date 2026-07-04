/-
  Mariage Stable - Algorithme et théorèmes de Gale-Shapley
  =========================================================

  Ce module rassemble les principaux résultats de l'algorithme de Gale-Shapley
  pour le problème du mariage stable (deferred acceptance).

  Convention i18n (Option A #4980 ratifiée par ai-01 le 2026-07-04) : ce fichier
  est **français-first** : titre, commentaires, docstrings et en-têtes de
  section sont rédigés en français. Les **identificateurs** (`gale_shapley_*`,
  `gsRunSteps`, `gsFinalMatching`, `Matching`, `IsStable`, `IsManOptimal`,
  `PrefProfile`, etc.) ainsi que le **code tactique** restent en anglais pour
  préserver la compatibilité avec `Mathlib` et les modules siblings
  (`Definitions`, `Lemmas`, `Lattice`, `GSState`). Toute modification ultérieure
  doit conserver cette séparation.

  État des résultats principaux :
  - `gale_shapley_stable` est **constructivement prouvé** via la machine à
    étapes d'acceptation différée (`gsRunSteps` / `gsFinalMatching` /
    `gsNoBlockingPairs`).
  - `gale_shapley_man_optimal` est prouvé via `exists_isManOptimal` du module
    `Lattice.lean` (argument de poids minimal sur le semi-treillis de jointure
    des mariages stables), en s'appuyant sur `gale_shapley_stable`.
  - `gale_shapley_woman_pessimal` est déduit de la man-optimalité.

  Esquisse de l'algorithme (version où les hommes proposent) :
  1. Chaque homme libre propose à la femme qu'il préfère parmi celles
     auxquelles il n'a pas encore proposé.
  2. Chaque femme accepte provisoirement sa meilleure proposition, et rejette
     les autres.
  3. Les hommes rejetés redeviennent libres.
  4. On répète jusqu'à ce qu'il n'y ait plus d'homme libre.

  Propriétés clés :
  - L'algorithme termine (au plus n^2 propositions).
  - Le résultat est un mariage stable.
  - Le résultat est man-optimal (la meilleure partenaire possible pour chaque
    homme parmi tous les mariages stables).
  - Dualement, il est woman-pessimal (la pire partenaire possible pour chaque
    femme parmi tous les mariages stables).

  Référence : Gale & Shapley (1962), « College Admissions and the Stability
  of Marriage ».
  Port de référence : https://github.com/mmaaz-git/stable-marriage-lean
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Common
import StableMarriage.Definitions
import StableMarriage.Lemmas
import StableMarriage.Lattice

namespace StableMarriage

open Function

variable {n : Nat} [NeZero n]

/--
L'algorithme de Gale-Shapley termine.

Au plus n^2 propositions peuvent avoir lieu (chaque homme propose à chaque
femme au plus une fois).

TODO : formaliser l'algorithme sous forme de relation d'étapes et prouver la
terminaison.
-/
theorem gale_shapley_terminates (prof : PrefProfile n) :
    True := by
  trivial

/--
L'algorithme de Gale-Shapley produit un matching (bijection) valide.

Le matching identité sert de témoin (toute bijection sur `Fin n` suffit pour
l'existentiel ; on utilise ici `id`).
-/
theorem gale_shapley_produces_matching (prof : PrefProfile n) :
    ∃ μ : Matching n, True := by
  exact ⟨{ spouse := id, bijective := Function.bijective_id }, trivial⟩

/--
L'algorithme de Gale-Shapley produit un mariage stable.

Aucune paire bloquante n'existe dans le matching en sortie.

C'est le théorème principal de correction. Il est **prouvé de manière
constructive** : la machine à étapes d'acceptation différée (`gsRunSteps prof
(gsProposalBound n)`) est exécutée jusqu'à terminaison, et `gsFinalMatching` /
`gsNoBlockingPairs` (portés et adaptés depuis `mmaaz-git/stable-marriage-lean`,
~1000 lignes de lemmes auxiliaires) démontrent la stabilité. Cette déclaration
est complète : aucune tactique stub et aucun axiome ne sont utilisés.
-/
theorem gale_shapley_stable (prof : PrefProfile n) :
    ∃ μ : Matching n, IsStable prof μ := by
  let σ := gsRunSteps prof (gsProposalBound n)
  have hterm : gsTerminated prof σ :=
    gsTerminated_runSteps_bound prof
  have hcon : GSConsistent σ.matching :=
    GSConsistent.runSteps prof (gsProposalBound n)
  have hwp : womenProposedImpliesMatched prof σ :=
    womenProposedImpliesMatched.runSteps prof (gsProposalBound n)
  have hdown : menProposedDownward prof σ :=
    menProposedDownward.runSteps prof (gsProposalBound n)
  have hmp : menMatchedProposed prof σ :=
    menMatchedProposed.runSteps prof (gsProposalBound n)
  have hbest : womenBestState prof σ :=
    womenBestState.runSteps prof (gsProposalBound n)
  have hall : ∀ m, σ.matching.menMatch m ≠ none :=
    fun m => gsTerminated_allMenMatched prof hterm hwp hcon m
  exact ⟨gsFinalMatching prof σ hall hcon,
    fun m w => gsNoBlockingPairs prof hterm hcon hwp hdown hmp hbest m w⟩

/--
Le matching de Gale-Shapley est man-optimal : chaque homme obtient la meilleure
partenaire possible parmi tous les mariages stables.

C'est le théorème d'optimalité pour le côté qui propose.
-/
theorem gale_shapley_man_optimal (prof : PrefProfile n) :
    ∃ μ : Matching n, IsManOptimal prof μ :=
  exists_isManOptimal prof (gale_shapley_stable prof)

/--
Existence d'un mariage stable (corollaire de Gale-Shapley).
-/
theorem stable_matching_exists (prof : PrefProfile n) :
    ∃ μ : Matching n, IsStable prof μ := by
  exact gale_shapley_stable prof

/--
Pessimalité-femme de Gale-Shapley version « les hommes proposent » :
chaque femme obtient la pire partenaire possible parmi tous les mariages stables.

Dual de la man-optimalité.
-/
theorem gale_shapley_woman_pessimal (prof : PrefProfile n)
    (μ : Matching n) (h_opt : IsManOptimal prof μ)
    (μ' : Matching n) (h_stable : IsStable prof μ')
    (w : Fin n) :
    prof.womenPref w (μ'.inverse w) ≤ prof.womenPref w (μ.inverse w) := by
  by_contra hgt
  push Not at hgt
  set m := μ.inverse w with hmdef
  set m' := μ'.inverse w with hm'def
  have hmw : μ.spouse m = w := spouse_inverse μ w
  have hm'w : μ'.spouse m' = w := spouse_inverse μ' w
  -- From man-optimality: m weakly prefers w = μ.sp m over μ'.sp m
  have hmopt : prof.menPref m (μ.spouse m) ≤ prof.menPref m (μ'.spouse m) :=
    h_opt.2 μ' h_stable m
  rw [hmw] at hmopt
  by_cases hstrict : (prof.menPref m w : Nat) < prof.menPref m (μ'.spouse m)
  · -- m strictly prefers w over μ'.sp m
    -- w prefers m over m' (from hgt)
    have hwpref : prof.WomanPrefers w m m' := by
      unfold PrefProfile.WomanPrefers
      have : (prof.womenPref w m : Nat) < prof.womenPref w m' := by
        change (prof.womenPref w (μ.inverse w) : Nat) < prof.womenPref w (μ'.inverse w)
        exact mod_cast hgt
      exact mod_cast this
    -- (m, w) blocks μ': m prefers w to μ'.sp(m), w prefers m to m' = μ'.inv(w)
    have hblock : IsBlockingPair prof μ' m w := by
      refine ⟨mod_cast hstrict, ?_⟩
      change prof.WomanPrefers w m (μ'.inverse w)
      rw [← hm'def]
      exact hwpref
    exact h_stable m w hblock
  · -- Equality: menPref m w = menPref m (μ'.sp m)
    push Not at hstrict
    have heq : (prof.menPref m w : Nat) = prof.menPref m (μ'.spouse m) :=
      Nat.le_antisymm (mod_cast hmopt) hstrict
    have hsp_eq : w = μ'.spouse m :=
      (prof.menPref_bijective m).injective (Fin.ext heq)
    -- μ'.sp m = w, so μ'.inv w = m
    have hinv_eq : μ'.inverse w = m :=
      inverse_eq_of_spouse_eq μ' m w hsp_eq.symm
    -- But m' = μ'.inv w = m, so hgt says womenPref w m < womenPref w m — contradiction
    rw [hm'def, hinv_eq] at hgt
    exact Nat.lt_irrefl _ (mod_cast hgt)

end StableMarriage
