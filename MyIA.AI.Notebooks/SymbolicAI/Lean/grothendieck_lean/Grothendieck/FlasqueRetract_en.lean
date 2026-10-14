/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Grothendieck tribute — Part 81 (EN sibling of Grothendieck/FlasqueRetract.lean):
flasqueness descends to retracts.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

Part 79 defined flasqueness at the level of sites
(Grothendieck.Flasque, IsFlasqueSieves): any compatible family on any
sieve admits an amalgamation. Part 80 (branch
feature/grothendieck-partie-80) studied stability under isomorphisms
and products. This part generalizes the first link: flasqueness descends
along a one-sided retraction.

  - isFlasqueSieves_of_retract: if Q is a retract of P — a pair
    e : P ⟶ Q, s : Q ⟶ P with s ≫ e = 𝟙 Q — and P is flasque,
    then Q is flasque. Invariance under isomorphism (Godement II.3.1)
    is the symmetric case (both compositions equal to the identity);
    here a single equality suffices. The proof pushes the family along
    the section s, amalgamates in P, and comes back through e:
    compatibility follows from the naturality of s, the conclusion
    from that of e and the identity e ≫ s = 𝟙.

  - isFlasqueSieves_of_retract': the same reading with the roles
    exchanged — if e ≫ s = 𝟙 P and Q is flasque, then P is
    flasque. This is the previous theorem renamed (P is then the
    retract of Q): both directions of a split pair are covered by a
    single statement, recorded separately for downstream consumption.

  - isFlasqueSieves_of_iso': invariance under isomorphism as a
    corollary of the retract (e.inv ≫ e.hom = 𝟙). A deliberate
    duplicate of the Part 80 theorem (branch under review): here it
    witnesses that the retract is indeed the generalization.

  - isFlasqueSieves_of_retract_addCommGrp: the bridge to the abelian
    world — for presheaves of abelian groups, the retract transports
    through forget (whiskering), so flasqueness read through forget
    also descends to retracts of abelian presheaves. This is the setting
    where practically useful retracts live (split sheaves, split direct
    images).

The conceptual reading, extending Part 80: what transports without
choice is not just the isomorphism — it is everything that is a
retract. A section s provides the transport back; no datum is chosen,
everything is canonically moved. The boundary established in Part 80
(the flasque => injective link requires Zorn) is confirmed: a retract
costs no choice, a maximal extension costs one.

References:
  - R. Godement, Topologie algebrique et theorie des faisceaux [God58],
    Chap. II §3 (prop. 3.1: invariance under isomorphism, of which the
    retract is the one-sided form).
  - SGA 4, Expose II (sites and sieves).
  - Part 79 (Grothendieck.Flasque): IsFlasqueSieves.
  - Part 80 (Grothendieck.FlasqueStability, branch
    feature/grothendieck-partie-80): invariance under iso, products,
    boundary of acyclicity.

i18n convention (EPIC #4980 ratified 2026-07-04): this module is the
English canonical twin of Grothendieck/FlasqueRetract.lean — _en
suffix on the namespace (Grothendieck.FlasqueRetract_en), identical
imports, translated docstrings and comments. Theorem statements, Lean
tactics, lemma names and Mathlib references remain in English (Mathlib 4,
standard tactic DSL). Only the /-- ... -/ docstrings and -- ... comments
differ between the two files. Anti-§D byte-identity guaranteed: the
namespace body is preserved bit-for-bit (statements and proofs
byte-identical between FlasqueRetract.lean and FlasqueRetract_en.lean).

Epic #1646, Phase 2 (#2159). All sorries eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Whiskering
import Grothendieck.Flasque

namespace Grothendieck.FlasqueRetract_en

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Retracte

variable {C : Type u} [Category.{v} C]

/-- Flasqueness descends to retracts: if Q is a retract of P
(e : P ⟶ Q, s : Q ⟶ P, s ≫ e = 𝟙 Q) and P is flasque, Q is
flasque. The Q-family pushes to a P-family via the section s,
compatibility follows from naturality, and the amalgamation t comes
back through e. Invariance under isomorphism (Godement II.3.1) is the
symmetric case: here a single composition equal to the identity
suffices. -/
theorem isFlasqueSieves_of_retract {P Q : Cᵒᵖ ⥤ Type (max v u)} (e : P ⟶ Q)
    (s : Q ⟶ P) (h : s ≫ e = 𝟙 Q) [IsFlasqueSieves P] : IsFlasqueSieves Q where
  amalgamates := by
    intro X S x hx
    obtain ⟨t, ht⟩ := IsFlasqueSieves.amalgamates (P := P) S
      (fun Y f hf => s.app (op Y) (x f hf))
      (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h' => by
        show P.map g₁.op (s.app (op Y₁) (x f₁ hf₁))
          = P.map g₂.op (s.app (op Y₂) (x f₂ hf₂))
        rw [← NatTrans.naturality_apply (φ := s) g₁.op (x f₁ hf₁),
          ← NatTrans.naturality_apply (φ := s) g₂.op (x f₂ hf₂),
          hx g₁ g₂ hf₁ hf₂ h'])
    refine ⟨e.app (op X) t, ?_⟩
    intro Y f hf
    have nat : (Q.map f.op) (e.app (op X) t)
        = e.app (op Y) ((P.map f.op) t) :=
      (NatTrans.naturality_apply (φ := e) f.op t).symm
    have hid : ∀ {Y : C} (z : Q.obj (op Y)),
        e.app (op Y) (s.app (op Y) z) = z := by
      intro Y z
      have hz := congrFun (congrArg (fun φ => φ.app (op Y)) h) z
      simpa using hz
    rw [nat, ht f hf, hid]

/-- The same reading, roles exchanged: if e ≫ s = 𝟙 P (P is then
the retract of Q) and Q is flasque, P is flasque. Both directions
of a split pair are covered by a single theorem; this named alias serves
downstream consumption. -/
theorem isFlasqueSieves_of_retract' {P Q : Cᵒᵖ ⥤ Type (max v u)} (e : P ⟶ Q)
    (s : Q ⟶ P) (h : e ≫ s = 𝟙 P) [IsFlasqueSieves Q] : IsFlasqueSieves P :=
  isFlasqueSieves_of_retract s e h

end Retracte

section Corollaires

variable {C : Type u} [Category.{v} C]

/-- Invariance under isomorphism as a corollary of the retract: the
Part 80 theorem is re-derived here in one line, witnessing that the
one-sided retract is indeed the generalization. -/
theorem isFlasqueSieves_of_iso' {P Q : Cᵒᵖ ⥤ Type (max v u)} (e : P ≅ Q)
    [IsFlasqueSieves P] : IsFlasqueSieves Q :=
  isFlasqueSieves_of_retract e.hom e.inv e.inv_hom_id

end Corollaires

section Abelian

variable {C : Type u} [Category.{v} C]

/-- Bridge to the abelian world: for presheaves of abelian groups,
the retract transports through forget (right whiskering preserves
composition and identity), so flasqueness read through forget descends
to retracts of abelian presheaves — the setting where practically useful
retracts live. -/
theorem isFlasqueSieves_of_retract_addCommGrp
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max v u}} (e : F ⟶ G) (s : G ⟶ F)
    (h : s ≫ e = 𝟙 G)
    [IsFlasqueSieves (F ⋙ forget AddCommGrpCat.{max v u})] :
    IsFlasqueSieves (G ⋙ forget AddCommGrpCat.{max v u}) :=
  isFlasqueSieves_of_retract (Functor.whiskerRight e (forget AddCommGrpCat.{max v u}))
    (Functor.whiskerRight s (forget AddCommGrpCat.{max v u})) (by rw [← Functor.whiskerRight_comp, h, Functor.whiskerRight_id'])

end Abelian

end Grothendieck.FlasqueRetract_en
