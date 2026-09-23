import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Tactic

/-!
# Computed Yoneda lemma: evaluation is a bijection, proved by the kernel

Kernel pendant of the notebook `04-lemme-yoneda-categories-finies.ipynb`
(*Serre 100* series, EPIC #16334 — "kernel pendants" graduation track).
The notebook *enumerates* the natural transformations of finite
categories in Python and *measures* the bijection; this module *proves*
it for any category, and has the kernel check the notebook's tables on
the concrete instances.

Plan, mirroring the notebook:

1. **A finite category**: Sierpinski and `cercle4` (two minima `a1`,
   `a3`, two maxima `a2`, `a4`) as preorders — the notebook's
   `cat_poset` construction, on the Lean side.
2. **The lemma: evaluation is a bijection**: the notebook's
   evaluation/inverse pair (`alpha ↦ alpha_X(id_X)` and
   `x ↦ (f ↦ F(f)(x))`) IS `coyonedaEquiv` in Mathlib — the two
   round-trips are theorems, not measurements.
3. **Full and faithful**: `Nat(h_X, h_Y) ≃ Hom(Y, X)` —
   `Coyoneda.fullyFaithful`, and the 4×4 matrix of `cercle4` checked by
   the kernel, entry by entry.
4. **The Čech bridge**: `h_x = U_x` — on a preorder, the covariant
   representable reads exactly the upper open set `U x = {y | x ≤ y}`
   of notebook 03.
5. **Exercises**: the constant functor (`Nat(h_X, cst_E) ≃ E`, card 3
   measured and proved on Sierpinski), the computed faithfulness, and
   the monoid `ℤ/3` (`|Nat(h_*, h_*)| = 3`, kernel).

Vocabulary remark: the notebook works with *covariant* functors
`C → Set` with `h_X(y) = Hom(X, y)` — on the Mathlib side this is
`coyoneda` (`Cᵒᵖ ⥤ C ⥤ Type`); the presheaf side `yoneda` is the dual
mirror.
-/

set_option autoImplicit false

namespace Serre100_en

open CategoryTheory Opposite

/-! ## 1. A finite category

Two finite preorders, the notebook's `cat_poset` construction: an
ordered set is a thin category (at most one arrow per pair), `x ⟶ y` is
the proof of `x ≤ y`. Sierpinski (two elements, `a ≤ b`) is the minimal
witness; `cercle4` is the category of cells 14-16 of the notebook: two
minima `a1`, `a3` under two maxima `a2`, `a4`.
-/

/-- The Sierpinski preorder: two elements, `a ≤ b` (notebook,
`sierpinski`). -/
inductive Sierpinski : Type where
  | a : Sierpinski
  | b : Sierpinski
  deriving DecidableEq

instance : LE Sierpinski := ⟨fun x y => x = .a ∨ x = y⟩

instance : DecidableLE Sierpinski := fun x y =>
  decidable_of_iff (x = Sierpinski.a ∨ x = y) Iff.rfl

instance : Preorder Sierpinski where
  le_refl x := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases x <;> rcases y <;> rcases z <;> tauto

/-- The notebook's `cercle4` category: two minima `a1`, `a3`, two
maxima `a2`, `a4` — `a1, a3 ≤ a2, a4` (notebook, cell 14). -/
inductive Cercle4 : Type where
  | a1 : Cercle4
  | a2 : Cercle4
  | a3 : Cercle4
  | a4 : Cercle4
  deriving DecidableEq

instance : LE Cercle4 :=
  ⟨fun x y => (x = .a1 ∨ x = .a3) ∧ (y = .a2 ∨ y = .a4) ∨ x = y⟩

instance : DecidableLE Cercle4 := fun x y =>
  decidable_of_iff ((x = Cercle4.a1 ∨ x = Cercle4.a3) ∧
    (y = Cercle4.a2 ∨ y = Cercle4.a4) ∨ x = y) Iff.rfl

instance : Preorder Cercle4 where
  le_refl x := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases x <;> rcases y <;> rcases z <;> tauto

-- The category instances come from `Preorder.smallCategory`:
-- `Hom x y := ULift (PLift (x ≤ y))`, thin by `subsingleton_hom`.

/-! ## 2. The lemma: evaluation is a bijection, computed

The notebook's pair — evaluation `α ↦ α_X(id_X)` and inverse
`x ↦ (f ↦ F(f)(x))` — is exactly `coyonedaEquiv`: the round-trip that
the notebook measures by exhaustive enumeration is a theorem of
Mathlib, and the computation of the inverse on an arrow is `rfl`.
-/

section Lemme

variable {C : Type} [SmallCategory C]

/-- The notebook's `h_X`: the covariant representable `Hom(X, ·)`.
It IS `coyoneda.obj (op X)`, component by component. -/
theorem hX_app (X : C) (Y : C) :
    (coyoneda.obj (op X)).obj Y = (X ⟶ Y) :=
  rfl

/-- **The notebook's evaluation is `coyonedaEquiv`**: the component at
`X` of the domain, on the identity, then the bijection (notebook §4,
`evaluation` + check "bijective/round-trip/natural inverse"). -/
theorem evaluation_eq (X : C) (F : C ⥤ Type) (α : coyoneda.obj (op X) ⟶ F) :
    coyonedaEquiv α = α.app X (𝟙 X) :=
  rfl

/-- **The notebook's inverse, on an arrow**: the component at `Y` of
`yoneda_inverse x` applied to `f : X ⟶ Y` is `F.map f x` — computed by
the kernel, without enumeration (notebook §4, `yoneda_inverse`). -/
theorem inverse_app (X : C) (F : C ⥤ Type) (x : F.obj X) (Y : C)
    (f : X ⟶ Y) : (coyonedaEquiv.symm x).app Y f = F.map f x :=
  rfl

/-- The notebook's first round-trip: evaluating the inverse image gives
back the original transformation — for any category, not only finite
ones (notebook, `round-trip`). -/
theorem round_trip_domain (X : C) (F : C ⥤ Type)
    (α : coyoneda.obj (op X) ⟶ F) :
    coyonedaEquiv.symm (coyonedaEquiv α) = α :=
  coyonedaEquiv.symm_apply_apply α

/-- The second round-trip: the inverse applied to the evaluation gives
back the element (notebook, `inverse naturel`). -/
theorem round_trip_codomain (X : C) (F : C ⥤ Type) (x : F.obj X) :
    coyonedaEquiv (coyonedaEquiv.symm x) = x :=
  coyonedaEquiv.apply_symm_apply x

end Lemme

/-! ## 3. Full and faithful: `Nat(h_X, h_Y) ≃ Hom(Y, X)`

The full faithfulness of `coyoneda` gives the bijection of section 5 of
the notebook; on a thin category each hom is a 0-or-1, and the matrix
of `cercle4` is checked by the kernel, entry by entry.
-/

section PleinFidele

variable {C : Type} [SmallCategory C]

/-- **Full and faithful** (notebook §5): the natural transformations
between representables are exactly the arrows. This is the lemma of
section 2 once more, instantiated at `F = h_Y` — the codomain is
`h_Y(X) = (Y ⟶ X)` by `hX_app`. It is the computational reading of
`Coyoneda.fullyFaithful`. -/
def natEquiv (X Y : C) :
    (coyoneda.obj (op X) ⟶ coyoneda.obj (op Y)) ≃ (Y ⟶ X) :=
  coyonedaEquiv

/-- The arrow is read off its transformation: evaluate at the point
`id_X` (notebook §5, computed faithfulness; Mathlib,
`fullyFaithful_preimage`). -/
theorem natEquiv_apply (X Y : C) (α : coyoneda.obj (op X) ⟶ coyoneda.obj (op Y)) :
    natEquiv X Y α = α.app X (𝟙 X) :=
  rfl

/-- The cardinal of a hom of a preorder: 1 if `x ≤ y`, 0 otherwise —
the notebook's matrix, on the kernel side. -/
def homCard {α : Type} [Preorder α] [DecidableLE α] (x y : α) : ℕ :=
  if x ≤ y then 1 else 0

/-- The matrix of `cercle4` (notebook, cell 14), non-trivial rows:
`|Hom(a1, ·)|` and `|Hom(a3, ·)|` — the two zeros `a1 → a3` and `a3 → a1`
are the non-trivial entries; the rows of the maxima `a2`, `a4` carry
only the identity. -/
example : ∀ y : Cercle4, homCard Cercle4.a1 y =
    (match y with | .a1 => 1 | .a2 => 1 | .a3 => 0 | .a4 => 1) := by
  intro y
  rcases y <;> decide

example : ∀ y : Cercle4, homCard Cercle4.a3 y =
    (match y with | .a1 => 0 | .a2 => 1 | .a3 => 1 | .a4 => 1) := by
  intro y
  rcases y <;> decide

example : ∀ y : Cercle4, homCard Cercle4.a2 y =
    (match y with | .a1 => 0 | .a2 => 1 | .a3 => 0 | .a4 => 0)
    ∧ homCard Cercle4.a4 y =
      (match y with | .a1 => 0 | .a2 => 0 | .a3 => 0 | .a4 => 1) := by
  intro y
  rcases y <;> decide

/-- **The Yoneda column of the matrix**: the cardinal of `Nat(h_X, h_Y)`
is the cardinal of `Hom(Y, X)` — the notebook's row "agreement = True"
over the whole matrix, for any category with finite homs. -/
theorem card_nat_eq_homCard {α : Type} [Preorder α] (X Y : α) :
    Nat.card (coyoneda.obj (op X) ⟶ coyoneda.obj (op Y)) = Nat.card (Y ⟶ X) :=
  Nat.card_congr (natEquiv X Y)

end PleinFidele

/-! ## 4. The Čech bridge: `h_x = U_x`

On a preorder, the covariant representable `h_x(y) = Hom(x, y)` reads
exactly the membership in the upper open set `U x = {y | x ≤ y}` — the
incidence table of notebook 03 (Čech cohomology), where the
presheaf-of-open-sets and the representable coincide.
-/

section PontCech

variable {α : Type} [Preorder α]

/-- The upper open set of `x`: the `U_x` of notebook 03. -/
def ouverture (x : α) : Set α := {y | x ≤ y}

/-- **`h_x = U_x`**: having an arrow `x ⟶ y` is belonging to the open
set `U x` — the Čech bridge of notebook §6, one entry of the incidence
table per pair of objects. -/
theorem pont_cech (x y : α) : Nonempty (x ⟶ y) ↔ y ∈ ouverture x := by
  constructor
  · intro ⟨f⟩
    exact leOfHom f
  · intro h
    exact ⟨homOfLE h⟩

end PontCech

/-! ## 5. Exercises — the notebook's three, on the kernel side

1. The constant functor: `Nat(h_X, cst_E) ≃ E` — the card 3 of
   Sierpinski, proved.
2. The computed faithfulness: `coyoneda.map` is injective (exercise 2).
3. The monoid `ℤ/3`: `|Nat(h_*, h_*)| = 3` (exercise 3), and the
   two-point `ℤ/2`-set of cell 11.
-/

section Exercices

/-- The notebook's constant functor: every object sees `E`, every arrow
sees the identity (`const C E`, cell 8). -/
def foncteurConstant (C) [SmallCategory C] (E : Type) : C ⥤ Type where
  obj _ := E
  map _ := 𝟙 E
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Exercise 1**: transformations from the representable to the
constant functor `E` = elements of `E` — the `F = cst` instance of the
lemma, card measured as 3 on Sierpinski in the notebook. -/
def nat_const (C : Type) [SmallCategory C] (X : C) (E : Type) :
    (coyoneda.obj (op X) ⟶ foncteurConstant C E) ≃ E :=
  coyonedaEquiv (X := X) (F := foncteurConstant C E)

/-- Exercise 1, kernel: on Sierpinski with `E = Fin 3`, the notebook's
count (`3`), proved by the kernel. -/
example : Nat.card
    (coyoneda.obj (op Sierpinski.a) ⟶ foncteurConstant Sierpinski (Fin 3)) = 3 := by
  rw [Nat.card_congr (nat_const Sierpinski Sierpinski.a (Fin 3))]
  rw [Nat.card_eq_fintype_card]
  decide

/-- **Exercise 2**: the computed faithfulness — every arrow gives a
transformation (by precomposition through the evaluation), and two
arrows with the same transformation are equal (notebook, "every arrow
IS a transformation"). -/
theorem fidelite (C : Type) [SmallCategory C] (X Y : C) :
    Function.Injective (natEquiv X Y) :=
  (natEquiv X Y).injective

/-- **Exercise 3**: the monoid `ℤ/3` (additive — transported to
multiplicative by `Multiplicative`) seen as a one-object category —
`|Nat(h_*, h_*)| = |ℤ/3| = 3`, kernel (notebook, cell 23). -/
example : Nat.card
    (coyoneda.obj (op (SingleObj.star (M := Multiplicative (ZMod 3)))) ⟶
     coyoneda.obj (op (SingleObj.star (M := Multiplicative (ZMod 3))))) = 3 := by
  rw [Nat.card_congr
    (natEquiv (SingleObj.star (M := Multiplicative (ZMod 3)))
      (SingleObj.star (M := Multiplicative (ZMod 3))))]
  rw [Nat.card_eq_fintype_card]
  decide

/-- The two-point `ℤ/2`-set of cell 11 of the notebook: `F_z2 = {p, q}`
with `t = (p q)` — here the regular `ℤ/2`-set (`ZMod 2` acting on
itself by translation), which is that swap: `t` exchanges the two
elements, `t ∘ t = id`. -/
def z2ensemble : SingleObj (Multiplicative (ZMod 2)) ⥤ Type where
  obj _ := ZMod 2
  map f := TypeCat.ofHom (fun x : ZMod 2 => x + Multiplicative.toAdd f)
  map_id := by
    intro X
    apply ConcreteCategory.hom_ext
    intro x
    show x + (0 : ZMod 2) = x
    ring
  map_comp := by
    intro X Y Z f g
    apply ConcreteCategory.hom_ext
    intro x
    show x + (Multiplicative.toAdd g + Multiplicative.toAdd f : ZMod 2)
      = x + Multiplicative.toAdd f + Multiplicative.toAdd g
    ring

section Z2

-- The finiteness of the type of transformations is inherited from the
-- lemma: it is `F_z2(*) = ℤ/2`, finite. Local instance, for the
-- statement below.
local instance : Fintype
    (coyoneda.obj (op (SingleObj.star (M := Multiplicative (ZMod 2)))) ⟶ z2ensemble) :=
  Fintype.ofEquiv (ZMod 2) (coyonedaEquiv
    (X := SingleObj.star (M := Multiplicative (ZMod 2))) (F := z2ensemble)).symm

/-- Cell 11 of the notebook, on the kernel side: on the group `ℤ/2`
(one object), `|Nat(h_*, F_z2)| = |F_z2(*)| = 2` — the lemma at work on
a non-preorder case. -/
example : Nat.card
    (coyoneda.obj (op (SingleObj.star (M := Multiplicative (ZMod 2)))) ⟶ z2ensemble)
      = 2 := by
  rw [Nat.card_congr (coyonedaEquiv
    (X := SingleObj.star (M := Multiplicative (ZMod 2))) (F := z2ensemble))]
  show Nat.card (ZMod 2) = 2
  rw [Nat.card_eq_fintype_card]
  exact ZMod.card 2

end Z2

end Exercices

end Serre100_en
