import Mathlib

/-!
# Argumentation frameworks (Dung 1995) — basic definitions

An **abstract argumentation framework** (Dung, 1995) is a pair `(A, R)` where `A`
is a set of arguments and `R ⊆ A × A` an attack relation. We encode it as a
structure `AF α` equipping a type of arguments `α` with an attack relation
`attacks : α → α → Prop`: we read `af.attacks a b` as "argument `a` attacks
argument `b`" (arrow `a → b`). The universe of arguments is the whole type `α`
— a standard encoding in formalization, which avoids carrying an explicit
subset `A` and makes `Set α` a complete lattice without any finiteness assumption.

Two fundamental notions:
- **Conflict-free**: no member of `S` attacks another.
- **Defence**: `S` defends an argument `a` if every attacker of `a` is in turn
  attacked by a member of `S`.

Defence is **monotone** in the defending set (more defenders ⇒ more defended
arguments) — the key property that makes the characteristic function
`F(S) = {a | S defends a}` an `OrderHom` (see `Characteristic.lean`).

Cross-reference:
- Notebook `Tweety-5-Abstract-Argumentation.ipynb` (Tweety series): Python
  presentation of Dung's frameworks, of which this formalization is the proved
  counterpart.
- Epic Argumentum #2137.
-/

namespace Argumentation_en

variable {α : Type*}

/-- Dung's abstract argumentation framework: a type of arguments `α` equipped
    with a binary attack relation. `af.attacks a b` reads "`a` attacks `b`". -/
structure AF (α : Type*) where
  /-- Attack relation: `attacks a b` means that argument `a` attacks `b`. -/
  attacks : α → α → Prop

namespace AF

variable (af : AF α)

/-- A set `S` is **conflict-free** if no member of it attacks another
(Dung 1995, Definition 1). -/
def conflictFree (S : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → ¬ af.attacks a b

/-- Argument `a` is **defended** by set `S` if every attacker of `a` is in turn
attacked by a member of `S` (Dung 1995, Definition 3). -/
def defends (S : Set α) (a : α) : Prop :=
  ∀ b, af.attacks b a → ∃ c ∈ S, af.attacks c b

/-- The set of arguments defended by `S`: the image of `S` under Dung's
characteristic function. Defined here for convenience; the bundled `OrderHom`
(monotone) version lives in `Characteristic.lean`. -/
def defendedBy (S : Set α) : Set α :=
  { a | af.defends S a }

/-!
## Elementary lemmas
-/

/-- The empty set is conflict-free: it has no member to attack. -/
theorem conflictFree_empty : af.conflictFree (∅ : Set α) := by
  rintro _ ⟨⟩

/-- Defence is **monotone** in the defending set: if `S ⊆ T` and `S` defends
`a`, then `T` also defends `a`. This is the *growth* of the characteristic
function, the heart of Dung's fixed-point theory. -/
theorem defends_mono {S T : Set α} (hST : S ⊆ T) {a : α} (hS : af.defends S a) :
    af.defends T a := by
  intro b hb
  obtain ⟨c, hcS, hcb⟩ := hS b hb
  exact ⟨c, hST hcS, hcb⟩

/-- If `S` is conflict-free, defends its own members, and defends `a`, then no
member of `S` attacks `a`: an internal attacker of `a` would itself be attacked
by a defender of `a` in `S`, contradicting conflict-freeness. Key lemma for the
proof of Dung's *Fundamental Lemma*. -/
theorem no_internal_attack_on_defended {S : Set α} (hcf : af.conflictFree S)
    (hself : ∀ a ∈ S, af.defends S a) {a : α} (hdef : af.defends S a) :
    ∀ b, b ∈ S → ¬ af.attacks b a := by
  intro b hbS hbatt
  obtain ⟨c, hcS, hcb⟩ := hdef b hbatt
  exact hcf hcS hbS hcb

end AF

end Argumentation_en
