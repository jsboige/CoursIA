import Mathlib
import Argumentation.Basic_en
import Argumentation.Extensions_en

/-!
# Dung's Fundamental Lemma (1995)

> **Fundamental Lemma (Dung, Proposition 6).** Let `S` be admissible and `a`, `b`
> two arguments **defended** by `S`. Then (i) `S ∪ {a}` is admissible, and
> (ii) `b` is defended by `S ∪ {a}`.

This lemma is the **cornerstone** of Dung's theory: it guarantees that defence
is *robust* to the addition of defended arguments, and underpins the existence
of the complete/grounded/preferred extensions. It is proved here **without any
`sorry`**, by first-order reasoning:

- **Internal conflict of `S ∪ {a}`**: an internal attacker `x` of a member `y`
  triggers (according to the 4 cases `x,y ∈ {a} ∪ S`) a chain of counter-attacks
  contradicting the conflict-freeness of `S` combined with the fact that `S`
  defends `a`.
- **Defence of members**: `S ∪ {a}` defends `a` (given) and each `s ∈ S` (by
  admissibility of `S`), since `S ⊆ S ∪ {a}` and defence is monotone.
- **(ii)**: immediate by monotonicity (`S ⊆ S ∪ {a}`).

Reference: Dung, *On the Acceptability of Arguments and its Fundamental Role in
Nonmonotonic Reasoning, Logic Programming and n-Person Games*, Artificial
Intelligence 77 (1995), Proposition 6.
-/

namespace Argumentation_en

variable {α : Type*}

namespace AF

variable (af : AF α)

/-- **Dung Fundamental Lemma (i)**: if `S` is admissible and defends `a`, then
`S ∪ {a}` is admissible. -/
theorem fundamental_lemma {S : Set α} {a : α}
    (hS : af.Admissible S) (ha : af.defends S a) :
    af.Admissible (insert a S) := by
  refine ⟨?_, ?_⟩
  · -- (1) S ∪ {a} is conflict-free : 2×2 analysis of the positions of x,y ∈ {a}∪S.
    rintro x hx y hy hxy
    obtain hxa | hxS := Set.mem_insert_iff.1 hx
    · -- x = a : a attacks y.
      obtain hya | hyS := Set.mem_insert_iff.1 hy
      · -- a attacks a : S defends a ⇒ ∃ c ∈ S attacks a ; but no member of S
        -- attacks a (cf. `no_internal_attack_on_defended`). Contradiction.
        subst x; subst y
        obtain ⟨c, hcS, hca⟩ := ha a hxy
        exact af.no_internal_attack_on_defended hS.1 hS.2 ha c hcS hca
      · -- a attacks y ∈ S : S defends y ⇒ ∃ c ∈ S attacks a ; no member of S
        -- attacks a. Contradiction.
        subst x
        obtain ⟨c, hcS, hca⟩ := hS.2 y hyS a hxy
        exact af.no_internal_attack_on_defended hS.1 hS.2 ha c hcS hca
    · -- x ∈ S : x attacks y.
      obtain hya | hyS := Set.mem_insert_iff.1 hy
      · -- x ∈ S attacks a : impossible (no member of S attacks a).
        subst y
        exact af.no_internal_attack_on_defended hS.1 hS.2 ha x hxS hxy
      · -- x ∈ S attacks y ∈ S : contradicts the conflict-freeness of S.
        exact hS.1 hxS hyS hxy
  · -- (2) S ∪ {a} defends each of its members (by monotonicity : S ⊆ S ∪ {a}).
    rintro y hy
    obtain hya | hyS := Set.mem_insert_iff.1 hy
    · -- defend a : S defends a, and S ⊆ S ∪ {a}.
      subst y
      exact af.defends_mono (Set.subset_insert a S) ha
    · -- defend y ∈ S : S (admissible) defends y, and S ⊆ S ∪ {a}.
      exact af.defends_mono (Set.subset_insert a S) (hS.2 y hyS)

/-- **Dung Fundamental Lemma (ii)**: if `S` (admissible) defends `a` and `b`,
then `S ∪ {a}` still defends `b`. Immediate by monotonicity of defence
(`S ⊆ S ∪ {a}`). -/
theorem fundamental_lemma_defends {S : Set α} {a b : α}
    (hS : af.Admissible S) (ha : af.defends S a) (hb : af.defends S b) :
    af.defends (insert a S) b :=
  af.defends_mono (Set.subset_insert a S) hb

/-- **Corollary**: if `S` is admissible and defends `a`, then `a` is defended
by `S ∪ {a}` (special case of (ii) with `b = a`). -/
theorem fundamental_lemma_defends_self {S : Set α} {a : α}
    (hS : af.Admissible S) (ha : af.defends S a) :
    af.defends (insert a S) a :=
  af.defends_mono (Set.subset_insert a S) ha

end AF

end Argumentation_en
