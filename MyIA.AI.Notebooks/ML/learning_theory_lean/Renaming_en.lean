import MathUniverse_en

/-!
# Renaming — structure equivalence under renaming (R16 §III "baggage")

Follow-up to the `MathUniverse` module on issue **#16753** (Appendix A of
R16 — *The Mathematical Universe*, Tegmark). `MathUniverse` defined the
finite relational structure (`FinRelStruct`), the group `aut`, and the
decidability of equivalence `EquivStruct` by table enumeration. This slice
formalizes what §III of the paper calls **baggage**: element names are not
part of the structure — renaming the entities of a definition yields *the
same* structure, and it is precisely this equivalence under renaming that
the halting algorithm of Appendix A decides.

Distilled content:

1. **`EquivStruct` is an equivalence** (`equivStruct_refl`,
   `equivStruct_symm`, `equivStruct_trans`) — reflexive, symmetric,
   transitive across carrier types: the relation of "being two definitions
   of the same structure".
2. **Cardinality invariants**: equivalence requires equipotent carriers
   (`equivStruct_card_eq` — C₂ and C₃ are NOT equivalent: 2 ≠ 3, theorem
   and kernel confirmation) and preserves the size of every relation table
   (`equivStruct_rel_card` via `relFinset`) — two equipotent structures of
   the same signature can still be told apart: `c3` (addition table of Z/3)
   versus `point3` (pointed structure), `c2` versus `diag2` (diagonal). The
   discrimination is visible in the output: `decide` returns `false` with
   no witness supplied.
3. **Renaming is a permutation enumeration** (`equivStruct_iff_perm`): on a
   single carrier, deciding equivalence means scanning the `m!`
   permutations rather than the `m^m` functions — the gap between the
   general formulation (bijection between distinct carriers) and the
   concrete case of renaming one fixed set of entities.
4. **The torsor of renamings under Aut(S)**: two isomorphisms differ by an
   automorphism (`iso_symm_mul_aut`), Aut(S) acts on isomorphisms on the
   right (`iso_mul_aut`), and Aut-membership transports by conjugation
   (`mem_aut_conj_iff`) — corollary: any structure equivalent to the
   two-element Boolean algebra has a trivial automorphism group
   (`aut_trivial_of_equiv_bool8`). This is the bridge to
   `EffectiveTheory.InfoBits` (`b = log₂(n!/|Aut G|)`): the information
   content is an invariant of renaming.

Source PDF (GDrive, sha8): R16 `85712871`. French twin `Renaming`
(Epic #4980).
-/

namespace MathUniverse.Renaming_en

open MathUniverse_en (FinRelStruct EquivStruct aut Preserves mem_aut_iff)
open MathUniverse_en.Examples (c2 c3 bool8 bool8Sig c2Sig c3Sig aut_bool8_trivial)

section
variable {α : Type*} {β : Type*} {γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  {n : ℕ} {σ : Fin n → ℕ}

/-! ## 1. `EquivStruct` is an equivalence across types -/

/-- Reflexivity: every structure is equivalent to itself — the identity is
the witness. -/
theorem equivStruct_refl (S : FinRelStruct α σ) : EquivStruct S S :=
  ⟨Equiv.refl α, fun _ _ => Iff.rfl⟩

/-- Symmetry: if `f` carries the relations of `S` onto those of `T`, then
`f.symm` carries those of `T` onto those of `S`. -/
theorem equivStruct_symm {S : FinRelStruct α σ} {T : FinRelStruct β σ}
    (h : EquivStruct S T) : EquivStruct T S := by
  obtain ⟨f, hrel⟩ := h
  refine ⟨f.symm, fun i t => ?_⟩
  have key := hrel i (f.symm ∘ t)
  rw [show ⇑f ∘ (⇑f.symm ∘ t) = t from
    funext fun x => f.apply_symm_apply (t x)] at key
  exact key.symm

/-- Transitivity: composing the witnesses composes the equivalences. -/
theorem equivStruct_trans {S : FinRelStruct α σ} {T : FinRelStruct β σ}
    {U : FinRelStruct γ σ} (h₁ : EquivStruct S T) (h₂ : EquivStruct T U) :
    EquivStruct S U := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨f.trans g, fun i t => (hf i t).trans (hg i (f ∘ t))⟩

/-! ## 2. Invariants: cardinalities and table sizes -/

/-- Equivalence requires equipotent carriers: the witness IS an
equipotence. The first barrier to cross before any table comparison. -/
theorem equivStruct_card_eq {S : FinRelStruct α σ} {T : FinRelStruct β σ}
    (h : EquivStruct S T) : Fintype.card α = Fintype.card β := by
  obtain ⟨f, _⟩ := h
  exact Fintype.card_congr f

/-- The table of a relation, as a finite set of tuples: the effective datum
that §A.2 of the paper calls "specifying the structure by its tables".
Decidability comes from the `rel_dec` field (passed explicitly: a structure
field is not an instance). -/
def relFinset (S : FinRelStruct α σ) (i : Fin n) [DecidableEq α]
    (d : ∀ t : Fin (σ i) → α, Decidable (S.rel i t)) :
    Finset (Fin (σ i) → α) :=
  @Finset.filter _ (fun t => S.rel i t) d Finset.univ

/-- **The size of a table is an invariant of renaming**: if `S` and `T` are
equivalent, each relation occupies the same number of lines in its table —
the witness carries tuples one by one. -/
theorem equivStruct_rel_card {S : FinRelStruct α σ} {T : FinRelStruct β σ}
    (h : EquivStruct S T) (i : Fin n) [DecidableEq α] [DecidableEq β]
    (dS : ∀ t : Fin (σ i) → α, Decidable (S.rel i t))
    (dT : ∀ t : Fin (σ i) → β, Decidable (T.rel i t)) :
    (relFinset S i dS).card = (relFinset T i dT).card := by
  obtain ⟨f, hrel⟩ := h
  have hinjF : Function.Injective (fun t : Fin (σ i) → α => f ∘ t) :=
    fun t₁ t₂ ht => funext fun j => f.injective (congrFun ht j)
  have hinjS : Function.Injective (fun u : Fin (σ i) → β => f.symm ∘ u) :=
    fun u₁ u₂ ht => funext fun j => f.symm.injective (congrFun ht j)
  have hST : (relFinset S i dS).image (fun t => f ∘ t) ⊆ relFinset T i dT := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hrel i t).mp (Finset.mem_filter.mp ht).2⟩
  have hTS : (relFinset T i dT).image (fun u => f.symm ∘ u) ⊆ relFinset S i dS := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hiff := hrel i (f.symm ∘ u)
    rw [show ⇑f ∘ (⇑f.symm ∘ u) = u from
      funext fun x => f.apply_symm_apply (u x)] at hiff
    exact hiff.mpr (Finset.mem_filter.mp hu).2
  refine le_antisymm ?_ ?_
  · calc (relFinset S i dS).card
        = ((relFinset S i dS).image (fun t => f ∘ t)).card :=
          (Finset.card_image_of_injOn fun a _ b _ hab => hinjF hab).symm
    _ ≤ (relFinset T i dT).card := Finset.card_le_card hST
  · calc (relFinset T i dT).card
        = ((relFinset T i dT).image (fun u => f.symm ∘ u)).card :=
          (Finset.card_image_of_injOn fun a _ b _ hab => hinjS hab).symm
    _ ≤ (relFinset S i dS).card := Finset.card_le_card hTS

/-! ## 3. Renaming is a permutation enumeration -/

/-- On a single carrier, equivalence is decided by scanning the
**permutations** (`m!` candidates) rather than the functions (`m^m`):
renaming a fixed set of entities is exactly the operational counterpart of
"two definitions describe the same structure". -/
theorem equivStruct_iff_perm (S T : FinRelStruct α σ) [DecidableEq α] :
    EquivStruct S T ↔
      ∃ p : Equiv.Perm α, ∀ i (t : Fin (σ i) → α), S.rel i t ↔ T.rel i (p ∘ t) := by
  constructor
  · exact fun ⟨f, h⟩ => ⟨f, h⟩
  · exact fun ⟨p, h⟩ => ⟨p, h⟩

/-! ## 4. The torsor of renamings under Aut(S) -/

/-- The unfolded witness of an isomorphism from `S` to `T` carried by the
permutation `p`: every relation of `S` reads as that of `T` after renaming
by `p`. -/
def IsoWit (S T : FinRelStruct α σ) (p : Equiv.Perm α) : Prop :=
  ∀ i (t : Fin (σ i) → α), S.rel i t ↔ T.rel i (p ∘ t)

/-- **Aut(S) acts on isomorphisms on the right**: composing an isomorphism
with an automorphism (source side) yields an isomorphism. -/
theorem iso_mul_aut {S T : FinRelStruct α σ} {p : Equiv.Perm α}
    (hp : IsoWit S T p) {g : Equiv.Perm α} (hg : g ∈ aut S) :
    IsoWit S T (p * g) := by
  intro i t
  have h1 : S.rel i t ↔ S.rel i (g ∘ t) := (mem_aut_iff S g).mp hg i t
  have h2 : S.rel i (g ∘ t) ↔ T.rel i (p ∘ (g ∘ t)) := hp i (g ∘ t)
  rw [show ⇑(p * g) ∘ t = p ∘ (g ∘ t) from funext fun j => rfl]
  exact h1.trans h2

/-- **Two isomorphisms differ by an automorphism**: the quotient
`p₁⁻¹ * p₂` preserves `S`. This is the torsor — the set of renamings
identifying `S` with `T` is a principal torsor under `Aut(S)`, whose
cardinality (the invariant `|Aut S|` of `EffectiveTheory.InfoBits`) does
not depend on the chosen witness. -/
theorem iso_symm_mul_aut {S T : FinRelStruct α σ} {p₁ p₂ : Equiv.Perm α}
    (h₁ : IsoWit S T p₁) (h₂ : IsoWit S T p₂) : p₁⁻¹ * p₂ ∈ aut S := by
  rw [mem_aut_iff]
  intro i t
  have hA : S.rel i t ↔ T.rel i (p₂ ∘ t) := h₂ i t
  have hB := h₁ i (⇑(p₁⁻¹) ∘ ⇑p₂ ∘ t)
  rw [show ⇑p₁ ∘ (⇑(p₁⁻¹) ∘ ⇑p₂ ∘ t) = ⇑p₂ ∘ t from
    funext fun j => p₁.apply_symm_apply (p₂ (t j))] at hB
  rw [show ⇑(p₁⁻¹ * p₂) ∘ t = ⇑(p₁⁻¹) ∘ ⇑p₂ ∘ t from funext fun j => rfl]
  exact hA.trans hB.symm

omit [Fintype α] in
/-- The conjugation of one permutation by another, pointwise:
`(e * p * e⁻¹) x = e (p (e.symm x))` — technical lemma for transporting
`aut` along a renaming. -/
private theorem coe_conj_apply (e p : Equiv.Perm α) (x : α) :
    (e * p * e⁻¹) x = e (p (e.symm x)) := by
  simp only [Equiv.Perm.inv_def, Equiv.Perm.mul_apply]

/-- **Aut-membership transports by conjugation**: conjugating an
automorphism of `S` by an isomorphism `S → T` yields an automorphism of
`T`, and conversely. The automorphism group is an invariant of renaming —
not an artifact of the definition. -/
theorem mem_aut_conj_iff {S T : FinRelStruct α σ} {e : Equiv.Perm α}
    (he : IsoWit S T e) (p : Equiv.Perm α) :
    p ∈ aut S ↔ e * p * e⁻¹ ∈ aut T := by
  constructor
  · intro hp
    rw [mem_aut_iff]
    intro i t
    have hE := he i (fun j => e.symm (t j))
    rw [show ⇑e ∘ (fun j => e.symm (t j)) = t from
      funext fun j => e.apply_symm_apply (t j)] at hE
    have hP := (mem_aut_iff S p).mp hp i (fun j => e.symm (t j))
    have hE' := he i (fun j => p (e.symm (t j)))
    rw [show ⇑(e * p * e⁻¹) ∘ t = fun j => e (p (e.symm (t j))) from
      funext fun j => coe_conj_apply e p (t j)]
    exact (hE.symm.trans hP).trans hE'
  · intro hq
    rw [mem_aut_iff]
    intro i t
    have hE : S.rel i t ↔ T.rel i (e ∘ t) := he i t
    have hQ := (mem_aut_iff T (e * p * e⁻¹)).mp hq i (e ∘ t)
    rw [show ⇑(e * p * e⁻¹) ∘ (⇑e ∘ t) = ⇑e ∘ (⇑p ∘ t) from
      funext fun j => by
        simp only [Function.comp_apply, coe_conj_apply, e.symm_apply_apply]] at hQ
    have hE' := he i (p ∘ t)
    exact (hE.trans hQ).trans hE'.symm

/-- **Corollary (the InfoBits bridge)**: any structure equivalent to the
two-element Boolean algebra has a trivial automorphism group. The "1 bit"
of `b = log₂(n!/|Aut G|)` transports along renaming: the information lives
in the structure, not in the names. -/
theorem aut_trivial_of_equiv_bool8 {T : FinRelStruct Bool bool8Sig}
    (h : EquivStruct bool8 T) {q : Equiv.Perm Bool} (hq : q ∈ aut T) : q = 1 := by
  obtain ⟨f, hrel⟩ := h
  have hqP : Preserves T q := (mem_aut_iff T q).mp hq
  -- the conjugate x ↦ f.symm (q (f x)) preserves bool8
  have key : ∀ i (t : Fin (bool8Sig i) → Bool),
      bool8.rel i t ↔ bool8.rel i (fun j => f.symm (q (f (t j)))) := by
    intro i t
    have h1 : bool8.rel i t ↔ T.rel i (f ∘ t) := hrel i t
    have h2 : T.rel i (f ∘ t) ↔ T.rel i (q ∘ (f ∘ t)) := hqP i (f ∘ t)
    have h3 := hrel i (fun j => f.symm (q (f (t j))))
    rw [show ⇑f ∘ (fun j => f.symm (q (f (t j)))) = q ∘ f ∘ t from
      funext fun j => f.apply_symm_apply (q (f (t j)))] at h3
    exact h1.trans (h2.trans h3.symm)
  have hconj : (f.trans (q.trans f.symm) : Equiv.Perm Bool) ∈ aut bool8 := by
    rw [mem_aut_iff]
    intro i t
    rw [show ⇑(f.trans (q.trans f.symm) : Equiv.Perm Bool) ∘ t
          = fun j => f.symm (q (f (t j))) from
      funext fun j => by simp]
    exact key i t
  have h1 : (f.trans (q.trans f.symm) : Equiv.Perm Bool) = 1 :=
    aut_bool8_trivial _ hconj
  have hcoe : ∀ x : Bool, f.symm (q (f x)) = x := by
    intro x
    have hx := congrArg (fun w : Equiv.Perm Bool => w x) h1
    simpa [Equiv.Perm.coe_one] using hx
  ext z
  obtain ⟨y, hy⟩ := f.surjective z
  have hz1 : f.symm (q z) = y := by rw [← hy, hcoe y]
  have hz2 : f.symm z = y := by rw [← hy, f.symm_apply_apply]
  have hz : q z = z := f.symm.injective (by rw [hz1, hz2])
  simpa [Equiv.Perm.coe_one] using hz

end

/-! ## 5. Examples: discrimination by invariants and by the kernel -/

namespace Examples

/-- **C₂ ≇ C₃**: the cardinality invariant suffices — 2 ≠ 3, there is no
equipotence `Bool ≃ Fin 3`. -/
theorem not_equivStruct_c2_c3 : ¬ EquivStruct c2 c3 := by
  intro h
  have hc := equivStruct_card_eq h
  rw [show Fintype.card Bool = 2 from by decide, Fintype.card_fin] at hc
  exact absurd hc (by decide)

/-- The kernel recovers it: the table enumeration of Appendix A returns
`false` with no witness supplied. -/
example : ¬ EquivStruct c2 c3 := by decide +kernel

/-- **Pointed** structure on `Fin 3`: a single ternary relation containing
only the triple `(0, 0, 0)` — same cardinality as `c3`, same signature,
different table size. -/
def point3 : FinRelStruct (Fin 3) c3Sig where
  rel := fun _ t => t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 0
  rel_dec := fun i _ =>
    match i with
    | 0 => inferInstance

/-- **Diagonal** structure on `Bool`: the relation retains only the
triples `(b, b, b)` — same cardinality (2) and same signature as `c2`,
different table size. -/
def diag2 : FinRelStruct Bool c2Sig where
  rel := fun _ t => t 0 = t 1 ∧ t 1 = t 2
  rel_dec := fun i _ =>
    match i with
    | 0 => inferInstance

/-- The addition table of Z/3 counts nine triples (one result per pair of
operands). -/
theorem card_rel_c3 : (relFinset c3 (0 : Fin 1) (c3.rel_dec 0)).card = 9 := by decide

/-- The pointed structure counts a single triple. -/
theorem card_rel_point3 : (relFinset point3 (0 : Fin 1) (point3.rel_dec 0)).card = 1 := by
  decide

/-- The addition table of Z/2 counts four triples. -/
theorem card_rel_c2 : (relFinset c2 (0 : Fin 1) (c2.rel_dec 0)).card = 4 := by decide

/-- The diagonal of `Bool` counts only two triples. -/
theorem card_rel_diag2 : (relFinset diag2 (0 : Fin 1) (diag2.rel_dec 0)).card = 2 := by
  decide

/-- **C₃ ≇ point3**: equipotent, same signature — told apart by the table
size (the invariant `equivStruct_rel_card`). -/
theorem not_equivStruct_c3_point3 : ¬ EquivStruct c3 point3 := by
  intro h
  have hc := equivStruct_rel_card h (0 : Fin 1) (c3.rel_dec 0) (point3.rel_dec 0)
  rw [card_rel_c3, card_rel_point3] at hc
  exact absurd hc (by decide)

/-- **C₂ ≇ diag2**: same carrier, same signature — told apart by the
table size (four versus two). -/
theorem not_equivStruct_c2_diag2 : ¬ EquivStruct c2 diag2 := by
  intro h
  have hc := equivStruct_rel_card h (0 : Fin 1) (c2.rel_dec 0) (diag2.rel_dec 0)
  rw [card_rel_c2, card_rel_diag2] at hc
  exact absurd hc (by decide)

/-- The kernel confirms both discriminations with no witness supplied. -/
example : ¬ EquivStruct c3 point3 := by decide +kernel

example : ¬ EquivStruct c2 diag2 := by decide +kernel

end Examples

end MathUniverse.Renaming_en
