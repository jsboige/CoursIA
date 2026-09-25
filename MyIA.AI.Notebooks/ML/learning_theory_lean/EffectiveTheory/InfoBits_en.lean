import Mathlib

/-!
# InfoBits — b = log₂(n!/|Aut G|): the informational content of a structure

Tranche **R06** of the "effective theory" arc (#16741, issue #16752):
*Baek, Liu & Tegmark, GenEFT* (arXiv:2402.05916). The paper measures the
informational content `b` of a structure with `n` nodes as
`b = log₂(n! / |Aut G|)`: labelling `n` nodes costs `log₂ n!` bits, minus
`log₂ |Aut G|` bits offered by the symmetries of the automorphism group.

Formalized content:

1. **Definition** — `infoBits G := log₂ (n! / |MulAut G|)` for a finite
   group `G`.
2. **Concrete anchors** (the issue asks for "concrete automorphism groups"):
   - `infoBits_trivial`: trivial group, `b = log₂(1/1) = 0` — no
     information required, no symmetry to cash in;
   - `infoBits_card_two`: any two-element group, `b = log₂(2/1) = 1`
     bit — the automorphism group is trivial (`card_mulAut_eq_one`:
     an automorphism fixes `1`, and the single other element has nowhere
     to go), hence no symmetry: labelling one node costs exactly 1 bit;
   - `infoBits_cyclicSeven`: the cyclic group `C₇` (companion of the
     `CircleOfDays` module, whose rotation of the days is the representation
     of this group), `b = log₂(7!/6) = log₂ 840` — a cyclic group of order
     `n` has φ(n) automorphisms (`IsCyclic.card_mulAut`), so the 6 rotations
     of C₇ discount the labelling by log₂ 6 ≈ 2.58 bits.
3. **Statics on graphs — Section III of GenEFT**: relabelling the `n` nodes
   of a graph is the natural action of `Equiv.Perm (Fin n)` on
   `SimpleGraph (Fin n)` (instances `permSmul`, `MulAction`); the bridge
   `mem_aut_iff` identifies the stabilizer with the usual automorphism group
   (adjacency preservation in both directions); **orbit-stabilizer**
   `card_orbit_mul_card_aut` gives `|orbit| · |Aut G| = n!`, whence the
   description length `descLength G = log₂ |orbit|` and its quotient form
   `descLength_eq`: `b = log₂ (n! / |Aut G|)` (Eq. 4 of the paper) — the
   graph counterpart of the group-shaped `infoBits` definition.
   Migration from the dissolved module `GenEFT.lean` (#17480, arbitration
   c.38: dissolution, not a parallel module).

Dependencies: Mathlib only (`MulAut`, `Fintype.card`, `Real.log2`,
`SimpleGraph`, `MulAction`, `Real.logb`).
-/

namespace LearningTheory.EffectiveTheory_en

/-- Informational content of a finite-group structure (R06):
`b = log₂(n! / |Aut G|)` — bits of a raw labelling `n!` minus the bits
offered by the symmetries `|Aut G|`. -/
noncomputable def infoBits (G : Type*) [Group G] [Fintype G] [DecidableEq G] : ℝ :=
  Real.logb 2 ((Nat.factorial (Fintype.card G) : ℝ) / ((Fintype.card (MulAut G)) : ℝ))

/-- **Trivial group**: `b = log₂(1!/1) = 0` — a single labelling, a single
symmetry, no bit of information. -/
theorem infoBits_trivial (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G = 1) :
    infoBits G = 0 := by
  have hAut : Fintype.card (MulAut G) = 1 := by
    have hsub : Subsingleton G := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    haveI : Inhabited (MulAut G) := ⟨1⟩
    haveI : Unique (MulAut G) :=
      ⟨⟨1⟩, fun f => MulEquiv.ext fun x => hsub.elim (f x) x⟩
    simp [Fintype.card_unique]
  simp [infoBits, hG, hAut, Real.logb_one]

/-- **Two-element group**: its automorphism group is trivial.
An automorphism fixes `1`; the single element `a ≠ 1` cannot map there
(injectivity), so every automorphism is the identity. -/
theorem card_mulAut_eq_one {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G = 2) :
    Fintype.card (MulAut G) = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : G, a ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : Fintype.card G = 1 :=
      (Fintype.card_eq_one_iff.mpr ⟨(1 : G), fun y => hcon y⟩)
    omega
  have hcov : ∀ x : G, x = 1 ∨ x = a := by
    intro x
    by_contra hx
    push_neg at hx
    have hm1 : (1 : G) ∉ ({a, x} : Finset G) := by simp [ha.symm, (hx.1).symm]
    have hm2 : a ∉ ({x} : Finset G) := by simp [(hx.2).symm]
    have h3 : ({1, a, x} : Finset G).card = 3 := by
      rw [Finset.card_insert_of_notMem hm1, Finset.card_insert_of_notMem hm2,
        Finset.card_singleton]
    have hle : ({1, a, x} : Finset G).card ≤ Fintype.card G :=
      Finset.card_le_card (Finset.subset_univ _)
    omega
  haveI : Unique (MulAut G) :=
    ⟨⟨1⟩, fun f => MulEquiv.ext fun x => by
      show f x = x
      rcases hcov x with hx | hx
      · rw [hx, map_one]
      · rw [hx]
        have hfa : f a ≠ 1 := fun h =>
          ha (f.injective (by rw [h, map_one]))
        rcases hcov (f a) with h | h
        · exact absurd h hfa
        · rw [h]⟩
  simp [Fintype.card_unique]

/-- **Any two-element group**: `b = log₂(2!/1) = 1` bit exactly —
no symmetry discounts the cost of the labelling. -/
theorem infoBits_card_two {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G = 2) :
    infoBits G = 1 := by
  have hAut := card_mulAut_eq_one hG
  simp only [infoBits, hG, hAut]
  norm_num

/-- **Cyclic group C₇**: the automorphism group of a cyclic group of order
`n` has φ(n) elements (`IsCyclic.card_mulAut` — the images of the generator
are exactly its invertible powers), so `|Aut C₇| = φ(7) = 6` and
`b = log₂(7!/6) = log₂ 840 ≈ 9.71` bits: the 6 rotations discount the
labelling by log₂ 6 ≈ 2.58 bits. Companion of the `CircleOfDays` module
(the rotation of the days there is the representation of this C₇). -/
theorem infoBits_cyclicSeven :
    infoBits (Multiplicative (ZMod 7)) = Real.logb 2 840 := by
  have hcard : Fintype.card (Multiplicative (ZMod 7)) = 7 := by norm_num
  have h1 : Nat.card (Multiplicative (ZMod 7)) = 7 := by
    rw [Nat.card_eq_fintype_card]; exact hcard
  have hAut : Fintype.card (MulAut (Multiplicative (ZMod 7))) = 6 := by
    have h := IsCyclic.card_mulAut (Multiplicative (ZMod 7))
    rw [h1, Nat.totient_prime (by norm_num : (7 : ℕ).Prime)] at h
    rw [Nat.card_eq_fintype_card] at h
    exact h
  have hd : ((7 : ℕ).factorial : ℝ) / ((6 : ℕ) : ℝ) = 840 := by norm_num
  simp only [infoBits, hcard, hAut, hd]

/-! ## Statics on graphs — relabelling, automorphisms, description length

Section III of GenEFT: relabelling the `n` nodes of a graph is the natural
action of `Equiv.Perm (Fin n)` on `SimpleGraph (Fin n)`; graphs "of the same
structure" are exactly the orbit, and orbit-stabilizer gives
`|orbit| · |Aut G| = n!` — encoding `G` amounts to choosing a point in an
orbit of size `n! / |Aut G|`, whence `b = log₂ (n! / |Aut G|)`. Migrated from
the dissolved module `GenEFT.lean` (#17480). -/

section Statics

variable {n : ℕ}

/-- The **relabelling** of a graph by a permutation `σ` of the vertices:
the edge `i—j` exists in `σ • G` iff `σ⁻¹ i — σ⁻¹ j` exists in `G`.
This is the natural action of the symmetric group on graph structures. -/
instance permSmul : SMul (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) where
  smul σ G :=
    { Adj := fun i j => G.Adj (σ.symm i) (σ.symm j)
      symm := by
        apply Std.Symm.mk
        intro i j h
        exact G.symm.symm (σ.symm i) (σ.symm j) h
      loopless := by
        apply Std.Irrefl.mk
        intro i h
        exact G.loopless.irrefl (σ.symm i) h }

/-- `Equiv.Perm (Fin n)` acts on graphs on `Fin n` by relabelling:
the symmetric group performs the vertex renamings. -/
instance : MulAction (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) where
  one_smul G := by
    ext i j
    have hone : ∀ x, (1 : Equiv.Perm (Fin n)).symm x = x := by
      intro x
      rw [show ((1 : Equiv.Perm (Fin n)).symm) = 1 from inv_one]
      exact Equiv.Perm.one_apply x
    show G.Adj ((1 : Equiv.Perm (Fin n)).symm i) ((1 : Equiv.Perm (Fin n)).symm j) ↔ G.Adj i j
    rw [hone i, hone j]
  mul_smul σ τ G := by
    ext i j
    have hst : ∀ x, (σ * τ).symm x = τ.symm (σ.symm x) := by
      intro x
      rw [show (σ * τ).symm = τ.symm * σ.symm from mul_inv_rev σ τ]
      simp [Equiv.Perm.mul_apply]
    show G.Adj ((σ * τ).symm i) ((σ * τ).symm j) ↔
      G.Adj (τ.symm (σ.symm i)) (τ.symm (σ.symm j))
    rw [hst i, hst j]

/-- **Bridge with the usual definition**: a permutation lies in the
stabilizer (the graph's "automaton", `Aut G`) **iff** it preserves
adjacency in both directions — the relabelling stabilizer IS the
automorphism group of the graph. -/
theorem mem_aut_iff {G : SimpleGraph (Fin n)} (σ : Equiv.Perm (Fin n)) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) G ↔
      ∀ i j, G.Adj i j ↔ G.Adj (σ i) (σ j) := by
  constructor
  · intro h i j
    have hsmul : σ • G = G := h
    constructor
    · intro hij
      have h3 : (σ • G).Adj (σ i) (σ j) := by
        show G.Adj (σ.symm (σ i)) (σ.symm (σ j))
        simpa using hij
      rw [hsmul] at h3
      exact h3
    · intro hij
      -- the graph equality σ • G = G transported to the pair (σ i, σ j)
      have hAdjeq : (σ • G).Adj = G.Adj := SimpleGraph.ext_iff.mp hsmul
      have h4 : (σ • G).Adj (σ i) (σ j) := by rw [hAdjeq]; exact hij
      have h5 : (σ • G).Adj (σ i) (σ j) ↔ G.Adj i j := by
        show G.Adj (σ.symm (σ i)) (σ.symm (σ j)) ↔ G.Adj i j
        simp
      exact h5.mp h4
  · intro h
    show σ • G = G
    ext i j
    show G.Adj (σ.symm i) (σ.symm j) ↔ G.Adj i j
    simpa using h (σ.symm i) (σ.symm j)

/-- **Orbit-stabilizer for graphs** (Section III of the paper): the number
of graphs of the same structure as `G` (its orbit under relabelling) times
the number of automorphisms of `G` (its stabilizer) equals `n!`. Encoding the
structure means choosing a point of the orbit. -/
theorem card_orbit_mul_card_aut (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)]
    [Fintype ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) G)] :
    Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G) *
      Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) =
        Fintype.card (Equiv.Perm (Fin n)) := by
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (G := Equiv.Perm (Fin n)) G

/-- The **description length** of the graph `G` (Eq. 4 of the paper): the
base-2 log of the size of the relabelling orbit, `b = log₂ (n! / |Aut G|)`.
This is the number of bits of the "shortest program" producing `G` up to
structure. -/
noncomputable def descLength (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)] : ℝ :=
  Real.logb 2 (Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G))

/-- `descLength` in quotient form: `b = log₂ (n! / |Aut G|)` — the
form used in the paper (Section III). -/
theorem descLength_eq (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)]
    [Fintype ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) G)] :
    descLength G =
      Real.logb 2 (Fintype.card (Equiv.Perm (Fin n)) /
        Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G)) := by
  have h := card_orbit_mul_card_aut G
  -- the stabilizer contains the identity, hence is non-empty with cardinal > 0
  have hcardpos : 0 < Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) :=
    Fintype.card_pos_iff.2 ⟨⟨1, one_smul _ G⟩⟩
  have haut : (Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast hcardpos)
  unfold descLength
  congr 1
  rw [eq_div_iff haut]
  exact_mod_cast h

end Statics

end LearningTheory.EffectiveTheory
