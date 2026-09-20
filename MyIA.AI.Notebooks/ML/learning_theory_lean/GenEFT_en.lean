import Mathlib

/-!
# GenEFT — description length, clustering, A vs r competition

English mirror of `GenEFT.lean` (FR-first canonical), EPIC #4980 (i18n Lean).
Convention ratified 2026-07-04 (issue #4980): namespace `GenEFT_en`.
Statements, proofs and tactic blocks are byte-identical to the canonical
file; only this documentation is translated.

**R06** tranche of the Tegmark corpus (EPIC #16741, claim #16752):
*GenEFT: A Generative Physics Framework for Automating Emergent Function
Tracking in Learning Machines* (Baek, Liu, Tegmark, arXiv:2402.05916v2).

This module formalizes the three quantitative pieces of the paper that
admit a short, complete proof:

1. **Statics — orbit-based description length** (Section III). Relabelling
   the `n` nodes of a graph `G` is the natural action of `Equiv.Perm (Fin n)`
   on `SimpleGraph (Fin n)`; the graphs "with the same structure as `G`" are
   exactly its orbit, and **orbit-stabilizer** gives
   `|orbit| · |Aut G| = n!`: encoding `G` amounts to choosing a point in an
   orbit of size `n! / |Aut G|`, hence the description length
   `b = log₂ (n! / |Aut G|)`. The bridge `mem_aut_iff` identifies the
   stabilizer with the usual notion of graph automorphism (adjacency
   preservation in both directions).

2. **Theorem 1 — clustering by an injective decoder** (Section IV). A
   classification autoencoder (input: two nodes, output: `1` if same class,
   `0` otherwise) with **zero** training loss and an **injective** decoder
   separates the classes exactly: two nodes have the same embedding **iff**
   they have the same label. The "perturbation" direction does not even use
   injectivity; the "grouping" direction uses it with the witness
   `k := i` (no third-party existence assumption).

3. **Dynamics — eq. 16 and the competition invariant** (Appendix C, eq. 10).
   For the localized quadratic loss of the paper, the external forcing of
   the gradient flow is **common-mode**: it cancels in the difference of
   trajectories, whose separation `r = x₁ − x₂` evolves autonomously
   (`rel_eqn_autonomous`). On the reduced `a₂, c` system, the quantity
   `η_x a₂² − 2 η_A c²` is **conserved** (`competition_invariant`): this is
   the quantitative core of Theorem 3 (critical learning rates), the
   competition between the growth of channel `a₂` and the separation `c`
   being arbitrated by this invariant.

Out of scope for V1 (quoted for honesty, cf. paper lines): the concrete
computation of `|Aut|` for the total-order tournament (`|Aut| = 1`,
b = log₂ n!) and the complete bipartite graph `K_{a,c}` (`|Aut| = a!·c!`,
b ≈ k·n) — each bound needs a dedicated degree argument; Theorem 2
(convergence, asymptotic); the stochastic balls-in-buckets derivation
(eq. 8). -/

namespace GenEFT_en

/-! ## Section 1 — Statics: description length via orbit-stabilizer -/

section Statics

variable {n : ℕ}

/-- The **relabeling** of a graph by a permutation `σ` of the vertices:
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

/-- `Equiv.Perm (Fin n)` acts on graphs over `Fin n` by relabeling:
the symmetric group performs vertex renamings. -/
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
stabilizer (the "automorphism group" `Aut G` of the graph) **iff** it
preserves adjacency in both directions — the stabilizer of relabeling IS
the automorphism group of the graph. -/
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
of graphs with the same structure as `G` (its orbit under relabeling) times
the number of automorphisms of `G` (its stabilizer) equals `n!`. Encoding
the structure means choosing a point of the orbit. -/
theorem card_orbit_mul_card_aut (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)]
    [Fintype ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) G)] :
    Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G) *
      Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) =
        Fintype.card (Equiv.Perm (Fin n)) := by
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (G := Equiv.Perm (Fin n)) G

/-- The **description length** of the graph `G` (eq. 4 of the paper): the
base-2 logarithm of the size of the relabeling orbit,
`b = log₂ (n! / |Aut G|)`. This is the bit count of the "shortest program"
that produces `G` up to structure. -/
noncomputable def descLength (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)] : ℝ :=
  Real.logb 2 (Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G))

/-- `descLength` as a quotient: `b = log₂ (n! / |Aut G|)` — the form used
in the paper (Section III). -/
theorem descLength_eq (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)]
    [Fintype ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) G)] :
    descLength G =
      Real.logb 2 (Fintype.card (Equiv.Perm (Fin n)) /
        Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G)) := by
  have h := card_orbit_mul_card_aut G
  -- the stabilizer contains the identity, hence is nonempty with positive cardinal
  have hcardpos : 0 < Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) :=
    Fintype.card_pos_iff.2 ⟨⟨1, one_smul _ G⟩⟩
  have haut : (Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast hcardpos)
  unfold descLength
  congr 1
  rw [eq_div_iff haut]
  exact_mod_cast h

end Statics

/-! ## Section 2 — Theorem 1: clustering by an injective decoder -/

section Clustering

variable {ι V : Type*}

/-- **Theorem 1 of the paper (quantitative core)**: a classification
autoencoder — input `(E i, E k)` (the embeddings of two nodes), output
`dec` equal to `1` for the same class and `0` otherwise — whose training
loss is **zero** (every pair is correctly classified, hypothesis `hLoss`)
and whose decoder is **injective** (`hInj`) **clusters the classes
exactly**: two nodes have the same embedding **if and only if** they have
the same label.

The `←` direction (same class ⟹ same embedding) is the one requiring
injectivity, with the witness `k := i` — no third-party existence is
needed. The `→` direction (equal embeddings, different classes ⟹
contradiction) only uses label correctness on the pair `(i, i)`. -/
theorem clustering (label : ι → Bool) (E : ι → V) (dec : V × V → ℝ)
    (hInj : Function.Injective dec)
    (hLoss : ∀ i k, dec (E i, E k) = if label i = label k then 1 else 0) :
    ∀ i j, E i = E j ↔ label i = label j := by
  intro i j
  constructor
  · -- equal embeddings, labels assumed different: contradiction 1 ≠ 0
    intro hE
    by_contra hlab
    have hii : dec (E i, E i) = 1 := by
      rw [hLoss i i]; simp
    have hji : dec (E j, E i) = 0 := by
      rw [hLoss j i]
      have : ¬ (label j = label i) := fun h => hlab h.symm
      simp [this]
    rw [hE] at hii hji
    rw [hii] at hji
    exact absurd hji (by norm_num)
  · -- same label: the decoder answers 1 on (i, i) and on (j, i),
    -- injectivity equalizes the inputs, hence the embeddings
    intro hlab
    have hii : dec (E i, E i) = 1 := by
      rw [hLoss i i]; simp
    have hji : dec (E j, E i) = 1 := by
      rw [hLoss j i]
      simp [hlab.symm]
    have hpair : (E i, E i) = (E j, E i) := hInj (by rw [hii, hji])
    exact (Prod.mk.injEq _ _ _ _).mp hpair |>.1

end Clustering

/-! ## Section 3 — Dynamics: eq. 16 (autonomy) and eq. 10 (invariant) -/

section Dynamics

/-- **Eq. 10 — the competition invariant.** On the reduced system of the
paper (Appendix C), the channel `a₂` and the separation `c` evolve via
`da₂/dt = -2 η_A c² a₂` and `dc/dt = -η_x a₂² c`: each inhibits the growth
of the other. The quantity `η_x a₂² - 2 η_A c²` is **constant along the
trajectories** — this invariant arbitrates the competition and yields the
critical learning rates of Theorem 3. -/
theorem competition_invariant (ηx ηA : ℝ) (a₂ c : ℝ → ℝ)
    (ha : ∀ t, HasDerivAt a₂ (-(2 * ηA) * (c t ^ 2) * a₂ t) t)
    (hc : ∀ t, HasDerivAt c (-(ηx) * (a₂ t ^ 2) * c t) t) (t : ℝ) :
    HasDerivAt (fun t => ηx * a₂ t ^ 2 - 2 * ηA * c t ^ 2) 0 t := by
  have hsub : HasDerivAt (fun t => ηx * a₂ t ^ 2 - 2 * ηA * c t ^ 2)
      (ηx * (2 * a₂ t ^ (2 - 1) * (-(2 * ηA) * (c t ^ 2) * a₂ t)) -
        2 * ηA * (2 * c t ^ (2 - 1) * (-(ηx) * (a₂ t ^ 2) * c t))) t := by
    have h1 : HasDerivAt (fun t => ηx * a₂ t ^ 2)
        (ηx * (2 * a₂ t ^ (2 - 1) * (-(2 * ηA) * (c t ^ 2) * a₂ t))) t :=
      ((ha t).pow 2).const_mul ηx
    have h2 : HasDerivAt (fun t => 2 * ηA * c t ^ 2)
        (2 * ηA * (2 * c t ^ (2 - 1) * (-(ηx) * (a₂ t ^ 2) * c t))) t :=
      ((hc t).pow 2).const_mul (2 * ηA)
    exact h1.sub h2
  have hzero : (ηx * (2 * a₂ t ^ (2 - 1) * (-(2 * ηA) * (c t ^ 2) * a₂ t)) -
        2 * ηA * (2 * c t ^ (2 - 1) * (-(ηx) * (a₂ t ^ 2) * c t))) = 0 := by
    norm_num
    ring
  rw [hzero] at hsub
  exact hsub

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Eq. 16 of Appendix C — autonomy of the separation.** In the gradient
flow of the paper, each trajectory undergoes the same external forcing `g`
(the recall term toward the target, carried by `Aᵀ y`) in addition to the
linear flow `F` (the `-η_x AᵀA` term). This forcing is **common-mode**: in
the difference `x₁ - x₂` it cancels exactly, and the separation evolves
autonomously — a Hooke spring `d(x₁ - x₂)/dt = F (x₁ - x₂)` with the
weakening `F = -η_x AᵀA`. -/
theorem rel_eqn_autonomous (x₁ x₂ : ℝ → E) (F : E →L[ℝ] E) (g : ℝ → E)
    (h₁ : ∀ t, HasDerivAt x₁ (F (x₁ t) + g t) t)
    (h₂ : ∀ t, HasDerivAt x₂ (F (x₂ t) + g t) t) (t : ℝ) :
    HasDerivAt (fun t => x₁ t - x₂ t) (F (x₁ t - x₂ t)) t := by
  have hd : HasDerivAt (fun t => x₁ t - x₂ t)
      ((F (x₁ t) + g t) - (F (x₂ t) + g t)) t :=
    (h₁ t).sub (h₂ t)
  convert hd using 2
  simp only [ContinuousLinearMap.map_sub]
  abel

end Dynamics

end GenEFT_en
