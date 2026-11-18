import Percolation.Basic_en
import Percolation.Boundary_en
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Finite percolation kernel — finite sharpness by counting (tranche 5)

Top floor of the finite socle: a **finite sharpness inequality**, a uniform
(`p = 1/2`) parametric form whose limit is the exponential decay inequality of
the reference article on supercritical percolation
(Diskin–Easo–Radhakrishnan–Sudakov–Tassion, arXiv:2603.03257, §3.0). The socle
stays uniform (the general Bernoulli-`p` case is out of the socle's scope,
cf `Percolation/Basic_en.lean`): the statement below lives on the counting
measure of `Finset (Edge G)`.

The argument is a **counting renewal** in three steps:

1. **Full boundary** `graphBoundary G A`: the edges of `G` (open or closed)
   leaving `A` — the ω-independent object of which `boundary` (tranche 4) is
   the trace on `ω`.
2. **Confinement ⇒ forced-closed edges**: if `A` is ω-closed, every edge of
   the full boundary is closed — the confinement event lives in the subcube
   where `|δA|` coordinates are fixed, hence has at most `2^(N − |δA|)`
   configurations.
3. **Union over small candidates**: the open component of `v` is itself
   ω-closed, so the event « component of size ≤ k » is covered by the union of
   confinements to candidates `A ∋ v` of size ≤ k — each candidate paying its
   `2^(N − |δA|)` factor.

The outcome is theorem `card_smallClusterEvent_le`: the « probability »
(counting measure normalised by `2^N`) that the component of `v` stays of size
≤ k is at most `Σ_{A ∋ v, |A| ≤ k} 2^(−|δA|)` — the finite form of the
article's inequality: an isoperimetric profile growing with `|A|` is enough to
crush small components exponentially.

The module also adds the missing link of the socle's Harris–Kleitman trilogy:
the **mixed** form `harris_kleitman_upper_lower` (an increasing and a
decreasing event are anticorrelated), instantiated on connectivity ×
confinement.

i18n convention EPIC #4980: docstrings in English here; the French mirror lives
in `Percolation/Sharpness.lean` (byte-identical apart from docstrings/comments).
-/

set_option linter.unusedSectionVars false

namespace Percolation_en

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [Fintype (Edge G)] [DecidableEq (Edge G)]

-- ============================================================
-- Confinement events (decreasing)
-- ============================================================

/-- **Closure event**: the configurations `ω` in which `A` is ω-closed — no
open edge leaves it. This is a **decreasing** event: removing open edges
cannot open an exit. -/
noncomputable def closedEvent (A : Finset V) : Finset (Finset (Edge G)) :=
  Finset.univ.filter (fun ω => openEdgeClosed G ω (↑A : Set V))

/-- **The closure event is decreasing**: if `A` is closed in a configuration,
it stays closed in any subconfiguration. -/
theorem closedEvent_isLowerSet (A : Finset V) :
    IsLowerSet (closedEvent G A : Set (Finset (Edge G))) := by
  intro ω₁ ω₂ hsub hmem
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro u v hu hadj
  exact ((Finset.mem_filter.mp hmem).2) hu (openAdj_mono G hsub u v hadj)

/-- **"Small component" event**: the configurations `ω` in which the open
component of `v` has at most `k` vertices. A **decreasing** event: adding open
edges can only grow the component. -/
noncomputable def smallClusterEvent (v : V) (k : ℕ) : Finset (Finset (Edge G)) :=
  Finset.univ.filter (fun ω => (Component G ω v).toFinset.card ≤ k)

/-- **The "small component" event is decreasing**: the component can only grow
when edges are opened (`connected_mono`). -/
theorem smallClusterEvent_isLowerSet (v : V) (k : ℕ) :
    IsLowerSet (smallClusterEvent G v k : Set (Finset (Edge G))) := by
  intro ω₁ ω₂ hsub hmem
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hmono : (Component G ω₂ v).toFinset ⊆ (Component G ω₁ v).toFinset := by
    refine Set.toFinset_subset_toFinset.mpr ?_
    intro w hw
    exact connected_mono G hsub v w hw
  exact le_trans (Finset.card_le_card hmono) ((Finset.mem_filter.mp hmem).2)

-- ============================================================
-- Mixed Harris–Kleitman: increasing × decreasing = anticorrelated
-- ============================================================

/-- **Uniform Harris–Kleitman inequality, mixed form**: an **increasing** event
`𝒜` and a **decreasing** event `ℬ` are **anticorrelated** — in the uniform
measure (`p = 1/2`), the probability of the intersection is at most the product
of the probabilities. This is the link the socle
(`harris_kleitman_upper_upper`, `harris_kleitman_lower_lower`) left open; the
proof dualises the "two decreasing" form by taking the complement of the
increasing event. -/
theorem harris_kleitman_upper_lower {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    #(𝒜 ∩ ℬ) * 2 ^ Fintype.card α ≤ #𝒜 * #ℬ := by
  classical
  have huniv : (Finset.univ : Finset (Finset α)).card = 2 ^ Fintype.card α := by
    rw [Finset.card_univ, Fintype.card_finset]
  -- The complement of an increasing event is decreasing.
  have hA' : IsLowerSet ((Finset.univ \ 𝒜 : Finset (Finset α)) : Set (Finset α)) := by
    intro ω₁ ω₂ hsub hmem
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun h => (Finset.mem_sdiff.mp hmem).2 (h𝒜 hsub h)⟩
  -- "Two decreasing" Harris–Kleitman on (complement of 𝒜, ℬ).
  have hk := harris_kleitman_lower_lower (Finset.univ \ 𝒜 : Finset (Finset α)) ℬ hA' hℬ
  have hcardA : #(Finset.univ \ 𝒜) = 2 ^ Fintype.card α - #𝒜 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ 𝒜), huniv]
  have hint : ((Finset.univ \ 𝒜 : Finset (Finset α)) ∩ ℬ) = ℬ \ (𝒜 ∩ ℬ) := by
    ext ω; simp [Finset.mem_sdiff]; tauto
  rw [hint, Finset.card_sdiff_of_subset (inter_subset_right), hcardA] at hk
  -- hk : (2^n − #𝒜) · #ℬ ≤ 2^n · (#ℬ − #(𝒜 ∩ ℬ)) ; truncated ℕ arithmetic.
  have hN₂ : #(𝒜 ∩ ℬ) ≤ #ℬ := card_le_card (inter_subset_right)
  have e1 : (2 ^ Fintype.card α - #𝒜) * #ℬ
      = 2 ^ Fintype.card α * #ℬ - #𝒜 * #ℬ := Nat.sub_mul _ _ _
  have e2 : 2 ^ Fintype.card α * (#ℬ - #(𝒜 ∩ ℬ))
      = 2 ^ Fintype.card α * #ℬ - 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) := Nat.mul_sub _ _ _
  rw [e1, e2] at hk
  have final : 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) ≤ #𝒜 * #ℬ :=
    (Nat.sub_le_sub_iff_left (Nat.mul_le_mul_left _ hN₂)).mp hk
  exact Nat.mul_comm _ _ ▸ final

/-- **Connectivity × confinement anticorrelation**: the event "`u` and `v` are
connected" (increasing, `connectedEvent_isUpperSet`) and the event "`A` is
closed" (decreasing) are anticorrelated — the finite uniform form of the
supercritical intuition: being confined penalises large connections. -/
theorem card_inter_connected_closed_le (u v : V) (A : Finset V) :
    #((connectedEvent G u v) ∩ (closedEvent G A)) * 2 ^ Fintype.card (Edge G) ≤
      #(connectedEvent G u v) * #(closedEvent G A) :=
  harris_kleitman_upper_lower _ _ (connectedEvent_isUpperSet G)
    (closedEvent_isLowerSet G A)

-- ============================================================
-- Full boundary and confinement counting
-- ============================================================
variable (G : SimpleGraph V) [Fintype (Edge G)] [DecidableEq (Edge G)] [DecidableRel G.Adj]

/-- **Full boundary `δA`**: all edges of `G` (open or not) leaving `A` — the
ω-independent object of the counting. The open boundary `boundary` of tranche 4
is its trace on a configuration (`boundary_eq_inter`). -/
def graphBoundary (A : Finset V) : Finset (Edge G) :=
  Finset.univ.filter (fun e : Edge G =>
    ∃ (u : V) (v : V) (huv : G.Adj u v),
      u ∈ A ∧ v ∉ A ∧ e = ⟨s(u, v), (show s(u, v) ∈ G.edgeSet from huv)⟩)

/-- **The open boundary is the trace of the full boundary**: `∂A` (tranche 4)
is the intersection of the configuration `ω` with the full boundary. -/
theorem boundary_eq_inter_graphBoundary (ω : Finset (Edge G)) (A : Finset V) :
    boundary G ω A = ω ∩ graphBoundary G A := by
  ext e
  simp [boundary, graphBoundary, Finset.mem_filter, Finset.mem_inter]

/-- **Confinement ⇒ full boundary closed**: if `A` is ω-closed, no edge of the
full boundary is open — `|δA|` coordinates are **forced closed**, the lever of
the counting. -/
theorem disjoint_graphBoundary_of_openEdgeClosed {ω : Finset (Edge G)} {A : Finset V}
    (h : openEdgeClosed G ω (↑A : Set V)) : Disjoint ω (graphBoundary G A) :=
  Finset.disjoint_left.mpr fun _e heω hebd =>
    let ⟨_, _, _, huv, hu, hv, heq⟩ := Finset.mem_filter.mp hebd
    hv (h hu ⟨huv, heq ▸ heω⟩)

/-- **Confinement counting**: the configurations where `A` is ω-closed are at
most `2^(N − |δA|)` — the event lives in the subcube where the `|δA|` full
boundary edges are fixed closed (`N` = total number of edges). -/
theorem card_closedEvent_le (A : Finset V) :
    (closedEvent G A).card ≤
      2 ^ ((Finset.univ : Finset (Edge G)).card - (graphBoundary G A).card) := by
  have hsub : (closedEvent G A) ≤ (Finset.univ \ graphBoundary G A).powerset := by
    intro ω hω
    refine Finset.mem_powerset.mpr (Finset.subset_sdiff.mpr
      ⟨Finset.subset_univ _, disjoint_graphBoundary_of_openEdgeClosed G
        ((Finset.mem_filter.mp hω).2)⟩)
  calc (closedEvent G A).card
      ≤ ((Finset.univ \ graphBoundary G A).powerset).card := Finset.card_le_card hsub
    _ = 2 ^ (Finset.univ \ graphBoundary G A).card := Finset.card_powerset _
    _ = 2 ^ ((Finset.univ : Finset (Edge G)).card - (graphBoundary G A).card) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]

/-- **Confinement candidates for `v`**: the finite sets containing `v`, of
cardinality at most `k` — the possible witnesses of "the component of `v`
lives in `A`". -/
def confineCandidates (v : V) (k : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun A => v ∈ A ∧ A.card ≤ k)

/-- **Covering of the "small component" event**: if the component of `v` has
at most `k` vertices, it is itself a candidate — ω-closed (`component_closed`),
containing `v` (`component_self`), of size ≤ k. -/
theorem smallClusterEvent_subset_biUnion (v : V) (k : ℕ) :
    (smallClusterEvent G v k) ≤ (confineCandidates v k).biUnion (closedEvent G) := by
  intro ω hω
  rw [Finset.mem_biUnion]
  refine ⟨(Component G ω v).toFinset, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Set.mem_toFinset.mpr (component_self G v), (Finset.mem_filter.mp hω).2⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Set.coe_toFinset]
    exact component_closed (ω := ω) G v

/-- **Finite sharpness inequality** (uniform, `p = 1/2`): the configurations
where the open component of `v` stays of size ≤ k are at most

`Σ_{A ∋ v, |A| ≤ k} 2^(N − |δA|)`,

i.e., after normalising by `2^N` (the uniform measure), the finite form of the
decay inequality of the supercritical article (arXiv:2603.03257, §3.0):
`P(|C(v)| ≤ k) ≤ Σ_{A ∋ v, |A| ≤ k} 2^(−|δA|)`. Any isoperimetric profile
bounding `|δA|` from below therefore crushes small components exponentially —
the finite parametric content that the supercritical limit of the article
generalises. -/
theorem card_smallClusterEvent_le (v : V) (k : ℕ) :
    (smallClusterEvent G v k).card ≤ ∑ A ∈ confineCandidates v k,
      2 ^ ((Finset.univ : Finset (Edge G)).card - (graphBoundary G A).card) := by
  calc (smallClusterEvent G v k).card
      ≤ ((confineCandidates v k).biUnion (closedEvent G)).card :=
        Finset.card_le_card (smallClusterEvent_subset_biUnion G v k)
    _ ≤ ∑ A ∈ confineCandidates v k, (closedEvent G A).card := Finset.card_biUnion_le
    _ ≤ ∑ A ∈ confineCandidates v k,
          2 ^ ((Finset.univ : Finset (Edge G)).card - (graphBoundary G A).card) :=
        Finset.sum_le_sum fun A _ => card_closedEvent_le G A

-- ============================================================
-- C₃ / C₄ witnesses: the counting evaluated on the triangle and the square
-- ============================================================

/-- **Full boundary of the singleton `{0}` in `C₃`**: the two edges `0—1` and
`0—2` leave `{0}`. -/
theorem graphBoundary_C3_singleton :
    #(graphBoundary C3 ({0} : Finset (Fin 3))) = 2 := by decide

/-- **Full boundary of the singleton `{0}` in `C₄`**: the two edges `0—1` and
`0—3` leave `{0}` (the square has no `0—2` edge). -/
theorem graphBoundary_C4_singleton :
    #(graphBoundary C4 ({0} : Finset (Fin 4))) = 2 := by decide

/-- **A single confinement candidate `k = 1` on `C₃`**: the set `{0}` itself
(the candidates depend only on the vertex type, not on `G`). -/
theorem confineCandidates_C3_one :
    (confineCandidates (0 : Fin 3) 1).card = 1 := by decide

/-- **A single confinement candidate `k = 1` on `C₄`**: the set `{0}` itself. -/
theorem confineCandidates_C4_one :
    (confineCandidates (0 : Fin 4) 1).card = 1 := by decide

/-- **The sharpness sum on `C₃` (`k = 1`) is exactly `2 = 2^(3−2)`**: a single
candidate `{0}`, of full boundary `2`, for `N = 3` edges. -/
theorem sharpness_sum_C3_one :
    ∑ A ∈ confineCandidates (0 : Fin 3) 1,
      2 ^ ((Finset.univ : Finset (Edge C3)).card - #(graphBoundary C3 A)) = 2 := by
  decide

/-- **The sharpness sum on `C₄` (`k = 1`) is exactly `4 = 2^(4−2)`**: a single
candidate `{0}`, of full boundary `2`, for `N = 4` edges. -/
theorem sharpness_sum_C4_one :
    ∑ A ∈ confineCandidates (0 : Fin 4) 1,
      2 ^ ((Finset.univ : Finset (Edge C4)).card - #(graphBoundary C4 A)) = 4 := by
  decide

/-- **Finite sharpness on `C₃`**: at most `2` configurations out of `2^3 = 8`
keep the component of `0` confined to a single vertex — a proportion
`≤ 2^(−2) = 1/4`. The bound is tight (the two configurations close both edges
at `0`). -/
theorem sharpness_C3_one : (smallClusterEvent C3 (0 : Fin 3) 1).card ≤ 2 := by
  have h := card_smallClusterEvent_le C3 (0 : Fin 3) 1
  rw [sharpness_sum_C3_one] at h
  exact h

/-- **Finite sharpness on `C₄`**: at most `4` configurations out of `2^4 = 16`
keep the component of `0` confined to a single vertex — a proportion
`≤ 2^(−2) = 1/4`. -/
theorem sharpness_C4_one : (smallClusterEvent C4 (0 : Fin 4) 1).card ≤ 4 := by
  have h := card_smallClusterEvent_le C4 (0 : Fin 4) 1
  rw [sharpness_sum_C4_one] at h
  exact h

end Percolation_en
