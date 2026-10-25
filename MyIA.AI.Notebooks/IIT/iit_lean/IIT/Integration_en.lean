/-
! # Cut integration — relational proxy (Phase 1)

First module of the first Lean lake of the IIT series (Epic Aaronson #16781,
vein 5 — "the object that bit IIT, in Lean if possible"). Sub-grain #18599.

What is formalized here is a **relational decomposition-by-cut proxy**, not a
version of Φ (see the grade below). A deterministic system with `n` elements
is a function on states; a cut splits it into two nonempty sides; the cut is
*independent* if the image of the system is exactly the product of the images
of its parts. Aaronson's critique (build an object with huge integration and
trivial behaviour) becomes a **pair of theorems**:

* `cutIndep_of_sides_independent` — a system whose two halves evolve
  independently of each other is **decomposable**;
* `broadcast_integrated` — the *parity broadcast* system (every element takes
  the parity of the global state) is **integrated for every cut**, while its
  dynamics is trivial: `broadcast_two_cycle` shows every orbit reaches a
  fixed point in two steps.

**Grade (the forbidden overreach)**: the proxy measures the deterministic
decomposition of the image. It captures neither effective information under
perturbation, nor the minimal partition in the MIP sense, nor any numerical
value of Φ. The quantitative cardinality (`|imA| * |imB| - |im f|`) is
deferred to Phase 2. The source of the critique is a blog post (2014), not a
formal publication: this lake **creates** the formal object; it is not a
transcription of one.

No Mathlib dependency: the proofs are constructive witnesses over `Fin`,
`Bool` and `xor`; no cardinal arithmetic is needed.
-/

namespace IIT_en

/-- A state of a system with `n` elements: a Boolean valuation of the elements. -/
abbrev State (n : Nat) := Fin n → Bool

/-- Deterministic system: transition matrix as a function on states. -/
abbrev System (n : Nat) := State n → State n

/-- A nontrivial cut of a system with `n` elements: each side carries at least one element. -/
structure Cut (n : Nat) where
  /-- `sel i = true` puts element `i` on side A, `false` on side B. -/
  sel : Fin n → Bool
  /-- Side A is nonempty. -/
  ha : ∃ i, sel i = true
  /-- Side B is nonempty. -/
  hb : ∃ i, sel i = false

/-- Side-A pattern of a state: A bits kept, B bits set to `false`. -/
def projT {n : Nat} (c : Cut n) (s : State n) : State n :=
  fun i => if c.sel i then s i else false

/-- Side-B pattern of a state: B bits kept, A bits set to `false`. -/
def projF {n : Nat} (c : Cut n) (s : State n) : State n :=
  fun i => if c.sel i then false else s i

/-- A cut is **independent** for a system if every pair of separately
realizable patterns is jointly realizable: the image of the system is the
product of the images of its two parts. -/
def cutIndep {n : Nat} (c : Cut n) (f : System n) : Prop :=
  ∀ x y : State n, ∃ z : State n,
    projT c (f z) = projT c (f x) ∧ projF c (f z) = projF c (f y)

/-- A system is **decomposable** if some cut is independent. -/
def decomposable {n : Nat} (f : System n) : Prop := ∃ c : Cut n, cutIndep c f

/-- A system is **integrated** if no cut is independent. -/
def integrated {n : Nat} (f : System n) : Prop := ¬ decomposable f

/-! ## Theorem A — product systems are decomposable

If each side of a cut influences only itself (side-A output bits depend only
on side-A input bits, likewise for B), then the cut is independent: the
witness `z` simply mixes the inputs of the two sides. -/

/-- Decomposition of systems with independent side dynamics: mixing the
inputs realizes every pair of separately realizable patterns. -/
theorem cutIndep_of_sides_independent {n : Nat} (c : Cut n) (f : System n)
    (hA : ∀ s s' : State n, (∀ i, c.sel i = true → s i = s' i) →
      ∀ i, c.sel i = true → f s i = f s' i)
    (hB : ∀ s s' : State n, (∀ i, c.sel i = false → s i = s' i) →
      ∀ i, c.sel i = false → f s i = f s' i) :
    cutIndep c f := by
  intro x y
  refine ⟨fun i => if c.sel i then x i else y i, ?_, ?_⟩
  · funext i
    by_cases h : c.sel i = true
    · simp only [projT, h]
      exact hA _ _ (fun j hj => by simp only [hj, if_true]) i h
    · simp [projT, h]
  · funext i
    by_cases h : c.sel i = false
    · simp only [projF, h]
      exact hB _ _ (fun j hj => by simp [hj]) i h
    · simp [projF, h]

/-- Frozen statement #1 of #18599: a system whose two halves evolve
independently (relative to a cut) is decomposable. Alias of
`cutIndep_of_sides_independent` under the name frozen in the issue. -/
theorem product_decomposable {n : Nat} (c : Cut n) (f : System n)
    (hA : ∀ s s' : State n, (∀ i, c.sel i = true → s i = s' i) →
      ∀ i, c.sel i = true → f s i = f s' i)
    (hB : ∀ s s' : State n, (∀ i, c.sel i = false → s i = s' i) →
      ∀ i, c.sel i = false → f s i = f s' i) :
    decomposable f :=
  ⟨c, cutIndep_of_sides_independent c f hA hB⟩

/-! ## The parity broadcast system

Every element of the next state takes the **parity** of the current state:
global information is broadcast everywhere, and the image of the system
shrinks to two constant states. This is the simplest form of "the object
that bit IIT": maximal integration in the proxy's sense, trivial behaviour. -/

/-- Parity of a state (number of true bits modulo 2), by recursion on `n`:
head at index 0 then tail shifted by `Fin.succ`. -/
def parity : (n : Nat) → State n → Bool
  | 0, _ => false
  | n + 1, s => xor (s ⟨0, Nat.succ_pos n⟩) (parity n (fun i => s i.succ))

/-- The parity broadcast system: the next state is uniformly the parity of
the current state. -/
def broadcast {n : Nat} : System n := fun s => fun _ => parity n s

/-- The parity of an all-false state is zero, by a structural recursion
mirroring `parity` (recursing on `n` alone does not generalize `s`). -/
theorem parity_allFalse : ∀ (n : Nat) (s : State n), (∀ i, s i = false) →
    parity n s = false
  | 0, _, _ => rfl
  | n + 1, s, h => by
      rw [parity, h ⟨0, Nat.succ_pos n⟩,
        parity_allFalse n (fun i => s i.succ) (fun i => h i.succ)]
      rfl

/-- The parity of an all-true state encodes the oddness of `n` (without a
dedicated `Nat.mod` lemma: the flip step is closed by `omega` on `% 2`). -/
theorem parity_allTrue {n : Nat} :
    parity n (fun _ => true) = decide (n % 2 = 1) := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [parity]
      show xor true (parity m (fun _ => true)) = decide ((m + 1) % 2 = 1)
      rw [ih]
      cases hm : m % 2 with
      | zero =>
          have h1 : (m + 1) % 2 = 1 := by omega
          simp [h1]
      | succ k =>
          have hk : k = 0 := by omega
          have h1 : (m + 1) % 2 = 0 := by omega
          simp [hk, h1]

/-- The single bit at index 0 makes the parity odd, whatever the size
(explicit-`decide` phrasing: the Prop→Bool coercion is not inserted in an
untyped `have` expecting `Bool`). -/
theorem parity_oneHot_zero : ∀ (n : Nat), 0 < n →
    parity n (fun j => decide (j.val = 0)) = true
  | 0, h => absurd h (Nat.not_lt_zero 0)
  | n + 1, _ => by
      have hp : parity n (fun i : Fin n =>
          decide ((i.succ : Fin (n + 1)).val = 0)) = false :=
        parity_allFalse _ _ (fun i => by simp)
      rw [parity, hp]
      rfl

/-- Parity of a constant state: false if the bit is false, parity of `n` otherwise. -/
theorem parity_const (n : Nat) (b : Bool) :
    parity n (fun _ => b) = (b && decide (n % 2 = 1)) := by
  cases b with
  | false => exact parity_allFalse _ _ (fun _ => rfl)
  | true => simp [parity_allTrue]

/-! ## Theorem B — the broadcast is integrated for every cut -/

/-- **The object that bit IIT, as a theorem.** The parity broadcast is
integrated for every cut: for any nontrivial split, the pattern pair
(side A broadcast true, side B broadcast false) is never jointly realized —
while each pattern is realized separately. Universal integration, trivial
behaviour. -/
theorem broadcast_integrated {n : Nat} : integrated (broadcast (n := n)) := by
  intro ⟨c, hc⟩
  obtain ⟨i₀, hi₀⟩ := c.ha
  obtain ⟨j₀, hj₀⟩ := c.hb
  have hn : 0 < n := Fin.pos i₀
  have hx := hc (fun j => decide (j.val = 0)) (fun _ => false)
  obtain ⟨z, hzT, hzF⟩ := hx
  have hT : parity n z = true := by
    have h0 := congrFun hzT i₀
    simp [projT, hi₀, broadcast] at h0
    rw [h0, parity_oneHot_zero n hn]
  have hF : parity n z = false := by
    have h1 := congrFun hzF j₀
    simp [projF, hj₀, broadcast] at h1
    rw [h1, parity_allFalse n (fun _ => false) (fun _ => rfl)]
  rw [hF] at hT
  exact absurd hT (by simp)

/-! ## Theorem C — the broadcast dynamics is trivial -/

/-- Every orbit of the broadcast reaches a fixed point in two steps: the
dynamics is trivial although the system is integrated for every cut. The
contrast with `broadcast_integrated` is the formal content of the critique. -/
theorem broadcast_two_cycle {n : Nat} (s : State n) :
    broadcast (broadcast (broadcast s)) = broadcast (broadcast s) := by
  funext i
  show parity n (fun _ => parity n (fun _ => parity n s))
     = parity n (fun _ => parity n s)
  rw [parity_const, parity_const]
  simp

/-- Frozen statement #3 of #18599: the broadcast dynamics is trivial.
Alias of `broadcast_two_cycle` under the name frozen in the issue. -/
theorem broadcast_trivial_dynamics {n : Nat} (s : State n) :
    broadcast (broadcast (broadcast s)) = broadcast (broadcast s) :=
  broadcast_two_cycle s

end IIT_en
