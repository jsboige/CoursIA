import Mathlib
import ERC20.State_en
import ERC20.Ops_en

/-!
# ERC20.Invariant — preservation of the conservation invariant

We prove that the invariant `Σ balances = totalSupply` is preserved by each of
the three standard operations (`mint`, `burn`, `transfer`), then by an arbitrary
sequence of reachable operations (induction on the trace). These are the target
theorems of issue #4047.

The key technical ingredient is the **additive extraction** of a point from a
finite sum: on `Fin n` (a finite type), `∑ a ∈ s, f a = f a₀ + ∑ a ∈ s.erase a₀, f a`
whenever `a₀ ∈ s`. We carefully avoid distributing truncated subtraction on `ℕ`
over the sum (`∑ (f - g) = ∑ f - ∑ g` is false in general on `ℕ`), reasoning
instead by extraction (via `insert_erase`/`sum_insert`, additive form) then
`ℕ` arithmetic (`Nat.add_sub_assoc`, `omega`).
-/

namespace ERC20_en

variable {n : ℕ}

open Finset

/-- Additive extraction of a point from a finite sum: if `a ∈ s`, the sum over
    `s` equals the value at `a` plus the sum over `s.erase a`. Additive form
    (no subtraction), hence valid over `ℕ`. -/
lemma sum_split_mem (f : Address n → ℕ) (s : Finset (Address n)) (a : Address n)
    (ha : a ∈ s) : (∑ x ∈ s, f x) = f a + ∑ x ∈ s.erase a, f x := by
  conv_lhs => rw [← insert_erase ha]
  exact sum_insert (fun h => (mem_erase.mp h).1 rfl)

/-- Special case `s = univ` (the sum over all addresses). -/
lemma sum_univ_split (f : Address n → ℕ) (a : Address n) :
    (∑ x : Address n, f x) = f a + ∑ x ∈ (univ : Finset (Address n)).erase a, f x :=
  sum_split_mem f univ a (mem_univ a)

/-- A single account balance is bounded by the total supply (under the invariant):
    each term of an `ℕ` sum is bounded by the total sum. -/
lemma balance_le_totalSupply (s : State n) (a : Address n) (h : supplyInvariant s) :
    s.balances a ≤ s.totalSupply := by
  rw [← h]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)

/-- **`mint` preserves the supply.** Minting `amount` to `dst` credits `amount`
    to the balances AND to the total supply: the invariant is conserved. -/
theorem mint_preserves_supply (s : State n) (dst : Address n) (amount : ℕ)
    (h : supplyInvariant s) : supplyInvariant (mint s dst amount) := by
  show ∑ a : Address n, (mint s dst amount).balances a = (mint s dst amount).totalSupply
  simp only [mint]
  have key : ∀ a : Address n,
      (if a = dst then s.balances a + amount else s.balances a) =
      s.balances a + (if a = dst then amount else (0:ℕ)) := by
    intro a; split_ifs <;> simp
  rw [sum_congr rfl (fun a _ => key a), sum_add_distrib,
      sum_univ_split (fun a : Address n => if a = dst then amount else (0:ℕ)) dst,
      if_pos (rfl : dst = dst)]
  -- Le surplus (`amount`) ne vient que de `dst` ; sur `erase dst`, l'ite vaut 0.
  have hr : ∑ a ∈ (univ : Finset (Address n)).erase dst,
      (if a = dst then amount else (0:ℕ)) = 0 := by
    apply sum_eq_zero
    intro a ha
    rw [mem_erase] at ha
    exact if_neg ha.1
  rw [hr, add_zero, ← h]

/-- **`burn` preserves the supply.** Burning `amount` from `src` (sufficient
    balance) removes `amount` from the balances AND from the total supply: the
    invariant is conserved. -/
theorem burn_preserves_supply (s : State n) (src : Address n) (amount : ℕ)
    (hguard : s.balances src ≥ amount) (h : supplyInvariant s) :
    supplyInvariant (burn s src amount) := by
  show ∑ a : Address n, (burn s src amount).balances a = (burn s src amount).totalSupply
  simp only [burn]
  rw [← h, sum_univ_split
        (fun a : Address n => if a = src then s.balances a - amount else s.balances a) src,
      if_pos (rfl : src = src)]
  -- Sur `erase src` (a ≠ src), l'ite dégénère vers `s.balances a`.
  have hr : ∑ a ∈ (univ : Finset (Address n)).erase src,
      (if a = src then s.balances a - amount else s.balances a : ℕ) =
    ∑ a ∈ (univ : Finset (Address n)).erase src, s.balances a := by
    apply sum_congr rfl
    intro a ha
    rw [mem_erase] at ha
    exact if_neg ha.1
  rw [hr, sum_univ_split s.balances src]
  omega

/-- **`transfer` preserves the supply.** Transferring `amount` from `src` to
    `dst` (distinct addresses, sufficient balance) moves the tokens without
    creating or destroying: the sum of balances is unchanged, as is the total
    supply. -/
theorem transfer_preserves_supply (s : State n) (src dst : Address n) (amount : ℕ)
    (hguard : s.balances src ≥ amount) (hne : src ≠ dst) (h : supplyInvariant s) :
    supplyInvariant (transfer s src dst amount) := by
  show ∑ a : Address n, (transfer s src dst amount).balances a =
        (transfer s src dst amount).totalSupply
  simp only [transfer]
  rw [← h, sum_univ_split
        (fun a : Address n =>
          if a = src then s.balances a - amount
          else if a = dst then s.balances a + amount else s.balances a) src,
      if_pos (rfl : src = src)]
  -- Sur `erase src` (a ≠ src), l'ite dégénère vers la branche `dst`.
  have hr1 : ∑ a ∈ (univ : Finset (Address n)).erase src,
      (if a = src then s.balances a - amount
        else if a = dst then s.balances a + amount else s.balances a : ℕ) =
    ∑ a ∈ (univ : Finset (Address n)).erase src,
        (if a = dst then s.balances a + amount else s.balances a) := by
    apply sum_congr rfl
    intro a ha
    rw [mem_erase] at ha
    exact if_neg ha.1
  have hdst_mem : (dst : Address n) ∈ (univ : Finset (Address n)).erase src :=
    mem_erase.mpr ⟨hne.symm, mem_univ _⟩
  rw [hr1, sum_split_mem _ _ dst hdst_mem, if_pos (rfl : dst = dst)]
  -- Sur `(erase src).erase dst` (a ≠ src, a ≠ dst), l'ite vaut `s.balances a`.
  have hr2 : ∑ a ∈ ((univ : Finset (Address n)).erase src).erase dst,
        (if a = dst then s.balances a + amount else s.balances a) =
      ∑ a ∈ ((univ : Finset (Address n)).erase src).erase dst, s.balances a := by
    apply sum_congr rfl
    intro a ha
    rw [mem_erase] at ha
    exact if_neg ha.1
  rw [hr2, sum_univ_split s.balances src,
      sum_split_mem s.balances ((univ : Finset (Address n)).erase src) dst hdst_mem]
  omega

/-- **`transfer` debits the source exactly by `amount`, without underflow.**
    The source account balance after `transfer` is `bal src - amount`, and the
    guard makes this subtraction reversible (no semantic underflow). -/
theorem transfer_no_underflow (s : State n) (src dst : Address n) (amount : ℕ)
    (hguard : s.balances src ≥ amount) :
    (transfer s src dst amount).balances src = s.balances src - amount ∧
    s.balances src - amount + amount = s.balances src := by
  refine ⟨?_, Nat.sub_add_cancel hguard⟩
  simp [transfer]

/-- **Reachable operation.** A step `s → s'` is one of the three operations
    `mint`/`burn`/`transfer` executed from a state carrying the invariant. -/
inductive Op (n : ℕ) : State n → State n → Prop
  | mint (s : State n) (dst : Address n) (amount : ℕ) (h : supplyInvariant s) :
      Op n s (mint s dst amount)
  | burn (s : State n) (src : Address n) (amount : ℕ)
      (hguard : s.balances src ≥ amount) (h : supplyInvariant s) :
      Op n s (burn s src amount)
  | transfer (s : State n) (src dst : Address n) (amount : ℕ)
      (hguard : s.balances src ≥ amount) (hne : src ≠ dst) (h : supplyInvariant s) :
      Op n s (transfer s src dst amount)

/-- A reachable operation preserves the invariant (case-by-case). -/
lemma op_preserves_invariant (s s' : State n) (hop : Op n s s') (h : supplyInvariant s) :
    supplyInvariant s' := by
  cases hop with
  | mint dst amount _ => exact mint_preserves_supply s dst amount h
  | burn src amount hguard _ => exact burn_preserves_supply s src amount hguard h
  | transfer src dst amount hguard hne _ =>
    exact transfer_preserves_supply s src dst amount hguard hne h

/-- **Reflexive-transitive reachability.** `Reachable n s s'`: `s'` is reachable
    from `s` by zero, one or several operations. -/
inductive Reachable (n : ℕ) : State n → State n → Prop
  | refl (s : State n) : Reachable n s s
  | step (s₁ s₂ s₃ : State n) (hop : Op n s₁ s₂) (hrest : Reachable n s₂ s₃) :
      Reachable n s₁ s₃

/-- **Induction on the trace:** any sequence of reachable operations preserves
    the invariant end-to-end. The final state still carries the invariant. -/
theorem reachable_preserves_invariant (s s' : State n) (h : supplyInvariant s)
    (hr : Reachable n s s') : supplyInvariant s' := by
  induction hr with
  | refl => exact h
  | step s₁ s₂ s₃ hop hrest ih =>
    exact ih (op_preserves_invariant s₁ s₂ hop h)

end ERC20_en
