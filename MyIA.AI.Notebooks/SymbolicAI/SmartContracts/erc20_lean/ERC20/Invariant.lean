import Mathlib
import ERC20.State
import ERC20.Ops

/-!
# ERC20.Invariant — préservation de l'invariant de conservation

On prouve que l'invariant `Σ balances = totalSupply` est préservé par chacune
des trois opérations standard (`mint`, `burn`, `transfer`), puis par une
séquence arbitraire d'opérations atteignables (induction sur la trace). Ce sont
les théorèmes cibles de l'issue #4047.

L'ingrédient technique clé est l'**extraction additive** d'un point d'une somme
finie : sur `Fin n` (type fini), `∑ a ∈ s, f a = f a₀ + ∑ a ∈ s.erase a₀, f a`
dès que `a₀ ∈ s`. On évite soigneusement de distribuer la soustraction tronquée
de `ℕ` sur la somme (`∑ (f - g) = ∑ f - ∑ g` est faux en général sur `ℕ`), en
raisonnant plutôt par extraction (via `insert_erase`/`sum_insert`, forme
additive) puis arithmétique `ℕ` (`Nat.add_sub_assoc`, `omega`).
-/

namespace ERC20

variable {n : ℕ}

open Finset

/-- Extraction additive d'un point d'une somme finie : si `a ∈ s`, la somme sur
    `s` égale la valeur en `a` plus la somme sur `s.erase a`. Forme additive
    (sans soustraction), donc valable sur `ℕ`. -/
lemma sum_split_mem (f : Address n → ℕ) (s : Finset (Address n)) (a : Address n)
    (ha : a ∈ s) : (∑ x ∈ s, f x) = f a + ∑ x ∈ s.erase a, f x := by
  conv_lhs => rw [← insert_erase ha]
  exact sum_insert (fun h => (mem_erase.mp h).1 rfl)

/-- Cas particulier `s = univ` (la somme sur toutes les adresses). -/
lemma sum_univ_split (f : Address n → ℕ) (a : Address n) :
    (∑ x : Address n, f x) = f a + ∑ x ∈ (univ : Finset (Address n)).erase a, f x :=
  sum_split_mem f univ a (mem_univ a)

/-- Le solde d'un compte est borné par l'offre totale (sous invariant) :
    chaque terme d'une somme de `ℕ` est majoré par la somme totale. -/
lemma balance_le_totalSupply (s : State n) (a : Address n) (h : supplyInvariant s) :
    s.balances a ≤ s.totalSupply := by
  rw [← h]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)

/-- **`mint` préserve l'offre.** Frapper `amount` à `dst` crédite `amount` aux
    soldes ET à l'offre totale : l'invariant est conservé. -/
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

/-- **`burn` préserve l'offre.** Brûler `amount` depuis `src` (solde suffisant)
    retire `amount` aux soldes ET à l'offre totale : l'invariant est conservé. -/
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

/-- **`transfer` préserve l'offre.** Transférer `amount` de `src` vers `dst`
    (adresses distinctes, solde suffisant) déplace les tokens sans créer ni
    détruire : la somme des soldes est inchangée, comme l'offre totale. -/
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

/-- **`transfer` débite la source exactement de `amount`, sans underflow.** Le
    solde du compte source après `transfer` est `bal src - amount`, et la garde
    rend cette soustraction réversible (pas d'underflow sémantique). -/
theorem transfer_no_underflow (s : State n) (src dst : Address n) (amount : ℕ)
    (hguard : s.balances src ≥ amount) :
    (transfer s src dst amount).balances src = s.balances src - amount ∧
    s.balances src - amount + amount = s.balances src := by
  refine ⟨?_, Nat.sub_add_cancel hguard⟩
  simp [transfer]

/-- **Opération atteignable.** Une étape `s → s'` est l'une des trois opérations
    `mint`/`burn`/`transfer` exécutée depuis un état portant l'invariant. -/
inductive Op (n : ℕ) : State n → State n → Prop
  | mint (s : State n) (dst : Address n) (amount : ℕ) (h : supplyInvariant s) :
      Op n s (mint s dst amount)
  | burn (s : State n) (src : Address n) (amount : ℕ)
      (hguard : s.balances src ≥ amount) (h : supplyInvariant s) :
      Op n s (burn s src amount)
  | transfer (s : State n) (src dst : Address n) (amount : ℕ)
      (hguard : s.balances src ≥ amount) (hne : src ≠ dst) (h : supplyInvariant s) :
      Op n s (transfer s src dst amount)

/-- Une opération atteignable préserve l'invariant (au cas-par-cas). -/
lemma op_preserves_invariant (s s' : State n) (hop : Op n s s') (h : supplyInvariant s) :
    supplyInvariant s' := by
  cases hop with
  | mint dst amount _ => exact mint_preserves_supply s dst amount h
  | burn src amount hguard _ => exact burn_preserves_supply s src amount hguard h
  | transfer src dst amount hguard hne _ =>
    exact transfer_preserves_supply s src dst amount hguard hne h

/-- **Atteignabilité réflexive-transitive.** `Reachable n s s'` : `s'` est
    atteignable depuis `s` par zéro, une ou plusieurs opérations. -/
inductive Reachable (n : ℕ) : State n → State n → Prop
  | refl (s : State n) : Reachable n s s
  | step (s₁ s₂ s₃ : State n) (hop : Op n s₁ s₂) (hrest : Reachable n s₂ s₃) :
      Reachable n s₁ s₃

/-- **Induction sur la trace :** toute séquence d'opérations atteignables préserve
    l'invariant de bout en bout. L'état final porte encore l'invariant. -/
theorem reachable_preserves_invariant (s s' : State n) (h : supplyInvariant s)
    (hr : Reachable n s s') : supplyInvariant s' := by
  induction hr with
  | refl => exact h
  | step s₁ s₂ s₃ hop hrest ih =>
    exact ih (op_preserves_invariant s₁ s₂ hop h)

end ERC20
