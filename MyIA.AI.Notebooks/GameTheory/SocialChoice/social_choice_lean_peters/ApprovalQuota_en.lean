/-
  Approval quotas — Hare `n/k` and Droop `n/(k+1)`
  ================================================

  Residue of issue #17988 raised by the coordinator on 2026-10-13: "the Hare
  n/k and Droop n/(k+1) quotas are defined nowhere in the lake". This file
  defines them, together with the coalition threshold they induce.

  Two distinct notions coexist in the literature and are kept apart here:

  1. **The quota** is a number of voters. Hare is `n / k`, Droop is
     `n / (k + 1)` — integer division, hence a floor. The strict form of the
     Droop quota (`⌊n/(k+1)⌋ + 1`), which is the electoral one, is exposed
     separately as `droopThreshold`: conflating the two is the classic
     mistake, and keeping them under two names prevents a caller from
     picking one while believing it is the other.
  2. **The coalition threshold** is a predicate on a cardinal. A coalition of
     `s` voters meets the Hare quota when `n ≤ s * k`. That integer form is
     **exact**: it avoids the rounding of `n / k`, which would let a coalition
     of `⌊n/k⌋` voters pass as sufficient although `k * ⌊n/k⌋ < n` (for
     instance `n = 5`, `k = 2`: the quota is 2, but `2 * 2 = 4 < 5`).

  The bridge between the two is `isQuotaLarge_iff_hareQuota_le`, stated under
  the hypothesis `k ∣ n`: that is exactly the case where the floor loses
  nothing, and outside it the equivalence is false (the counter-example
  above). Stating it without that hypothesis would be a false lemma, not a
  simplification.

  No `sorry`, no `native_decide`. This file only depends on `Nat` arithmetic.

  i18n convention #4980: this file carries the namespace `ApprovalQuota_en`
  (EN). The sibling `ApprovalQuota.lean` carries `ApprovalQuota` (FR).
  Byte-identity preserved except docstrings — verified by
  `scripts/lean/check_i18n_siblings.py`.
-/

import Mathlib.Data.Nat.Basic

namespace ApprovalQuota_en

/-- Hare quota: `n / k` voters, integer division (floor). -/
def hareQuota (n k : ℕ) : ℕ := n / k

/-- Droop quota as in the paper: `n / (k + 1)` voters, integer division
    (floor). -/
def droopQuota (n k : ℕ) : ℕ := n / (k + 1)

/-- **Strict** form of the Droop quota, the one of electoral definitions:
    `⌊n / (k + 1)⌋ + 1`. It is not `droopQuota` — see the file docstring. -/
def droopThreshold (n k : ℕ) : ℕ := droopQuota n k + 1

/-- A coalition of `s` voters meets the Hare quota over `n` voters and a
    committee of size `k` when `n ≤ s * k`. Exact integer form: no division,
    hence no rounding. -/
def IsQuotaLarge (n k s : ℕ) : Prop := n ≤ s * k

/-- The Hare quota never exceeds the number of voters. -/
lemma hareQuota_le_self (n k : ℕ) : hareQuota n k ≤ n :=
  Nat.div_le_self n k

/-- The Hare quota times the committee size never exceeds the number of
    voters: this is the loss of the floor, made explicit. -/
lemma hareQuota_mul_le (n k : ℕ) : hareQuota n k * k ≤ n :=
  Nat.div_mul_le_self n k

/-- The Droop quota is bounded by the Hare quota as soon as `k ≥ 1`: Droop's
    denominator is larger, hence its quotient smaller. -/
lemma droopQuota_le_hareQuota {n k : ℕ} (hk : 0 < k) :
    droopQuota n k ≤ hareQuota n k := by
  unfold droopQuota hareQuota
  exact Nat.div_le_div_left (Nat.le_succ k) hk

/-- The strict Droop threshold strictly exceeds the Droop quota. -/
lemma droopQuota_lt_droopThreshold (n k : ℕ) :
    droopQuota n k < droopThreshold n k :=
  Nat.lt_succ_self _

/-- The threshold predicate is monotone in coalition size: enlarging a
    coalition cannot make it lose the quota. -/
lemma isQuotaLarge_mono {n k s s' : ℕ} (h : s ≤ s') (hs : IsQuotaLarge n k s) :
    IsQuotaLarge n k s' := by
  unfold IsQuotaLarge at *
  exact le_trans hs (Nat.mul_le_mul_right k h)

/-- The coalition of all voters meets the Hare quota as soon as the committee
    is non-empty. -/
lemma isQuotaLarge_self (n k : ℕ) (hk : 1 ≤ k) : IsQuotaLarge n k n := by
  unfold IsQuotaLarge
  calc n = n * 1 := (Nat.mul_one n).symm
    _ ≤ n * k := Nat.mul_le_mul_left n hk

/-- Bridge between the quota and the threshold, under the hypothesis
    `k ∣ n`. Outside that hypothesis the equivalence is **false**: `n = 5`,
    `k = 2`, `s = 2` gives `hareQuota = 2 ≤ 2` while `5 ≤ 4` is false. -/
lemma isQuotaLarge_iff_hareQuota_le {n k s : ℕ} (hk : 0 < k) (hdvd : k ∣ n) :
    IsQuotaLarge n k s ↔ hareQuota n k ≤ s := by
  have hmul : hareQuota n k * k = n := by
    unfold hareQuota
    exact Nat.div_mul_cancel hdvd
  constructor
  · intro h
    have h' : hareQuota n k * k ≤ s * k := by rw [hmul]; exact h
    exact Nat.le_of_mul_le_mul_right h' hk
  · intro h
    have h' : hareQuota n k * k ≤ s * k := Nat.mul_le_mul_right k h
    rw [hmul] at h'
    exact h'

end ApprovalQuota_en
