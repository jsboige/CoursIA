/-
  Quotas and payment systems — approval core (BGP 2026)
  ====================================================

  "Payment" tranche of the execution plan for issue #17988, on top of the
  Tranche 1 socle (`ApprovalDefs_en.lean`). Reference result: Becker,
  Greger and Peters (2026), arXiv 2609.11912.

  This file contributes the three bricks that the delivered tranches 1-3
  (`ApprovalDefs`, `ApprovalCore`, `ApprovalPareto`) do not cover:

  1. **Quotas** — `hareQuota` (n/k) and `droopQuota` (n/(k+1)), with
     ordering lemmas (`droopQuota_le_hareQuota`) and positivity.
  2. **Payment system** (faithful to Def 3.2 of the paper) — each voter
     has a unit budget, pays `payment v c` for each approved winner `c`,
     keeps the `reserve v`, and each winner receives at most `q`. The
     lemma `paymentSystem_trivial` witnesses non-emptiness
     (`P(W) ≠ ∅`, remark under Def 3.2, for `q ≥ 0`).
     This system is DISTINCT from the zero-sum `PaymentFunction` of
     Tranche 1, which models the payments of the objective function;
     here payments certify stability.
  3. **Certificate characterisation** ("certificate ⟹ core" direction of
     Theorem 3.3 of the paper) — a payment system whose payments never
     exceed the reserve (`pays_at_most_reserve`) and whose reserves
     strictly beat every losing candidate (`reserves_beat_losers`)
     rules out any proportional blocking coalition: see
     `not_blocksCore_of_paymentCertificate`.

  Core reading retained: **external deviation** — the coalition `T`
  proposes a set `B` of candidates **outside the committee** (`B`
  disjoint from `S`) with the proportional entitlement `|T| ≥ q · |B|`
  (intro definition of the paper, in its external reading; the
  "arbitrary B" variant of the intro allows overlap with the committee,
  which the certificate of Definition 3.2 does not address — its
  reserves only constrain losers). The `BlocksCore` definition below
  encodes this external reading, consistent with Theorem 3.3.

  Proof of the main theorem (elementary, no Farkas and no LP duality —
  the same weighted bookkeeping as the paper's proof, unrolled by hand
  for the classical external core). For each voter `v` of the blocking
  coalition:

    reserve v + Σ (payments to approved winners) = 1             (budget)
    Σ payments ≤ |A_v ∩ S| · reserve v                           (p ≤ r)
    |A_v ∩ B| > |A_v ∩ S|                                         (blocking)

  hence `(Happiness v + 1) · reserve v ≥ 1`, and therefore
  `|A_v ∩ B| · reserve v ≥ 1`. Summing over `T` and double-counting
  the pairs (v, c):

    |T| ≤ Σ_{c ∈ B} Σ_{v approves c} reserve v < Σ_{c ∈ B} q = |B| · q ≤ |T|

  — a contradiction. No sign assumption on `q` is needed: the
  contradiction is purely combinatorial.

  No `sorry`. i18n convention #4980: this file carries the namespace
  `ApprovalPayment_en` (EN). The sibling `ApprovalPayment.lean` carries
  `ApprovalPayment` (FR). Byte-identity preserved except docstrings —
  verified by `scripts/lean/check_i18n_siblings.py`.
-/

import ApprovalDefs_en
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ApprovalPayment_en

open ApprovalDefs_en

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
/-- Counting identity used throughout: the sum of a constant over a
    `Finset` is the cardinality (cast into ℚ) times the constant. Proven
    by induction so as not to depend on the exact shape of Mathlib's
    `sum_const` / smul lemmas. -/
private lemma sum_const_card_mul {α : Type} (F : Finset α) (r : ℚ) :
    ∑ _a ∈ F, r = (F.card : ℚ) * r := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.card_insert_of_notMem hx, ih]
      push_cast
      ring

/-! ## Quotas (Hare n/k, Droop n/(k+1)) -/

/-- The set of voters who approve candidate `c`. -/
def approvers (P : ApprovalProfile V A) (c : A) : Finset V :=
  Finset.univ.filter (fun v => c ∈ (P.ballots v).approved)

/-- Hare quota: `n` voters for `k` seats. -/
def hareQuota (P : ApprovalProfile V A) : ℚ :=
  (Fintype.card V : ℚ) / (P.committeeSize : ℚ)

/-- Droop quota: `n` voters for `k + 1` ballots. Always at most the Hare
    quota as soon as `k ≥ 1`. -/
def droopQuota (P : ApprovalProfile V A) : ℚ :=
  (Fintype.card V : ℚ) / ((P.committeeSize : ℚ) + 1)

omit [DecidableEq A] in
/-- Positivity of the Hare quota as soon as there is one voter and one
    seat. -/
lemma hareQuota_pos (P : ApprovalProfile V A) (hn : 0 < Fintype.card V)
    (hk : 0 < P.committeeSize) : 0 < hareQuota P :=
  div_pos (by exact_mod_cast hn) (by exact_mod_cast hk)

omit [DecidableEq A] in
/-- The Droop quota is at most the Hare quota: `n/(k+1) ≤ n/k` as soon
    as `k ≥ 1` (at fixed `n`, splitting across more seats shrinks the
    share; the `n = 0` case gives `0 ≤ 0`). -/
lemma droopQuota_le_hareQuota (P : ApprovalProfile V A)
    (hk : 0 < P.committeeSize) : droopQuota P ≤ hareQuota P := by
  have hn : (0:ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast Nat.zero_le _
  have hk' : (0:ℚ) < (P.committeeSize : ℚ) := by exact_mod_cast hk
  have hk1 : (0:ℚ) < (P.committeeSize : ℚ) + 1 := by linarith
  rw [hareQuota, droopQuota]
  field_simp
  nlinarith [hn]

/-! ## Payment system (Definition 3.2 of the paper) -/

/-- Payment system for committee `S` under quota `q`: each voter `v` pays
    `payment v c ≥ 0` for each approved winner `c`, keeps the reserve
    `reserve v ≥ 0`, the total budget is exactly 1
    (`reserve v + Σ payment v = 1` — the additive form of the paper's
    `r_i = 1 − Σ p_ic`), and each winner `c ∈ S` receives at most `q`
    from its approvers. -/
structure PaymentSystem (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (q : ℚ) where
  /-- Payment of voter `v` to candidate `c`. -/
  payment : V → A → ℚ
  /-- Payments are non-negative. -/
  payment_nonneg : ∀ v c, 0 ≤ payment v c
  /-- Reserve of voter `v` after paying approved winners. -/
  reserve : V → ℚ
  /-- Reserves are non-negative. -/
  reserve_nonneg : ∀ v, 0 ≤ reserve v
  /-- Budget: the reserve plus the sum of payments to approved winners
      is exactly 1 (paper, Def 3.2: `r_i = 1 − Σ p_ic`). -/
  budget : ∀ v, reserve v +
      ∑ c ∈ (P.ballots v).approved.filter (fun x => x ∈ S.val), payment v c = 1
  /-- Each winner receives at most the quota from its approvers. -/
  winner_bound : ∀ c ∈ S.val, ∑ v ∈ approvers P c, payment v c ≤ q

/-- The trivial payment system (no payment, full reserves) exists as
    soon as `q ≥ 0`: this is the non-emptiness `P(W) ≠ ∅` remarked under
    Definition 3.2 of the paper. It does not generally satisfy the
    certificate's condition on losers — otherwise the core would be
    trivial. -/
def paymentSystem_trivial (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (q : ℚ) (hq : 0 ≤ q) :
    PaymentSystem P S q where
  payment _ _ := 0
  payment_nonneg := by intro; simp
  reserve _ := 1
  reserve_nonneg := by intro; simp
  budget := by intro v; simp
  winner_bound := by
    intro c _
    simp [approvers]
    exact hq

/-- Core certificate ("easy" half of Theorem 3.3 of the paper): a payment
    system where (i) every payment to an approved winner does not exceed
    the payer's reserve, and (ii) for every losing candidate, the sum of
    the reserves of its approvers is **strictly** below the quota. -/
structure PaymentCertificate (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (q : ℚ) extends PaymentSystem P S q where
  /-- Condition (i): `p_vw ≤ r_v` for every winner `w` approved by `v`. -/
  pays_at_most_reserve : ∀ v (w : A), w ∈ (P.ballots v).approved → w ∈ S.val →
    payment v w ≤ reserve v
  /-- Condition (ii): for every loser `c`, the reserves of its approvers
      sum strictly below the quota. -/
  reserves_beat_losers : ∀ c, c ∉ S.val → ∑ v ∈ approvers P c, reserve v < q

/-! ## Approval core with entitlement (external reading) -/

/-- The coalition `T` **blocks** committee `S` under quota `q` via the
    external set `B` (disjoint from `S`): `B` is nonempty, the coalition
    is large enough for its entitlement (`|T| ≥ q · |B|`), and every
    member of `T` approves strictly more members of `B` than members of
    the committee. -/
def BlocksCore (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (q : ℚ) (T : Finset V) (B : Finset A) : Prop :=
  T.Nonempty ∧ B.Nonempty ∧ Disjoint B S.val ∧ (T.card : ℚ) ≥ q * (B.card : ℚ) ∧
    ∀ v ∈ T, (B.filter (fun c => c ∈ (P.ballots v).approved)).card > Happiness P S v

/-- Committee `S` is in the **approval core** under quota `q`: no pair
    (coalition, external set) blocks it. -/
def InApprovalCore (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (q : ℚ) : Prop :=
  ∀ (T : Finset V) (B : Finset A), ¬ BlocksCore P S q T B

/-! ## "Certificate ⟹ core" direction of Theorem 3.3 -/

/-- **Certificate direction of Theorem 3.3** (Becker-Greger-Peters
    2026): if committee `S` admits a payment system whose payments never
    exceed the reserves and whose reserves strictly beat every losing
    candidate, then no coalition can block `S` — `S` is in the approval
    core (external reading). No sign assumption on `q`: the
    contradiction is purely combinatorial. -/
theorem not_blocksCore_of_paymentCertificate (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) {q : ℚ}
    (cert : PaymentCertificate P S q) (T : Finset V) (B : Finset A) :
    ¬ BlocksCore P S q T B := by
  rintro ⟨hT, hB, hdisj, hsize, himp⟩
  -- Voter step: budget + payments under reserve + strict improvement
  -- give `(Happiness v + 1) · reserve v ≥ 1`, hence `|A_v ∩ B| · reserve v ≥ 1`.
  have key : ∀ v ∈ T,
      (1:ℚ) ≤ ((B.filter (fun c => c ∈ (P.ballots v).approved)).card : ℚ) *
        cert.reserve v := by
    intro v hv
    have hap_eq : Happiness P S v =
        ((P.ballots v).approved.filter (fun x => x ∈ S.val)).card := rfl
    -- v's payments to approved winners do not exceed Happiness · reserve
    have hpr : ∑ c ∈ (P.ballots v).approved.filter (fun x => x ∈ S.val),
        cert.payment v c ≤ (Happiness P S v : ℚ) * cert.reserve v := by
      calc ∑ c ∈ (P.ballots v).approved.filter (fun x => x ∈ S.val),
            cert.payment v c
          ≤ ∑ c ∈ (P.ballots v).approved.filter (fun x => x ∈ S.val),
              cert.reserve v :=
            Finset.sum_le_sum (fun c hc =>
              cert.pays_at_most_reserve v c (Finset.mem_filter.mp hc).1
                (Finset.mem_filter.mp hc).2)
        _ = ((P.ballots v).approved.filter (fun x => x ∈ S.val)).card *
              cert.reserve v := sum_const_card_mul _ _
        _ = (Happiness P S v : ℚ) * cert.reserve v := by rw [hap_eq]
    -- strict improvement: |A_v ∩ B| ≥ Happiness v + 1
    have hcard : (Happiness P S v + 1 : ℕ) ≤
        (B.filter (fun c => c ∈ (P.ballots v).approved)).card :=
      Nat.succ_le_of_lt (himp v hv)
    -- chain: 1 = reserve + Σ payments ≤ reserve + Happiness · reserve
    --        = (Happiness + 1) · reserve ≤ |A_v ∩ B| · reserve
    calc (1:ℚ) = cert.reserve v +
          ∑ c ∈ (P.ballots v).approved.filter (fun x => x ∈ S.val),
            cert.payment v c := (cert.budget v).symm
      _ ≤ cert.reserve v + (Happiness P S v : ℚ) * cert.reserve v := by
            gcongr
      _ = ((Happiness P S v : ℚ) + 1) * cert.reserve v := by ring
      _ ≤ ((B.filter (fun c => c ∈ (P.ballots v).approved)).card : ℚ) *
            cert.reserve v := by
            gcongr
            · exact cert.reserve_nonneg v
            · exact_mod_cast hcard
  -- Sum over the coalition: Σ_v 1 = |T| ≤ Σ_v |A_v ∩ B| · reserve v
  have hT1 : ∑ v ∈ T, (1:ℚ) ≤ ∑ v ∈ T,
      ((B.filter (fun c => c ∈ (P.ballots v).approved)).card : ℚ) *
        cert.reserve v :=
    Finset.sum_le_sum (fun v hv => key v hv)
  -- Double counting of the pairs (v, c) with c ∈ B approved by v ∈ T
  have hswap : ∑ v ∈ T,
      ((B.filter (fun c => c ∈ (P.ballots v).approved)).card : ℚ) *
        cert.reserve v
      = ∑ c ∈ B, ∑ v ∈ T.filter (fun v => c ∈ (P.ballots v).approved),
          cert.reserve v := by
    have expand : ∀ v ∈ T,
        ((B.filter (fun c => c ∈ (P.ballots v).approved)).card : ℚ) *
          cert.reserve v
        = ∑ c ∈ B, if c ∈ (P.ballots v).approved then cert.reserve v else 0 := by
      intro v _
      rw [← sum_const_card_mul, Finset.sum_filter]
    rw [Finset.sum_congr rfl expand, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ =>
      (Finset.sum_filter (fun v => c ∈ (P.ballots v).approved)
        (fun v => cert.reserve v)).symm)
  -- Every loser c ∈ B sees the reserves of its approvers strictly below
  -- the quota; so does the inner sum (restricted to T).
  have hupper : ∑ c ∈ B, ∑ v ∈ T.filter (fun v => c ∈ (P.ballots v).approved),
      cert.reserve v < (B.card : ℚ) * q := by
    have hinner : ∀ c ∈ B, ∑ v ∈ T.filter (fun v => c ∈ (P.ballots v).approved),
        cert.reserve v < q := by
      intro c hc
      have hc' : c ∉ S.val := fun hmem => Finset.disjoint_right.mp hdisj hmem hc
      have hsub : T.filter (fun v => c ∈ (P.ballots v).approved) ⊆ approvers P c := by
        intro v hv
        rw [Finset.mem_filter] at hv
        simp only [approvers, Finset.mem_filter, Finset.mem_univ]
        exact ⟨trivial, hv.2⟩
      have hle : ∑ v ∈ T.filter (fun v => c ∈ (P.ballots v).approved),
          cert.reserve v ≤ ∑ v ∈ approvers P c, cert.reserve v :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => cert.reserve_nonneg v)
      exact lt_of_le_of_lt hle (cert.reserves_beat_losers c hc')
    obtain ⟨c, hc⟩ := hB
    have hall : ∀ c' ∈ B, ∑ v ∈ T.filter (fun v => c' ∈ (P.ballots v).approved),
        cert.reserve v ≤ q := fun c' hc' => le_of_lt (hinner c' hc')
    rw [← sum_const_card_mul]
    exact Finset.sum_lt_sum hall ⟨c, hc, hinner c hc⟩
  -- Conclusion: |T| ≤ Σ < |B| · q ≤ |T| — contradiction.
  have hTcard : ∑ v ∈ T, (1:ℚ) = (T.card : ℚ) := by
    rw [sum_const_card_mul]; ring
  have hchain : (T.card : ℚ) < (T.card : ℚ) :=
    calc (T.card : ℚ) = ∑ v ∈ T, (1:ℚ) := hTcard.symm
      _ ≤ ∑ v ∈ T, ((B.filter (fun c => c ∈ (P.ballots v).approved)).card : ℚ) *
            cert.reserve v := hT1
      _ = ∑ c ∈ B, ∑ v ∈ T.filter (fun v => c ∈ (P.ballots v).approved),
            cert.reserve v := hswap
      _ < (B.card : ℚ) * q := hupper
      _ ≤ (T.card : ℚ) := by rwa [mul_comm]
  exact absurd hchain (lt_irrefl _)

end ApprovalPayment_en
