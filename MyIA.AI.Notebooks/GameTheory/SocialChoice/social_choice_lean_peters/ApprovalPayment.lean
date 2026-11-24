/-
  Quotas et système de paiement — core d'approbation (BGP 2026)
  =============================================================

  Tranche « paiement » du plan d'exécution de l'issue #17988, au-dessus du
  socle de la Tranche 1 (`ApprovalDefs.lean`). Résultat de référence :
  Becker, Greger et Peters (2026), arXiv 2609.11912.

  Ce fichier apporte les trois briques que les tranches 1-3 livrées
  (`ApprovalDefs`, `ApprovalCore`, `ApprovalPareto`) ne couvrent pas :

  1. **Quotas** — `hareQuota` (n/k) et `droopQuota` (n/(k+1)), avec leurs
     lemmes d'ordre (`droopQuota_le_hareQuota`) et de positivité.
  2. **Système de paiement** (définition 3.2 du papier, fidèle) — chaque
     votant dispose d'un budget 1, paye `payment v c` pour chaque gagnant
     approuvé `c`, conserve la réserve `reserve v`, et chaque gagnant
     reçoit au plus `q`. Le lemme `paymentSystem_trivial` atteste la
     non-vacuité (`P(W) ≠ ∅`, remarque du papier, à `q ≥ 0`).
     Ce système est DISTINCT de la `PaymentFunction` somme-nulle de la
     Tranche 1, qui modélise les paiements de la fonction objectif ; ici
     les paiements certifient la stabilité.
  3. **Caractérisation par certificat** (sens « certificat ⟹ core » du
     théorème 3.3 du papier) — un système de paiement dont les paiements
     n'excèdent jamais la réserve (`pays_at_most_reserve`) et dont les
     réserves battent tout candidat perdant strictement
     (`reserves_beat_losers`) exclut toute coalition bloquante
     proportionnelle : c'est `not_blocksCore_of_paymentCertificate`.

  Lecture du core retenue : **déviation externe** — la coalition `T`
  propose un ensemble `B` de candidats **hors du comité** (`B` disjoint
  de `S`) avec l'entitlement proportionnel `|T| ≥ q · |B|` (définition de
  l'intro du papier, dans sa lecture externe ; la variante « B
  quelconque » de l'intro autorise un recouvrement avec le comité, que
  le certificat de la définition 3.2 ne couvre pas — ses réserves ne
  contraignent que les perdants). La définition `BlocksCore` ci-dessous
  encode cette lecture externe, cohérente avec le théorème 3.3.

  Preuve du théorème principal (élémentaire, sans Farkas ni dualité LP —
  la même comptabilité pondérée que la preuve du papier, déroulée à la
  main pour le core classique externe). Pour chaque votant `v` de la
  coalition bloquante :

    réserve v + Σ (paiements aux gagnants approuvés) = 1          (budget)
    Σ paiements ≤ |A_v ∩ S| · réserve v                           (p ≤ r)
    |A_v ∩ B| > |A_v ∩ S|                                          (blocage)

  donc `(Happiness v + 1) · réserve v ≥ 1`, puis
  `|A_v ∩ B| · réserve v ≥ 1`. En sommant sur `T` et en comptant deux
  fois les paires (v, c) :

    |T| ≤ Σ_{c ∈ B} Σ_{v approuve c} réserve v < Σ_{c ∈ B} q = |B| · q ≤ |T|

  — contradiction. Aucune hypothèse de signe sur `q` n'est requise : la
  contradiction est purement comptable.

  Aucun `sorry`. Convention i18n #4980 : ce fichier porte le namespace
  `ApprovalPayment` (FR). Le sibling `ApprovalPayment_en.lean` porte le
  namespace `ApprovalPayment_en` (EN). Préservation byte-identity hors
  docstrings — vérifiée par `scripts/lean/check_i18n_siblings.py`.
-/

import ApprovalDefs
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

namespace ApprovalPayment

open ApprovalDefs

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
/-- Identité de comptage utilisée partout : la somme d'une constante sur un
    `Finset` est le cardinal (casté dans ℚ) fois la constante. Prouvée par
    induction pour ne pas dépendre de la forme exacte des lemmes
    `sum_const` / smul de Mathlib. -/
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

/-- Ensemble des votants qui approuvent le candidat `c`. -/
def approvers (P : ApprovalProfile V A) (c : A) : Finset V :=
  Finset.univ.filter (fun v => c ∈ (P.ballots v).approved)

/-- Quota de Hare : `n` votants pour `k` sièges. -/
def hareQuota (P : ApprovalProfile V A) : ℚ :=
  (Fintype.card V : ℚ) / (P.committeeSize : ℚ)

/-- Quota de Droop : `n` votants pour `k + 1` bulletins. Toujours au plus
    le quota de Hare dès que `k ≥ 1`. -/
def droopQuota (P : ApprovalProfile V A) : ℚ :=
  (Fintype.card V : ℚ) / ((P.committeeSize : ℚ) + 1)

omit [DecidableEq A] in
/-- Positivité du quota de Hare dès qu'il y a un votant et un siège. -/
lemma hareQuota_pos (P : ApprovalProfile V A) (hn : 0 < Fintype.card V)
    (hk : 0 < P.committeeSize) : 0 < hareQuota P :=
  div_pos (by exact_mod_cast hn) (by exact_mod_cast hk)

omit [DecidableEq A] in
/-- Le quota de Droop est au plus le quota de Hare : `n/(k+1) ≤ n/k` dès
    que `k ≥ 1` (à `n` fixé, partager entre plus de sièges réduit la
    part ; le cas `n = 0` donne `0 ≤ 0`). -/
lemma droopQuota_le_hareQuota (P : ApprovalProfile V A)
    (hk : 0 < P.committeeSize) : droopQuota P ≤ hareQuota P := by
  have hn : (0:ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast Nat.zero_le _
  have hk' : (0:ℚ) < (P.committeeSize : ℚ) := by exact_mod_cast hk
  have hk1 : (0:ℚ) < (P.committeeSize : ℚ) + 1 := by linarith
  rw [hareQuota, droopQuota]
  field_simp
  nlinarith [hn]

/-! ## Système de paiement (définition 3.2 du papier) -/

/-- Système de paiement pour le comité `S` sous le quota `q` : chaque votant
    `v` paye `payment v c ≥ 0` pour chaque gagnant approuvé `c`, conserve la
    réserve `reserve v ≥ 0`, son budget total vaut exactement 1
    (`reserve v + Σ payment v = 1` — la forme additive de
    `r_i = 1 − Σ p_ic` du papier), et chaque gagnant `c ∈ S` reçoit au plus
    `q` de la part de ses approbateurs. -/
structure PaymentSystem (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (q : ℚ) where
  /-- Paiement du votant `v` au candidat `c`. -/
  payment : V → A → ℚ
  /-- Les paiements sont non négatifs. -/
  payment_nonneg : ∀ v c, 0 ≤ payment v c
  /-- Réserve du votant `v` après paiement des gagnants approuvés. -/
  reserve : V → ℚ
  /-- Les réserves sont non négatives. -/
  reserve_nonneg : ∀ v, 0 ≤ reserve v
  /-- Budget : la réserve plus la somme des paiements aux gagnants approuvés
      vaut exactement 1 (papier, déf. 3.2 : `r_i = 1 − Σ p_ic`). -/
  budget : ∀ v, reserve v +
      ∑ c ∈ (P.ballots v).approved.filter (fun x => x ∈ S.val), payment v c = 1
  /-- Chaque gagnant reçoit au plus le quota de ses approbateurs. -/
  winner_bound : ∀ c ∈ S.val, ∑ v ∈ approvers P c, payment v c ≤ q

/-- Le système de paiement trivial (aucun paiement, réserves pleines)
    existe dès que `q ≥ 0` : c'est la non-vacuité `P(W) ≠ ∅` remarquée
    sous la définition 3.2 du papier. Il ne satisfait en général pas la
    condition sur les perdants du certificat — sinon le core serait
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

/-- Certificat de core (moitié « facile » du théorème 3.3 du papier) : un
    système de paiement dont (i) chaque paiement à un gagnant approuvé
    n'excède pas la réserve du payeur, et (ii) pour chaque candidat
    perdant, la somme des réserves de ses approbateurs est **strictement**
    sous le quota. -/
structure PaymentCertificate (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (q : ℚ) extends PaymentSystem P S q where
  /-- Condition (i) : `p_vw ≤ r_v` pour tout gagnant `w` approuvé par `v`. -/
  pays_at_most_reserve : ∀ v (w : A), w ∈ (P.ballots v).approved → w ∈ S.val →
    payment v w ≤ reserve v
  /-- Condition (ii) : pour tout perdant `c`, les réserves de ses
      approbateurs somment strictement sous le quota. -/
  reserves_beat_losers : ∀ c, c ∉ S.val → ∑ v ∈ approvers P c, reserve v < q

/-! ## Core d'approbation à entitlement (lecture externe) -/

/-- La coalition `T` **bloque** le comité `S` sous le quota `q` via
    l'ensemble externe `B` (disjoint de `S`) : `B` est non vide, la
    coalition est assez grosse pour son entitlement (`|T| ≥ q · |B|`), et
    chaque membre de `T` approuve strictement plus de membres de `B` que
    de membres du comité. -/
def BlocksCore (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (q : ℚ) (T : Finset V) (B : Finset A) : Prop :=
  T.Nonempty ∧ B.Nonempty ∧ Disjoint B S.val ∧ (T.card : ℚ) ≥ q * (B.card : ℚ) ∧
    ∀ v ∈ T, (B.filter (fun c => c ∈ (P.ballots v).approved)).card > Happiness P S v

/-- Le comité `S` est dans le **core d'approbation** sous le quota `q` :
    aucune paire (coalition, ensemble externe) ne le bloque. -/
def InApprovalCore (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (q : ℚ) : Prop :=
  ∀ (T : Finset V) (B : Finset A), ¬ BlocksCore P S q T B

/-! ## Sens « certificat ⟹ core » du théorème 3.3 -/

/-- **Sens certificat du théorème 3.3** (Becker-Greger-Peters 2026) : si le
    comité `S` admet un système de paiement dont les paiements n'excèdent
    jamais les réserves et dont les réserves battent strictement tout
    candidat perdant, alors aucune coalition ne peut bloquer `S` — `S` est
    dans le core d'approbation (lecture externe). Aucune hypothèse de
    signe sur `q` : la contradiction est purement comptable. -/
theorem not_blocksCore_of_paymentCertificate (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) {q : ℚ}
    (cert : PaymentCertificate P S q) (T : Finset V) (B : Finset A) :
    ¬ BlocksCore P S q T B := by
  rintro ⟨hT, hB, hdisj, hsize, himp⟩
  -- Étape votant : budget + paiements sous réserve + amélioration stricte
  -- donnent `(Happiness v + 1) · réserve v ≥ 1`, donc `|A_v ∩ B| · réserve v ≥ 1`.
  have key : ∀ v ∈ T,
      (1:ℚ) ≤ ((B.filter (fun c => c ∈ (P.ballots v).approved)).card : ℚ) *
        cert.reserve v := by
    intro v hv
    have hap_eq : Happiness P S v =
        ((P.ballots v).approved.filter (fun x => x ∈ S.val)).card := rfl
    -- les paiements de v aux gagnants approuvés ne dépassent pas Happiness · réserve
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
    -- amélioration stricte : |A_v ∩ B| ≥ Happiness v + 1
    have hcard : (Happiness P S v + 1 : ℕ) ≤
        (B.filter (fun c => c ∈ (P.ballots v).approved)).card :=
      Nat.succ_le_of_lt (himp v hv)
    -- chaîne : 1 = réserve + Σ paiements ≤ réserve + Happiness · réserve
    --          = (Happiness + 1) · réserve ≤ |A_v ∩ B| · réserve
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
  -- Somme sur la coalition : Σ_v 1 = |T| ≤ Σ_v |A_v ∩ B| · réserve v
  have hT1 : ∑ v ∈ T, (1:ℚ) ≤ ∑ v ∈ T,
      ((B.filter (fun c => c ∈ (P.ballots v).approved)).card : ℚ) *
        cert.reserve v :=
    Finset.sum_le_sum (fun v hv => key v hv)
  -- Double comptage des paires (v, c) avec c ∈ B approuvé par v ∈ T
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
  -- Chaque perdant c ∈ B voit les réserves de ses approbateurs
  -- strictement sous le quota ; la somme interne (restreinte à T) aussi.
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
  -- Conclusion : |T| ≤ Σ < |B| · q ≤ |T| — contradiction.
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

end ApprovalPayment
