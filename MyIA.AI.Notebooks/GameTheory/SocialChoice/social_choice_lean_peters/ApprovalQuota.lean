/-
  Quotas d'approbation — Hare `n/k` et Droop `n/(k+1)`
  =====================================================

  Résidu de l'issue #17988 pointé par le coordinateur le 2026-10-13 : « les
  quotas Hare n/k et Droop n/(k+1) ne sont définis nulle part dans le lake ».
  Ce fichier les définit, avec le seuil de coalition qu'ils induisent.

  Deux notions distinctes cohabitent dans la littérature et sont séparées ici :

  1. **Le quota** est un nombre de votants. Hare vaut `n / k`, Droop vaut
     `n / (k + 1)` — division entière, donc plancher. La forme stricte du
     quota de Droop (`⌊n/(k+1)⌋ + 1`), qui est celle des définitions
     électorales, est exposée séparément comme `droopThreshold` : confondre
     les deux est l'erreur classique, et les garder sous deux noms empêche
     qu'un appelant choisisse l'une en croyant l'autre.
  2. **Le seuil de coalition** est une prédicat sur un cardinal. Une coalition
     de `s` votants atteint le quota de Hare lorsque `n ≤ s * k`. Cette
     formulation entière est **exacte** : elle évite l'arrondi de `n / k`, qui
     ferait passer une coalition de `⌊n/k⌋` votants pour suffisante alors que
     `k * ⌊n/k⌋ < n` (par exemple `n = 5`, `k = 2` : le quota vaut 2, mais
     `2 * 2 = 4 < 5`).

  Le pont entre les deux est `isQuotaLarge_iff_hareQuota_le`, énoncé sous
  l'hypothèse `k ∣ n` : c'est exactement le cas où le plancher ne perd rien,
  et hors de ce cas l'équivalence est fausse (le contre-exemple ci-dessus).
  L'énoncer sans cette hypothèse serait un faux lemme, pas une simplification.

  Aucun `sorry`, aucun `native_decide`. Ce fichier ne dépend que de
  l'arithmétique de `Nat`.

  Convention i18n #4980 : ce fichier porte le namespace `ApprovalQuota` (FR).
  Le sibling `ApprovalQuota_en.lean` porte le namespace `ApprovalQuota_en` (EN).
  Préservation byte-identity hors docstrings — vérifiée par
  `scripts/lean/check_i18n_siblings.py`.
-/

import Mathlib.Data.Nat.Basic

namespace ApprovalQuota

/-- Quota de Hare : `n / k` votants, division entière (plancher). -/
def hareQuota (n k : ℕ) : ℕ := n / k

/-- Quota de Droop au sens du papier : `n / (k + 1)` votants, division
    entière (plancher). -/
def droopQuota (n k : ℕ) : ℕ := n / (k + 1)

/-- Forme **stricte** du quota de Droop, celle des définitions électorales :
    `⌊n / (k + 1)⌋ + 1`. Elle n'est pas `droopQuota` — voir le docstring du
    fichier. -/
def droopThreshold (n k : ℕ) : ℕ := droopQuota n k + 1

/-- Une coalition de `s` votants atteint le quota de Hare sur `n` votants et
    un comité de taille `k` lorsque `n ≤ s * k`. Formulation entière exacte :
    aucune division, donc aucun arrondi. -/
def IsQuotaLarge (n k s : ℕ) : Prop := n ≤ s * k

/-- Le quota de Hare ne dépasse jamais le nombre de votants. -/
lemma hareQuota_le_self (n k : ℕ) : hareQuota n k ≤ n :=
  Nat.div_le_self n k

/-- Le quota de Hare multiplié par la taille du comité ne dépasse jamais le
    nombre de votants : c'est la perte du plancher, explicite. -/
lemma hareQuota_mul_le (n k : ℕ) : hareQuota n k * k ≤ n :=
  Nat.div_mul_le_self n k

/-- Le quota de Droop est majoré par le quota de Hare dès que `k ≥ 1` : le
    dénominateur de Droop est plus grand, donc le quotient plus petit. -/
lemma droopQuota_le_hareQuota {n k : ℕ} (hk : 0 < k) :
    droopQuota n k ≤ hareQuota n k := by
  unfold droopQuota hareQuota
  exact Nat.div_le_div_left (Nat.le_succ k) hk

/-- Le seuil strict de Droop dépasse strictement le quota de Droop. -/
lemma droopQuota_lt_droopThreshold (n k : ℕ) :
    droopQuota n k < droopThreshold n k :=
  Nat.lt_succ_self _

/-- Le prédicat de seuil est monotone en la taille de la coalition : élargir
    une coalition ne lui fait pas perdre le quota. -/
lemma isQuotaLarge_mono {n k s s' : ℕ} (h : s ≤ s') (hs : IsQuotaLarge n k s) :
    IsQuotaLarge n k s' := by
  unfold IsQuotaLarge at *
  exact le_trans hs (Nat.mul_le_mul_right k h)

/-- La coalition de tous les votants atteint le quota de Hare dès que le
    comité n'est pas vide. -/
lemma isQuotaLarge_self (n k : ℕ) (hk : 1 ≤ k) : IsQuotaLarge n k n := by
  unfold IsQuotaLarge
  calc n = n * 1 := (Nat.mul_one n).symm
    _ ≤ n * k := Nat.mul_le_mul_left n hk

/-- Pont entre le quota et le seuil, sous l'hypothèse `k ∣ n`. Hors de cette
    hypothèse l'équivalence est **fausse** : `n = 5`, `k = 2`, `s = 2` donne
    `hareQuota = 2 ≤ 2` mais `5 ≤ 4` est faux. -/
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

end ApprovalQuota
