/-
  Lemmes de comptage sur listes triées
  ====================================

  Lemmes auxiliaires pour compter les éléments dans des listes triées relativement à un pivot
  (typiquement l'élément médian à la position `length / 2`).

  Ces lemmes factorisent l'argument structurel de comptage requis par
  `Voting.lean median_voter_theorem_strict` (sorries aux lignes L355 et L385).

  STRATÉGIE DE PREUVE (factorisée depuis Voting.lean L338-L354) :
  1. Soit `l` une liste triée avec un pivot à la position `k = l.length / 2`.
  2. Décomposer `l = take k ++ drop k`.
  3. Par tri, tous les éléments de `drop k` sont ≥ `l[k]`.
  4. Donc `l.countP (· < l[k]) ≤ (take k).length = k`.
  5. Symétriquement, `l.countP (l[k] ≤ ·) ≥ (drop k).length = l.length - k`.

  Une fois ces helpers prouvés, Voting.lean L355 et L385 se réduisent à un
  argument de pont :
    A := Finset.filter (peaks i < median) Finset.univ
    A.card = (univ.toList.filter (peaks · < median)).length
           = (univ.toList.map peaks).countP (· < median)
           = (sortedPeaksList.countP (· < median))   [par Perm.countP_eq]
           ≤ k                                        [par countP_lt_kth_le_half]

  LEMMES MATHLIB CLÉS (API cible) :
  - `List.Pairwise (· ≤ ·)` (primitive de tri dans le Mathlib actuel)
  - `List.sorted_mergeSort` / `List.mergeSort_perm`
  - `List.Perm.countP_eq`, `List.countP_append`, `List.countP_eq_zero`
  - `List.length_take`, `List.length_drop`, `List.take_append_drop`

  STATUT : fichier avec preuves complètes (les sorries initiaux ont été comblés).
  Cycle 25 Wave 3 ai-01 backup pour po-2026 Track 2.
  Référence : dispatché dans msg-20260511T233949-r0i1xs (2026-05-11).
-/

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Count
import Mathlib.Tactic

namespace SocialChoice.SortedListCounting

variable {α : Type*}

/-! ## Comptage des éléments relatifs au pivot d'une liste triée -/

/-- Pour une liste `l` triée par `(· ≤ ·)` et un pivot `l[k]`, le nombre d'éléments
    strictement inférieurs à `l[k]` est au plus `k`.

    ESQUISSE DE PREUVE :
    - Décomposer `l = l.take k ++ l.drop k` via `List.take_append_drop`.
    - `(l.take k).length = k` par `List.length_take` (en utilisant `hk : k < l.length`).
    - `(l.drop k).head = l[k]` par indexation.
    - Par `Pairwise.drop` et le raisonnement head-of-drop, tous les éléments de `l.drop k`
      sont `≥ l[k]`.
    - Donc `(l.drop k).countP (· < l[k]) = 0` par `List.countP_eq_zero`.
    - Combinant via `List.countP_append` et `List.countP_le_length` :
        `l.countP (· < l[k]) = (l.take k).countP (· < l[k]) + 0 ≤ k`. -/
theorem countP_lt_kth_le_half [LinearOrder α]
    {l : List α} (hsort : l.Pairwise (· ≤ ·)) {k : ℕ} (hk : k < l.length) :
    l.countP (fun x => decide (x < l[k])) ≤ k := by
  set p : α := l[k] with hp
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  conv_lhs => rw [hsplit]
  rw [List.countP_append]
  have h1 : (l.take k).countP (fun x => decide (x < p)) ≤ k := by
    calc (l.take k).countP (fun x => decide (x < p))
        ≤ (l.take k).length := List.countP_le_length
      _ = min k l.length := List.length_take
      _ ≤ k := min_le_left _ _
  have h2 : (l.drop k).countP (fun x => decide (x < p)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro x hx
    simp only [decide_eq_true_eq, not_lt, hp]
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    rw [List.getElem_drop]
    have hki_lt : k + i < l.length := by
      have hi' := hi
      rw [List.length_drop] at hi'
      omega
    by_cases hi0 : i = 0
    · subst hi0; simp
    · have hlt : k < k + i := by omega
      exact List.pairwise_iff_getElem.mp hsort k (k + i) hk hki_lt hlt
  omega

/-- Pour une liste `l` triée par `(· ≤ ·)` et un pivot `l[k]`, le nombre d'éléments
    `≥ l[k]` est au moins `l.length - k`.

    Dual de `countP_lt_kth_le_half`, donnant une borne inférieure sur
    le « côté droit » du pivot.

    ESQUISSE DE PREUVE :
    - Décomposer `l = l.take k ++ l.drop k`.
    - `(l.drop k).length = l.length - k` par `List.length_drop`.
    - Tous les éléments de `l.drop k` sont `≥ l[k]` (head + tri).
    - Donc `(l.drop k).countP (l[k] ≤ ·) = (l.drop k).length`.
    - Ajouter `(l.take k).countP (l[k] ≤ ·) ≥ 0` donne la borne. -/
theorem countP_ge_kth_ge_half_succ [LinearOrder α]
    {l : List α} (hsort : l.Pairwise (· ≤ ·)) {k : ℕ} (hk : k < l.length) :
    l.length - k ≤ l.countP (fun x => decide (l[k] ≤ x)) := by
  set p : α := l[k] with hp
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  conv_rhs => rw [hsplit]
  rw [List.countP_append]
  have hdrop_all : (l.drop k).countP (fun x => decide (p ≤ x)) = (l.drop k).length := by
    rw [List.countP_eq_length]
    intro x hx
    simp only [decide_eq_true_eq, hp]
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    rw [List.getElem_drop]
    have hki_lt : k + i < l.length := by
      have hi' := hi
      rw [List.length_drop] at hi'
      omega
    by_cases hi0 : i = 0
    · subst hi0; simp
    · have hlt : k < k + i := by omega
      exact List.pairwise_iff_getElem.mp hsort k (k + i) hk hki_lt hlt
  have hdrop_len : (l.drop k).length = l.length - k := List.length_drop
  rw [hdrop_all, hdrop_len]
  omega

/-- Dual de `countP_ge_kth_ge_half_succ` depuis le côté gauche : pour une liste triée `l`
    et un pivot `l[k]`, le nombre d'éléments `≤ l[k]` est au moins `k + 1`.

    PREUVE : décomposer `l = take (k+1) ++ drop (k+1)`. Les `k+1` premiers éléments
    (positions `0..k`) sont tous `≤ l[k]` par tri, contribuant `k+1`. -/
theorem countP_le_kth_ge_half_succ [LinearOrder α]
    {l : List α} (hsort : l.Pairwise (· ≤ ·)) {k : ℕ} (hk : k < l.length) :
    k + 1 ≤ l.countP (fun x => decide (x ≤ l[k])) := by
  set p : α := l[k] with hp
  have hsplit : l = l.take (k + 1) ++ l.drop (k + 1) := (List.take_append_drop (k + 1) l).symm
  conv_rhs => rw [hsplit]
  rw [List.countP_append]
  have htake_all : (l.take (k + 1)).countP (fun x => decide (x ≤ p)) = (l.take (k + 1)).length := by
    rw [List.countP_eq_length]
    intro x hx
    simp only [decide_eq_true_eq, hp]
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    rw [List.getElem_take]
    have hi_lt_k1 : i < k + 1 := by
      have hi' := hi
      rw [List.length_take] at hi'
      omega
    have hi_lt_l : i < l.length := by
      have hi' := hi
      rw [List.length_take] at hi'
      omega
    by_cases hi_eq : i = k
    · subst hi_eq; simp
    · have hlt : i < k := by omega
      exact List.pairwise_iff_getElem.mp hsort i k hi_lt_l hk hlt
  have htake_len : (l.take (k + 1)).length = k + 1 := by
    rw [List.length_take]
    omega
  rw [htake_all, htake_len]
  omega

/-! ## Pont : cardinalité de Finset.filter ↔ List.countP

    Pour appliquer `countP_lt_kth_le_half` / `countP_ge_kth_ge_half_succ` à
    `Voting.lean median_voter_theorem_strict`, nous devons traduire
    `(Finset.filter p Finset.univ).card` en `l.countP (decide ∘ p)` où
    `l := (Finset.univ.toList.map peaks).mergeSort (· ≤ ·)`. -/

/-- La cardinalité d'un filtre Finset vaut countP sur la toList sous-jacente. -/
theorem finset_filter_card_eq_toList_countP
    {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Bool) :
    (s.filter (fun a => p a = true)).card = s.toList.countP p := by
  rw [Finset.card, Finset.filter_val, ← Multiset.countP_eq_card_filter,
      ← Multiset.coe_toList s.val, Multiset.coe_countP]
  simp [Finset.toList]

/-- Pont spécialisé pour `Fintype` et la configuration de l'électeur médian :
    `A.card = (univ.toList.map f).countP p` (sans passer par le filtre).
    L'étape `mergeSort` est laissée à l'appelant (via `List.Perm.countP_eq`). -/
theorem finset_filter_lt_card_eq_toList_map_countP
    {ι α : Type*} [Fintype ι] [DecidableEq ι] (f : ι → α) (p : α → Bool) :
    (Finset.filter (fun i => p (f i) = true) Finset.univ).card =
      (Finset.univ.toList.map f).countP p := by
  rw [finset_filter_card_eq_toList_countP, List.countP_map]
  rfl

end SocialChoice.SortedListCounting
