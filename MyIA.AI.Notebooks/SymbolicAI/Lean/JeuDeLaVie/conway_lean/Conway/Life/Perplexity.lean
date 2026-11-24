/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## Perplexite structurelle du Jeu de la Vie — Etage 1

Implementation Lean de l'etage 1 de la perplexite structurelle (issue #20205,
enonce vise c.6090816461 sur #18446, arbitre par le coordinateur) :
comptage constructif LZ76 d'un bitstream, perplexite fenetree
`windowedPerplexity`, evenement `maintainsAbove`, et les familles de lemmes
(sous-additivite, convexite en W, invariance par symetrie).

Toutes les fonctions sont recursives structurellement (evaluables par le
noyau, temoin par `decide` — jamais `native_decide`).
-/

import Mathlib.Tactic
import Conway.Life

/-
  Convention i18n (EPIC #4980) : ce fichier est FR canonique, miroir dans
  `Perplexity_en.lean`. Les enonces, tactiques et noms restent en anglais.
-/

namespace Conway
namespace Life

/-! ## Occurrences (facteurs contigus)

`occursIn v h` : le mot `v` apparait-il comme troncon contigu de `h` ?
Defini avec un test de prefixe maison (`isPrefixB`) pour garder le controle
total des lemmes, sans dependre des identifiants Mathlib.
-/

/-- Test de prefixe booleen : `v` est-il un prefixe de `w` ? -/
def isPrefixB : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => (a == b) && isPrefixB as bs

/-- `v` apparait-il comme troncon contigu de `h` ? -/
def occursIn (v h : List Bool) : Bool :=
  match v, h with
  | [], _ => true
  | _ :: _, [] => false
  | _ :: _, a :: t => isPrefixB v (a :: t) || occursIn v t

theorem isPrefixB_refl (v : List Bool) : isPrefixB v v = true := by
  induction v with
  | nil => simp [isPrefixB]
  | cons a as ih => simp [isPrefixB, ih]

theorem isPrefixB_append_right {v w t : List Bool} (h : isPrefixB v w = true) :
    isPrefixB v (w ++ t) = true := by
  induction v generalizing w with
  | nil => simp [isPrefixB]
  | cons a as ih =>
      cases w with
      | nil => simp [isPrefixB] at h
      | cons b bs =>
          simp only [isPrefixB, List.cons_append, Bool.and_eq_true, beq_iff_eq] at h ⊢
          obtain ⟨ rfl, hrest ⟩ := h
          exact ⟨ rfl, ih hrest ⟩

theorem isPrefixB_take (s : List Bool) (k : ℕ) : isPrefixB (s.take k) s = true := by
  induction k generalizing s with
  | zero => simp [isPrefixB]
  | succ k ih =>
      cases s with
      | nil => simp [isPrefixB]
      | cons a as => simp [isPrefixB, ih as]

theorem isPrefixB_drop (v w : List Bool) (d : ℕ) (h : isPrefixB v w = true) :
    isPrefixB (v.drop d) (w.drop d) = true := by
  induction v generalizing w d with
  | nil => simp [isPrefixB]
  | cons a as ih =>
      cases w with
      | nil => simp [isPrefixB] at h
      | cons b bs =>
          simp only [isPrefixB, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨ rfl, hrest ⟩ := h
          cases d with
          | zero =>
              simp only [List.drop_zero, isPrefixB, Bool.and_eq_true, beq_iff_eq]
              exact ⟨ by simp, hrest ⟩
          | succ d =>
              simp only [List.drop]
              exact ih bs d hrest

theorem isPrefixB_append_exists {v w : List Bool} (h : isPrefixB v w = true) :
    ∃ t, w = v ++ t := by
  induction v generalizing w with
  | nil => exact ⟨ w, rfl ⟩
  | cons a as ih =>
      cases w with
      | nil => simp [isPrefixB] at h
      | cons b bs =>
          simp only [isPrefixB, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨ rfl, hrest ⟩ := h
          obtain ⟨ t, ht ⟩ := ih hrest
          exact ⟨ t, by simp [ht] ⟩

theorem isPrefixB_append_left {x t w : List Bool} (h : isPrefixB (x ++ t) w = true) :
    isPrefixB x w = true := by
  induction x generalizing w with
  | nil => simp [isPrefixB]
  | cons a as ih =>
      cases w with
      | nil => simp [isPrefixB] at h
      | cons c cs =>
          simp only [isPrefixB, List.cons_append, Bool.and_eq_true, beq_iff_eq] at h ⊢
          obtain ⟨ rfl, hrest ⟩ := h
          exact ⟨ by simp, ih hrest ⟩

theorem isPrefixB_trans {x y z : List Bool} (hxy : isPrefixB x y = true)
    (hyz : isPrefixB y z = true) : isPrefixB x z = true := by
  obtain ⟨ t, rfl ⟩ := isPrefixB_append_exists hxy
  exact isPrefixB_append_left hyz

theorem occursIn_of_isPrefix {v h : List Bool} (hv : isPrefixB v h = true) :
    occursIn v h = true := by
  cases v with
  | nil => simp [occursIn]
  | cons a as =>
      cases h with
      | nil => simp [isPrefixB] at hv
      | cons b bs => simpa [occursIn] using Or.inl hv

/-- Preceder d'une cellule preserve les occurrences (O3). -/
theorem occursIn_cons {v h : List Bool} {a : Bool} (hv : occursIn v h = true) :
    occursIn v (a :: h) = true := by
  cases v with
  | nil => simp [occursIn]
  | cons x xs => simpa [occursIn] using Or.inr hv

/-- Etendre le tas a droite preserve les occurrences (O0). -/
theorem occursIn_append_left {v h t : List Bool} (hv : occursIn v h = true) :
    occursIn v (h ++ t) = true := by
  induction h generalizing v with
  | nil =>
      cases v with
      | nil => simp [occursIn]
      | cons a as => simp [occursIn] at hv
  | cons b bs ih =>
      cases v with
      | nil => simp [occursIn]
      | cons a as =>
          simp only [occursIn, List.cons_append, Bool.or_eq_true] at hv ⊢
          rcases hv with hp | ht
          · exact Or.inl (isPrefixB_append_right hp)
          · exact Or.inr (ih ht)

/-- Preceder le tas d'un mot preserve les occurrences (O4). -/
theorem occursIn_prepend (z : List Bool) {v h : List Bool} (hv : occursIn v h = true) :
    occursIn v (z ++ h) = true := by
  induction z with
  | nil => simpa using hv
  | cons c cs ih => exact occursIn_cons (ih)

/-- Le mot entier est un troncon de lui-meme, a toute position de depart. -/
theorem occursIn_drop_self (h : List Bool) : ∀ d, occursIn (h.drop d) h = true := by
  induction h with
  | nil => intro d; simp [occursIn]
  | cons b bs ih =>
      intro d
      cases d with
      | zero => exact occursIn_of_isPrefix (isPrefixB_refl (b :: bs))
      | succ d => exact occursIn_cons (ih d)

theorem occursIn_trans {x y z : List Bool} (hxy : occursIn x y = true)
    (hyz : occursIn y z = true) : occursIn x z = true := by
  induction z with
  | nil =>
      cases y with
      | nil =>
          cases x with
          | nil => simp [occursIn]
          | cons a as => simp [occursIn] at hxy
      | cons b bs => simp [occursIn] at hyz
  | cons c cs ih =>
      cases x with
      | nil => simp [occursIn]
      | cons a as =>
          cases y with
          | nil => simp [occursIn] at hxy
          | cons b bs =>
              simp only [occursIn, Bool.or_eq_true] at hyz
              rcases hyz with hp | htr
              · obtain ⟨ t, hteq ⟩ := isPrefixB_append_exists hp
                rw [hteq]
                exact occursIn_append_left hxy
              · exact occursIn_cons (ih htr)

/-- Un troncon demarrant en position `d` de `h` y apparait (O2). -/
theorem occursIn_drop_take (h : List Bool) (d k : ℕ) :
    occursIn ((h.drop d).take k) h = true :=
  occursIn_trans (occursIn_of_isPrefix (isPrefixB_take (h.drop d) k))
    (occursIn_drop_self h d)

/-- Un suffixe d'un mot occurrent reste occurrent (O1). -/
theorem occursIn_drop_of_occursIn {v h : List Bool}
    (hv : occursIn v h = true) (d : ℕ) : occursIn (v.drop d) h = true := by
  induction h generalizing v with
  | nil =>
      cases v with
      | nil => simp [occursIn]
      | cons a as => simp [occursIn] at hv
  | cons b bs ih =>
      cases v with
      | nil => simp [occursIn]
      | cons a as =>
          cases hd : (a :: as).drop d with
          | nil => simp [occursIn]
          | cons x xs =>
              simp only [occursIn, Bool.or_eq_true] at hv
              rcases hv with hp | ht
              · rw [← hd]
                exact occursIn_trans
                  (occursIn_of_isPrefix (isPrefixB_drop (a :: as) (b :: bs) d hp))
                  (occursIn_drop_self (b :: bs) d)
              · have hrec := ih ht
                rw [hd] at hrec
                exact occursIn_cons hrec

/-! ## Algebre take/drop

Identites de base du raisonnement positionnel, prouvees de zero pour ne
pas dependre des identifiants Mathlib.
-/

theorem take_append_take (s : List Bool) (p j : ℕ) :
    s.take p ++ (s.drop p).take j = s.take (p + j) := by
  induction s generalizing p with
  | nil => simp
  | cons a as ih =>
      cases p with
      | zero => simp
      | succ p' => simp [Nat.succ_add, ih p']

theorem take_drop_comm : ∀ (j : ℕ) (l : List Bool) (d : ℕ),
    (l.take j).drop d = (l.drop d).take (j - d) := by
  intro j
  induction j with
  | zero => intro l d; simp
  | succ j ih =>
      intro l d
      cases l with
      | nil => simp
      | cons a as =>
          cases d with
          | zero => simp
          | succ d' =>
              have h := ih as d'
              have hsub : j + 1 - (d' + 1) = j - d' := by omega
              simp [h, hsub]

theorem drop_take_drop (s : List Bool) (p j d : ℕ) :
    ((s.drop p).take j).drop d = (s.drop (p + d)).take (j - d) := by
  rw [take_drop_comm j (s.drop p) d, List.drop_drop]

theorem take_append_of_le (a b : List Bool) (k : ℕ) (hk : k ≤ a.length) :
    (a ++ b).take k = a.take k := by
  induction a generalizing k with
  | nil =>
      have h0 : k = 0 := by simpa using hk
      subst h0; simp
  | cons x xs ih =>
      cases k with
      | zero => simp
      | succ k' => simp [ih k' (by simpa using hk)]

theorem drop_append_of_le (a b : List Bool) (k : ℕ) (hk : k ≤ a.length) :
    (a ++ b).drop k = a.drop k ++ b := by
  induction a generalizing k with
  | nil =>
      have h0 : k = 0 := by simpa using hk
      subst h0; simp
  | cons x xs ih =>
      cases k with
      | zero => simp
      | succ k' => simp [ih k' (by simpa using hk)]

theorem take_append_of_ge (a b : List Bool) (k : ℕ) (hk : a.length ≤ k) :
    (a ++ b).take k = a ++ b.take (k - a.length) := by
  induction a generalizing k b with
  | nil => simp
  | cons x xs ih =>
      cases k with
      | zero => simp only [List.length_cons] at hk; omega
      | succ k' =>
          have hsub : k' + 1 - (xs.length + 1) = k' - xs.length := by omega
          simp [ih b k' (by simp only [List.length_cons] at hk; omega), hsub]

theorem drop_append_of_ge (a b : List Bool) (k : ℕ) (hk : a.length ≤ k) :
    (a ++ b).drop k = b.drop (k - a.length) := by
  induction a generalizing k b with
  | nil => simp
  | cons x xs ih =>
      cases k with
      | zero => simp only [List.length_cons] at hk; omega
      | succ k' =>
          have hsub : k' + 1 - (xs.length + 1) = k' - xs.length := by omega
          simp [ih b k' (by simp only [List.length_cons] at hk; omega), hsub]

/-! ## La phrase LZ76

`phraseGo r h fuel k` : longueur de la phrase LZ76 commencant au debut du
reste `r` sachant l'historique `h`. La phrase est le plus court prefixe
`r.take k` qui ne reapparait pas dans `h ++ r.take (k - 1)` ; si tout le
reste reapparait, la phrase est le reste entier. Recursion structurelle
sur `fuel` (au plus `r.length + 1 - k` appels), evaluable par le noyau.
-/

/-- Boucle de scan de la phrase LZ76. `k` est le candidat courant. -/
def phraseGo (r h : List Bool) : ℕ → ℕ → ℕ
  | 0, k => if k ≤ r.length then k else r.length
  | fuel + 1, k =>
      if k ≤ r.length then
        (if occursIn (r.take k) (h ++ r.take (k - 1)) then phraseGo r h fuel (k + 1) else k)
      else k - 1

/-- Longueur de la phrase LZ76 du reste `r` avec historique `h`. -/
def phraseLenH (h r : List Bool) : ℕ := phraseGo r h r.length 1

/-- Longueur de la phrase a la position absolue `i` du mot `s`. -/
def phraseLenAt (s : List Bool) (i : ℕ) : ℕ := phraseGo (s.drop i) (s.take i) (s.drop i).length 1

theorem phraseGo_le (r h : List Bool) : ∀ (fuel k : ℕ), 1 ≤ k → k ≤ r.length + 1 →
    phraseGo r h fuel k ≤ r.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro k _ _
      simp only [phraseGo]
      by_cases hc : k ≤ r.length
      · rw [if_pos hc]; exact hc
      · rw [if_neg hc]
  | succ fuel ih =>
      intro k _ hkle
      simp only [phraseGo]
      by_cases hc : k ≤ r.length
      · rw [if_pos hc]
        by_cases ho : occursIn (r.take k) (h ++ r.take (k - 1)) = true
        · rw [if_pos ho]; exact ih (k + 1) (by omega) (by omega)
        · rw [if_neg ho]; exact hc
      · rw [if_neg hc]; omega

theorem phraseGo_ge_pred (r h : List Bool) : ∀ (fuel k : ℕ), k ≤ r.length + 1 →
    k - 1 ≤ phraseGo r h fuel k := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hkle
      simp only [phraseGo]
      by_cases hc : k ≤ r.length
      · rw [if_pos hc]; omega
      · rw [if_neg hc]; omega
  | succ fuel ih =>
      intro k hkle
      simp only [phraseGo]
      by_cases hc : k ≤ r.length
      · rw [if_pos hc]
        by_cases ho : occursIn (r.take k) (h ++ r.take (k - 1)) = true
        · rw [if_pos ho]; have := ih (k + 1) (by omega); omega
        · rw [if_neg ho]; omega
      · rw [if_neg hc]

theorem phraseGo_pos (r h : List Bool) (hr : r ≠ []) : ∀ (fuel k : ℕ), 1 ≤ k →
    k ≤ r.length + 1 → 1 ≤ phraseGo r h fuel k := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hk1 _
      simp only [phraseGo]
      by_cases hc : k ≤ r.length
      · rw [if_pos hc]; exact hk1
      · rw [if_neg hc]
        cases r with
        | nil => exact absurd rfl hr
        | cons a as => simp only [List.length_cons] at hc ⊢; omega
  | succ fuel ih =>
      intro k _ _
      simp only [phraseGo]
      by_cases hc : k ≤ r.length
      · rw [if_pos hc]
        by_cases ho : occursIn (r.take k) (h ++ r.take (k - 1)) = true
        · rw [if_pos ho]; exact ih (k + 1) (by omega) (by omega)
        · rw [if_neg ho]; omega
      · rw [if_neg hc]
        cases r with
        | nil => exact absurd rfl hr
        | cons a as => simp only [List.length_cons] at hc ⊢; omega

/-- Tout candidat passe avant la sortie a verifie sa condition. -/
theorem phraseGo_cond_lt (r h : List Bool) : ∀ (fuel k k' : ℕ), k ≤ k' →
    k' < phraseGo r h fuel k → occursIn (r.take k') (h ++ r.take (k' - 1)) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro k k' hkle hlt
      simp only [phraseGo] at hlt
      by_cases hc : k ≤ r.length
      · rw [if_pos hc] at hlt; omega
      · rw [if_neg hc] at hlt; omega
  | succ fuel ih =>
      intro k k' hkle hlt
      simp only [phraseGo] at hlt
      by_cases hc : k ≤ r.length
      · rw [if_pos hc] at hlt
        by_cases ho : occursIn (r.take k) (h ++ r.take (k - 1)) = true
        · rw [if_pos ho] at hlt
          rcases Nat.lt_or_ge k' (k + 1) with hlt' | hge
          · have hke : k' = k := by omega
            subst hke
            exact ho
          · exact ih (k + 1) k' (by omega) hlt
        · rw [if_neg ho] at hlt; omega
      · rw [if_neg hc] at hlt; omega

/-- Si toutes les conditions tiennent jusqu'a `k₁`, la phrase atteint `k₁`. -/
theorem phraseGo_ge_from (r h : List Bool) : ∀ (fuel k k₁ : ℕ), k ≤ k₁ → k₁ ≤ r.length →
    fuel ≥ k₁ - k + 1 →
    (∀ k', k ≤ k' → k' < k₁ → occursIn (r.take k') (h ++ r.take (k' - 1)) = true) →
    k₁ ≤ phraseGo r h fuel k := by
  intro fuel
  induction fuel with
  | zero =>
      intro k k₁ hkle hlen hfuel _
      simp only [phraseGo]
      have hke : k = k₁ := by omega
      subst hke
      split
      · next hk => exact le_refl _
      · omega
  | succ fuel ih =>
      intro k k₁ hkle hlen hfuel hcond
      simp only [phraseGo]
      split
      · next hk =>
        rcases Nat.eq_or_lt_of_le hkle with rfl | hlt
        · split
          · next hcondk =>
            have hge := phraseGo_ge_pred r h fuel (k + 1) (by omega); omega
          · exact le_refl _
        · rw [if_pos (hcond k (le_refl k) (by omega))]
          exact ih (k + 1) k₁ (by omega) hlen (by omega)
            (fun k' hk' hlt' => hcond k' (by omega) hlt')
      · omega

theorem phraseGo_guard (r h : List Bool) (fuel k : ℕ) (hgt : r.length < k)
    (hle : k ≤ r.length + 1) : phraseGo r h fuel k = r.length := by
  cases fuel with
  | zero =>
      simp only [phraseGo]
      rw [if_neg (by omega)]
  | succ fuel =>
      simp only [phraseGo]
      rw [if_neg (by omega)]
      omega

/-- Deux scans aux conditions identiques (jusqu'a la borne) rendent le meme resultat. -/
theorem phraseGo_agree (r₁ h₁ r₂ h₂ : List Bool) (hlen : r₁.length = r₂.length)
    (hcond : ∀ k, 1 ≤ k → k ≤ r₁.length →
      r₁.take k = r₂.take k ∧ (h₁ ++ r₁.take (k - 1)) = (h₂ ++ r₂.take (k - 1)))
    (fuel₁ fuel₂ k : ℕ) (hk : 1 ≤ k) (hklen : k ≤ r₁.length + 1)
    (hf₁ : r₁.length + 1 - k ≤ fuel₁) (hf₂ : r₂.length + 1 - k ≤ fuel₂) :
    phraseGo r₁ h₁ fuel₁ k = phraseGo r₂ h₂ fuel₂ k := by
  induction fuel₁ generalizing k fuel₂ with
  | zero =>
      have hk1 : k = r₁.length + 1 := by omega
      subst hk1
      rw [hlen, phraseGo_guard r₁ h₁ 0 (r₂.length + 1) (by omega) (by omega),
          phraseGo_guard r₂ h₂ fuel₂ (r₂.length + 1) (by omega) (by omega)]
      exact hlen
  | succ fuel ih =>
      rcases Nat.lt_or_ge k (r₁.length + 1) with hlt | hge
      · have hkle : k ≤ r₁.length := by omega
        have hkle₂ : k ≤ r₂.length := by omega
        cases fuel₂ with
        | zero => omega
        | succ fuel₂' =>
            obtain ⟨ htake, hhist ⟩ := hcond k hk hkle
            simp only [phraseGo]
            rw [hlen, htake, hhist]
            by_cases hc : occursIn (r₂.take k) (h₂ ++ r₂.take (k - 1)) = true
            · rw [if_pos hkle₂, if_pos hkle₂, if_pos hc, if_pos hc]
              have e3 : r₁.length + 1 - (k + 1) ≤ fuel := by omega
              have e4 : r₂.length + 1 - (k + 1) ≤ fuel₂' := by omega
              exact ih fuel₂' (k + 1) (by omega) (by omega) e3 e4
            · rw [if_pos hkle₂, if_pos hkle₂, if_neg hc, if_neg hc]
      · have hk1 : k = r₁.length + 1 := by omega
        subst hk1
        rw [hlen, phraseGo_guard r₁ h₁ (fuel + 1) (r₂.length + 1) (by omega) (by omega),
            phraseGo_guard r₂ h₂ fuel₂ (r₂.length + 1) (by omega) (by omega)]
        exact hlen

theorem phraseLenH_le (h r : List Bool) : phraseLenH h r ≤ r.length :=
  phraseGo_le r h r.length 1 (by omega) (by omega)

theorem phraseLenH_pos (h r : List Bool) (hr : r ≠ []) : 1 ≤ phraseLenH h r :=
  phraseGo_pos r h hr r.length 1 (by omega) (by omega)

theorem phraseLenH_holds (h r : List Bool) (k' : ℕ) (hk' : 1 ≤ k')
    (hlt : k' < phraseLenH h r) : occursIn (r.take k') (h ++ r.take (k' - 1)) = true :=
  phraseGo_cond_lt r h r.length 1 k' (by omega) hlt

theorem phraseLenH_agree (r₁ h₁ r₂ h₂ : List Bool) (hlen : r₁.length = r₂.length)
    (hcond : ∀ k, 1 ≤ k → k ≤ r₁.length →
      r₁.take k = r₂.take k ∧ (h₁ ++ r₁.take (k - 1)) = (h₂ ++ r₂.take (k - 1))) :
    phraseLenH h₁ r₁ = phraseLenH h₂ r₂ := by
  simp only [phraseLenH]
  exact phraseGo_agree r₁ h₁ r₂ h₂ hlen hcond r₁.length r₂.length 1 (by omega) (by omega)
    (by omega) (by omega)

theorem phraseLenAt_pos (s : List Bool) (i : ℕ) (hi : i < s.length) :
    1 ≤ phraseLenAt s i := by
  have hne : s.drop i ≠ [] := by
    intro h
    have hlen : (s.drop i).length = 0 := by rw [h]; rfl
    rw [List.length_drop] at hlen
    omega
  exact phraseGo_pos (s.drop i) (s.take i) hne (s.drop i).length 1 (by omega)
    (by rw [List.length_drop]; omega)

theorem phraseLenAt_le (s : List Bool) (i : ℕ) : phraseLenAt s i ≤ s.length - i := by
  have h1 := phraseGo_le (s.drop i) (s.take i) (s.drop i).length 1 (by omega) (by omega)
  simp only [phraseLenAt] at h1 ⊢
  rw [List.length_drop] at h1 ⊢
  exact h1

/-! ## Comptage des phrases

`countFromGo s fuel i` : nombre de phrases pour couvrir `s` a partir de la
position absolue `i` (historique canonique `s.take i`). Structurel en `fuel`.
-/

def countFromGo (s : List Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, i =>
      if i < s.length then
        1 + countFromGo s fuel (i + phraseLenAt s i)
      else 0

/-- Nombre de phrases couvrant `s` a partir de la position `i`. -/
def countFrom (s : List Bool) (i : ℕ) : ℕ := countFromGo s s.length i

/-- La complexite LZ76 : nombre de facteurs de la factorisation du mot entier. -/
def lz76Count (s : List Bool) : ℕ := countFrom s 0

theorem countFromGo_of_ge {s : List Bool} {i : ℕ} (h : s.length ≤ i) (f : ℕ) :
    countFromGo s f i = 0 := by
  cases f with
  | zero => rfl
  | succ f' =>
      simp only [countFromGo]
      rw [if_neg (by omega)]

theorem countFromGo_enough (s : List Bool) : ∀ (d i f : ℕ), s.length - i ≤ d → s.length - i ≤ f →
    countFromGo s f i = countFromGo s s.length i := by
  intro d
  induction d with
  | zero =>
      intro i f hdi _
      have h : s.length ≤ i := by omega
      simp only [countFromGo_of_ge h]
  | succ d ih =>
      intro i f hdi hf
      by_cases hi : i < s.length
      · have hK : 1 ≤ phraseLenAt s i := phraseLenAt_pos s i hi
        obtain ⟨ f', rfl ⟩ : ∃ f', f = f' + 1 := ⟨ f - 1, by omega ⟩
        obtain ⟨ m, hm ⟩ : ∃ m, s.length = m + 1 := ⟨ s.length - 1, by omega ⟩
        simp only [countFromGo, if_pos hi]
        rw [hm]
        simp only [countFromGo, if_pos hi]
        have e1 := ih (i + phraseLenAt s i) f' (by omega) (by omega)
        have e2 := ih (i + phraseLenAt s i) m (by omega) (by omega)
        rw [e1, e2]
      · have h : s.length ≤ i := by omega
        simp only [countFromGo_of_ge h]

theorem countFrom_eq_countFromGo (s : List Bool) (i f : ℕ) (hf : s.length ≤ f) :
    countFrom s i = countFromGo s f i := by
  rw [countFrom, countFromGo_enough s (s.length - i) i f (by omega) (by omega)]

theorem countFrom_succ (s : List Bool) (i : ℕ) (hi : i < s.length) :
    countFrom s i = 1 + countFrom s (i + phraseLenAt s i) := by
  have h1 := countFrom_eq_countFromGo s i (s.length + 1) (by omega)
  have h2 := countFrom_eq_countFromGo s (i + phraseLenAt s i) s.length (by omega)
  rw [h1]
  simp only [countFromGo, if_pos hi]
  rw [← h2]

theorem countFrom_of_eq_length {s : List Bool} (i : ℕ) (hi : s.length ≤ i) :
    countFrom s i = 0 := countFromGo_of_ge hi s.length

theorem countFrom_pos_of_lt (s : List Bool) (i : ℕ) (hi : i < s.length) :
    1 ≤ countFrom s i := by
  rw [countFrom_succ s i hi]; omega

/-! ## Agreement d'un scan avec un reste etendu

Si la phrase du reste etendu `a ++ b` tient dans `a`, elle coïncide avec la
phrase du reste court `a` (les conditions et les tas sont identiques tant
que le candidat reste dans `a`).
-/

theorem phraseLenH_prefix_eq (h a b : List Bool) (hK : phraseLenH h (a ++ b) ≤ a.length) :
    phraseLenH h a = phraseLenH h (a ++ b) := by
  by_cases ha : a = []
  · rw [ha, List.nil_append] at hK ⊢
    have h1 : phraseLenH h [] = 0 := by simp [phraseLenH, phraseGo]
    rw [h1]
    simp at hK
    omega
  have hab : a ++ b ≠ [] := by
    intro hc
    obtain ⟨ hc1, _ ⟩ := List.append_eq_nil_iff.mp hc
    exact ha hc1
  have hpos1 : 1 ≤ phraseLenH h a := phraseLenH_pos h a ha
  have hpos2 : 1 ≤ phraseLenH h (a ++ b) := phraseLenH_pos h (a ++ b) hab
  have hlenapp : (a ++ b).length = a.length + b.length := List.length_append
  have hcoinc : ∀ k, 1 ≤ k → k ≤ a.length →
      (a ++ b).take k = a.take k ∧ (h ++ (a ++ b).take (k - 1)) = (h ++ a.take (k - 1)) := by
    intro k _ hk
    refine ⟨take_append_of_le a b k hk, ?_⟩
    rw [take_append_of_le a b (k - 1) (by omega)]
  have hcond1 : ∀ k', 1 ≤ k' → k' < phraseLenH h (a ++ b) →
      occursIn (a.take k') (h ++ a.take (k' - 1)) = true := by
    intro k' hk' hlt
    have hc := phraseLenH_holds h (a ++ b) k' hk' hlt
    obtain ⟨ ht1, ht2 ⟩ := hcoinc k' hk' (by omega)
    rw [← ht1, ← ht2]
    exact hc
  have hKa_le : phraseLenH h a ≤ a.length := phraseLenH_le h a
  have hcond2 : ∀ k', 1 ≤ k' → k' < phraseLenH h a →
      occursIn ((a ++ b).take k') (h ++ (a ++ b).take (k' - 1)) = true := by
    intro k' hk' hlt
    have hc := phraseLenH_holds h a k' hk' hlt
    obtain ⟨ ht1, ht2 ⟩ := hcoinc k' hk' (by omega)
    rw [ht1, ht2]
    exact hc
  have hge1 := phraseGo_ge_from a h a.length 1 (phraseLenH h (a ++ b))
    (by omega) (by omega) (by omega) (fun k' hk' hlt => hcond1 k' (by omega) hlt)
  have hge2 := phraseGo_ge_from (a ++ b) h (a ++ b).length 1 (phraseLenH h a)
    (by omega) (by omega) (by omega) (fun k' hk' hlt => hcond2 k' (by omega) hlt)
  simp only [phraseLenH] at hge1 hge2 ⊢
  omega

/-! ## Lemme maitre : plus d'historique ne coute pas plus de phrases

Parser `z ++ s` a partir de la position `|z| + q` (historique enrichi du
prefixe `z`) ne demande pas plus de phrases que parser `s` a partir de
`p ≤ q`. Chaque phrase du parse riche depasse la prochaine frontiere du
parse pauvre (argument du suffixe d'occurrence, O1). C'est le coeur de la
sous-additivite.
-/

theorem countFrom_le_of_prefixHist (z s : List Bool) : ∀ (d p q : ℕ), s.length - p ≤ d →
    p ≤ q → q ≤ s.length → countFrom (z ++ s) (z.length + q) ≤ countFrom s p := by
  intro d
  induction d with
  | zero =>
      intro p q hd hpq hq
      have hp : p = s.length := by omega
      subst hp
      have hq' : q = s.length := by omega
      subst hq'
      rw [countFrom_of_eq_length (z.length + s.length)
            (by simp only [List.length_append]; omega),
          countFrom_of_eq_length s.length (by omega)]
  | succ d ih =>
      intro p q hd hpq hq
      by_cases hps : p < s.length
      · have hKp := phraseLenAt_pos s p hps
        have hKple := phraseLenAt_le s p
        rw [countFrom_succ s p hps]
        by_cases hqs : q < s.length
        · have hlenapp : (z ++ s).length = z.length + s.length := List.length_append
          have hQlt : z.length + q < (z ++ s).length := by omega
          have hKrpos := phraseLenAt_pos (z ++ s) (z.length + q) hQlt
          have hKrle := phraseLenAt_le (z ++ s) (z.length + q)
          rw [countFrom_succ (z ++ s) (z.length + q) hQlt]
          -- (F'') : la phrase riche atteint au moins la frontiere pauvre
          have hreach : p + phraseLenAt s p ≤ q + phraseLenAt (z ++ s) (z.length + q) := by
            by_cases htriv : p + phraseLenAt s p ≤ q
            · omega
            · -- le scan riche doit franchir k₁ = frontiere pauvre - position riche
              have hk₁pos : 1 ≤ p + phraseLenAt s p - q := by omega
              -- conditions pauvres
              have hpoor : ∀ k', 1 ≤ k' → k' < phraseLenAt s p →
                  occursIn ((s.drop p).take k')
                    (s.take p ++ (s.drop p).take (k' - 1)) = true := by
                intro k' hk' hlt
                exact phraseLenH_holds (s.take p) (s.drop p) k' hk' hlt
              -- identites de cadrage de la position riche
              have hdr : (z ++ s).drop (z.length + q) = s.drop q := by
                rw [drop_append_of_ge z s (z.length + q) (by omega)]
                congr 1
                omega
              have htk : (z ++ s).take (z.length + q) = z ++ s.take q := by
                rw [take_append_of_ge z s (z.length + q) (by omega), Nat.add_sub_cancel_left]
              have hrlen : (s.drop q).length = s.length - q := List.length_drop
              -- conditions riches
              have hrich : ∀ k', 1 ≤ k' → k' < p + phraseLenAt s p - q →
                  occursIn ((s.drop q).take k')
                    ((z ++ s.take q) ++ (s.drop q).take (k' - 1)) = true := by
                intro k' hk' hlt
                have hk'' : 1 ≤ (q - p) + k' ∧ (q - p) + k' < phraseLenAt s p := by omega
                have hp := hpoor ((q - p) + k') hk''.1 hk''.2
                -- tas pauvre = s.take (q + k' - 1)
                have hhay : s.take p ++ (s.drop p).take ((q - p) + k' - 1)
                    = s.take (q + k' - 1) := by
                  rw [take_append_take s p ((q - p) + k' - 1)]
                  congr 1
                  omega
                rw [hhay] at hp
                -- fragment riche = suffixe du fragment pauvre (I2 + O1)
                have hocc : occursIn ((s.drop q).take k') (s.take (q + k' - 1)) = true := by
                  have hd := occursIn_drop_of_occursIn hp (q - p)
                  rw [drop_take_drop s p ((q - p) + k') (q - p)] at hd
                  have hfraglen : (q - p) + k' - (q - p) = k' := by omega
                  rw [hfraglen] at hd
                  have hpqnorm : p + (q - p) = q := by omega
                  rw [hpqnorm] at hd
                  exact hd
                -- le tas riche contient le tas pauvre (O0)
                have hqk : q + k' - 1 = q + (k' - 1) := by omega
                rw [hqk] at hocc
                rw [List.append_assoc, take_append_take s q (k' - 1)]
                exact occursIn_prepend z hocc
              -- le scan riche atteint la frontiere pauvre
              have hscan : p + phraseLenAt s p - q
                  ≤ phraseLenAt (z ++ s) (z.length + q) := by
                have hge := phraseGo_ge_from (s.drop q) (z ++ s.take q) (s.drop q).length 1
                  (p + phraseLenAt s p - q) (by omega) (by omega) (by omega) hrich
                have hunf : phraseLenAt (z ++ s) (z.length + q)
                    = phraseGo (s.drop q) (z ++ s.take q) (s.drop q).length 1 := by
                  simp only [phraseLenAt, hdr, htk]
                rw [hunf]
                exact hge
              omega
          -- recursion : la frontiere pauvre est atteinte, induction sur d
          have hrec := ih (p + phraseLenAt s p) (q + phraseLenAt (z ++ s) (z.length + q))
            (by omega) (by omega)
            (by
              have hK := phraseLenAt_le (z ++ s) (z.length + q)
              simp only [List.length_append] at hK
              have hdrops : (z ++ s).drop (z.length + q) = s.drop q := by
                rw [drop_append_of_ge z s (z.length + q) (by omega)]
                congr 1
                omega
              simp only [phraseLenAt, hdrops, List.length_drop] at hK
              omega)
          have hpos : z.length + q + phraseLenAt (z ++ s) (z.length + q)
              = z.length + (q + phraseLenAt (z ++ s) (z.length + q)) := by omega
          rw [hpos]
          omega
        · have hq' : q = s.length := by omega
          subst hq'
          rw [countFrom_of_eq_length (z.length + s.length)
                (by rw [List.length_append])]
          omega
      · have hp' : p = s.length := by omega
        subst hp'
        have hq' : q = s.length := by omega
        subst hq'
        rw [countFrom_of_eq_length s.length (by omega),
            countFrom_of_eq_length (z.length + s.length)
              (by rw [List.length_append])]

/-! ## Sous-additivite de C_LZ

Le parse glouton de `u ++ v` ne coute pas plus de phrases que `u` et `v`
separes : les phrases qui demarrent dans `u` coincident avec celles du
parse de `u` tant qu'elles y tiennent, et la phrase a cheval sur la
frontiere est absorbee par la premiere phrase du parse de `u`.
-/

theorem countFrom_append_aux (u v : List Bool) : ∀ (n i : ℕ), u.length - i ≤ n → i ≤ u.length →
    ∃ ℓ, ℓ ≤ v.length ∧ countFrom (u ++ v) i
      ≤ countFrom u i + countFrom (u ++ v) (u.length + ℓ) := by
  intro n
  induction n with
  | zero =>
      intro i hni hi
      have hie : i = u.length := by omega
      subst hie
      refine ⟨ 0, by omega, ?_ ⟩
      rw [Nat.add_zero]
      exact Nat.le_add_left _ _
  | succ n ih =>
      intro i hni hi
      by_cases hilt : i < u.length
      · have hlenapp : (u ++ v).length = u.length + v.length := List.length_append
        have hKpos := phraseLenAt_pos (u ++ v) i (by omega)
        have hKle := phraseLenAt_le (u ++ v) i
        simp only [List.length_append] at hKle
        rw [countFrom_succ (u ++ v) i (by omega)]
        by_cases hfit : i + phraseLenAt (u ++ v) i ≤ u.length
        · -- la phrase tient dans u : les parses coincident
          have hdrop : (u ++ v).drop i = (u.drop i) ++ v :=
            drop_append_of_le u v i (by omega)
          have htake : (u ++ v).take i = u.take i :=
            take_append_of_le u v i (by omega)
          have hdrlen : (u.drop i).length = u.length - i := List.length_drop
          have hpreq : phraseLenAt u i = phraseLenAt (u ++ v) i := by
            have hKfit : phraseLenH (u.take i) ((u.drop i) ++ v) ≤ (u.drop i).length := by
              have hdef : phraseLenH (u.take i) ((u.drop i) ++ v) = phraseLenAt (u ++ v) i := by
                simp only [phraseLenH, phraseLenAt, htake, hdrop]
              rw [hdef, hdrlen]
              omega
            have hpg := phraseLenH_prefix_eq (u.take i) (u.drop i) v hKfit
            calc phraseLenAt u i = phraseLenH (u.take i) (u.drop i) := rfl
              _ = phraseLenH (u.take i) ((u.drop i) ++ v) := hpg
              _ = phraseLenAt (u ++ v) i := by simp only [phraseLenH, phraseLenAt, htake, hdrop]
          rw [← hpreq, countFrom_succ u i hilt]
          obtain ⟨ ℓ, hℓv, hle ⟩ := ih (i + phraseLenAt u i) (by omega) (by omega)
          refine ⟨ ℓ, hℓv, ?_ ⟩
          omega
        · -- phrase a cheval sur la frontiere : absorbee par le parse de u
          have hpos_u : 1 ≤ countFrom u i := countFrom_pos_of_lt u i hilt
          have hconv : i + phraseLenAt (u ++ v) i
              = u.length + (i + phraseLenAt (u ++ v) i - u.length) := by omega
          refine ⟨ i + phraseLenAt (u ++ v) i - u.length, by omega, ?_ ⟩
          rw [← hconv]
          omega
      · have hie : i = u.length := by omega
        subst hie
        refine ⟨ 0, by omega, ?_ ⟩
        rw [Nat.add_zero]
        exact Nat.le_add_left _ _

/-- **Sous-additivite forte** : la complexite LZ76 d'une concatenation ne
depasse pas la somme des complexites (la phrase a cheval sur la frontiere
remplace une phrase du parse de `u`). -/
theorem lz76Count_append (u v : List Bool) :
    lz76Count (u ++ v) ≤ lz76Count u + lz76Count v := by
  obtain ⟨ ℓ, hℓv, hle ⟩ := countFrom_append_aux u v u.length 0 (by omega) (by omega)
  have hmaster := countFrom_le_of_prefixHist u v v.length 0 ℓ (by omega) (by omega) hℓv
  unfold lz76Count
  omega

/-- Forme classique avec la constante de frontiere. -/
theorem lz76Count_append_le (u v : List Bool) :
    lz76Count (u ++ v) ≤ lz76Count u + lz76Count v + 1 := by
  have h := lz76Count_append u v
  omega

/-! ## Invariance par bijection d'alphabet (complement des bits)

Le complement point a point du bitstream est une bijection d'alphabet :
prefixes, occurrences et phrases se transportent exactement, donc le
compte LZ76 est invariant. C'est la premiere famille de symetrie de
l'instrument (la seconde, forme canonique sur l'orbite diedrale de la
boite, vit sur la serialisation elle-meme).
-/

section Complement

/-- Abreviation locale pour la negation point a point. -/
local notation "φ" => (fun b : Bool => !b)

theorem isPrefixB_map_not (v w : List Bool) :
    isPrefixB (v.map φ) (w.map φ) = isPrefixB v w := by
  induction v generalizing w with
  | nil => simp [isPrefixB]
  | cons a as ih =>
      cases w with
      | nil => simp [isPrefixB]
      | cons b bs =>
          simp only [isPrefixB, List.map_cons, Bool.and_eq_true, beq_iff_eq, ih]
          cases a <;> cases b <;> simp

theorem occursIn_map_not (v h : List Bool) :
    occursIn (v.map φ) (h.map φ) = occursIn v h := by
  induction h with
  | nil =>
      cases v <;> simp [occursIn]
  | cons b bs ih =>
      cases v with
      | nil => simp [occursIn]
      | cons a as =>
          show (isPrefixB ((a::as).map φ) ((b::bs).map φ)
              || occursIn ((a::as).map φ) (bs.map φ))
              = (isPrefixB (a::as) (b::bs) || occursIn (a::as) bs)
          rw [isPrefixB_map_not, ← ih]

theorem take_map_not (l : List Bool) : ∀ k, (l.take k).map φ = (l.map φ).take k := by
  intro k
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
      cases l with
      | nil => simp
      | cons a as => simp [ih as]

theorem drop_map_not (l : List Bool) : ∀ k, (l.drop k).map φ = (l.map φ).drop k := by
  intro k
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
      cases l with
      | nil => simp
      | cons a as => simp [ih as]

theorem phraseGo_map_not (r h : List Bool) : ∀ (fuel k : ℕ),
    phraseGo (r.map φ) (h.map φ) fuel k = phraseGo r h fuel k := by
  intro fuel
  induction fuel with
  | zero =>
      intro k
      simp only [phraseGo, List.length_map]
  | succ fuel ih =>
      intro k
      simp only [phraseGo, List.length_map]
      have hcond : occursIn ((r.map φ).take k) ((h.map φ) ++ (r.map φ).take (k - 1))
          = occursIn (r.take k) (h ++ r.take (k - 1)) := by
        rw [← take_map_not r k, ← take_map_not r (k - 1), ← List.map_append]
        exact occursIn_map_not _ _
      rw [hcond]
      by_cases hk : k ≤ r.length
      · rw [if_pos hk, if_pos hk]
        by_cases hc : occursIn (r.take k) (h ++ r.take (k - 1)) = true
        · rw [if_pos hc, if_pos hc, ih (k + 1)]
        · rw [if_neg hc, if_neg hc]
      · rw [if_neg hk, if_neg hk]

theorem countFromGo_map_not (s : List Bool) : ∀ (f i : ℕ),
    countFromGo (s.map φ) f i = countFromGo s f i := by
  intro f
  induction f with
  | zero => intro i; rfl
  | succ f ih =>
      intro i
      simp only [countFromGo, List.length_map]
      by_cases hi : i < s.length
      · rw [if_pos hi, if_pos hi]
        have hphr : phraseLenAt (s.map φ) i = phraseLenAt s i := by
          simp only [phraseLenAt]
          rw [← take_map_not s i, ← drop_map_not s i, List.length_map]
          exact phraseGo_map_not (s.drop i) (s.take i) (s.drop i).length 1
        rw [hphr, ih]
      · rw [if_neg hi, if_neg hi]

/-- **Invariance par complement d'alphabet** : neguer chaque bit ne change
pas la complexite LZ76. -/
theorem lz76Count_map_not (s : List Bool) :
    lz76Count (s.map φ) = lz76Count s := by
  have h1 := countFromGo_map_not s s.length 0
  simp only [lz76Count, countFrom, List.length_map]
  exact h1

end Complement

/-! ## Serialisation d'une trajectoire et perplexite fenetree

`serializeI N W t` : les W grilles de la trajectoire, chacune lue dans la
boite N×N d'origine en row-major, concatenees. Le niveau
`windowedPerplexity` divise par W·N² (bits par cellule et par generation).
-/

/-- Bit de la cellule (i, j) de la boite N×N d'origine. -/
def cellBit (g : Grid) (i j : Nat) : Bool := isAlive g ((i : Int), (j : Int))

/-- Boite N×N serialee en row-major. -/
def encodeBox (N : Nat) (g : Grid) : List Bool :=
  (List.range N).flatMap fun i => (List.range N).map fun j => cellBit g i j

/-- Trajectoire seriale : W grilles concatenees (recursion structurelle sur W). -/
def serializeI (N W : Nat) (t : Nat → Grid) : List Bool :=
  match W with
  | 0 => []
  | W + 1 => encodeBox N (t 0) ++ serializeI N W (fun k => t (k + 1))

theorem serializeI_zero : ∀ (W : Nat) (t : Nat → Grid), serializeI 0 W t = [] := by
  intro W
  induction W with
  | zero => intro t; rfl
  | succ W' ih =>
      intro t
      simp [serializeI, encodeBox, ih]

theorem serializeI_split (N : Nat) : ∀ (W₁ W₂ : Nat) (t : Nat → Grid),
    serializeI N (W₁ + W₂) t
      = serializeI N W₁ t ++ serializeI N W₂ (fun k => t (W₁ + k)) := by
  intro W₁
  induction W₁ with
  | zero =>
      intro W₂ t
      simp [serializeI]
  | succ W₁ ih =>
      intro W₂ t
      have e1 : W₁ + 1 + W₂ = (W₁ + W₂) + 1 := by omega
      have hshift : (fun k : Nat => (fun m => t (m + 1)) (W₁ + k))
          = fun k => t (W₁ + 1 + k) := by
        funext k
        simp only []
        congr 1
        omega
      simp only [e1, serializeI]
      rw [ih W₂ (fun m => t (m + 1)), hshift, List.append_assoc]

/-- **Convexite en W, forme comptage** : le compte LZ de la fenetre reunion
ne depasse pas la somme des comptes des sous-fenetres consecutives. -/
theorem lz76Count_serialize_split (N W₁ W₂ : Nat) (t : Nat → Grid) :
    lz76Count (serializeI N (W₁ + W₂) t)
      ≤ lz76Count (serializeI N W₁ t) + lz76Count (serializeI N W₂ (fun k => t (W₁ + k))) := by
  rw [serializeI_split N W₁ W₂ t]
  exact lz76Count_append _ _

/-- Perplexite fenetree π(t, W) = C_LZ(fenetre) / (W·N²), en bits par
cellule et par generation. Si W·N² = 0, la division rationnelle rend 0. -/
def windowedPerplexity (N W : Nat) (t : Nat → Grid) : ℚ :=
  (lz76Count (serializeI N W t) : ℚ) / (((W * N * N : ℕ) : ℚ))

theorem windowedPerplexity_mul_denom (N W : Nat) (t : Nat → Grid) :
    windowedPerplexity N W t * (((W * N * N : ℕ) : ℚ))
      = (lz76Count (serializeI N W t) : ℚ) := by
  unfold windowedPerplexity
  by_cases hz : (W * N * N : ℕ) = 0
  · have hs : serializeI N W t = [] := by
      cases W with
      | zero => rfl
      | succ W' =>
          cases N with
          | zero => exact serializeI_zero (W' + 1) t
          | succ N' => simp at hz
    rw [hz, hs]
    simp [lz76Count, countFrom, countFromGo]
  · exact div_mul_cancel₀ _ (by exact_mod_cast hz)

/-- **Convexite en W, forme echellee** : π(fenetre reunion) × W_reunion·N²
ne depasse pas la somme des π × denominateurs plus une constante de
frontiere. -/
theorem windowedPerplexity_union_le (N W₁ W₂ : Nat) (t : Nat → Grid) :
    windowedPerplexity N (W₁ + W₂) t * (((W₁ + W₂) * N * N : ℕ) : ℚ)
      ≤ windowedPerplexity N W₁ t * ((W₁ * N * N : ℕ) : ℚ)
        + windowedPerplexity N W₂ (fun k => t (W₁ + k)) * ((W₂ * N * N : ℕ) : ℚ)
        + 1 := by
  have hsplit := lz76Count_serialize_split N W₁ W₂ t
  rw [windowedPerplexity_mul_denom, windowedPerplexity_mul_denom,
      windowedPerplexity_mul_denom]
  have h1 : ((lz76Count (serializeI N (W₁ + W₂) t) : ℕ) : ℚ)
      ≤ (((lz76Count (serializeI N W₁ t) + lz76Count (serializeI N W₂
          (fun k => t (W₁ + k)))) : ℕ) : ℚ) := by
    exact_mod_cast hsplit
  push_cast at h1
  linarith

/-! ## Fenetres et evenement de maintien du niveau -/

/-- Fenetre de W generations consecutives de la trajectoire de `x₀`,
commencant a la generation `k`. -/
def window (W k : Nat) (x₀ : Grid) : Nat → Grid := fun i => evolve (k + i) x₀

/-- Evenement : la perplexite de chaque fenetre de la trajectoire de `x₀`
reste au-dessus du seuil τ sur l'horizon T. -/
def maintainsAbove (N W T : Nat) (τ : ℚ) (x₀ : Grid) : Prop :=
  ∀ k, k * W + W ≤ T → τ ≤ windowedPerplexity N W (window W k x₀)

/-! ## Temoins decides

Deux temoins par `decide` (evaluation par le noyau, jamais
`native_decide`) : la valeur exacte du compte LZ sur la fenetre glider
(croisee avec l'instrument Python `scripts/hashlife/k_trajectory.py` dans
`scripts/hashlife/tests/test_conway_lean_witness.py`), et le fait que le
Block, vie immobile, maintient son niveau constant.
-/

theorem evolve_block (n : Nat) : evolve n block = block := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [evolve_succ, ih]
      exact eq_of_beq block_still_life

theorem window_block (W k : Nat) : window W k block = fun _ => block := by
  funext i
  simp [window, evolve_block]

/-- Le Block maintient son niveau : la perplexite de chacune de ses
fenetres est la constante de la fenetre de reference. -/
theorem maintainsAbove_block (N W T : Nat) :
    maintainsAbove N W T (windowedPerplexity N W (window W 0 block)) block := by
  intro k _
  have hwin : window W k block = window W 0 block := by
    funext i
    simp [window, evolve_block]
  rw [hwin]

set_option maxRecDepth 1000000 in
/-- Valeur du compte LZ76 sur la fenetre glider (boite 8×8, W = 4) :
13 phrases pour 256 bits, decide par le noyau. Croisee avec
l'instrument Python (`scripts/hashlife/tests/test_conway_lean_witness.py`,
reimplementation independante du comptage sur le meme bitstream). -/
theorem witness_glider_lz76 :
    lz76Count (serializeI 8 4 (window 4 0 glider)) = 13 := by decide

/-- Perplexite fenetree de la fenetre glider : 13/256 bits par cellule et
par generation. -/
theorem witness_glider_perplexity :
    windowedPerplexity 8 4 (window 4 0 glider) = 13 / 256 := by
  rw [windowedPerplexity, witness_glider_lz76]
  norm_num

end Life
end Conway
