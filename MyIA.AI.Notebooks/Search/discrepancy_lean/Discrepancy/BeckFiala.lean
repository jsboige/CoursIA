import Discrepancy.Progress

/-!
# b4 — Terminaison et assemblage : le théorème classique de Beck-Fiala

Dernière boute du grignotage de `BeckFialaClassic` (`disc ≤ 2k−1`), voir
`FORMAL_STATUS.md`. L'algorithme de Beck-Fiala part de la coloration partielle
identiquement nulle (tous les éléments flottants, `|c x| < 1`) et exécute des
**phases** : tant qu'une ligne est dangereuse (`> k` flottants), b1 fournit
une direction de noyau `v` (les sommes des lignes dangereuses sont préservées
exactement), b3 avance jusqu'au premier contact avec la frontière du cube et
fige au moins un nouveau flottant en `±1`. Chaque phase fait décroître
strictement le nombre de flottants : la récursion est bien fondée sur `|X|`.
À l'arrêt, chaque ligne porte `≤ k` flottants et son **état d'abandon** est
enregistré ; l'arrondi final `±1` et l'invariant b2 (`frozen_line_sum_le`)
concluent `|∑ c| ≤ 2k−1` sur chaque ligne.

Contenu :

* `BFInv` — l'invariant complet de la coloration partielle : flottants
  strictement intérieurs, figés exactement en `±1`, lignes dangereuses de
  somme nulle, lignes abandonnées munies de leur état d'abandon `(c₀, Y)` ;
* `exists_phase` — une phase : décroissance stricte de `|X|` et préservation
  de l'invariant ;
* `exists_coloring_of_no_danger` — l'arrondi final lorsque plus aucune ligne
  n'est dangereuse (assemblage avec b2) ;
* `bf_loop` — terminaison par induction sur un majorant de `|X|` ;
* `beck_fiala_classic` — **le théorème classique** : toute famille de degré
  maximal `≤ k` (`k ≥ 1`) admet une coloration `±1` de discrépance `≤ 2k−1`.
-/

namespace Discrepancy

section Assembly

variable {α : Type*} [DecidableEq α]

/-- **b4 — invariant de boucle de Beck-Fiala.** Un état `(X, c, g)` : les
flottants `X` (strictement intérieurs), la coloration partielle rationnelle
`c`, et un registre `g` qui enregistre pour chaque ligne déjà abandonnée
l'état `c₀` et les flottants `Y` **au moment de l'abandon** — les données
exactes que l'invariant b2 consommera à l'arrondi final. L'algorithme part
de `X = univ` : tout élément hors des flottants est figé, exactement en
`±1`. -/
def BFInv (F : Finset (Finset α)) (k : ℕ) (X : Finset α) (c : α → ℚ)
    (g : Finset α → (α → ℚ) × Finset α) : Prop :=
  (∀ x ∈ X, |c x| < 1)
  ∧ (∀ x, x ∉ X → |c x| = 1)
  ∧ (∀ S ∈ F, k < (S ∩ X).card → ∑ x ∈ S, c x = 0)
  ∧ (∀ S ∈ F, (S ∩ X).card ≤ k →
      (g S).2 ⊆ S ∧ (g S).2.card ≤ k ∧ (∀ y ∈ (g S).2, |(g S).1 y| < 1)
        ∧ (∑ x ∈ S, (g S).1 x = 0)
        ∧ (∀ x ∈ S, x ∉ (g S).2 → x ∉ X ∧ c x = (g S).1 x))

/-- Arrondi final d'un état en coloration `±1` : les valeurs `≥ 1` (donc
exactement `1` pour les figés hauts) partent à `1`, les autres à `-1`. -/
private def finalColoring {α : Type*} (c : α → ℚ) : α → ℤ :=
  fun x => if 1 ≤ c x then 1 else -1

private theorem finalColoring_is_coloring {α : Type*} (c : α → ℚ) :
    IsColoring (finalColoring c) := by
  intro x
  by_cases h : 1 ≤ c x <;> simp [finalColoring, h]

private theorem finalColoring_eq {α : Type*} (c : α → ℚ) (x : α)
    (h : |c x| = 1) : ((finalColoring c x : ℤ) : ℚ) = c x := by
  by_cases hx : 0 ≤ c x
  · have habs : |c x| = c x := abs_of_nonneg hx
    rw [habs] at h
    simp [finalColoring, h]
  · have hxlt : c x < 0 := not_le.mp hx
    have habs : |c x| = -c x := abs_of_neg hxlt
    rw [habs] at h
    have hc : c x = -1 := by linarith
    simp [finalColoring, hc]

/-- **b4 — une phase de Beck-Fiala.** Depuis un état invariant comportant au
moins une ligne dangereuse, il existe un état suivant strictement plus proche
de l'arrêt (strictement moins de flottants) qui préserve l'invariant. -/
theorem exists_phase (F : Finset (Finset α)) (k : ℕ) (hdeg : ∀ x, degree F x ≤ k)
    (X : Finset α) (c : α → ℚ) (g : Finset α → (α → ℚ) × Finset α)
    (hinv : BFInv F k X c g) (hdang : ∃ S₀ ∈ F, k < (S₀ ∩ X).card) :
    ∃ X' : Finset α, ∃ c' : α → ℚ, ∃ g' : Finset α → (α → ℚ) × Finset α,
      X'.card < X.card ∧ BFInv F k X' c' g' := by
  classical
  obtain ⟨I1, I2, I3, I4⟩ := hinv
  obtain ⟨S₀, hS₀F, hS₀d⟩ := hdang
  -- Les flottants sont non vides : une ligne dangereuse en porte > k ≥ 0.
  have hXne : X.Nonempty := by
    have hpos : 0 < (S₀ ∩ X).card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    exact ⟨x, (Finset.mem_inter.mp hx).2⟩
  -- b1 : direction de noyau, tronquée au support flottant pour ne jamais
  -- déplacer un élément figé.
  obtain ⟨v, ⟨x₀, hx₀X, hx₀v⟩, hvker⟩ :=
    exists_dangerous_kernel_vec F X k hXne (fun x _ => hdeg x)
  set v' : α → ℚ := fun x => if x ∈ X then v x else 0 with hv'
  have hv'X : ∀ x ∈ X, v' x = v x := fun x hx => by
    rw [hv']; exact if_pos hx
  have hv'out : ∀ x, x ∉ X → v' x = 0 := fun x hx => by
    rw [hv']; exact if_neg hx
  have hv'ne : ∃ x₀ ∈ X, v' x₀ ≠ 0 :=
    ⟨x₀, hx₀X, by rw [hv'X x₀ hx₀X]; exact hx₀v⟩
  have hv'ker : ∀ S ∈ F.filter (fun S => k < (S ∩ X).card),
      ∑ x ∈ X, (if x ∈ S then (1 : ℚ) else 0) * v' x = 0 := by
    intro S hS
    calc ∑ x ∈ X, (if x ∈ S then (1 : ℚ) else 0) * v' x
        = ∑ x ∈ X, (if x ∈ S then (1 : ℚ) else 0) * v x :=
          Finset.sum_congr rfl fun x hx => by rw [hv'X x hx]
      _ = 0 := hvker S hS
  -- b3 : le pas de la phase — premier contact avec la frontière du cube.
  obtain ⟨t, _htpos, htcube, hthit⟩ := exists_step_hits_boundary c v' X hXne I1 hv'ne
  set c' : α → ℚ := fun x => c x + t * v' x with hc'
  have htcube' : ∀ x ∈ X, |c' x| ≤ 1 := by
    rw [hc']; exact htcube
  set X' : Finset α := X.filter (fun x => |c' x| < 1) with hX'
  have hX'sub : X' ⊆ X := Finset.filter_subset _ _
  -- Décroissance stricte : le contact fige au moins un flottant.
  obtain ⟨x₁, hx₁X, hx₁hit⟩ := hthit
  have hx₁out : x₁ ∉ X' := by
    intro hmem
    have hlt : |c' x₁| < 1 := (Finset.mem_filter.mp hmem).2
    rw [hc'] at hlt
    simp only [] at hlt
    linarith
  -- Somme d'une ligne dangereuse après le pas : préservée exactement (noyau).
  have hsumpres : ∀ S ∈ F, k < (S ∩ X).card → ∑ x ∈ S, c' x = 0 := by
    intro S hSF hd
    have hker := hv'ker S (Finset.mem_filter.mpr ⟨hSF, hd⟩)
    -- Le noyau, relu comme une somme sur les flottants de la ligne.
    have hker2 : ∑ x ∈ S ∩ X, v' x = 0 := by
      have hstep : ∑ x ∈ S ∩ X, (if x ∈ S then v' x else 0)
          = ∑ x ∈ X, (if x ∈ S then v' x else 0) :=
        Finset.sum_subset (Finset.inter_subset_right)
          (fun x hxX hxno => by
            have hxS : x ∉ S := fun h => hxno (Finset.mem_inter.mpr ⟨h, hxX⟩)
            simp [hxS])
      calc ∑ x ∈ S ∩ X, v' x
          = ∑ x ∈ S ∩ X, (if x ∈ S then v' x else 0) :=
            Finset.sum_congr rfl fun x hx => by
              have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
              simp [hxS]
        _ = ∑ x ∈ X, (if x ∈ S then v' x else 0) := hstep
        _ = ∑ x ∈ X, (if x ∈ S then (1 : ℚ) else 0) * v' x :=
            Finset.sum_congr rfl fun x _ => by
              by_cases hxS : x ∈ S <;> simp [hxS]
        _ = 0 := hker
    -- Découpage de la somme déplacée.
    have hrestrict : ∑ x ∈ S, v' x = ∑ x ∈ S ∩ X, v' x :=
      (Finset.sum_subset (Finset.inter_subset_left)
        (fun x hxS hxno => by
          rw [hv'out x (fun hX => hxno (Finset.mem_inter.mpr ⟨hxS, hX⟩))])).symm
    calc ∑ x ∈ S, c' x = ∑ x ∈ S, (c x + t * v' x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hc']
        _ = (∑ x ∈ S, c x) + ∑ x ∈ S, t * v' x := Finset.sum_add_distrib
        _ = (∑ x ∈ S, c x) + t * ∑ x ∈ S, v' x := by rw [Finset.mul_sum]
        _ = (∑ x ∈ S, c x) + t * ∑ x ∈ S ∩ X, v' x := by
              congr 1
              rw [hrestrict]
        _ = 0 := by rw [hker2, I3 S hSF hd, mul_zero, add_zero]
  -- Invariant au nouvel état.
  have I1' : ∀ x ∈ X', |c' x| < 1 := fun x hx => (Finset.mem_filter.mp hx).2
  have I2' : ∀ x, x ∉ X' → |c' x| = 1 := by
    intro x hxout
    by_cases hxX : x ∈ X
    · rcases eq_or_lt_of_le (htcube' x hxX) with h | h
      · exact h
      · exact absurd (Finset.mem_filter.mpr ⟨hxX, h⟩) hxout
    · have hc1 : |c x| = 1 := I2 x hxX
      have hc'x : c' x = c x := by
        calc c' x = c x + t * v' x := by rw [hc']
          _ = c x + t * 0 := by rw [hv'out x hxX]
          _ = c x := by ring
      rw [hc'x]
      exact hc1
  have I3' : ∀ S ∈ F, k < (S ∩ X').card → ∑ x ∈ S, c' x = 0 := by
    intro S hSF hd'
    have hle : (S ∩ X').card ≤ (S ∩ X).card :=
      Finset.card_mono (Finset.inter_subset_inter_left hX'sub)
    exact hsumpres S hSF (by omega)
  set g' : Finset α → (α → ℚ) × Finset α :=
    fun S => if k < (S ∩ X).card then (c', S ∩ X') else g S with hg'
  have I4' : ∀ S ∈ F, (S ∩ X').card ≤ k →
      (g' S).2 ⊆ S ∧ (g' S).2.card ≤ k ∧ (∀ y ∈ (g' S).2, |(g' S).1 y| < 1)
        ∧ (∑ x ∈ S, (g' S).1 x = 0)
        ∧ (∀ x ∈ S, x ∉ (g' S).2 → x ∉ X' ∧ c' x = (g' S).1 x) := by
    intro S hSF hle
    by_cases hd : k < (S ∩ X).card
    · -- La ligne abandonne pendant cette phase : on enregistre (c', S ∩ X').
      have hg'eq : g' S = (c', S ∩ X') := by
        rw [hg']
        exact if_pos hd
      rw [hg'eq]
      refine ⟨Finset.inter_subset_left, hle, ?_, hsumpres S hSF hd, ?_⟩
      · intro y hy
        exact (Finset.mem_filter.mp (Finset.mem_of_mem_inter_right hy)).2
      · intro x hxS hxout
        exact ⟨fun hX' => hxout (Finset.mem_inter.mpr ⟨hxS, hX'⟩), rfl⟩
    · -- Ligne déjà abandonnée (ou jamais dangereuse) : registre inchangé.
      have hg'eq : g' S = g S := by
        rw [hg']
        exact if_neg hd
      rw [hg'eq]
      obtain ⟨h1, h2, h3, h4, h5⟩ := I4 S hSF (by omega)
      refine ⟨h1, h2, h3, h4, ?_⟩
      intro x hxS hxout
      obtain ⟨hxX, hcx⟩ := h5 x hxS hxout
      refine ⟨fun hX' => hxX (hX'sub hX'), ?_⟩
      calc c' x = c x + t * v' x := by rw [hc']
        _ = c x + t * 0 := by rw [hv'out x hxX]
        _ = c x := by ring
        _ = (g S).1 x := hcx
  have hcard : X'.card < X.card := by
    have hins : insert x₁ X' ⊆ X := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact hx₁X
      · exact hX'sub hy'
    have h3 : (insert x₁ X').card = X'.card + 1 :=
      Finset.card_insert_of_notMem hx₁out
    have h4 : X'.card + 1 ≤ X.card := by
      rw [← h3]
      exact Finset.card_mono hins
    omega
  exact ⟨X', c', g', hcard, ⟨I1', I2', I3', I4'⟩⟩

/-- **b4 — l'arrondi final.** Lorsque plus aucune ligne n'est dangereuse,
l'arrondi `±1` de l'état courant vérifie la borne `2k−1` sur chaque ligne :
l'invariant b2 s'applique à chaque ligne avec son état d'abandon enregistré. -/
theorem exists_coloring_of_no_danger (F : Finset (Finset α)) (k : ℕ)
    (X : Finset α) (c : α → ℚ) (g : Finset α → (α → ℚ) × Finset α)
    (hinv : BFInv F k X c g) (hnone : ∀ S ∈ F, (S ∩ X).card ≤ k) :
    ∃ c_f : α → ℤ, IsColoring c_f ∧
      ∀ S ∈ F, (∑ x ∈ S, c_f x).natAbs ≤ 2 * k - 1 := by
  obtain ⟨_I1, I2, _I3, I4⟩ := hinv
  refine ⟨finalColoring c, finalColoring_is_coloring c, ?_⟩
  intro S hSF
  obtain ⟨h1, h2, h3, h4, h5⟩ := I4 S hSF (hnone S hSF)
  refine frozen_line_sum_le (g S).1 (finalColoring c) (g S).2 S k h1 h2
    (finalColoring_is_coloring c) h3 h4 ?_
  intro x hxS hxout
  obtain ⟨hxX, hcx⟩ := h5 x hxS hxout
  rw [finalColoring_eq c x (I2 x hxX)]
  exact hcx

/-- **b4 — terminaison.** Par induction sur un majorant du nombre de
flottants : chaque phase en consomme au moins un, l'algorithme s'arrête et
produit une coloration `±1` bornée par `2k−1` sur chaque ligne. -/
theorem bf_loop (F : Finset (Finset α)) (k : ℕ) (hdeg : ∀ x, degree F x ≤ k) :
    ∀ (n : ℕ) (X : Finset α) (c : α → ℚ) (g : Finset α → (α → ℚ) × Finset α),
      X.card ≤ n → BFInv F k X c g →
      ∃ c_f : α → ℤ, IsColoring c_f ∧
        ∀ S ∈ F, (∑ x ∈ S, c_f x).natAbs ≤ 2 * k - 1 := by
  intro n
  induction n with
  | zero =>
    intro X c g hcard hinv
    refine exists_coloring_of_no_danger F k X c g hinv ?_
    intro S _hSF
    have h1 : (S ∩ X).card ≤ X.card :=
      Finset.card_le_card (Finset.inter_subset_right)
    omega
  | succ n ih =>
    intro X c g hcard hinv
    by_cases hdang : ∃ S₀ ∈ F, k < (S₀ ∩ X).card
    · obtain ⟨X', c', g', hlt, hinv'⟩ := exists_phase F k hdeg X c g hinv hdang
      exact ih X' c' g' (by omega) hinv'
    · refine exists_coloring_of_no_danger F k X c g hinv ?_
      intro S hSF
      by_contra hlt
      exact hdang ⟨S, hSF, not_le.mp hlt⟩

/-- **b4 — le théorème classique de Beck-Fiala.** Toute famille `F` de
parties d'un type fini, de degré maximal `≤ k` (avec `k ≥ 1`), admet une
coloration `±1` dont la discrépance est au plus `2k−1`.

C'est l'assemblage final des boutes b1 (noyau dimensionnel), b3 (progrès) et
b2 (invariant de ligne figée) : l'algorithme à variables flottantes, sa
terminaison par décroissance stricte du nombre de flottants, et l'arrondi
final. L'énoncé `BeckFialaClassic` de `Discrepancy.Basic` devient un
théorème. -/
theorem beck_fiala_classic : BeckFialaClassic := by
  intro n k F hk _hk1
  classical
  have hdeg : ∀ x : Fin n, degree F x ≤ k := fun x =>
    (Finset.le_sup (Finset.mem_univ x)).trans hk
  -- État initial : tous les éléments flottants à `0`, registre des lignes
  -- jamais dangereuses pointant sur l'état nul.
  have hinv0 : BFInv F k (Finset.univ) (fun _ => (0 : ℚ))
      (fun S => ((fun _ => (0 : ℚ)), S)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x _; norm_num
    · intro x hxout; exact absurd (Finset.mem_univ x) hxout
    · intro S _hd; simp
    · intro S _hSF hle
      rw [Finset.inter_univ] at hle
      refine ⟨fun _ hx => hx, hle, fun y _ => by norm_num, by simp, ?_⟩
      intro x hxS hxout; exact absurd hxS hxout
  obtain ⟨c_f, hcolor, hsum⟩ :=
    bf_loop (α := Fin n) F k hdeg (Finset.univ).card (Finset.univ)
      (fun _ => (0 : ℚ)) (fun S => ((fun _ => (0 : ℚ)), S))
      (Nat.le_refl _) hinv0
  refine ⟨c_f, hcolor, ?_⟩
  have hsup : (F.image fun S => (S.sum c_f).natAbs).sup id ≤ 2 * k - 1 :=
    Finset.sup_le fun b hb => by
      obtain ⟨S, hSF, rfl⟩ := Finset.mem_image.mp hb
      exact hsum S hSF
  have hnle : discrepancy F c_f ≤ 2 * k - 1 := by
    unfold discrepancy
    exact hsup
  have h21 : (1 : ℕ) ≤ 2 * k := by omega
  have hcast : ((2 * k - 1 : ℕ) : ℤ) = 2 * (k : ℤ) - 1 := by
    rw [Nat.cast_sub h21]; push_cast; ring
  have hfin : ((discrepancy F c_f : ℕ) : ℤ) ≤ ((2 * k - 1 : ℕ) : ℤ) := by
    exact_mod_cast hnle
  rw [hcast] at hfin
  exact hfin

end Assembly

end Discrepancy
