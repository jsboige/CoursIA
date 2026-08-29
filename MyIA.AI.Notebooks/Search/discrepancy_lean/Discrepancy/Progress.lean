import Discrepancy.Partial

/-!
# b3 — Lemme de progrès

Troisième boute du grignotage de `BeckFialaClassic` (`disc ≤ 2k−1`), voir
`FORMAL_STATUS.md`. Une phase de Beck-Fiala part de l'état partiel `c₀`
(flottants strictement intérieurs), suit la direction de noyau `v` fournie
par b1 (non triviale sur les flottants), et s'arrête au **premier contact**
avec la frontière du cube `[-1,1]` : le pas `t` est le minimum des temps de
contact des directions actives. À l'arrivée, au moins un flottant vérifie
`|c₀ x + t * v x| = 1` : c'est lui que la phase fige. Aucun flottant ne
sort du cube fermé.

Contenu :

* `hitTime` — le temps de premier contact d'une direction `d ≠ 0` partant
  d'un point strictement intérieur ;
* `abs_le_one_of_le_hitTime` / `abs_eq_one_of_hitTime` — les bornes 1-D :
  rester avant le contact maintient dans le cube, le contact atteint `±1` ;
* `exists_step_hits_boundary` — **b3** : le pas minimal existe, est
  strictement positif, garde tout le monde dans le cube et fige au moins un
  flottant.

L'assemblage avec l'invariant b2 et la terminaison (b4) conclut
`BeckFialaClassic`.
-/

namespace Discrepancy

section Progress

variable {α : Type*} [DecidableEq α]

/-- Temps de premier contact : partant de `a` strictement intérieur à
`[-1, 1]`, le pas positif auquel `a + t * d` atteint la frontière `±1` en
suivant la direction `d ≠ 0`. -/
def hitTime (a d : ℚ) : ℚ :=
  if 0 < d then (1 - a) / d else (-1 - a) / d

/-- Le temps de contact d'une direction non nulle partant de l'intérieur est
strictement positif. -/
private theorem hitTime_pos (a d : ℚ) (ha : |a| < 1) (hd : d ≠ 0) :
    0 < hitTime a d := by
  rcases lt_or_gt_of_ne hd with hdn | hdp
  · rw [hitTime, if_neg (by linarith : ¬ 0 < d)]
    have hnum : (-1 - a) / d > 0 := by
      apply div_pos_of_neg_of_neg
      · linarith [abs_lt.mp ha]
      · linarith
    exact hnum
  · rw [hitTime, if_pos hdp]
    apply div_pos _ hdp
    linarith [abs_lt.mp ha]

/-- Avant le contact, on reste dans le cube fermé : si `|a| < 1`, `d ≠ 0`,
`0 ≤ t` et `t ≤ hitTime a d`, alors `|a + t * d| ≤ 1`. -/
theorem abs_le_one_of_le_hitTime (a d t : ℚ) (ha : |a| < 1) (hd : d ≠ 0)
    (ht : 0 ≤ t) (htle : t ≤ hitTime a d) : |a + t * d| ≤ 1 := by
  have hbounds := abs_lt.mp ha
  rcases lt_or_gt_of_ne hd with hdn | hdp
  · rw [hitTime, if_neg (by linarith : ¬ 0 < d)] at htle
    have hd' : d ≠ 0 := by linarith
    have htd : (-1 - a) ≤ t * d := by
      have h1 := mul_le_mul_of_nonpos_right htle (le_of_lt hdn)
      rwa [div_mul_cancel₀ _ hd'] at h1
    rw [abs_le]
    constructor
    · linarith
    · have hnp : t * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hdn.le
      linarith
  · rw [hitTime, if_pos hdp] at htle
    have hd' : d ≠ 0 := by linarith
    have htd : t * d ≤ 1 - a := by
      have h1 := mul_le_mul_of_nonneg_right htle (le_of_lt hdp)
      rwa [div_mul_cancel₀ _ hd'] at h1
    rw [abs_le]
    constructor
    · have hnn : 0 ≤ t * d := mul_nonneg ht hdp.le
      linarith
    · linarith

/-- Au contact exactement, on atteint la frontière :
`|a + hitTime a d * d| = 1`. -/
theorem abs_eq_one_of_hitTime (a d : ℚ) (hd : d ≠ 0) :
    |a + hitTime a d * d| = 1 := by
  rcases lt_or_gt_of_ne hd with hdn | hdp
  · rw [hitTime, if_neg (by linarith : ¬ 0 < d)]
    have hd' : d ≠ 0 := by linarith
    rw [div_mul_cancel₀ _ hd']
    simp
  · rw [hitTime, if_pos hdp]
    have hd' : d ≠ 0 := by linarith
    rw [div_mul_cancel₀ _ hd']
    simp

/-- **b3 — le progrès d'une phase.** Depuis un état partiel `c₀` à flottants
strictement intérieurs sur `X` non vide, le long d'une direction `v` non
triviale sur `X`, il existe un pas `t > 0` tel que l'état intermédiaire
`c₀ + t • v` reste dans le cube fermé `|·| ≤ 1` sur `X` et atteint la
frontière : au moins un flottant vérifie `|c₀ x + t * v x| = 1`. C'est ce
flottant que la phase fige — chaque phase fait strictement progresser la
coloration partielle. -/
theorem exists_step_hits_boundary (c₀ v : α → ℚ) (X : Finset α)
    (_hX : X.Nonempty) (hinterior : ∀ x ∈ X, |c₀ x| < 1)
    (hv : ∃ x₀ ∈ X, v x₀ ≠ 0) :
    ∃ t : ℚ, 0 < t ∧ (∀ x ∈ X, |c₀ x + t * v x| ≤ 1)
      ∧ ∃ x₁ ∈ X, |c₀ x₁ + t * v x₁| = 1 := by
  classical
  -- Les flottants que la direction déplace réellement.
  obtain ⟨x₀, hx₀X, hx₀v⟩ := hv
  set A := X.filter (fun x => v x ≠ 0) with hA
  have hxA : x₀ ∈ A := Finset.mem_filter.mpr ⟨hx₀X, hx₀v⟩
  have hAne : A.Nonempty := ⟨x₀, hxA⟩
  -- Le pas de la phase : le premier temps de contact parmi les actifs.
  set T := A.image (fun x => hitTime (c₀ x) (v x)) with hT
  have hTne : T.Nonempty :=
    ⟨hitTime (c₀ x₀) (v x₀), Finset.mem_image.mpr ⟨x₀, hxA, rfl⟩⟩
  set t := T.min' hTne with ht
  -- Positivité : tous les temps de contact sont > 0, et t en est un.
  have hTpos : ∀ q ∈ T, 0 < q := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    exact hitTime_pos (c₀ x) (v x) (hinterior x (Finset.mem_filter.mp hx).1)
      (Finset.mem_filter.mp hx).2
  have htpos : 0 < t := hTpos t (ht ▸ Finset.min'_mem T hTne)
  refine ⟨t, htpos, ?_, ?_⟩
  · -- Aucun flottant ne sort du cube fermé.
    intro x hxX
    by_cases hxv : v x = 0
    · rw [hxv, mul_zero, add_zero]
      exact le_of_lt (hinterior x hxX)
    · have hxA' : x ∈ A := Finset.mem_filter.mpr ⟨hxX, hxv⟩
      have hxT : hitTime (c₀ x) (v x) ∈ T :=
        Finset.mem_image.mpr ⟨x, hxA', rfl⟩
      exact abs_le_one_of_le_hitTime (c₀ x) (v x) t (hinterior x hxX) hxv
        (le_of_lt htpos) (Finset.min'_le T _ hxT)
  · -- Le premier contact fige au moins un flottant.
    obtain ⟨x₁, hx₁A, heq⟩ := Finset.mem_image.mp (ht ▸ Finset.min'_mem T hTne)
    have hx₁X : x₁ ∈ X := (Finset.mem_filter.mp hx₁A).1
    refine ⟨x₁, hx₁X, ?_⟩
    have := abs_eq_one_of_hitTime (c₀ x₁) (v x₁) (Finset.mem_filter.mp hx₁A).2
    rwa [heq] at this

end Progress

end Discrepancy
