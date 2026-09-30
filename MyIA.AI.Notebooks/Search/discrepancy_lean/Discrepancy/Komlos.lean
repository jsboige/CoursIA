import Discrepancy.Basic

/-!
# Komlós et Bansal–Jiang : colonnes unitaires et régime grand degré

Deuxième volet du lake `discrepancy_lean` (issue #12823) : les énoncés de la
frontière SOTA, en la forme exacte de la conjecture de **Komlós** (matrices
à colonnes unitaires, bornée `O(1)` conjecturée) et les formes du papier
**Bansal–Jiang 2025** (arXiv:2508.03961, « Decoupling via Affine
Spectral-Independence: Beck-Fiala and Komlós Bounds Beyond Banaszczyk ») :

- régime grand degré : la conjecture de Beck–Fiala vaut dès `k ≥ (log n)²` ;
- Komlós en `Õ(log^(1/4) n)`, au-delà du `O(√(log n))` de Banaszczyk.

Honnêteté documentée : ces théorèmes exigent un étage absent de Mathlib
(SDP + dualité, indépendance spectrale affine, mouvement brownien discret
guidé, concentration matricielle). Les énoncés vivent donc en `Prop` nommées
**dès maintenant** ; les preuves attendront l'étage amont (P3 = aspiration
documentée, jamais promesse). Pour la forme Komlós du papier, on énonce une
**version affaiblie concrète** (`C * (log n)²`), vraie dès que le théorème
du papier l'est — les exposants polylog exacts du `Õ` ne sont pas pretended.

Les sommes sont écrites à la main (`∑ i, A i j * c j`) plutôt qu'avec
`Matrix.mulVec` : la colonne-ligne reste lisible comme une somme de produits,
au plus près des définitions papier.
-/

namespace Discrepancy

/-- **Conjecture de Komlós** : il existe une constante universelle `C` telle
que toute matrice `A` à `n` colonnes **unitaires** (`∑ i, A i j ^ 2 = 1`)
admet une coloration `±1` des colonnes dont chaque somme de ligne reste
bornée par `C` en valeur absolue.

Le théorème de Banaszczyk (1998) donne `O(√(log n))` ; la conjecture exige
`O(1)`. En 2026, le preprint arXiv:2609.11189 (Guo–Fang–Lu, 10/09/2026)
annonce la résolution : la somme signée est de norme `ℓ∞` **inférieure à**
`3√(2π) ≈ 7,52`, indépendamment de la dimension et du nombre de colonnes.

Ce preprint n'est **pas encore revu par les pairs**. L'énoncé ci-dessus reste
un `Prop` nommé — aucune preuve formelle n'est engagée. Noter qu'il est posé
sur `ℚ` avec `C : ℚ` alors que la borne du papier est **réelle** : tout
alignement futur devra choisir explicitement un témoin rationnel (`8`
convient). -/
def KomlosConjecture : Prop :=
  ∃ C : ℚ, ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
    (∀ j : Fin n, ∑ i, A i j * A i j = 1) →
      ∃ c : Fin n → ℚ,
        (∀ j : Fin n, c j = 1 ∨ c j = -1) ∧ ∀ i : Fin m, |∑ j, A i j * c j| ≤ C

/-- **Bansal–Jiang 2025, régime grand degré** (arXiv:2508.03961,
théorème 1) : la conjecture de Beck–Fiala vaut dès que le degré domine le
carré du logarithme, `k ≥ (log₂ n)²` — avec la même conclusion `O(√k)` à
constante universelle. Résout la conjecture de Beck–Fiala pour `k ≥ log² n`. -/
def BansalJiangLargeDegree : Prop :=
  ∃ C : ℕ,
    ∀ (n k : ℕ) (F : Finset (Finset (Fin n))) (_hk : maxDegree F ≤ k)
      (_hlog : (Nat.log 2 n) ^ 2 ≤ k),
      ∃ c : Fin n → ℤ, IsColoring c ∧ discrepancy F c ≤ C * Nat.sqrt k

/-- **Komlós, forme affaiblie concrète d'après Bansal–Jiang 2025** : pour
les matrices à colonnes unitaires, une coloration `±1` borne chaque somme de
ligne par `C * (log₂ n)²`.

Le papier prouve `Õ(log^(1/4) n)` — plus fort. Un exposant polylog
conservateur (ici `2`) donne un énoncé **impliqué** par le théorème du
papier, donc vrai dès que le papier l'est, tout en restant au-delà de
l'objectif Banaszczyk en petites puissances. C'est la frontière SOTA telle
que le dépôt peut l'énoncer honnêtement sans l'étage SDP. -/
def KomlosBansalJiangWeak : Prop :=
  ∃ C : ℚ,
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
      (∀ j : Fin n, ∑ i, A i j * A i j = 1) →
        ∃ c : Fin n → ℚ,
          (∀ j : Fin n, c j = 1 ∨ c j = -1) ∧
            ∀ i : Fin m, |∑ j, A i j * c j| ≤ C * ((Nat.log 2 n : ℚ) ^ 2)

/-! ## Probe de réduction Komlós ⇒ Beck–Fiala (cas régulier)

Fragment formalisable **sans étage analytique** de la réduction nommée par le
verdict de #15944 (§2b, « le premier probe à tenter avant d'écrire une ligne
de preuve »). -/

/-- **Réduction de Komlós vers Beck–Fiala, cas régulier** (probe #15944) :
tout oracle de Komlós **réel** — matrices à colonnes unitaires, sommes de
lignes majorées par `C` — implique la conclusion de Beck–Fiala pour les
familles **régulières** (chaque élément appartient à exactement `k` parties),
à constante au plus doublée `2 * ⌈C⌉₊`.

Le scaling uniforme `1 / √k` est licite précisément parce que les degrés
sont tous égaux : chaque colonne de la matrice d'incidence porte exactement
`k` uns, donc norme `√k`, et la division par `√k` la rend unitaire. La
coloration de l'oracle donne alors `|∑_{j ∈ S} c j| ≤ C * √k` partie par
partie ; la conversion vers la forme entière (`Nat.sqrt`, constante
naturelle) coûte le facteur `2` via `√k ≤ Nat.sqrt k + 1`.

Deux limites, mesurées et documentées dans `FORMAL_STATUS.md` : le cas
général (degrés hétérogènes) ne se factorise pas — la réduction connue
exige la coloration partielle itérée ; et l'énoncé `ℚ` de
`KomlosConjecture` ci-dessus ne suffit pas comme oracle, le scaling
`1 / √k` étant irrationnel — la forme réelle est le bon pont. -/
theorem komlos_oracle_imp_beck_fiala_regular
    (C : ℝ) (hC : 0 ≤ C)
    (oracle : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
      (∀ j : Fin n, ∑ i, A i j * A i j = 1) →
        ∃ c : Fin n → ℝ, (∀ j : Fin n, c j = 1 ∨ c j = -1) ∧
          ∀ i : Fin m, |∑ j, A i j * c j| ≤ C) :
    ∀ (n k : ℕ), 1 ≤ k → ∀ F : Finset (Finset (Fin n)),
      (∀ j : Fin n, degree F j = k) →
      ∃ c : Fin n → ℤ, IsColoring c ∧
        discrepancy F c ≤ 2 * ⌈C⌉₊ * Nat.sqrt k := by
  intro n k hk F hreg
  classical
  have h0k : 0 < k := by omega
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast h0k
  have hknz : (k : ℝ) ≠ 0 := ne_of_gt hk0
  have hskne : Real.sqrt (k : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hk0
  have hss : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) :=
    Real.mul_self_sqrt hk0.le
  -- Énumération des parties de la famille
  obtain ⟨e⟩ : Nonempty (Fin F.card ≃ ({x // x ∈ F} : Type)) := ⟨F.equivFin.symm⟩
  have hemem : ∀ i : Fin F.card, (e i : Finset (Fin n)) ∈ F := fun i => (e i).2
  -- Le comptage clef : colonnes de la matrice d'incidence = degrés
  have hcount : ∀ j : Fin n,
      (Finset.univ.filter fun i => j ∈ (e i : Finset (Fin n))).card = degree F j := by
    intro j
    rw [degree]
    refine Finset.card_nbij (fun i : Fin F.card => (e i : Finset (Fin n))) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter] at hi ⊢
      exact ⟨hemem i, hi.2⟩
    · intro a _ b _ hab
      exact e.injective (Subtype.ext hab)
    · intro S hS
      simp only [Finset.mem_coe, Finset.mem_filter] at hS
      refine ⟨e.symm ⟨S, hS.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.apply_symm_apply]
        exact hS.2
      · simp
  -- Somme d'indicatrices = cardinal filtré
  have hsumind : ∀ j : Fin n,
      ∑ i ∈ Finset.univ, (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
        = (degree F j : ℝ) := by
    intro j
    have hn : ∑ i ∈ Finset.univ, (if j ∈ (e i : Finset (Fin n)) then (1 : ℕ) else 0)
        = degree F j := by
      rw [← Finset.sum_filter]
      exact (Finset.card_eq_sum_ones _).symm.trans (hcount j)
    exact_mod_cast hn
  -- Les colonnes de la matrice scalée sont unitaires
  have hunit : ∀ j : Fin n, ∑ i,
      ((Matrix.of fun i j =>
          (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0) / Real.sqrt (k : ℝ))
        : Matrix (Fin F.card) (Fin n) ℝ) i j
      * ((Matrix.of fun i j =>
          (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0) / Real.sqrt (k : ℝ))
        : Matrix (Fin F.card) (Fin n) ℝ) i j = 1 := by
    intro j
    simp only [Matrix.of_apply]
    have hterm : ∀ i : Fin F.card,
        ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0) / Real.sqrt (k : ℝ))
          * ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0) / Real.sqrt (k : ℝ))
        = ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
            * (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)) / (k : ℝ) := by
      intro i
      rw [div_mul_div_comm, hss]
    have hindsq : ∀ i : Fin F.card,
        ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
          * (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0))
        = if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0 := by
      intro i
      by_cases h : j ∈ (e i : Finset (Fin n)) <;> simp [h]
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_div,
      Finset.sum_congr rfl fun i _ => hindsq i,
      hsumind j, hreg j, div_self hknz]
  -- L'oracle, appliqué à la matrice d'incidence scalée
  obtain ⟨d, hdpm, hdbound⟩ :=
    oracle F.card n
      (Matrix.of fun i j =>
        (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0) / Real.sqrt (k : ℝ)) hunit
  · refine ⟨fun j => if d j = 1 then (1 : ℤ) else -1, ?_, ?_⟩
    · intro j
      rcases hdpm j with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by
          have hn : ¬((-1 : ℝ) = 1) := by norm_num
          simp only [h, if_neg hn])
    · rw [discrepancy]
      apply Finset.sup_le
      intro S' hS'
      obtain ⟨S, hSF, rfl⟩ := Finset.mem_image.mp hS'
      have hrei : (e (e.symm ⟨S, hSF⟩) : Finset (Fin n)) = S := by simp
      set i := e.symm ⟨S, hSF⟩ with hi
      -- Somme colorée réelle de la partie S
      have hreal : (((∑ j ∈ S, (if d j = 1 then (1 : ℤ) else -1) : ℤ)) : ℝ)
          = ∑ j ∈ S, d j := by
        rw [Int.cast_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rcases hdpm j with h | h
        · simp [h]
        · have hn : ¬((-1 : ℝ) = 1) := by norm_num
          simp only [h, if_neg hn, Int.cast_neg, Int.cast_one]
      -- Elle facteurise via la ligne i de la matrice scalée
      have hroweq : (∑ j : Fin n,
            ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
              / Real.sqrt (k : ℝ)) * d j)
          = (∑ j ∈ S, d j) / Real.sqrt (k : ℝ) := by
        have hterm2 : ∀ j : Fin n,
            ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
              / Real.sqrt (k : ℝ)) * d j
            = (if j ∈ S then d j else 0) / Real.sqrt (k : ℝ) := by
          intro j
          rw [show (e i : Finset (Fin n)) = S from hrei]
          by_cases hj : j ∈ S
          · rw [if_pos hj, if_pos hj, div_mul_eq_mul_div, one_mul]
          · simp [hj]
        rw [Finset.sum_congr rfl fun j _ => hterm2 j, ← Finset.sum_div]
        have hinner : (∑ j : Fin n, (if j ∈ S then d j else 0)) = ∑ j ∈ S, d j := by
          rw [← Finset.sum_subset (Finset.subset_univ S) fun j _ hj => if_neg hj]
          exact Finset.sum_congr rfl fun j hj => if_pos hj
        exact congrArg (· / Real.sqrt (k : ℝ)) hinner
      have horacle : |(∑ j : Fin n,
            ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
              / Real.sqrt (k : ℝ)) * d j)|
          ≤ C := by
        have h := hdbound i
        simpa only [Matrix.of_apply] using h
      rw [hroweq] at horacle
      have hsqrtC : |(∑ j ∈ S, d j : ℝ)| ≤ C * Real.sqrt (k : ℝ) := by
        have hmul : |(∑ j ∈ S, d j : ℝ)|
            = |(∑ j ∈ S, d j : ℝ) / Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ)| := by
          rw [div_mul_cancel₀ _ hskne]
        rw [hmul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_mul_of_nonneg_right horacle (Real.sqrt_nonneg _)
      -- Conversion vers la forme entière
      have hceil : C ≤ ((⌈C⌉₊ : ℕ) : ℝ) := Nat.le_ceil C
      have hs1 : (1 : ℝ) ≤ ((Nat.sqrt k : ℕ) : ℝ) := by
        have h11 : 1 * 1 ≤ k := by simpa using hk
        exact_mod_cast Nat.le_sqrt.mpr h11
      have hs2 : Real.sqrt (k : ℝ) ≤ ((Nat.sqrt k : ℕ) : ℝ) + 1 := by
        have h1 : ((Nat.sqrt k : ℕ) : ℝ) * ((Nat.sqrt k : ℕ) : ℝ) ≤ (k : ℝ) :=
          by exact_mod_cast Nat.sqrt_le k
        have h2 : (k : ℝ) < (((Nat.sqrt k : ℕ) + 1 : ℕ) : ℝ)
            * (((Nat.sqrt k : ℕ) + 1 : ℕ) : ℝ) :=
          by exact_mod_cast Nat.lt_succ_sqrt k
        have h3 : Real.sqrt (k : ℝ) ≤
            Real.sqrt ((((Nat.sqrt k : ℕ) + 1 : ℕ) : ℝ)
              * (((Nat.sqrt k : ℕ) + 1 : ℕ) : ℝ)) :=
          Real.sqrt_le_sqrt (le_of_lt h2)
        have hq : (0 : ℝ) ≤ (((Nat.sqrt k : ℕ) + 1 : ℕ) : ℝ) := by positivity
        rw [Real.sqrt_mul hq, Real.mul_self_sqrt hq, Nat.cast_add, Nat.cast_one] at h3
        exact h3
      have hfinal : ((∑ j ∈ S, (if d j = 1 then (1 : ℤ) else -1)).natAbs : ℝ)
          ≤ (((2 * ⌈C⌉₊ * Nat.sqrt k : ℕ) : ℝ)) := by
        have hconv : ∀ x : ℤ, ((x.natAbs : ℕ) : ℝ) = |(x : ℝ)| := by
          intro x
          calc ((x.natAbs : ℕ) : ℝ)
              = (((x.natAbs : ℕ) : ℤ) : ℝ) := (Int.cast_natCast _).symm
            _ = ((|x| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
            _ = |(x : ℝ)| := Int.cast_abs
        have habs : ((∑ j ∈ S, (if d j = 1 then (1 : ℤ) else -1)).natAbs : ℝ)
            = |(∑ j ∈ S, d j : ℝ)| := by
          rw [hconv, hreal]
        rw [habs]
        have hcast : (((2 * ⌈C⌉₊ * Nat.sqrt k : ℕ) : ℝ))
            = 2 * ((⌈C⌉₊ : ℕ) : ℝ) * ((Nat.sqrt k : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hcast]
        have hbound : C * Real.sqrt (k : ℝ)
            ≤ 2 * ((⌈C⌉₊ : ℕ) : ℝ) * ((Nat.sqrt k : ℕ) : ℝ) := by
          nlinarith [hC, hceil, hs1, hs2,
            mul_nonneg hC (by positivity : (0 : ℝ) ≤ ((Nat.sqrt k : ℕ) : ℝ))]
        linarith
      exact_mod_cast hfinal

end Discrepancy
