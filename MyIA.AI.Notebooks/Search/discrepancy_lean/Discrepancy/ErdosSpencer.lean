import Mathlib
import Discrepancy.Basic
import PacLearning.Hoeffding

/-!
# Boute P2 — borne inférieure d'Erdős–Spencer `√k/2` (méthode probabiliste)

Palier P2 de l'issue #12823 (voir `FORMAL_STATUS.md`) : la contrepartie
optimale du théorème de Beck–Fiala `disc ≤ 2k − 1` — il existe des familles
de degré au plus `k` dont AUCUNE coloration `±1` n'abaisse la discrépance
sous `√k / 2`, justifiant que la borne `O(√k)` ne peut pas être améliorée
en `o(√k)` en général.

La preuve cible réutilise le kernel `PacLearning.Hoeffding` du lake frère
`learning_theory_lean` (import, pas duplication — mandat FORMAL_STATUS) :

1. **Anti-concentration** (boute `p1`) : pour une coloration fixée `c` et un
   ensemble `S` tiré au hasard (Bernoulli indépendant), la somme colorée
   `∑_{i∈S} c i` s'écarte de `√k/2` avec probabilité minorée — via la
   concentration du kernel (`PacLearning.hoeffding_concentration`).
2. **Familles aléatoires** (boute `p2`) : `m` tirages indépendants → pour une
   coloration fixée, la probabilité que TOUS les ensembles restent sous
   `√k/2` décroît exponentiellement en `m`.
3. **Union bound sur les colorations** (boute `p3`) : `2^n · p^m < 1` pour
   `m` assez grand — il existe une réalisation dont toute coloration laisse
   au moins un ensemble à somme `≥ √k/2`.
4. **Contrôle du degré** (boute `p4`) : élagage/conditionnement du tirage
   pour `maxDegree ≤ k` en régime `k ≤ n / C`.

Tant que la preuve n'est pas assemblée, l'énoncé vit comme `Prop` nommée
(convention du lake : conjecture = `def ... : Prop`, zéro `sorry`).
-/

namespace Discrepancy

/-- **Borne inférieure d'Erdős–Spencer (1972)** : pour tout `k ≥ 1` et `n`
assez grand devant `k`, il existe une famille de parties de `Fin n`, de degré
maximal au plus `k`, dont toute coloration `±1` laisse une somme colorée de
valeur absolue au moins `√k / 2` — écrit sans division :
`Nat.sqrt k ≤ 2 * discrepancy F c`. -/
def ErdosSpencerLB : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k ≤ n →
    ∃ F : Finset (Finset (Fin n)),
      maxDegree F ≤ k ∧
        ∀ c : Fin n → ℤ, IsColoring c → Nat.sqrt k ≤ 2 * discrepancy F c

/-! ## Boute p1a — moments de la somme de Rademacher colorée

L'aléa de la construction : un ensemble aléatoire `S` est une fonction
`Fin n → Bool` tirée selon le produit de pièces équitable (chaque élément
entre dans `S` indépendamment avec probabilité `1/2`). Pour une coloration
fixée `c`, la quantité `Z S = ∑ i, c i • sign (S i)` (où `sign` vaut `+1`
pour `true`, `-1` pour `false`) est une **somme de Rademacher colorée** :
`Z S = 2 • (∑_{i ∈ S} c i) − ∑ i, c i`, donc `|Z| ≥ t` force la somme
colorée de `S` à s'écarter de sa moyenne d'au moins `t/2`.

Les moments de `Z` sont **uniformes en `c`** (les termes croisés disparaissent
quelle que soit la coloration) — c'est le cœur quantitatif de la méthode
probabiliste d'Erdős–Spencer. Cette boute établit `E[Z] = 0` et
`E[Z²] = ∑ i, (c i)² = n` pour une coloration ; la boute suivante (p1b)
ajoutera le 4ᵉ moment et Paley–Zygmund pour la minoration de queue. -/

section Moments

open PacLearning

/-- **Pièce équitable** : distribution uniforme sur `Bool` (poids `1/2`
partout), dans le cadre ℝ-weight du kernel `PacLearning` (réutilisé, pas
dupliqué). -/
noncomputable def fairCoin : Distribution Bool where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by
    simp only [Fintype.univ_bool, Finset.sum_insert, Finset.sum_singleton]
    norm_num

theorem fairCoin_weight (b : Bool) : fairCoin.weight b = 1 / 2 := rfl

/-- **Signe de Rademacher** : `+1` pour `true`, `-1` pour `false`. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

/-- L'espérance d'un signe scalé est nulle : `E[a * sign] = 0` pour tout
scalaire — la pièce équitable centrée, appliquée à un facteur symbolique. -/
theorem expect_mul_boolSign_eq_zero (a : ℝ) :
    expect fairCoin (fun b => a * boolSign b) = 0 := by
  simp only [expect, fairCoin_weight, boolSign, Fintype.univ_bool,
    Finset.sum_insert, Finset.sum_singleton]
  norm_num

/-- Le second moment d'un signe scalé : `E[(a * sign)^2] = a^2`. -/
theorem expect_mul_boolSign_sq (a : ℝ) :
    expect fairCoin (fun b => (a * boolSign b) * (a * boolSign b)) = a ^ 2 := by
  simp only [expect, fairCoin_weight, boolSign, Fintype.univ_bool,
    Finset.sum_insert, Finset.sum_singleton]
  norm_num
  ring

/-- **Produit à deux indices distingués** : si `v i = a`, `v j = b` (`i != j`)
et `v k = 1` ailleurs, alors le produit total vaut `a * b`. Brique
combinatoire servant à évaluer les produits où seules deux coordonnées
portent une valeur non triviale. -/
theorem prod_two_special {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (a b : ℝ) (v : ι → ℝ)
    (hi : v i = a) (hj : v j = b) (hrest : ∀ k, k ≠ i → k ≠ j → v k = 1) :
    ∏ k, v k = a * b := by
  have hsub : ({i, j} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  have hrest' : ∀ x ∈ Finset.univ, x ∉ ({i, j} : Finset ι) → v x = 1 := by
    intro x _ hx
    exact hrest x (fun h => hx (by simp [h])) (fun h => hx (by simp [h]))
  rw [← Finset.prod_subset hsub hrest', Finset.prod_pair hij, hi, hj]

/-- **Factorisation deux-coordonnées** (`i != j`) : l'espérance du produit de
deux fonctions de coordonnées distinctes est le produit des espérances —
l'indépendance sous la loi produit `D^n`. C'est la brique qui fait
disparaître tous les termes croisés des moments. -/
theorem sampleExpect_coord_mul_coord {X : Type*} [Fintype X] (D : Distribution X)
    (g₁ g₂ : X → ℝ) {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    sampleExpect D (fun S : Fin n → X ↦ g₁ (S i) * g₂ (S j)) =
      expect D g₁ * expect D g₂ := by
  dsimp only [PacLearning.sampleExpect, PacLearning.sampleWeight]
  let G : Fin n → X → ℝ := fun k x ↦ D.weight x *
    (if k = i then g₁ x else if k = j then g₂ x else 1)
  have hprod : ∀ S : Fin n → X, ∏ k, G k (S k) =
      (∏ k, D.weight (S k)) * (g₁ (S i) * g₂ (S j)) := by
    intro S
    have h1 : ∀ k : Fin n, G k (S k) = D.weight (S k) *
        (if k = i then g₁ (S k) else if k = j then g₂ (S k) else 1) :=
      fun _ => rfl
    rw [Finset.prod_congr rfl (fun k _ => h1 k), Finset.prod_mul_distrib,
      prod_two_special hij (g₁ (S i)) (g₂ (S j))
        (fun k => if k = i then g₁ (S k) else if k = j then g₂ (S k) else 1)
        (by rw [if_pos rfl])
        (by rw [if_neg (fun h : j = i => hij h.symm), if_pos rfl])
        (fun k hk1 hk2 => by
          rw [if_neg (fun h : k = i => hk1 h),
              if_neg (fun h : k = j => hk2 h)])]
  rw [Finset.sum_congr rfl (fun S _ => (hprod S).symm),
    ← Fintype.prod_sum (κ := fun _ : Fin n => X) G]
  have hsum : ∀ k : Fin n, ∑ x, G k x =
      if k = i then expect D g₁ else if k = j then expect D g₂ else 1 := by
    intro k
    by_cases h1 : k = i
    · subst h1
      simp [G, expect]
    · by_cases h2 : k = j
      · subst h2
        simp [G, h1, expect]
      · simp [G, h1, h2, D.sum_one]
  simp only [hsum]
  exact prod_two_special hij (expect D g₁) (expect D g₂)
    (fun k => if k = i then expect D g₁ else if k = j then expect D g₂ else 1)
    (by rw [if_pos rfl])
    (by rw [if_neg (fun h : j = i => hij h.symm), if_pos rfl])
    (fun k hk1 hk2 => by
      rw [if_neg (fun h : k = i => hk1 h), if_neg (fun h : k = j => hk2 h)])

/-- **Somme de Rademacher colorée** : pour une coloration `c` et un ensemble
aléatoire `S` (fonction indicatrice), `Z S = ∑ i, (c i : ℝ) * boolSign (S i)`.
Chaque terme vaut `± (c i : ℝ)`, signe tiré à pile ou face. -/
def rademacherSum {n : ℕ} (c : Fin n → ℤ) (S : Fin n → Bool) : ℝ :=
  ∑ i, (c i : ℝ) * boolSign (S i)

/-- **Espérance nulle** : chaque coordonnée est centrée (`E[a * sign] = 0`),
donc `E[Z] = 0` — indépendamment de `c`. -/
theorem expect_rademacherSum_eq_zero {n : ℕ} (c : Fin n → ℤ) :
    sampleExpect fairCoin (rademacherSum c) = 0 := by
  show sampleExpect fairCoin
      (fun S : Fin n → Bool ↦ ∑ i, (c i : ℝ) * boolSign (S i)) = 0
  rw [PacLearning.sampleExpect_sum]
  have h : ∀ i : Fin n, sampleExpect fairCoin
      (fun S : Fin n → Bool ↦ (c i : ℝ) * boolSign (S i)) = 0 := by
    intro i
    rw [PacLearning.sampleExpect_coord (fun x => (c i : ℝ) * boolSign x) i,
      expect_mul_boolSign_eq_zero]
  simp only [h, Finset.sum_const_zero]

/-- **Second moment exact** : `E[Z²] = ∑ i, (c i : ℝ)²` — le carré se
développe en somme double (`Finset.sum_mul_sum`), les termes croisés
`i != j` disparaissent par indépendance (`sampleExpect_coord_mul_coord`,
chacun portant un facteur `E[a * sign] = 0`), les termes diagonaux valent
`(c i)²`. Uniforme en `c`. -/
theorem expect_rademacherSum_sq {n : ℕ} (c : Fin n → ℤ) :
    sampleExpect fairCoin (fun S => (rademacherSum c S) ^ 2) =
      ∑ i, ((c i : ℝ) ^ 2) := by
  have hexp : (fun S : Fin n → Bool => (rademacherSum c S) ^ 2) =
      fun S : Fin n → Bool ↦ ∑ i, ∑ j,
        ((c i : ℝ) * boolSign (S i)) * ((c j : ℝ) * boolSign (S j)) := by
    funext S
    simp only [rademacherSum, sq, Finset.sum_mul_sum]
  rw [hexp, PacLearning.sampleExpect_sum]
  have hinner : ∀ i : Fin n,
      sampleExpect fairCoin (fun S : Fin n → Bool ↦ ∑ j,
        ((c i : ℝ) * boolSign (S i)) * ((c j : ℝ) * boolSign (S j))) =
      ((c i : ℝ) ^ 2) := by
    intro i
    rw [PacLearning.sampleExpect_sum]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hj => by
      rw [sampleExpect_coord_mul_coord fairCoin
        (fun x => (c i : ℝ) * boolSign x) (fun x => (c j : ℝ) * boolSign x)
        (Ne.symm hj),
        expect_mul_boolSign_eq_zero, zero_mul])]
    rw [PacLearning.sampleExpect_coord
      (fun x => ((c i : ℝ) * boolSign x) * ((c i : ℝ) * boolSign x)) i,
      expect_mul_boolSign_sq]
  simp only [hinner]

/-- **Factorisation sur un ensemble d'indices** : l'espérance d'un produit de
fonctions une-coordonnée indexé par un `Finset` de coordonnées se factorise
en le produit des espérances — l'indépendance sous la loi produit `D^n`.
Généralise à la fois `sampleExpect_coord_mul_coord` (deux coordonnées
distinguées) et le `PacLearning.sampleExpect_prod_coord` du kernel (toutes
les coordonnées, même fonction). C'est la brique maîtresse des moments
d'ordre supérieur (boute p1b) : tout moment mixte `E[∏_q g q (S q)]` se
réduit à un produit d'espérances une-coin. -/
theorem sampleExpect_prod_over_finset {X : Type*} [Fintype X] (D : Distribution X)
    {n : ℕ} (s : Finset (Fin n)) (g : Fin n → X → ℝ) :
    sampleExpect D (fun S : Fin n → X ↦ ∏ p ∈ s, g p (S p)) =
      ∏ p ∈ s, expect D (g p) := by
  dsimp only [PacLearning.sampleExpect, PacLearning.sampleWeight]
  let G : Fin n → X → ℝ :=
    fun k x ↦ D.weight x * (if k ∈ s then g k x else 1)
  have hprod : ∀ S : Fin n → X, ∏ k, G k (S k) =
      (∏ k, D.weight (S k)) * ∏ p ∈ s, g p (S p) := by
    intro S
    have h1 : ∀ k : Fin n, G k (S k) = D.weight (S k) *
        (if k ∈ s then g k (S k) else 1) := fun _ => rfl
    rw [Finset.prod_congr rfl (fun k _ => h1 k), Finset.prod_mul_distrib,
      ← Finset.prod_subset (Finset.subset_univ s) (fun k _ hk => if_neg hk)]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    exact if_pos hp
  simp only [← hprod]
  rw [← Fintype.prod_sum (κ := fun _ : Fin n => X) G]
  have hsum : ∀ k : Fin n, ∑ x, G k x =
      if k ∈ s then expect D (g k) else 1 := by
    intro k
    by_cases hk : k ∈ s
    · simp [G, hk, expect]
    · simp [G, hk, D.sum_one]
  simp only [hsum]
  have hfin : ∏ k : Fin n, (if k ∈ s then expect D (g k) else 1) =
      ∏ p ∈ s, expect D (g p) :=
    (Finset.prod_subset (Finset.subset_univ s) (fun k _ hk => if_neg hk)).symm.trans
      (Finset.prod_congr rfl (fun p hp => if_pos hp))
  rw [hfin]

/-- **Parité des moments du signe** : `(boolSign b)^k = 1` quand `k` est
pair (le signe est ±1). -/
theorem boolSign_pow_eq_one (b : Bool) {k : ℕ} (hk : Even k) :
    (boolSign b) ^ k = 1 := by
  obtain ⟨m, hm⟩ := hk
  rw [hm, ← Nat.two_mul m, pow_mul]
  norm_num [boolSign]

/-- **Parité des moments du signe** : `(boolSign b)^k = boolSign b` quand
`k` est impair. -/
theorem boolSign_pow_eq_self (b : Bool) {k : ℕ} (hk : Odd k) :
    (boolSign b) ^ k = boolSign b := by
  obtain ⟨m, hm⟩ := hk
  rw [hm, pow_add, pow_one, boolSign_pow_eq_one b ⟨m, by omega⟩, one_mul]

/-- **Moment de la pièce par parité** : `E[a * sign^k] = a` si `k` pair,
`0` si `k` impair. C'est le discriminateur qui annule tous les termes
croisés impairs des moments d'ordre supérieur. -/
theorem expect_mul_boolSign_pow (a : ℝ) (k : ℕ) :
    expect fairCoin (fun b => a * (boolSign b) ^ k) =
      if Even k then a else 0 := by
  rcases Nat.even_or_odd k with hk | hk
  · have hb : ∀ b : Bool, (boolSign b) ^ k = 1 := fun b => boolSign_pow_eq_one b hk
    simp only [hb, mul_one, if_pos hk]
    show ∑ b : Bool, fairCoin.weight b * a = a
    rw [← Finset.sum_mul, fairCoin.sum_one, one_mul]
  · obtain ⟨m, hm⟩ := hk
    have hb : ∀ b : Bool, (boolSign b) ^ k = boolSign b :=
      fun b => boolSign_pow_eq_self b ⟨m, hm⟩
    simp only [hb]
    rw [if_neg (by rintro ⟨c, hc⟩; omega)]
    exact expect_mul_boolSign_eq_zero a

/-- **Annulation d'un moment mixte** : si une coordonnée `p ∈ s` porte une
fonction d'espérance nulle (typiquement une puissance impaire du signe),
le moment mixte entier `E[∏_{q ∈ s} g q (S q)]` est nul. Application directe
de la factorisation `sampleExpect_prod_over_finset`. -/
theorem expect_prod_eq_zero_of_mem {X : Type*} [Fintype X] (D : Distribution X)
    {n : ℕ} (s : Finset (Fin n)) (g : Fin n → X → ℝ) {p : Fin n} (hp : p ∈ s)
    (hp0 : expect D (g p) = 0) :
    sampleExpect D (fun S : Fin n → X ↦ ∏ q ∈ s, g q (S q)) = 0 := by
  rw [sampleExpect_prod_over_finset D s g, Finset.prod_eq_zero hp hp0]

/-- **Corollaire coloration** : pour une vraie coloration `±1`, le second
moment vaut exactement `n` — la variance de la marche aléatoire colorée est
le nombre d'éléments, quelle que soit la coloration. C'est
l'**uniformité en `c`** qui rend la méthode probabiliste possible. -/
theorem expect_rademacherSum_sq_of_isColoring {n : ℕ} (c : Fin n → ℤ)
    (hc : IsColoring c) :
    sampleExpect fairCoin (fun S => (rademacherSum c S) ^ 2) = (n : ℝ) := by
  rw [expect_rademacherSum_sq]
  have h : ∀ i : Fin n, ((c i : ℝ) ^ 2) = 1 := by
    intro i
    rcases hc i with h | h <;> simp [h]
  simp only [h]
  simp

end Moments

end Discrepancy
