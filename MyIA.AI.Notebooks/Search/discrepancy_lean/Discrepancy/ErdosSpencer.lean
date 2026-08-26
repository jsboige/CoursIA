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

/-! ## Boute p1b — moteurs du 4e moment

Le développement de `E[Z^4]` classe chaque quadruplet d'indices `(i,j,k,l)`
par son motif d'egalites : les termes non nuls sont exactement les
« apparies » (chaque coordonnee apparaissant un nombre pair de fois). Les
trois moteurs ci-dessous evaluent chaque motif ; l'assemblage (classification
complète et comptage) viendra par-dessus. -/

/-- Le signe est involutif pour la multiplication : `s * s = 1` (le signe
de Rademacher est `+-1`). Brique d'effondrement des paires. -/
theorem boolSign_mul_self (b : Bool) : boolSign b * boolSign b = 1 := by
  cases b <;> norm_num [boolSign]

/-- **Moteur deux paires** : `E[(a i * s_i)^2 * (a k * s_k)^2] = (a i)^2 (a k)^2`
— un quadruplet entièrement apparié `(i,i,k,k)` est CONSTANT au point près
(les deux `s^2` s'effondrent en 1), son espérance est sa valeur. -/
theorem expect_quad_two_pairs {n : ℕ} (a : Fin n → ℝ) (i k : Fin n) :
    sampleExpect fairCoin (fun S : Fin n → Bool ↦
      (a i * boolSign (S i)) * (a i * boolSign (S i)) *
      (a k * boolSign (S k)) * (a k * boolSign (S k))) =
      a i * a i * (a k * a k) := by
  have hc : ∀ S : Fin n → Bool, ∀ q : Fin n,
      (a q * boolSign (S q)) * (a q * boolSign (S q)) = a q * a q :=
    fun S q => by rw [mul_mul_mul_comm, boolSign_mul_self, mul_one]
  have hfun : ∀ S : Fin n → Bool,
      (a i * boolSign (S i)) * (a i * boolSign (S i)) *
      (a k * boolSign (S k)) * (a k * boolSign (S k)) =
        a i * a i * (a k * a k) := by
    intro S
    rw [hc S i, mul_assoc, hc S k]
  rw [funext hfun, PacLearning.sampleExpect_const]

/-- **Moteur paire + deux distinctes** : `E[(a i * s_i)^2 * (a k * s_k) *
(a l * s_l)] = 0` quand `k != l` — la paire s'effondre en `(a i)^2`, reste un
produit de deux coordonnées distinctes à espérances nulles. Fonctionne même
si `k` ou `l` égale `i` (la factorisation ne demande que `k != l`). -/
theorem expect_quad_pair_and_two {n : ℕ} (a : Fin n → ℝ) (i k l : Fin n)
    (hkl : k ≠ l) :
    sampleExpect fairCoin (fun S : Fin n → Bool ↦
      (a i * boolSign (S i)) * (a i * boolSign (S i)) *
      (a k * boolSign (S k)) * (a l * boolSign (S l))) = 0 := by
  have hc : ∀ S : Fin n → Bool,
      (a i * boolSign (S i)) * (a i * boolSign (S i)) = a i * a i :=
    fun S => by rw [mul_mul_mul_comm, boolSign_mul_self, mul_one]
  have hfun : ∀ S : Fin n → Bool,
      (a i * boolSign (S i)) * (a i * boolSign (S i)) *
      (a k * boolSign (S k)) * (a l * boolSign (S l)) =
        (a i * a i) * ((a k * boolSign (S k)) * (a l * boolSign (S l))) := by
    intro S
    rw [hc S, mul_assoc]
  rw [funext hfun, PacLearning.sampleExpect_smul,
    sampleExpect_coord_mul_coord fairCoin
      (fun x => a k * boolSign x) (fun x => a l * boolSign x) hkl,
    expect_mul_boolSign_eq_zero, expect_mul_boolSign_eq_zero,
    mul_zero, mul_zero]

/-- **Moteur quatre distinctes** : `E[(a i * s_i) * (a j * s_j) *
(a k * s_k) * (a l * s_l)] = 0` quand les quatre indices sont deux à deux
distincts — le produit est exactement un produit sur l'ensemble
`{i,j,k,l}`, chaque facteur ayant une espérance nulle. -/
theorem expect_quad_four_distinct {n : ℕ} (a : Fin n → ℝ) (i j k l : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) :
    sampleExpect fairCoin (fun S : Fin n → Bool ↦
      (a i * boolSign (S i)) * (a j * boolSign (S j)) *
      (a k * boolSign (S k)) * (a l * boolSign (S l))) = 0 := by
  have hset : (fun S : Fin n → Bool =>
      (a i * boolSign (S i)) * (a j * boolSign (S j)) *
      (a k * boolSign (S k)) * (a l * boolSign (S l))) =
      (fun S : Fin n → Bool => ∏ q ∈ ({i, j, k, l} : Finset (Fin n)),
        (a q * boolSign (S q))) := by
    funext S
    rw [Finset.prod_insert (by simp [hij, hik, hil]),
        Finset.prod_insert (by simp [hjk, hjl]),
        Finset.prod_insert (by simp [hkl]),
        Finset.prod_singleton]
    ring
  have hstep : sampleExpect fairCoin
      (fun S : Fin n → Bool => ∏ q ∈ ({i, j, k, l} : Finset (Fin n)),
        a q * boolSign (S q)) =
      ∏ q ∈ ({i, j, k, l} : Finset (Fin n)),
        expect fairCoin (fun x => a q * boolSign x) :=
    sampleExpect_prod_over_finset fairCoin _ (fun q x => a q * boolSign x)
  rw [hset, hstep]
  exact Finset.prod_eq_zero (Finset.mem_insert_self i _)
    (expect_mul_boolSign_eq_zero (a i))

/-! ### Assemblage du 4e moment

Décomposition du carré : `Z^2 = diag + crossSum` (diagonale constante +
somme croisée sur les paires ordonnées d'indices distincts), puis
annulation de l'espérance de la partie croisée. -/

/-- **Somme croisée** : paires ordonnées `(p, q)` d'indices distincts du
développement du carré. -/
def crossSum {n : ℕ} (a : Fin n → ℝ) (S : Fin n → Bool) : ℝ :=
  ∑ p : Fin n × Fin n,
    if p.1 ≠ p.2 then (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) else 0

/-- **Décomposition du carré** : `Z(S)^2 = diag + crossSum` — le carré de la
somme se décompose en la somme des carrés des coefficients (diagonale,
CONSTANTE en `S` : les signes s'effondrent) et la somme croisée sur les
paires ordonnées distinctes. -/
theorem rademacher_sq_split {n : ℕ} (a : Fin n → ℝ) (S : Fin n → Bool) :
    (∑ i, a i * boolSign (S i)) ^ 2 = ∑ i, a i * a i + crossSum a S := by
  have hdiag : (∑ i : Fin n, a i * a i) =
      ∑ p : Fin n × Fin n, if p.1 = p.2 then a p.1 * a p.2 else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Prod.fst, Prod.snd]
    rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin n)) i (fun j => a i * a j)]
    simp
  have hprod : (∑ i : Fin n, ∑ j : Fin n, a i * boolSign (S i) * (a j * boolSign (S j))) =
      ∑ p : Fin n × Fin n, (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) :=
    (Fintype.sum_prod_type
      (fun q : Fin n × Fin n => (a q.1 * boolSign (S q.1)) * (a q.2 * boolSign (S q.2)))).symm
  rw [sq, Finset.sum_mul_sum, hprod, hdiag]
  simp only [crossSum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.1 = p.2
  · simp only [if_pos h, if_neg (show ¬(p.1 ≠ p.2) by simp [h]), add_zero]
    rw [← h, mul_mul_mul_comm, boolSign_mul_self (S p.1), mul_one]
  · simp only [if_neg h, if_pos h, zero_add]

/-- **Espérance nulle de la partie croisée** : chaque terme de `crossSum`
est un produit de deux coordonnées distinctes à espérances nulles. -/
theorem expect_crossSum_eq_zero {n : ℕ} (a : Fin n → ℝ) :
    sampleExpect fairCoin (crossSum a) = 0 := by
  rw [show crossSum a = (fun S : Fin n → Bool => ∑ p : Fin n × Fin n,
      if p.1 ≠ p.2 then (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) else 0) from rfl]
  rw [PacLearning.sampleExpect_sum]
  have h : ∀ p : Fin n × Fin n, sampleExpect fairCoin
      (fun S : Fin n → Bool =>
        if p.1 ≠ p.2 then (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) else 0) = 0 := by
    intro p
    by_cases hp : p.1 ≠ p.2
    · simp only [if_pos hp]
      rw [sampleExpect_coord_mul_coord fairCoin
        (fun x => a p.1 * boolSign x) (fun x => a p.2 * boolSign x) hp,
        expect_mul_boolSign_eq_zero, expect_mul_boolSign_eq_zero, mul_zero]
    · simp only [if_neg hp, PacLearning.sampleExpect_const]
  simp only [h, Finset.sum_const_zero]

/-! ### Moteurs de multiplicité (préparation assemblage-2)

L'espérance d'un produit de coordonnées à multiplicités entières se
factorise en un produit de `if Even (m r) then (a r) ^ m r else 0` :
une multiplicité impaire tue le terme. -/

/-- Moment d'une coordonnée à puissance arbitraire : la parité de `m`
décide. -/
theorem expect_coord_pow (c : ℝ) (m : ℕ) :
    expect fairCoin (fun b : Bool => (c * boolSign b) ^ m) =
      if Even m then c ^ m else 0 := by
  have h : (fun b : Bool => (c * boolSign b) ^ m) =
      fun b : Bool => c ^ m * (boolSign b) ^ m := by
    funext b
    exact mul_pow _ _ _
  rw [h, expect_mul_boolSign_pow]

/-- **Moteur de multiplicité** : produit de coordonnées `x r ^ m r`
sur un `Finset` d'indices — chaque indice de multiplicité impaire
contribue un facteur nul. -/
theorem expect_prod_coord_mult {n : ℕ} (u : Finset (Fin n)) (m : Fin n → ℕ)
    (a : Fin n → ℝ) :
    sampleExpect fairCoin (fun S : Fin n → Bool =>
      ∏ r ∈ u, (a r * boolSign (S r)) ^ m r) =
      ∏ r ∈ u, if Even (m r) then (a r) ^ m r else 0 := by
  rw [sampleExpect_prod_over_finset fairCoin u (fun r x => (a r * boolSign x) ^ m r)]
  apply Finset.prod_congr rfl
  intro r _
  exact expect_coord_pow (a r) (m r)

/-! ### Classification des quadruplets (assemblage-3)

Un produit de quatre coordonnées `x i * x j * x k * x l` (avec
`x t = a t * boolSign (S t)`) a une espérance non nulle seulement si
les indices se répartissent en deux paires — sinon un indice garde une
multiplicité impaire et sa coordonnée centrée tue le terme. Ces lemmes
sont l'interface de classification du développement de `Z^4`. -/

/-- **Quadruplet apparié (forme directe)** : `E[x i * x j * x i * x j]`
vaut `(a i)^2 * (a j)^2` — les deux signes de chaque indice se
dupliquent et s'effondrent. -/
theorem expect_quad_paired {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) :
    sampleExpect fairCoin (fun S : Fin n → Bool =>
      (a i * boolSign (S i)) * (a j * boolSign (S j)) *
      (a i * boolSign (S i)) * (a j * boolSign (S j))) =
      a i * a i * (a j * a j) := by
  have hperm : (fun S : Fin n → Bool =>
      (a i * boolSign (S i)) * (a j * boolSign (S j)) *
      (a i * boolSign (S i)) * (a j * boolSign (S j))) =
      (fun S : Fin n → Bool =>
      (a i * boolSign (S i)) * (a i * boolSign (S i)) *
      (a j * boolSign (S j)) * (a j * boolSign (S j))) :=
    funext fun S => by ring
  rw [hperm]
  exact expect_quad_two_pairs a i j

/-- **Quadruplet apparié (forme croisée)** : `E[x i * x j * x j * x i]`
vaut aussi `(a i)^2 * (a j)^2`. -/
theorem expect_quad_paired_swap {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) :
    sampleExpect fairCoin (fun S : Fin n → Bool =>
      (a i * boolSign (S i)) * (a j * boolSign (S j)) *
      (a j * boolSign (S j)) * (a i * boolSign (S i))) =
      a i * a i * (a j * a j) := by
  have hperm : (fun S : Fin n → Bool =>
      (a i * boolSign (S i)) * (a j * boolSign (S j)) *
      (a j * boolSign (S j)) * (a i * boolSign (S i))) =
      (fun S : Fin n → Bool =>
      (a i * boolSign (S i)) * (a i * boolSign (S i)) *
      (a j * boolSign (S j)) * (a j * boolSign (S j))) :=
    funext fun S => by ring
  rw [hperm]
  exact expect_quad_two_pairs a i j

/-- **Quadruplet non apparié** : si `i ≠ j`, `k ≠ l` et que `{k, l}` ne
recollent pas `{i, j}` (ni directement ni croisé), l'espérance est
nulle. -/
theorem expect_quad_unpaired_zero {n : ℕ} (a : Fin n → ℝ) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l)
    (h1 : ¬(i = k ∧ j = l)) (h2 : ¬(i = l ∧ j = k)) :
    sampleExpect fairCoin (fun S : Fin n → Bool =>
      (a i * boolSign (S i)) * (a j * boolSign (S j)) *
      (a k * boolSign (S k)) * (a l * boolSign (S l))) = 0 := by
  by_cases hik : i = k
  · rw [hik]
    have hjl : ¬(j = l) := fun hl => h1 ⟨hik, hl⟩
    have hperm : (fun S : Fin n → Bool =>
        (a k * boolSign (S k)) * (a j * boolSign (S j)) *
        (a k * boolSign (S k)) * (a l * boolSign (S l))) =
        (fun S : Fin n → Bool =>
        (a k * boolSign (S k)) * (a k * boolSign (S k)) *
        (a j * boolSign (S j)) * (a l * boolSign (S l))) :=
      funext fun S => by ring
    rw [hperm]
    exact expect_quad_pair_and_two a k j l hjl
  · by_cases hil : i = l
    · rw [hil]
      have hjk : ¬(j = k) := fun hj => h2 ⟨hil, hj⟩
      have hperm : (fun S : Fin n → Bool =>
          (a l * boolSign (S l)) * (a j * boolSign (S j)) *
          (a k * boolSign (S k)) * (a l * boolSign (S l))) =
          (fun S : Fin n → Bool =>
          (a l * boolSign (S l)) * (a l * boolSign (S l)) *
          (a j * boolSign (S j)) * (a k * boolSign (S k))) :=
        funext fun S => by ring
      rw [hperm]
      exact expect_quad_pair_and_two a l j k hjk
    · by_cases hjk : j = k
      · rw [hjk]
        have hperm : (fun S : Fin n → Bool =>
            (a i * boolSign (S i)) * (a k * boolSign (S k)) *
            (a k * boolSign (S k)) * (a l * boolSign (S l))) =
            (fun S : Fin n → Bool =>
            (a k * boolSign (S k)) * (a k * boolSign (S k)) *
            (a i * boolSign (S i)) * (a l * boolSign (S l))) :=
          funext fun S => by ring
        rw [hperm]
        exact expect_quad_pair_and_two a k i l hil
      · by_cases hjl : j = l
        · rw [hjl]
          have hperm : (fun S : Fin n → Bool =>
              (a i * boolSign (S i)) * (a l * boolSign (S l)) *
              (a k * boolSign (S k)) * (a l * boolSign (S l))) =
              (fun S : Fin n → Bool =>
              (a l * boolSign (S l)) * (a l * boolSign (S l)) *
              (a i * boolSign (S i)) * (a k * boolSign (S k))) :=
            funext fun S => by ring
          rw [hperm]
          exact expect_quad_pair_and_two a l i k hik
        · exact expect_quad_four_distinct a i j k l hij hik hil hjk hjl hkl

/-- **Somme interne du produit croisé** : pour une paire ordonnée `p`
hors diagonale, la somme sur `q` des espérances des termes
`F p * F q` vaut exactement `2 (a p.1)^2 (a p.2)^2` — les deux seuls
contributeurs sont `q = p` et `q = transposé p` ; tout le reste
s'éteint par multiplicité impaire. Sur la diagonale (`p.1 = p.2`), la
somme est nulle. -/
theorem sum_expect_cross_pair {n : ℕ} (a : Fin n → ℝ) (p : Fin n × Fin n) :
    ∑ q : Fin n × Fin n, sampleExpect fairCoin (fun S : Fin n → Bool =>
      (if p.1 ≠ p.2 then (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) else 0) *
      (if q.1 ≠ q.2 then (a q.1 * boolSign (S q.1)) * (a q.2 * boolSign (S q.2)) else 0)) =
      if p.1 ≠ p.2 then 2 * (a p.1 * a p.1 * (a p.2 * a p.2)) else 0 := by
  by_cases hp : p.1 ≠ p.2
  · have hval : (fun q : Fin n × Fin n => sampleExpect fairCoin
        (fun S : Fin n → Bool =>
          (if p.1 ≠ p.2 then (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) else 0) *
          (if q.1 ≠ q.2 then (a q.1 * boolSign (S q.1)) * (a q.2 * boolSign (S q.2)) else 0))) =
        (fun q : Fin n × Fin n =>
          if q = (p.1, p.2) ∨ q = (p.2, p.1) then a p.1 * a p.1 * (a p.2 * a p.2) else 0) := by
      funext q
      by_cases hqq : q = (p.1, p.2) ∨ q = (p.2, p.1)
      · rcases hqq with hq | hq
        · rw [hq]
          simp only [Prod.fst, Prod.snd, if_pos hp]
          have hperm : (fun S : Fin n → Bool =>
              (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) *
              ((a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)))) =
              (fun S : Fin n → Bool =>
              (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) *
              (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2))) :=
            funext fun S => by ring
          rw [hperm, if_pos (by simp)]
          exact expect_quad_paired a p.1 p.2
        · rw [hq]
          simp only [Prod.fst, Prod.snd, if_pos hp, if_pos (Ne.symm hp)]
          have hperm : (fun S : Fin n → Bool =>
              (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) *
              ((a p.2 * boolSign (S p.2)) * (a p.1 * boolSign (S p.1)))) =
              (fun S : Fin n → Bool =>
              (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) *
              (a p.2 * boolSign (S p.2)) * (a p.1 * boolSign (S p.1))) :=
            funext fun S => by ring
          rw [hperm, if_pos (by simp)]
          exact expect_quad_paired_swap a p.1 p.2
      · rw [if_neg hqq]
        have hx : q ≠ (p.1, p.2) := fun h => hqq (Or.inl h)
        have hy : q ≠ (p.2, p.1) := fun h => hqq (Or.inr h)
        have h1 : ¬(p.1 = q.1 ∧ p.2 = q.2) :=
          fun h => hx (by rw [h.1, h.2, Prod.eta])
        have h2 : ¬(p.1 = q.2 ∧ p.2 = q.1) :=
          fun h => hy (by rw [h.2, h.1, Prod.eta])
        by_cases hq : q.1 ≠ q.2
        · simp only [if_pos hp, if_pos hq]
          have hperm : (fun S : Fin n → Bool =>
              (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) *
              ((a q.1 * boolSign (S q.1)) * (a q.2 * boolSign (S q.2)))) =
              (fun S : Fin n → Bool =>
              (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) *
              (a q.1 * boolSign (S q.1)) * (a q.2 * boolSign (S q.2))) :=
            funext fun S => by ring
          rw [hperm]
          exact expect_quad_unpaired_zero a p.1 p.2 q.1 q.2 hp hq h1 h2
        · simp only [if_neg hq, mul_zero, PacLearning.sampleExpect_const]
    have hxy : (p.1, p.2) ≠ (p.2, p.1) := fun h => hp (congrArg Prod.fst h)
    have hsplit : ∀ q : Fin n × Fin n,
        (if q = (p.1, p.2) ∨ q = (p.2, p.1) then a p.1 * a p.1 * (a p.2 * a p.2) else 0) =
        ((if q = (p.1, p.2) then a p.1 * a p.1 * (a p.2 * a p.2) else 0) +
         (if q = (p.2, p.1) then a p.1 * a p.1 * (a p.2 * a p.2) else 0)) := by
      intro q
      by_cases h1 : q = (p.1, p.2)
      · rw [h1, if_pos (Or.inl rfl), if_pos rfl, if_neg hxy, add_zero]
      · by_cases h2 : q = (p.2, p.1)
        · rw [h2, if_pos (Or.inr rfl), if_neg (Ne.symm hxy), if_pos rfl,
            zero_add]
        · rw [if_neg (fun hor => hor.elim h1 h2), if_neg h1, if_neg h2]
          ring
    rw [hval, if_pos hp]
    simp only [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    ring
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q _
    simp only [if_neg hp, zero_mul, PacLearning.sampleExpect_const]

/-- **Deuxième moment de la somme croisée** : `E[C^2] = 2(S2^2 - S4)` où
`S2 = ∑ (a i)^2` et `S4 = ∑ (a i)^4`. Chaque paire `p` contribue
exactement deux fois sa valeur `(a p.1)^2 (a p.2)^2` (elle-même et sa
transposée, boute assemblage-4) ; la somme totale des `c p` vaut
`S2^2` (produit de sommes) et la diagonale `S4`. -/
theorem expect_crossSum_sq {n : ℕ} (a : Fin n → ℝ) :
    sampleExpect fairCoin (fun S : Fin n → Bool => crossSum a S * crossSum a S) =
      2 * ((∑ i, a i * a i) * (∑ i, a i * a i) - ∑ i, a i * a i * (a i * a i)) := by
  have hstep : (fun S : Fin n → Bool => crossSum a S * crossSum a S) =
      (fun S : Fin n → Bool =>
        ∑ p : Fin n × Fin n,
          ∑ q : Fin n × Fin n,
            (if p.1 ≠ p.2 then (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) else 0) *
            (if q.1 ≠ q.2 then (a q.1 * boolSign (S q.1)) * (a q.2 * boolSign (S q.2)) else 0)) := by
    funext S
    simp only [crossSum, Finset.sum_mul_sum]
  have hinner : ∀ p : Fin n × Fin n,
      sampleExpect fairCoin (fun S : Fin n → Bool =>
        ∑ q : Fin n × Fin n,
          (if p.1 ≠ p.2 then (a p.1 * boolSign (S p.1)) * (a p.2 * boolSign (S p.2)) else 0) *
          (if q.1 ≠ q.2 then (a q.1 * boolSign (S q.1)) * (a q.2 * boolSign (S q.2)) else 0)) =
      if p.1 ≠ p.2 then 2 * (a p.1 * a p.1 * (a p.2 * a p.2)) else 0 := by
    intro p
    rw [PacLearning.sampleExpect_sum]
    exact sum_expect_cross_pair a p
  have htotal : (∑ i : Fin n, a i * a i) * (∑ i : Fin n, a i * a i) =
      ∑ p : Fin n × Fin n, a p.1 * a p.1 * (a p.2 * a p.2) := by
    rw [Finset.sum_mul_sum]
    exact (Fintype.sum_prod_type (fun p : Fin n × Fin n =>
      a p.1 * a p.1 * (a p.2 * a p.2))).symm
  have hdiag4 : (∑ i : Fin n, a i * a i * (a i * a i)) =
      ∑ p : Fin n × Fin n, if p.1 = p.2 then a p.1 * a p.1 * (a p.2 * a p.2) else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Prod.fst, Prod.snd]
    rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin n)) i (fun j => a i * a i * (a j * a j))]
    simp
  have hsplit : ∀ p : Fin n × Fin n,
      a p.1 * a p.1 * (a p.2 * a p.2) =
      (if p.1 ≠ p.2 then a p.1 * a p.1 * (a p.2 * a p.2) else 0) +
      (if p.1 = p.2 then a p.1 * a p.1 * (a p.2 * a p.2) else 0) := by
    intro p
    by_cases h : p.1 = p.2
    · rw [if_neg (show ¬(p.1 ≠ p.2) by simp [h]), if_pos h, zero_add]
    · rw [if_pos h, if_neg h, add_zero]
  have hoff : ∑ p : Fin n × Fin n,
      (if p.1 ≠ p.2 then a p.1 * a p.1 * (a p.2 * a p.2) else 0) =
      (∑ i : Fin n, a i * a i) * (∑ i : Fin n, a i * a i) -
      ∑ i : Fin n, a i * a i * (a i * a i) := by
    rw [htotal]
    have h1 : ∑ p : Fin n × Fin n, a p.1 * a p.1 * (a p.2 * a p.2) =
        ∑ p : Fin n × Fin n,
          ((if p.1 ≠ p.2 then a p.1 * a p.1 * (a p.2 * a p.2) else 0) +
           (if p.1 = p.2 then a p.1 * a p.1 * (a p.2 * a p.2) else 0)) :=
      Finset.sum_congr rfl (fun p _ => hsplit p)
    rw [h1, Finset.sum_add_distrib, ← hdiag4]
    linarith
  have hmul : ∀ p : Fin n × Fin n,
      (if p.1 ≠ p.2 then 2 * (a p.1 * a p.1 * (a p.2 * a p.2)) else 0) =
      2 * (if p.1 ≠ p.2 then a p.1 * a p.1 * (a p.2 * a p.2) else 0) := by
    intro p
    by_cases h : p.1 ≠ p.2
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hstep, PacLearning.sampleExpect_sum]
  simp only [hinner]
  simp only [hmul]
  rw [← Finset.mul_sum, hoff]

/-- **Additivité** : `E[f + g] = E[f] + E[g]` — complément local au kernel
(via la définition et `Finset.sum_add_distrib`), nécessaire pour
l'assemblage du 4ᵉ moment. -/
theorem sampleExpect_add {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    sampleExpect fairCoin (fun S : Fin n → Bool => f S + g S) =
      sampleExpect fairCoin f + sampleExpect fairCoin g := by
  simp only [PacLearning.sampleExpect, mul_add, Finset.sum_add_distrib]

/-- **Quatrième moment de la somme de Rademacher** : `E[Z^4] =
3(S2^2) - 2 S4` avec `S2 = ∑ (a i)^2`, `S4 = ∑ (a i)^4`. Assemblage :
`Z^4 = (diag + C)^2` (décomposition du carré), additivité,
`E[diag^2] = diag^2` (constante), termes croisés nuls (`E[C] = 0`),
et `E[C^2] = 2(S2^2 - S4)` (boute assemblage-5). -/
theorem expect_rademacher_fourth_moment {n : ℕ} (a : Fin n → ℝ) :
    sampleExpect fairCoin (fun S : Fin n → Bool =>
      (∑ i, a i * boolSign (S i)) ^ 4) =
      3 * ((∑ i, a i * a i) * (∑ i, a i * a i)) - 2 * ∑ i, a i * a i * (a i * a i) := by
  have hsplit : (fun S : Fin n → Bool => (∑ i, a i * boolSign (S i)) ^ 4) =
      (fun S : Fin n → Bool =>
        (∑ i, a i * a i) * (∑ i, a i * a i) +
        ((∑ i, a i * a i) * crossSum a S +
        (crossSum a S * (∑ i, a i * a i) + crossSum a S * crossSum a S))) := by
    funext S
    have h4 : (∑ i, a i * boolSign (S i)) ^ 4 =
        ((∑ i, a i * boolSign (S i)) ^ 2) ^ 2 := by ring
    rw [h4, rademacher_sq_split a S]
    ring
  rw [hsplit, sampleExpect_add, sampleExpect_add, sampleExpect_add]
  rw [PacLearning.sampleExpect_const]
  rw [PacLearning.sampleExpect_smul, expect_crossSum_eq_zero, mul_zero]
  have hcomm : (fun S : Fin n → Bool => crossSum a S * (∑ i, a i * a i)) =
      (fun S : Fin n → Bool => (∑ i, a i * a i) * crossSum a S) :=
    funext fun S => mul_comm _ _
  rw [hcomm, PacLearning.sampleExpect_smul, expect_crossSum_eq_zero, mul_zero]
  rw [expect_crossSum_sq]
  ring

/-- **Corollaire coloration — le 4ᵉ moment exact** : pour une coloration
`±1`, `E[Z^4] = 3n² − 2n`, uniforme en `c`. C'est la borne de Paley–
Zygmund : `3n² − 2n ≤ 3n²` pour `n ≥ 1`. -/
theorem expect_rademacherSum_fourth_moment_of_isColoring {n : ℕ} (c : Fin n → ℤ)
    (hc : IsColoring c) :
    sampleExpect fairCoin (fun S => (rademacherSum c S) ^ 4) = 3 * (n : ℝ) ^ 2 - 2 * (n : ℝ) := by
  rw [show rademacherSum c = (fun S : Fin n → Bool =>
      ∑ i, (c i : ℝ) * boolSign (S i)) from rfl,
    expect_rademacher_fourth_moment]
  have h2 : ∀ i : Fin n, ((c i : ℝ) * (c i : ℝ)) = 1 := by
    intro i
    rcases hc i with h | h <;> simp [h]
  simp only [h2]
  simp
  ring

/-! ### Paley–Zygmund discret (boute p1b-PZ)

Dans le cadre ℝ-weight du kernel, la probabilité d'un événement est
l'espérance de son indicatrice. La clé est une forme faible de
Cauchy–Schwarz : `E[f·g] ≤ √(E[f²·g]) · √(E[g])` pour `g` indicatrice
(positive), démontrée à la main sur les poids — puis l'argument
Paley–Zygmund une étape : `E[Z²] ≤ √(E[Z⁴]·P) + seuil`. -/

/-- **Probabilité d'un événement (cadre ℝ-weight)** : espérance de
l'indicatrice `if P S then 1 else 0` sous la loi produit fairCoin. -/
noncomputable def probEvt {n : ℕ} (P : (Fin n → Bool) → Prop)
    [DecidablePred P] : ℝ :=
  sampleExpect fairCoin (fun S => if P S then 1 else 0)

/-- **Séparation événement/complément** : l'espérance d'une fonction
est la somme de sa restriction à un événement et de sa restriction au
complémentaire. -/
theorem sampleExpect_split_indicator {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (P : (Fin n → Bool) → Prop) [DecidablePred P] :
    sampleExpect fairCoin f =
      sampleExpect fairCoin (fun S => if P S then f S else 0) +
      sampleExpect fairCoin (fun S => if ¬P S then f S else 0) := by
  have h : (fun S : Fin n → Bool => f S) =
      (fun S : Fin n → Bool =>
        (if P S then f S else 0) + (if ¬P S then f S else 0)) := by
    funext S
    by_cases hS : P S
    · rw [if_pos hS, if_neg (fun h => h hS), add_zero]
    · rw [if_neg hS, if_pos hS, zero_add]
  show sampleExpect fairCoin (fun S : Fin n → Bool => f S) = _
  rw [h, sampleExpect_add]

/-- **Cauchy–Schwarz pondéré (π-type fini)** : pour des poids `w`
non négatifs, `(∑ w u v)² ≤ (∑ w u²)(∑ w v²)`. Preuve par discriminant :
le trinôme `t ↦ ∑ w (u − t v)²` est positif partout ; en `t = B/C`
(avec `C = ∑ w v² > 0`), il vaut `A − B²/C ≥ 0`. -/
theorem weighted_cauchy {ι : Type*} [Fintype ι] (w u v : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * u i * v i) ^ 2 ≤
      (∑ i, w i * u i * u i) * (∑ i, w i * v i * v i) := by
  set A := ∑ i, w i * u i * u i with hA
  set B := ∑ i, w i * u i * v i with hB
  set C := ∑ i, w i * v i * v i with hC
  have hCnn : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro i _
    nlinarith [mul_self_nonneg (v i), hw i]
  rcases eq_or_lt_of_le hCnn with h0 | hpos
  · -- h0 : 0 = C : tous les termes s'annulent, donc B = 0
    have hC0 : C = 0 := h0.symm
    have hsum0 : ∑ i, w i * v i * v i = 0 := by
      rw [← hC]
      exact hC0
    have htermnn : ∀ i, ∀ _ : i ∈ Finset.univ, 0 ≤ w i * v i * v i :=
      fun i _ => by nlinarith [mul_self_nonneg (v i), hw i]
    have hterms : ∀ i, w i * v i * v i = 0 :=
      fun i => Finset.sum_eq_zero_iff_of_nonneg htermnn |>.mp hsum0 i (Finset.mem_univ i)
    have hB0 : B = 0 := by
      rw [hB]
      apply Finset.sum_eq_zero
      intro i _
      have hsq : (w i * v i) * (w i * v i) = 0 := by
        rw [show (w i * v i) * (w i * v i) = w i * (w i * v i * v i) from by ring,
          hterms i, mul_zero]
      have hwv : w i * v i = 0 := mul_self_eq_zero.mp hsq
      rw [show w i * u i * v i = u i * (w i * v i) from by ring, hwv, mul_zero]
    rw [hB0, hC0]
    simp
  · -- 0 < C : discriminant en t = B / C
    have hCne : C ≠ 0 := ne_of_gt hpos
    set t := B / C with ht
    have hquad : 0 ≤ ∑ i, w i * (u i - t * v i) * (u i - t * v i) := by
      apply Finset.sum_nonneg
      intro i _
      nlinarith [mul_self_nonneg (u i - t * v i), hw i]
    have hterm : ∀ i, w i * (u i - t * v i) * (u i - t * v i) =
        w i * u i * u i - 2 * t * (w i * u i * v i) + t * t * (w i * v i * v i) :=
      fun i => by ring
    have hsplit : ∑ i, w i * (u i - t * v i) * (u i - t * v i) =
        (A - 2 * t * B) + t * t * C := by
      have hc : ∑ i, w i * (u i - t * v i) * (u i - t * v i) =
          ∑ i, (w i * u i * u i - 2 * t * (w i * u i * v i) + t * t * (w i * v i * v i)) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
      rw [hc]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← hB, ← hC]
    rw [hsplit] at hquad
    have hq2 : (A - 2 * t * B) + t * t * C = A - B * B / C := by
      rw [ht]
      field_simp
      ring
    rw [hq2] at hquad
    have hdiv : B * B / C ≤ A := by linarith
    rw [div_le_iff₀ hpos] at hdiv
    rw [pow_two]
    exact hdiv

/-- **Forme faible de Cauchy–Schwarz (événement)** :
`(E[f·1_B])² ≤ E[f²·1_B] · P[B]` — conséquence directe du Cauchy–
Schwarz pondéré appliqué aux fonctions `u = f·1_B` et `v = 1_B` (le
produit `u·v = u` et le carré `u² = f²·1_B`). -/
theorem expect_sq_le_mul_prob {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (B : (Fin n → Bool) → Prop) [DecidablePred B] :
    (sampleExpect fairCoin (fun S => if B S then f S else 0)) ^ 2 ≤
      sampleExpect fairCoin (fun S => if B S then f S * f S else 0) *
      probEvt B := by
  classical
  set u : (Fin n → Bool) → ℝ := fun S => if B S then f S else 0 with hu
  set v : (Fin n → Bool) → ℝ := fun S => if B S then (1 : ℝ) else 0 with hv
  have huv : ∀ S, u S * v S = u S := by
    intro S
    by_cases hS : B S
    · simp only [hu, hv, if_pos hS, mul_one]
    · simp only [hu, hv, if_neg hS, if_neg hS, mul_zero]
  have huu : ∀ S, u S * u S = if B S then f S * f S else 0 := by
    intro S
    by_cases hS : B S
    · simp only [hu, if_pos hS, if_pos hS, mul_one, mul_mul_mul_comm]
    · simp only [hu, if_neg hS, if_neg hS, mul_zero]
  have hvv : ∀ S, v S * v S = v S := by
    intro S
    by_cases hS : B S
    · simp only [hv, if_pos hS, if_pos hS, mul_one]
    · simp only [hv, if_neg hS, if_neg hS, mul_zero]
  set w : (Fin n → Bool) → ℝ := PacLearning.sampleWeight fairCoin with hwdef
  have hkey := weighted_cauchy w u v (fun S => PacLearning.sampleWeight_nonneg (D := fairCoin) S)
  -- Conversion des trois sommes pondérées vers espérances/probabilité
  have hc1 : ∀ S, w S * u S = w S * u S * v S := by
    intro S
    rw [mul_assoc, huv S]
  have hc2 : ∀ S, w S * u S * u S = w S * (if B S then f S * f S else 0) := by
    intro S
    rw [show w S * u S * u S = w S * (u S * u S) from by ring, huu S]
  have hc3 : ∀ S, w S * v S * v S = w S * v S := by
    intro S
    rw [show w S * v S * v S = w S * (v S * v S) from by ring, hvv S]
  have hu' : sampleExpect fairCoin u =
      ∑ S, w S * u S * v S := by
    rw [Finset.sum_congr rfl (fun S _ => (hc1 S).symm)]
    rfl
  have hf2' : sampleExpect fairCoin (fun S => if B S then f S * f S else 0) =
      ∑ S, w S * u S * u S := by
    rw [Finset.sum_congr rfl (fun S _ => hc2 S)]
    rfl
  have hv' : probEvt B = ∑ S, w S * v S * v S := by
    rw [Finset.sum_congr rfl (fun S _ => hc3 S)]
    simp only [probEvt, PacLearning.sampleExpect, hv, hwdef]
  show (sampleExpect fairCoin u) ^ 2 ≤ _ * probEvt B
  rw [hu', hf2', hv']
  exact hkey

/-- **Corollaire coloration — minoration de queue (Paley–Zygmund)** :
pour une coloration `±1` et `n ≥ 1`, la probabilité que `Z² ≥ n/2`
vaut au moins `1/12`. Dérivation : `E[Z²] = n` se scinde en
`E[Z²·1_A] + E[Z²·1_Ac]` ; sur `A^c`, `Z² < n/2` ; Cauchy–Schwarz
`(E[Z²·1_A])² ≤ E[Z⁴]·P[A]` avec `E[Z⁴] = 3n²−2n ≤ 3n²` donne
`(n/2)² ≤ 3n²·P[A]`, soit `P[A] ≥ 1/12`. -/
theorem prob_tail_ge_of_isColoring {n : ℕ} (c : Fin n → ℤ) (hc : IsColoring c)
    (hn : 1 ≤ n) :
    probEvt (fun S => (n : ℝ) / 2 ≤ rademacherSum c S * rademacherSum c S) ≥ 1 / 12 := by
  classical
  set A : (Fin n → Bool) → Prop :=
    fun S => (n : ℝ) / 2 ≤ rademacherSum c S * rademacherSum c S with hA
  set Z : (Fin n → Bool) → ℝ := rademacherSum c with hZ
  -- Étape 1 : E[Z^2] = n (moments p1a)
  have hE2 : sampleExpect fairCoin (fun S => Z S * Z S) = (n : ℝ) := by
    have h := expect_rademacherSum_sq_of_isColoring c hc
    have hconv : (fun S : Fin n → Bool => rademacherSum c S ^ 2) =
        (fun S : Fin n → Bool => rademacherSum c S * rademacherSum c S) := by
      funext S
      rw [pow_two]
    rw [hconv] at h
    exact h
  -- Étape 2 : scindage E[Z^2] = E[Z^2·1_A] + E[Z^2·1_Ac]
  have hsplit := sampleExpect_split_indicator (fun S => Z S * Z S) A
  -- Étape 3 : sur A^c, Z^2 < n/2, donc E[Z^2·1_Ac] ≤ n/2 (poids total 1)
  have hAc_le : sampleExpect fairCoin (fun S => if ¬A S then Z S * Z S else 0)
      ≤ (n : ℝ) / 2 := by
    have hbound : sampleExpect fairCoin (fun S => if ¬A S then Z S * Z S else 0) ≤
        sampleExpect fairCoin (fun S => if ¬A S then (n : ℝ) / 2 else 0) := by
      apply PacLearning.sampleExpect_mono
      intro S
      by_cases hS : ¬A S
      · show (if ¬A S then rademacherSum c S * rademacherSum c S else 0) ≤
            if ¬A S then (n : ℝ) / 2 else 0
        rw [if_pos hS, if_pos hS]
        exact le_of_lt (lt_of_not_ge hS)
      · show (if ¬A S then Z S * Z S else 0) ≤ if ¬A S then (n : ℝ) / 2 else 0
        rw [if_neg hS, if_neg hS]
    have hconst : sampleExpect fairCoin (fun S => if ¬A S then (n : ℝ) / 2 else 0)
        = ((n : ℝ) / 2) * probEvt (fun S => ¬A S) := by
      rw [show ((n : ℝ) / 2) * probEvt (fun S => ¬A S) =
          sampleExpect fairCoin (fun S => (n : ℝ) / 2 *
            (if ¬A S then (1 : ℝ) else 0)) from by
        rw [PacLearning.sampleExpect_smul]
        rfl]
      apply congrArg
      funext S
      by_cases hS : ¬A S
      · simp only [if_pos hS, mul_one]
      · simp only [if_neg hS, mul_zero]
    refine le_trans hbound ?_
    rw [hconst]
    have hp : probEvt (fun S => ¬A S) ≤ 1 := by
      have hle : sampleExpect fairCoin (fun S => if ¬A S then (1 : ℝ) else 0) ≤
          sampleExpect fairCoin (fun S : Fin n → Bool => (1 : ℝ)) := by
        apply PacLearning.sampleExpect_mono
        intro S
        show (if ¬A S then (1 : ℝ) else 0) ≤ 1
        by_cases hS : ¬A S
        · rw [if_pos hS]
        · rw [if_neg hS]
          exact zero_le_one
      have hone : sampleExpect fairCoin (fun S : Fin n → Bool => (1 : ℝ)) = 1 := by
        simp only [PacLearning.sampleExpect, mul_one]
        exact PacLearning.sampleWeight_sum_one (D := fairCoin) n
      exact hle.trans (le_of_eq hone)
    nlinarith [hp]
  -- Étape 4 : donc E[Z^2·1_A] ≥ n/2
  have hEA_ge : (n : ℝ) / 2 ≤ sampleExpect fairCoin (fun S => if A S then Z S * Z S else 0) := by
    linarith [hsplit, hE2, hAc_le]
  -- Étape 5 : Cauchy (E[Z^2·1_A])^2 <= E[Z^4]·P[A], E[Z^4] = 3n^2-2n <= 3n^2
  have hcauchy := expect_sq_le_mul_prob Z A
  have hE4 : sampleExpect fairCoin (fun S => Z S * Z S * (Z S * Z S)) =
      3 * (n : ℝ) ^ 2 - 2 * (n : ℝ) := by
    have h := expect_rademacherSum_fourth_moment_of_isColoring c hc
    have hconv : (fun S : Fin n → Bool => rademacherSum c S ^ 4) =
        (fun S : Fin n → Bool => rademacherSum c S * rademacherSum c S *
          (rademacherSum c S * rademacherSum c S)) := by
      funext S
      ring
    rw [hconv] at h
    exact h
  -- Final : (n/2)^2 <= E[Z^4]·P[A] <= 3n^2·P[A]  =>  P[A] >= 1/12
  have hcauchy2 : (sampleExpect fairCoin (fun S => if A S then Z S else 0)) ^ 2 ≤
      sampleExpect fairCoin (fun S => if A S then Z S * Z S else 0) * probEvt A :=
    hcauchy
  have hmono : sampleExpect fairCoin (fun S => if A S then Z S * Z S * (Z S * Z S) else 0) ≤
      sampleExpect fairCoin (fun S => Z S * Z S * (Z S * Z S)) := by
    apply PacLearning.sampleExpect_mono
    intro S
    by_cases hS : A S
    · simp only [if_pos hS, le_refl]
    · simp only [if_neg hS]
      have hZ2 : 0 ≤ Z S * Z S := mul_self_nonneg _
      nlinarith [hZ2]
  -- hcauchy adapté à f := Z² : (E[Z²·1_A])² ≤ E[Z⁴·1_A]·P[A]
  have hcauchy2 := expect_sq_le_mul_prob (fun S => Z S * Z S) A
  -- E[Z⁴·1_A] ≤ E[Z⁴] (mono, hmono ci-dessus)
  -- (E[Z²·1_A])² = (≥ n/2)² = n²/4 ≤ 3n²·P[A]  (E[Z⁴] ≤ 3n² car 3n²-2n ≤ 3n²)
  have hE4bound : sampleExpect fairCoin (fun S => Z S * Z S * (Z S * Z S)) ≤
      3 * (n : ℝ) ^ 2 := by
    rw [hE4]
    have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hbound : 3 * (n : ℝ) ^ 2 - 2 * (n : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by
      nlinarith [hnR]
    exact hbound
  have hP0 : 0 ≤ probEvt A := by
    have hle : sampleExpect fairCoin (fun S : Fin n → Bool => (0 : ℝ)) ≤
        sampleExpect fairCoin (fun S => if A S then (1 : ℝ) else 0) :=
      PacLearning.sampleExpect_mono (fun S => by
        by_cases hS : A S
        · simp only [if_pos hS, zero_le_one]
        · simp only [if_neg hS, le_refl])
    have h0 : sampleExpect fairCoin (fun S : Fin n → Bool => (0 : ℝ)) = 0 := by
      rw [PacLearning.sampleExpect_const]
    rw [h0] at hle
    rw [show probEvt A = sampleExpect fairCoin (fun S => if A S then (1 : ℝ) else 0) from rfl]
    exact hle
  have hkey : (sampleExpect fairCoin (fun S => if A S then Z S * Z S else 0)) ^ 2 ≤
      3 * (n : ℝ) ^ 2 * probEvt A := by
    have h1 := hcauchy2
    have h2' : sampleExpect fairCoin (fun S => if A S then Z S * Z S * (Z S * Z S) else 0) ≤
        3 * (n : ℝ) ^ 2 := hmono.trans hE4bound
    nlinarith [h1, h2', hP0]
  -- n/2 ≤ E[Z²·1_A] → n²/4 ≤ (E[Z²·1_A])² ≤ 3n²·P[A] → P ≥ 1/12
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hEA0 : 0 ≤ sampleExpect fairCoin (fun S => if A S then Z S * Z S else 0) := by
    have hle : sampleExpect fairCoin (fun S : Fin n → Bool => (0 : ℝ)) ≤
        sampleExpect fairCoin (fun S => if A S then Z S * Z S else 0) := by
      apply PacLearning.sampleExpect_mono
      intro S
      show (0 : ℝ) ≤ if A S then Z S * Z S else 0
      by_cases hS : A S
      · simp only [if_pos hS]
        exact mul_self_nonneg _
      · simp only [if_neg hS, le_refl]
    have h0 : sampleExpect fairCoin (fun S : Fin n → Bool => (0 : ℝ)) = 0 := by
      rw [PacLearning.sampleExpect_const]
    rw [h0] at hle
    exact hle
  have hsqge : ((n : ℝ) / 2) ^ 2 ≤
      (sampleExpect fairCoin (fun S => if A S then Z S * Z S else 0)) ^ 2 := by
    nlinarith [hEA_ge, hEA0]
  have hfinal : ((n : ℝ) / 2) ^ 2 ≤ 3 * (n : ℝ) ^ 2 * probEvt A :=
    hsqge.trans hkey
  have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := by
    nlinarith [hn0]
  have hdiv : (1 : ℝ) / 12 ≤ probEvt A := by
    have hexp : ((n : ℝ) / 2) ^ 2 = (n : ℝ) ^ 2 / 4 := by
      rw [div_pow]
      norm_num
    rw [hexp, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)] at hfinal
    -- hfinal : n^2 ≤ 3 n^2 P * 4 = 12 n^2 P ; n^2 > 0 → P ≥ 1/12
    nlinarith [hfinal, hn2pos]
  exact hdiv

end Moments

/-!
## Boute p2 - familles de tirages independants

L'etape familles aleatoires d'Erdos-Spencer : m tirages independants
de n pieces forment l'espace Fin m -> Fin n -> Bool. L'esperance s'y
calcule en reutilisant le kernel PacLearning au-dessus de la distribution
produit coinDist (le poids d'un n-echantillon, vu comme une
Distribution (Fin n -> Bool) a part entiere). Le lemme cle est
l'independance des blocs (Fubini discret, via Fintype.prod_sum) :
E[prod_k f k (F k)] = prod_k E[f k]. Combinee a la minoration de queue
d'un tirage isole (prob_tail_ge_of_isColoring), elle donne : une famille
de m tirages contient un tirage de grande somme avec probabilite
>= 1 - (11/12)^m - l'ingredient familles du second passage
probabiliste (p3 : union bound sur les 2^n colorations).
-/

section Families

open PacLearning

/-- **Distribution produit** : un n-echantillon de pieces equitables,
vu comme une Distribution (Fin n -> Bool) a part entiere (poids =
sampleWeight fairCoin). Emboiter sampleExpect coinDist au-dessus
modelise une famille de m tirages independants - l'espace des
familles aleatoires d'Erdos-Spencer. -/
noncomputable def coinDist {n : ℕ} : Distribution (Fin n → Bool) where
  weight := sampleWeight fairCoin
  nonneg := sampleWeight_nonneg (D := fairCoin)
  sum_one := sampleWeight_sum_one (D := fairCoin) n

/-- **Esperance sur les familles** : m tirages independants de n
pieces (loi produit coinDist^m). -/
noncomputable def familyExpect {m n : ℕ} (g : (Fin m → Fin n → Bool) → ℝ) : ℝ :=
  sampleExpect coinDist g

/-- **Independance des blocs (Fubini discret)** : l'esperance, sur les
familles, d'un produit de fonctions dependant chacune d'un seul tirage
F k se factorise en le produit des esperances. C'est ce lemme qui rend
les m tirages independants ; il decoule de la distributivite
produit/somme (Fintype.prod_sum) appliquee aux poids produits. -/
theorem familyExpect_prod_blocks {m n : ℕ} (f : Fin m → (Fin n → Bool) → ℝ) :
    familyExpect (fun F => ∏ k, f k (F k)) =
      ∏ k, sampleExpect fairCoin (f k) := by
  show ∑ F : Fin m → Fin n → Bool,
      (∏ k, sampleWeight fairCoin (F k)) * ∏ k, f k (F k) = _
  calc ∑ F : Fin m → Fin n → Bool,
        (∏ k, sampleWeight fairCoin (F k)) * ∏ k, f k (F k)
      = ∑ F : Fin m → Fin n → Bool,
          ∏ k, sampleWeight fairCoin (F k) * f k (F k) :=
        Finset.sum_congr rfl fun F _ => Finset.prod_mul_distrib.symm
    _ = ∏ k : Fin m, ∑ S : Fin n → Bool, sampleWeight fairCoin S * f k S :=
        (Fintype.prod_sum fun (k : Fin m) (S : Fin n → Bool) =>
          sampleWeight fairCoin S * f k S).symm
    _ = ∏ k, sampleExpect fairCoin (f k) := by
        simp only [PacLearning.sampleExpect]

/-- **Additivite** de l'esperance sur les familles (complement kernel,
meme preuve que sampleExpect_add). -/
theorem familyExpect_add {m n : ℕ} (g h : (Fin m → Fin n → Bool) → ℝ) :
    familyExpect (fun F => g F + h F) = familyExpect g + familyExpect h := by
  simp only [familyExpect, PacLearning.sampleExpect, mul_add,
    Finset.sum_add_distrib]

/-- **Normalisation** : l'esperance famille de la constante 1 vaut 1
(la masse totale des familles vaut 1). -/
theorem familyExpect_one {m n : ℕ} :
    familyExpect (fun _ : Fin m → Fin n → Bool => (1 : ℝ)) = 1 := by
  simp only [familyExpect, PacLearning.sampleExpect, mul_one]
  exact sampleWeight_sum_one (D := coinDist) m

/-- **Probabilite d'un evenement sur les familles** (cadre R-weight,
meme convention que probEvt). -/
noncomputable def familyProb {m n : ℕ} (P : (Fin m → Fin n → Bool) → Prop)
    [DecidablePred P] : ℝ :=
  familyExpect (fun F => if P F then 1 else 0)

/-- **Loi du complementaire sur les familles** : toute famille est soit
dans l'evenement, soit dans son complementaire (les indicatrices se
completent en 1). -/
theorem familyProb_compl {m n : ℕ} (P : (Fin m → Fin n → Bool) → Prop)
    [DecidablePred P] :
    familyProb P + familyProb (fun F => ¬ P F) = 1 := by
  have hfun : (fun F : Fin m → Fin n → Bool =>
        (if P F then (1 : ℝ) else 0) + (if ¬ P F then (1 : ℝ) else 0)) =
      (fun _ : Fin m → Fin n → Bool => (1 : ℝ)) := by
    funext F
    by_cases hF : P F
    · simp only [if_pos hF, if_neg (fun h : ¬ P F => h hF), add_zero]
    · simp only [if_neg hF, if_pos hF, zero_add]
  show familyExpect (fun F => if P F then (1 : ℝ) else 0) +
      familyExpect (fun F => if ¬ P F then (1 : ℝ) else 0) = 1
  rw [← familyExpect_add, hfun]
  exact familyExpect_one

/-- **Minoration de queue pour les familles** : si un tirage isole
atteint Z_S^2 >= n/2 avec probabilite >= 1/12 (boute p1b-PZ-2), alors
une famille de m tirages independants en contient au moins un avec
probabilite >= 1 - (11/12)^m. Preuve : la probabilite du complementaire
(aucun tirage n'atteint le seuil) est l'esperance d'un produit
d'indicatrices, qui se factorise par independance des blocs en
(11/12)^m. -/
theorem family_tail_ge {m n : ℕ} (c : Fin n → ℤ) (hc : IsColoring c) (hn : 1 ≤ n) :
    1 - (11 / 12 : ℝ) ^ m ≤
      familyProb (fun F => ∃ k : Fin m, (n : ℝ) / 2 ≤
        rademacherSum c (F k) * rademacherSum c (F k)) := by
  classical
  set A : (Fin n → Bool) → Prop :=
    fun S => (n : ℝ) / 2 ≤ rademacherSum c S * rademacherSum c S with hA
  have hptail : (1 : ℝ) / 12 ≤ probEvt A := prob_tail_ge_of_isColoring c hc hn
  -- Facteur : E[1_Ac] = 1 - P[A] <= 11/12 (scission de la constante 1)
  have hfactor : sampleExpect fairCoin (fun S => if A S then (0 : ℝ) else 1)
      ≤ 11 / 12 := by
    have hsplit1 := sampleExpect_split_indicator (fun _ : Fin n → Bool => (1 : ℝ)) A
    have hL : sampleExpect fairCoin (fun _ : Fin n → Bool => (1 : ℝ)) = 1 := by
      rw [PacLearning.sampleExpect_const]
    have hAind : sampleExpect fairCoin (fun S => if A S then (1 : ℝ) else 0)
        = probEvt A := rfl
    have hG : sampleExpect fairCoin (fun S => if ¬ A S then (1 : ℝ) else 0) =
        sampleExpect fairCoin (fun S => if A S then (0 : ℝ) else 1) := by
      congr 1
      funext S
      by_cases hS : A S
      · simp only [if_neg (fun h : ¬ A S => h hS), if_pos hS]
      · simp only [if_pos hS, if_neg hS]
    rw [hL, hAind, hG] at hsplit1
    linarith
  have hgnn : 0 ≤ sampleExpect fairCoin (fun S => if A S then (0 : ℝ) else 1) := by
    apply PacLearning.sampleExpect_nonneg
    intro S
    by_cases hS : A S
    · simp only [if_pos hS, le_refl]
    · simp only [if_neg hS]
      norm_num
  -- Complementaire : P[aucun tirage] = E[prod_k 1_Ac(F k)] = prod E[1_Ac] <= (11/12)^m
  have hfun : (fun F : Fin m → Fin n → Bool => if ¬ ∃ k : Fin m, A (F k) then (1 : ℝ) else 0) =
      (fun F => ∏ k, (if A (F k) then (0 : ℝ) else 1)) := by
    funext F
    by_cases hE : ∃ k : Fin m, A (F k)
    · rw [if_neg (fun h : ¬ ∃ k : Fin m, A (F k) => h hE)]
      obtain ⟨k₀, hk₀⟩ := hE
      refine Eq.symm (Finset.prod_eq_zero (Finset.mem_univ k₀) ?_)
      rw [if_pos hk₀]
    · rw [if_pos hE]
      exact (calc ∏ k, (if A (F k) then (0 : ℝ) else 1) = ∏ k : Fin m, (1 : ℝ) :=
          Finset.prod_congr rfl fun k _ =>
            if_neg fun hk : A (F k) => hE ⟨k, hk⟩
        _ = 1 := Finset.prod_const_one).symm
  have hblocks : familyExpect (fun F => ∏ k, (if A (F k) then (0 : ℝ) else 1)) =
      ∏ k, sampleExpect fairCoin (fun S => if A S then (0 : ℝ) else 1) :=
    familyExpect_prod_blocks fun _ : Fin m => fun S => if A S then (0 : ℝ) else 1
  have hcompl : familyExpect (fun F => if ¬ ∃ k : Fin m, A (F k) then (1 : ℝ) else 0)
      ≤ (11 / 12 : ℝ) ^ m := by
    rw [hfun, hblocks]
    calc ∏ k : Fin m, sampleExpect fairCoin (fun S => if A S then (0 : ℝ) else 1)
        ≤ ∏ k : Fin m, (11 / 12 : ℝ) :=
          Finset.prod_le_prod (fun k _ => hgnn) fun k _ => hfactor
      _ = (11 / 12 : ℝ) ^ m := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hlaw : familyExpect (fun F => if ∃ k : Fin m, A (F k) then (1 : ℝ) else 0) +
      familyExpect (fun F => if ¬ ∃ k : Fin m, A (F k) then (1 : ℝ) else 0) = 1 :=
    familyProb_compl (fun F => ∃ k : Fin m, A (F k))
  have hgoal : 1 - (11 / 12 : ℝ) ^ m ≤
      familyProb (fun F => ∃ k : Fin m, A (F k)) := by
    show 1 - (11 / 12 : ℝ) ^ m ≤
      familyExpect (fun F => if ∃ k : Fin m, A (F k) then (1 : ℝ) else 0)
    linarith
  exact hgoal

end Families

/-!
## Boute p3 - union bound sur les colorations

Le second passage probabiliste d'Erdos-Spencer : une famille aleatoire
de m tirages doit COUVRIR toutes les 2^n colorations simultanement.
Pour chaque coloration fixee, la famille la rate avec probabilite
<= (11/12)^m (boute p2) ; l'union bound donne
P[une coloration echappe] <= 2^n (11/12)^m. Pour m = 12 n,
(11/12)^12 < 1/2 donc 2^n (11/12)^(12n) < 1 : avec probabilite
strictement positive la famille bat TOUTES les colorations, et une
esperance d'indicatrice strictement positive force l'existence d'un
temoin - le passage probabiliste existential.

Remarque structurelle : `Fin n -> Z` n'est PAS un Fintype (Z infini),
les colorations sont donc denombrees comme IMAGE des `2^n` booleens
par `colorOf` (b mappe a la coloration i |-> if b i then 1 else -1).
-/

section UnionBound

open PacLearning

/-- **Encodage d'un booleen en coloration** : chaque vecteur booleen
donne une coloration ±1 ; tout l'espace des colorations est l'image
de `Fin n -> Bool` (de cardinal 2^n) par cette application. -/
def colorOf {n : ℕ} (b : Fin n → Bool) : Fin n → ℤ :=
  fun i => if b i then (1 : ℤ) else -1

open Classical in
/-- **Union bound ponctuel** : l'indicatrice d'une union existentielle
finie est majoree par la somme des indicatrices (point par point). -/
theorem indicator_bUnion_le_sum {ια α : Type*} [DecidableEq ια] (s : Finset ια)
    (P : ια → α → Prop) [∀ j, DecidablePred (P j)] (x : α) :
    (if ∃ j ∈ s, P j x then (1 : ℝ) else 0) ≤
      ∑ j ∈ s, (if P j x then (1 : ℝ) else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      by_cases h : ∃ j ∈ (∅ : Finset ια), P j x
      · exact absurd h (by rintro ⟨j, hj, _⟩; simp at hj)
      · rw [if_neg h]
  | @insert j t hj IH =>
      rw [Finset.sum_insert hj]
      by_cases hP : P j x
      · rw [if_pos ⟨j, Finset.mem_insert_self _ _, hP⟩, if_pos hP]
        exact le_add_of_nonneg_right
          (Finset.sum_nonneg fun _ _ => by positivity)
      · have hEx : (∃ j' ∈ insert j t, P j' x) ↔ ∃ j' ∈ t, P j' x := by
          constructor
          · rintro ⟨j', hj', hPj'⟩
            by_cases hjj : j' = j
            · subst hjj; exact absurd hPj' hP
            · exact ⟨j', (Finset.mem_insert.mp hj').resolve_left hjj, hPj'⟩
          · rintro ⟨j', hj', hPj'⟩
            exact ⟨j', Finset.mem_insert_of_mem hj', hPj'⟩
        simp only [hEx]
        rw [if_neg hP, zero_add]
        exact IH

/-- **Linearite en un Finset** : l'esperance famille d'une somme indexee
par un Finset (pas seulement un type) est la somme des esperances -
meme preuve que le kernel `sampleExpect_sum` (`mul_sum` + `sum_comm`). -/
theorem familyExpect_sum_finset {m n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → (Fin m → Fin n → Bool) → ℝ) :
    familyExpect (fun F => ∑ j ∈ s, f j F) = ∑ j ∈ s, familyExpect (f j) := by
  simp only [familyExpect, PacLearning.sampleExpect, Finset.mul_sum]
  exact Finset.sum_comm

open Classical in
/-- **Union bound en probabilite** : la probabilite (sur les familles)
qu'il EXISTE une coloration de `s` satisfaisant `B` est majoree par la
somme des probabilites individuelles. -/
theorem familyProb_union_le {m n : ℕ} (s : Finset (Fin n → ℤ))
    (B : (Fin n → ℤ) → (Fin m → Fin n → Bool) → Prop) [∀ c, DecidablePred (B c)] :
    familyProb (fun F => ∃ c ∈ s, B c F) ≤ ∑ c ∈ s, familyProb (B c) := by
  have h1 : familyExpect (fun F => if ∃ c ∈ s, B c F then (1 : ℝ) else 0) ≤
      familyExpect (fun F => ∑ c ∈ s, (if B c F then (1 : ℝ) else 0)) :=
    PacLearning.sampleExpect_mono (D := coinDist) (g' := fun F =>
      ∑ c ∈ s, (if B c F then (1 : ℝ) else 0))
      (fun F => indicator_bUnion_le_sum s B F)
  rw [familyExpect_sum_finset s (fun c F => if B c F then (1 : ℝ) else 0)] at h1
  exact h1

/-- **Cardinal des colorations** : l'image des booleens par `colorOf`
(qui contient toutes les colorations) a un cardinal <= `2^n`. -/
theorem card_colorings_le (n : ℕ) :
    ((Finset.univ : Finset (Fin n → Bool)).image colorOf).card ≤ 2 ^ n := by
  calc ((Finset.univ : Finset (Fin n → Bool)).image colorOf).card
      ≤ (Finset.univ : Finset (Fin n → Bool)).card :=
        Finset.card_image_le
    _ = 2 ^ n := by simp

/-- **Le temoin existentiel** : une probabilite strictement positive
force l'existence d'un point ou l'evenement tient. -/
theorem exists_of_familyProb_pos {m n : ℕ} (P : (Fin m → Fin n → Bool) → Prop)
    [DecidablePred P] (hP : 0 < familyProb P) : ∃ F, P F := by
  by_contra h
  push_neg at h
  have hz : familyProb P = 0 := by
    show ∑ F : Fin m → Fin n → Bool,
        PacLearning.sampleWeight coinDist F * (if P F then (1 : ℝ) else 0) = 0
    exact Finset.sum_eq_zero fun F _ => by
      rw [if_neg (h F), mul_zero]
  linarith

open Classical in
/-- **Une famille de 12n tirages bat toutes les colorations** : pour
`n ≥ 1`, il existe une famille `F` de `12n` tirages telle que CHAQUE
coloration `c` est atteinte par un tirage de `F`
(`Z_{c,F k}² ≥ n/2`). C'est le passage probabiliste existential :
le complementaire (une coloration echappe) a une probabilite
`≤ 2^n (11/12)^{12n} < 1` par union bound sur les `≤ 2^n` colorations. -/
theorem exists_family_beats_all_colorings {n : ℕ} (hn : 1 ≤ n) :
    ∃ F : Fin (12 * n) → Fin n → Bool,
      ∀ c : Fin n → ℤ, IsColoring c →
        ∃ k : Fin (12 * n), (n : ℝ) / 2 ≤
          rademacherSum c (F k) * rademacherSum c (F k) := by
  set m := 12 * n with hm
  set s : Finset (Fin n → ℤ) :=
    (Finset.univ : Finset (Fin n → Bool)).image colorOf with hs
  -- Toute coloration est dans l'image ; tout element de l'image est
  -- une coloration.
  have hmem : ∀ c : Fin n → ℤ, IsColoring c → c ∈ s := by
    intro c hc
    refine Finset.mem_image.mpr ⟨fun i => decide (c i = 1), Finset.mem_univ _, ?_⟩
    funext i
    rcases hc i with h | h <;> simp [colorOf, h]
  have hcoloring : ∀ c ∈ s, IsColoring c := by
    intro c hc
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hc
    subst hb
    intro i
    rcases hbi : b i with _ | _ <;> simp [colorOf, hbi]
  -- (1) une coloration fixee echappe avec probabilite <= (11/12)^m
  have hmiss : ∀ c ∈ s,
      familyProb (fun F => ¬ ∃ k : Fin m, (n : ℝ) / 2 ≤
        rademacherSum c (F k) * rademacherSum c (F k)) ≤ (11 / 12 : ℝ) ^ m := by
    intro c hc
    have hhit : 1 - (11 / 12 : ℝ) ^ m ≤ familyProb
        (fun F => ∃ k : Fin m, (n : ℝ) / 2 ≤
          rademacherSum c (F k) * rademacherSum c (F k)) :=
      family_tail_ge (m := m) c (hcoloring c hc) hn
    have hlaw : familyProb
        (fun F => ∃ k : Fin m, (n : ℝ) / 2 ≤
          rademacherSum c (F k) * rademacherSum c (F k)) +
        familyProb (fun F => ¬ ∃ k : Fin m, (n : ℝ) / 2 ≤
          rademacherSum c (F k) * rademacherSum c (F k)) = 1 :=
      familyProb_compl (fun F => ∃ k : Fin m, (n : ℝ) / 2 ≤
        rademacherSum c (F k) * rademacherSum c (F k))
    linarith
  -- (2) union bound + numerie : P[une coloration echappe] < 1
  have hmissall : familyProb (fun F => ∃ c ∈ s, ¬ ∃ k : Fin m, (n : ℝ) / 2 ≤
      rademacherSum c (F k) * rademacherSum c (F k)) < 1 := by
    have hkey : ((11 : ℝ) / 12) ^ 12 < 1 / 2 := by norm_num
    have hy : (2 : ℝ) * ((11 / 12 : ℝ) ^ 12) < 1 := by linarith
    have hy0 : (0 : ℝ) ≤ 2 * ((11 / 12 : ℝ) ^ 12) := by positivity
    -- numerie : (2 * (11/12)^12)^n < 1 par induction (base < 1, >= 0)
    have hpn : ∀ t : ℕ, 0 < t →
        (2 * ((11 / 12 : ℝ) ^ 12)) ^ t < 1 := by
      intro t
      induction t with
      | zero => simp
      | succ t IH =>
          intro _
          rcases Nat.eq_zero_or_pos t with ht | ht
          · subst ht
            simpa using hy
          · rw [pow_succ']
            have hx1 : (2 * ((11 / 12 : ℝ) ^ 12)) ^ t ≤ 1 := le_of_lt (IH ht)
            have h2 := mul_le_mul_of_nonneg_left hx1 hy0
            linarith
    have hpow : ((11 / 12 : ℝ) ^ 12) ^ n = (11 / 12 : ℝ) ^ m := by
      rw [hm]
      exact (pow_mul _ 12 n).symm
    have hfin : (2 : ℝ) ^ n * (11 / 12 : ℝ) ^ m < 1 := by
      rw [← hpow, ← mul_pow]
      exact hpn n (by omega)
    have hcardR : (↑s.card : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast card_colorings_le n
    have hX : (0 : ℝ) ≤ (11 / 12 : ℝ) ^ m := by positivity
    calc familyProb (fun F => ∃ c ∈ s, ¬ ∃ k : Fin m, (n : ℝ) / 2 ≤
          rademacherSum c (F k) * rademacherSum c (F k))
        ≤ ∑ c ∈ s, familyProb (fun F => ¬ ∃ k : Fin m, (n : ℝ) / 2 ≤
            rademacherSum c (F k) * rademacherSum c (F k)) :=
          familyProb_union_le (m := m) s
            (fun c F => ¬ ∃ k : Fin m, (n : ℝ) / 2 ≤
              rademacherSum c (F k) * rademacherSum c (F k))
      _ ≤ ∑ c ∈ s, (11 / 12 : ℝ) ^ m :=
          Finset.sum_le_sum fun c hc => hmiss c hc
      _ = ↑s.card * (11 / 12 : ℝ) ^ m := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ n * (11 / 12 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_right hcardR hX
      _ < 1 := hfin
  -- (3) le bon evenement a une probabilite > 0, donc un temoin existe
  have hgoodpos : 0 < familyProb (fun F => ¬ ∃ c ∈ s, ¬ ∃ k : Fin m, (n : ℝ) / 2 ≤
      rademacherSum c (F k) * rademacherSum c (F k)) := by
    have hlaw : familyProb (fun F => ∃ c ∈ s, ¬ ∃ k : Fin m, (n : ℝ) / 2 ≤
        rademacherSum c (F k) * rademacherSum c (F k)) +
        familyProb (fun F => ¬ ∃ c ∈ s, ¬ ∃ k : Fin m, (n : ℝ) / 2 ≤
          rademacherSum c (F k) * rademacherSum c (F k)) = 1 :=
      familyProb_compl (fun F => ∃ c ∈ s, ¬ ∃ k : Fin m, (n : ℝ) / 2 ≤
        rademacherSum c (F k) * rademacherSum c (F k))
    linarith
  obtain ⟨F, hF⟩ := exists_of_familyProb_pos (m := m) _ hgoodpos
  refine ⟨F, fun c hc => ?_⟩
  by_contra hno
  exact hF ⟨c, hmem c hc, hno⟩

end UnionBound

end Discrepancy
