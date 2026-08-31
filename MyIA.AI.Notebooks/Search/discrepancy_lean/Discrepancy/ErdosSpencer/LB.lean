import Mathlib
import Discrepancy.ErdosSpencer.Moments
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
4. **Contrôle du degré** (boute `p4`) : chaque tirage `j` contribue la
   PAIRE `(drawSet, bloc \ drawSet)` des coordonnées vraies / fausses
   d'un bloc de `t = k / 12` points — la paire désamorce le déséquilibre
   `∑ c` par triangulaire, et le degré de tout point est au plus le
   nombre de paires `12 t ≤ k`. Constante explicite obtenue : `√k / 14` ;
   la version optimiste `√k / 2` reste une `Prop` ouverte.

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

/-!
**Statut (08-26)** : cette forme « constante 1/2 » est OUVERTE — la
méthode des moments (Paley–Zygmund, hit 1/12) force `m ≥ 12 t` tirages
pour vaincre les `2^t` colorations alors que le degré exige `m ≤ k` :
le quotient est structurellement borné. La version PROUVÉE à constante
explicite est `erdos_spencer_lb_explicit` (`√k / 14`).
-/

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

/-!
## Boute p4 - controle du degre et assemblage

La derniere etape : convertir la famille probabiliste de `12 t` tirages
(boute p3) en famille de DEGRE <= k. Deux mecanismes :

1. **Desequilibre** : la somme de Rademacher `Z = 2x - s` (x = somme de
   l'ensemble des coordonnees vraies, s = somme du bloc) n'est pas une
   somme d'ensemble. En incluant la PAIRE `(drawSet, bloc \ drawSet)`
   de chaque tirage, la triangulaire `|Z| = |x + (x - s)| <= |x| + |x - s|`
   rend les deux membres controlables par la discrepance, chacun etant
   la somme coloree d'un ensemble de la famille.
2. **Degre** : `drawSet` et son complementaire relatif au bloc etant
   DISJOINTS, chaque paire contient un point donne au plus une fois :
   le degre de tout point est majore par le nombre de tirages (injection
   vers `Fin m` par choix classique et disjointness).

Constante finale : `disc >= |Z| / 2 >= sqrt(t/8)` avec `k <= 23 t`
(reste de la division par 12 absorbe), d'ou `Nat.sqrt k <= 14 * disc`.
Pour `k < 12` : singletons (degre 1, discrepance 1, `sqrt k <= 4`).
-/

section DegreeControl

open PacLearning

/-- **Identite Rademacher / sommes d'ensembles** : la somme de Rademacher
coloree est deux fois la somme sur les coordonnees vraies moins la somme
totale - le pont entre l'alea signe des boutes p1-p3 et les sommes
d'ensembles de la definition `discrepancy`. -/
theorem rademacherSum_eq_two_sub {t : ℕ} (c : Fin t → ℤ) (σ : Fin t → Bool) :
    rademacherSum c σ =
      2 * ((Finset.univ.filter (fun q => σ q = true)).sum fun q => (c q : ℝ)) -
        (Finset.univ.sum fun q => (c q : ℝ)) := by
  classical
  have hsplit : (Finset.univ.filter (fun q => σ q = true)).sum
        (fun q => (c q : ℝ)) +
      (Finset.univ.filter (fun q => ¬ (σ q = true))).sum (fun q => (c q : ℝ)) =
      (Finset.univ.sum fun q => (c q : ℝ)) :=
    Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin t))
      (fun q => σ q = true) (fun q => (c q : ℝ))
  have hlhs : rademacherSum c σ =
      (Finset.univ.filter (fun q => σ q = true)).sum (fun q => (c q : ℝ)) -
      (Finset.univ.filter (fun q => ¬ (σ q = true))).sum (fun q => (c q : ℝ)) := by
    rw [rademacherSum,
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin t))
        (fun q => σ q = true)
        (fun q => (c q : ℝ) * boolSign (σ q))]
    have h1 : (Finset.univ.filter (fun q => σ q = true)).sum
        (fun q => (c q : ℝ) * boolSign (σ q)) =
        (Finset.univ.filter (fun q => σ q = true)).sum (fun q => (c q : ℝ)) := by
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Finset.mem_filter] at hq
      simp only [boolSign, if_pos hq.2, mul_one]
    have h2m : ∀ q ∈ (Finset.univ.filter (fun q => ¬ (σ q = true)) :
        Finset (Fin t)), (c q : ℝ) * boolSign (σ q) = -((c q : ℝ)) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      simp only [boolSign, if_neg hq.2, mul_neg_one]
    have h2 : (Finset.univ.filter (fun q => ¬ (σ q = true))).sum
        (fun q => (c q : ℝ) * boolSign (σ q)) =
        -((Finset.univ.filter (fun q => ¬ (σ q = true))).sum
          (fun q => (c q : ℝ))) := by
      rw [Finset.sum_congr rfl h2m, Finset.sum_neg_distrib]
    rw [h1, h2]
    ring
  linarith [hsplit, hlhs]

/-- **Le bloc** : image des `t` premiers points dans `Fin n`
(injection `Fin.castLEEmb`). -/
def blockOf {t n : ℕ} (htn : t ≤ n) : Finset (Fin n) :=
  Finset.univ.map (Fin.castLEEmb htn)

/-- **L'ensemble d'un tirage** : coordonnees vraies du tirage `sigma`,
transportees dans `Fin n`. -/
def drawSet {t n : ℕ} (htn : t ≤ n) (σ : Fin t → Bool) : Finset (Fin n) :=
  (Finset.univ.filter (fun q => σ q = true)).map (Fin.castLEEmb htn)

/-- **La famille appariee** : pour chaque tirage, la paire de l'ensemble
des coordonnees vraies et de son complementaire relatif au bloc. La
disjointness de chaque paire borne le degre par le nombre de tirages. -/
def pairFamily {t n m : ℕ} (htn : t ≤ n) (G : Fin m → Fin t → Bool) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.image fun j => drawSet htn (G j)) ∪
    (Finset.univ.image fun j => blockOf htn \ drawSet htn (G j))

theorem blockOf_sum {t n : ℕ} (htn : t ≤ n) (C : Fin n → ℤ) :
    (blockOf htn).sum C = (Finset.univ : Finset (Fin t)).sum
      (fun q => C ((Fin.castLEEmb htn) q)) := by
  rw [blockOf, Finset.sum_map]

theorem drawSet_sum {t n : ℕ} (htn : t ≤ n) (σ : Fin t → Bool) (C : Fin n → ℤ) :
    (drawSet htn σ).sum C = (Finset.univ.filter (fun q => σ q = true)).sum
      (fun q => C ((Fin.castLEEmb htn) q)) := by
  rw [drawSet, Finset.sum_map]

theorem drawSet_subset {t n : ℕ} (htn : t ≤ n) (σ : Fin t → Bool) :
    drawSet htn σ ⊆ blockOf htn := by
  rw [drawSet, blockOf]
  exact Finset.map_subset_map.mpr
    (Finset.filter_subset (fun q => σ q = true) (Finset.univ : Finset (Fin t)))

theorem drawSet_mem {t n m : ℕ} (htn : t ≤ n) (G : Fin m → Fin t → Bool)
    (j : Fin m) : drawSet htn (G j) ∈ pairFamily htn G :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

theorem compDraw_mem {t n m : ℕ} (htn : t ≤ n) (G : Fin m → Fin t → Bool)
    (j : Fin m) : blockOf htn \ drawSet htn (G j) ∈ pairFamily htn G :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

/-- **Degre de la famille appariee** : chaque paire etant disjointe, un
point donne n'apparait au plus qu'une fois par tirage - le degre est
majore par le nombre de tirages. -/
theorem degree_pairFamily_le {t n m : ℕ} (htn : t ≤ n) (G : Fin m → Fin t → Bool)
    (i : Fin n) : degree (pairFamily htn G) i ≤ m := by
  classical
  have hpred : ∀ S ∈ (pairFamily htn G).filter (fun S => i ∈ S),
      ∃ j : Fin m, S = drawSet htn (G j) ∨
        S = blockOf htn \ drawSet htn (G j) := by
    intro S hS
    obtain ⟨hS, -⟩ := Finset.mem_filter.mp hS
    rw [pairFamily] at hS
    rcases Finset.mem_union.mp hS with h | h
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      exact ⟨j, Or.inl hj.symm⟩
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      exact ⟨j, Or.inr hj.symm⟩
  have hcard : ((pairFamily htn G).filter (fun S => i ∈ S)).card ≤ m := by
    have hle : ((pairFamily htn G).filter (fun S => i ∈ S)).card ≤
        (Finset.range m).card := by
      refine Finset.card_le_card_of_injOn
        (fun S => if h : ∃ j : Fin m, S = drawSet htn (G j) ∨
            S = blockOf htn \ drawSet htn (G j) then
              ((Classical.choose h : Fin m) : ℕ) else 0)
        (fun S hS =>
          have hx := hpred S hS
          Finset.mem_range.mpr
            (by simp only [dif_pos hx]; exact (Classical.choose hx).isLt))
        ?_
      intro S hS S' hS' hEq
      have hx := hpred S hS
      have hx' := hpred S' hS'
      simp only [dif_pos hx, dif_pos hx'] at hEq
      have hjj : Classical.choose hx = Classical.choose hx' :=
        Fin.val_injective hEq
      have hiS := (Finset.mem_filter.mp hS).2
      have hiS' := (Finset.mem_filter.mp hS').2
      rcases Classical.choose_spec hx with hS1 | hS1 <;>
        rcases Classical.choose_spec hx' with hS2 | hS2
      · rw [hS1, hS2, hjj]
      · rw [hS1] at hiS
        rw [← hjj] at hS2
        rw [hS2] at hiS'
        exact absurd hiS (Finset.mem_sdiff.mp hiS').2
      · rw [← hjj] at hS2
        rw [hS2] at hiS'
        rw [hS1] at hiS
        exact absurd hiS' (Finset.mem_sdiff.mp hiS).2
      · rw [hS1, hS2, hjj]
    calc ((pairFamily htn G).filter (fun S => i ∈ S)).card ≤ (Finset.range m).card := hle
      _ = m := Finset.card_range m
  exact hcard

open PacLearning in
/-- **Borne inferieure d'Erdos-Spencer (constante explicite)** : pour
`1 ≤ k ≤ n` il existe une famille de parties de `Fin n`, de degre
maximal au plus `k`, dont aucune coloration ±1 n'abaisse la discrepance
sous `sqrt(k) / 14` - la contrepartie asymptotique de Beck-Fiala (la
borne `O(sqrt k)` est serree), a constante explicite.

**Derivation de la constante 14** (volet 1 de #13508 - chaque maillon
chiffre, dans l'ordre ou la preuve l'assemble ; `t = k / 12` designe la
taille du bloc) :

1. Queue d'un tirage (`prob_tail_ge_of_isColoring`) : Paley-Zygmund au
   seuil `theta = 1/2` donne `P[Z² >= t/2] >= 1/12`, car
   `(1-theta)² * E[Z²]² / E[Z⁴]` avec `E[Z²] = t` (exact) et
   `E[Z⁴] = 3t² - 2t <= 3t²` (`expect_rademacherSum_sq/fourth_moment_...
   of_isColoring`), soit `(t/2)² / 3t² = 1/12`.
2. Famille existentielle (`exists_family_beats_all_colorings`) :
   `m = 12t` tirages battent TOUTES les `<= 2^t` colorations - union
   bound `2^t * (11/12)^{12t} = (2 * (11/12)^12)^t < 1`, la numerie
   etant `(11/12)^12 < 1/2` (`norm_num`). Le `12` de `m = 12t` est le
   `1/p` du maillon 1.
3. Choix du bloc `t = k / 12` : le degre de la famille appariee est
   `<= m = 12 * (k/12) <= k` (`degree_pairFamily_le`).
4. Garantie par coloration : `exists j, t / 2 <= Z_j ^ 2` (maillon 2).
5. Retour aux ensembles (`rademacherSum_eq_two_sub`) : `Z_j = 2 D_j - B`
   avec `D_j` la somme sur le tirage et `B` celle du bloc. La famille
   APPARIEE contient `D_j` ET son complement, chacun de somme majoree
   en valeur absolue par `d` : triangle
   `|Z_j| = |D_j + (D_j - B)| <= d + d = 2d`.
6. Combinaison : `t <= 2 * Z_j ^ 2 <= 2 * (2d)² = 8 d²`.
7. Partage euclidien : `k <= 12 * (k/12) + 11 <= 23 * (k/12) = 23 t`
   (branche `k >= 12`, donc `t >= 1` absorbe le reste `11`).
8. Total : `k <= 23 * 8 * d² = 184 d² < (14 d + 1)² = 196 d² + 28 d + 1`,
   donc `Nat.sqrt k < 14 d + 1` (strict, via `Nat.sqrt_lt`), soit
   `Nat.sqrt k <= 14 d`. La constante est `ceil(sqrt 184) = 14`
   (`sqrt 184 = 13,56...`).

**Meilleure constante atteignable par cette machinerie** : deux leviers
gachent un facteur ~1,6. (a) `lambda = m / t = 12` est surdimensionne :
l'union bound n'exige que `(11/12)^lambda < 1/2`, deja vraie pour
`lambda = 8` (`(11/12)^8 = 0,4986 < 1/2`, verifiable par `norm_num` en
exact : `2 * 11^8 < 12^8`) ; re-cabler `m = 8t` et `t = k / 8` (meme
Paley-Zygmund, aucun sous-lemme mathematique touche) donne
`k <= 15 t <= 120 d²`, soit `c = ceil(sqrt 120) = 11`. (b) l'arrondi
grossier `k <= (2s - 1) t` (facteur ~2 quand `s` est petit) :
l'optimum joint `theta = 1/3` (maximise `theta (1 - theta)²`),
`p = 4/27`, `lambda = 5` (`(23/27)^5 < 1/2` en exact) donne lui aussi
`c = 11` avec la technique d'arrondi actuelle, mais `c² -> 4 lambda /
theta = 60` (soit `c = 8`) des que le reste additif `s - 1` est absorbe
dans la marge `(c d + 1)²` pour `d` grand. Meilleure constante entiere
de cette methode : **11** (re-cablage seul), **8** (asymptotique). La
forme optimiste `sqrt k / 2` reste ouverte - obstruction structurelle
documentee : Paley-Zygmund exige `m >= lambda t` tirages quand le degre
borne `m <= k`, et le triangle du maillon 5 coute son facteur 2. -/
theorem erdos_spencer_lb_explicit : ∀ (n k : ℕ), 1 ≤ k → k ≤ n →
    ∃ F : Finset (Finset (Fin n)),
      maxDegree F ≤ k ∧
        ∀ C : Fin n → ℤ, IsColoring C → Nat.sqrt k ≤ 14 * discrepancy F C := by
  intro n k hk hkn
  rcases lt_or_ge k 12 with hsmall | hbig
  · -- Petit k (k < 12) : singletons - degre 1, discrepance 1
    refine ⟨(Finset.univ : Finset (Fin k)).image
      (fun q => ({Fin.castLE hkn q} : Finset (Fin n))), ?_, ?_⟩
    · refine Finset.sup_le fun i _ => ?_
      have h1 : degree ((Finset.univ : Finset (Fin k)).image
          (fun q => ({Fin.castLE hkn q} : Finset (Fin n)))) i ≤ 1 := by
        show (((Finset.univ : Finset (Fin k)).image
          (fun q => ({Fin.castLE hkn q} : Finset (Fin n)))).filter
          (fun S => i ∈ S)).card ≤ 1
        refine (Finset.card_le_one).mpr ?_
        intro a ha b hb
        obtain ⟨ha1, hia⟩ := Finset.mem_filter.mp ha
        obtain ⟨qa, -, hqa⟩ := Finset.mem_image.mp ha1
        obtain ⟨hb1, hib⟩ := Finset.mem_filter.mp hb
        obtain ⟨qb, -, hqb⟩ := Finset.mem_image.mp hb1
        rw [← hqa] at hia
        rw [← hqb] at hib
        have hia' : i = Fin.castLE hkn qa := Finset.mem_singleton.mp hia
        have hib' : i = Fin.castLE hkn qb := Finset.mem_singleton.mp hib
        rw [← hqa, ← hqb, ← hia', ← hib']
      omega
    · intro C hC
      obtain ⟨z⟩ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
      have h1 : 1 ≤ discrepancy ((Finset.univ : Finset (Fin k)).image
          (fun q => ({Fin.castLE hkn q} : Finset (Fin n)))) C := by
        refine Finset.le_sup_of_le
          (Finset.mem_image.mpr ⟨{Fin.castLE hkn z},
            Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩, rfl⟩) ?_
        show 1 ≤ (({Fin.castLE hkn z} : Finset (Fin n)).sum C).natAbs
        rw [Finset.sum_singleton]
        rcases hC (Fin.castLE hkn z) with h | h <;> simp [h]
      have h4 : Nat.sqrt k ≤ 4 := by
        have h5 : Nat.sqrt k < 5 := (Nat.sqrt_lt (n := 5)).mpr (by omega)
        omega
      omega
  · -- Gros k : bloc de k / 12 points, famille probabiliste de 12 * (k / 12) tirages
    obtain ⟨G, hG⟩ := exists_family_beats_all_colorings (n := k / 12) (by omega)
    have htn : k / 12 ≤ n := by omega
    refine ⟨pairFamily htn G, ?_, ?_⟩
    · have hdeg : maxDegree (pairFamily htn G) ≤ 12 * (k / 12) :=
        Finset.sup_le fun i _ => degree_pairFamily_le htn G i
      omega
    · intro C hC
      have hcc : IsColoring (fun q => C ((Fin.castLEEmb htn) q)) :=
        fun q => hC ((Fin.castLEEmb htn) q)
      obtain ⟨j, hj⟩ := hG _ hcc
      have hx : (drawSet htn (G j)).sum C =
          (Finset.univ.filter (fun q => G j q = true)).sum
            (fun q => C ((Fin.castLEEmb htn) q)) :=
        drawSet_sum htn (G j) C
      have hs : (blockOf htn).sum C =
          (Finset.univ : Finset (Fin (k / 12))).sum
            (fun q => C ((Fin.castLEEmb htn) q)) :=
        blockOf_sum htn C
      have hcomp : (blockOf htn \ drawSet htn (G j)).sum C =
          (blockOf htn).sum C - (drawSet htn (G j)).sum C := by
        have h := Finset.sum_sdiff (drawSet_subset htn (G j)) (f := C)
        linarith
      have hc1 : (Finset.univ.filter (fun q => G j q = true)).sum
          (fun q => ((C ((Fin.castLEEmb htn) q) : ℤ) : ℝ)) =
          ((Finset.univ.filter (fun q => G j q = true)).sum
            (fun q => C ((Fin.castLEEmb htn) q)) : ℤ) :=
        (Int.cast_sum _ _).symm
      have hc2 : (Finset.univ.sum
          (fun q => ((C ((Fin.castLEEmb htn) q) : ℤ) : ℝ))) =
          ((Finset.univ.sum (fun q => C ((Fin.castLEEmb htn) q)) : ℤ)) :=
        (Int.cast_sum _ _).symm
      have hZeq : rademacherSum (fun q => C ((Fin.castLEEmb htn) q)) (G j) =
          2 * (((drawSet htn (G j)).sum C : ℤ) : ℝ) -
            (((blockOf htn).sum C : ℤ) : ℝ) := by
        rw [rademacherSum_eq_two_sub, hc1, hc2, ← hx, ← hs]
      set d := discrepancy (pairFamily htn G) C with hd
      have hmem1 : ((drawSet htn (G j)).sum C).natAbs ∈
          (pairFamily htn G).image (fun S => (S.sum C).natAbs) :=
        Finset.mem_image.mpr ⟨drawSet htn (G j), drawSet_mem htn G j, rfl⟩
      have hmem2 : ((blockOf htn \ drawSet htn (G j)).sum C).natAbs ∈
          (pairFamily htn G).image (fun S => (S.sum C).natAbs) :=
        Finset.mem_image.mpr ⟨blockOf htn \ drawSet htn (G j),
          compDraw_mem htn G j, rfl⟩
      have hdx : ((drawSet htn (G j)).sum C).natAbs ≤ d :=
        Finset.le_sup_of_le hmem1 (le_refl _)
      have hds : ((blockOf htn).sum C - (drawSet htn (G j)).sum C).natAbs ≤ d := by
        have hh : ((blockOf htn \ drawSet htn (G j)).sum C).natAbs ≤ d :=
          Finset.le_sup_of_le hmem2 (le_refl _)
        rw [hcomp] at hh
        exact hh
      have hxz : |(((drawSet htn (G j)).sum C : ℤ) : ℝ)| ≤ (d : ℝ) := by
        have h1 : |(((drawSet htn (G j)).sum C : ℤ) : ℝ)|
            = ((((drawSet htn (G j)).sum C).natAbs : ℕ) : ℝ) := by norm_num
        rw [h1]
        exact_mod_cast hdx
      have hyz : |((((drawSet htn (G j)).sum C : ℤ) : ℝ) -
          (((blockOf htn).sum C : ℤ) : ℝ))| ≤ (d : ℝ) := by
        have hA : (((drawSet htn (G j)).sum C : ℤ) : ℝ) -
            (((blockOf htn).sum C : ℤ) : ℝ) =
            ((((drawSet htn (G j)).sum C - (blockOf htn).sum C : ℤ) : ℝ)) := by
          push_cast
          ring
        rw [hA]
        have hflip : ((((drawSet htn (G j)).sum C - (blockOf htn).sum C : ℤ) : ℝ)) =
            -((((blockOf htn).sum C - (drawSet htn (G j)).sum C : ℤ) : ℝ)) := by
          push_cast
          ring
        rw [hflip, abs_neg]
        have h1 : |((((blockOf htn).sum C - (drawSet htn (G j)).sum C : ℤ) : ℝ))|
            = ((((blockOf htn).sum C - (drawSet htn (G j)).sum C).natAbs : ℕ) : ℝ) := by
          norm_num
        rw [h1]
        exact_mod_cast hds
      have htri : |rademacherSum (fun q => C ((Fin.castLEEmb htn) q)) (G j)| ≤
          (d : ℝ) + (d : ℝ) := by
        rw [hZeq]
        have hsplit2 : (2 * (((drawSet htn (G j)).sum C : ℤ) : ℝ) -
            (((blockOf htn).sum C : ℤ) : ℝ)) =
            ((((drawSet htn (G j)).sum C : ℤ) : ℝ)) +
              ((((drawSet htn (G j)).sum C : ℤ) : ℝ) -
                (((blockOf htn).sum C : ℤ) : ℝ)) := by
          ring
        rw [hsplit2]
        calc |((((drawSet htn (G j)).sum C : ℤ) : ℝ)) +
              ((((drawSet htn (G j)).sum C : ℤ) : ℝ) -
                (((blockOf htn).sum C : ℤ) : ℝ))|
            ≤ |((((drawSet htn (G j)).sum C : ℤ) : ℝ))| +
                |(((((drawSet htn (G j)).sum C : ℤ) : ℝ)) -
                  (((blockOf htn).sum C : ℤ) : ℝ))| := abs_add_le _ _
          _ ≤ (d : ℝ) + (d : ℝ) := add_le_add hxz hyz
      have habs : (0 : ℝ) ≤
          |rademacherSum (fun q => C ((Fin.castLEEmb htn) q)) (G j)| :=
        abs_nonneg _
      rw [← abs_mul_abs_self] at hj
      have hZZ : |rademacherSum (fun q => C ((Fin.castLEEmb htn) q)) (G j)| *
          |rademacherSum (fun q => C ((Fin.castLEEmb htn) q)) (G j)| ≤
          ((d : ℝ) + (d : ℝ)) * ((d : ℝ) + (d : ℝ)) :=
        mul_le_mul htri htri (by positivity) (by positivity)
      have h8 : ((k / 12 : ℕ) : ℝ) ≤ 8 * (d : ℝ) * (d : ℝ) := by
        calc ((k / 12 : ℕ) : ℝ) = 2 * (((k / 12 : ℕ) : ℝ) / 2) := by ring
          _ ≤ 2 * (|rademacherSum (fun q => C ((Fin.castLEEmb htn) q)) (G j)| *
              |rademacherSum (fun q => C ((Fin.castLEEmb htn) q)) (G j)|) :=
              mul_le_mul_of_nonneg_left hj (by norm_num)
          _ ≤ 2 * (((d : ℝ) + (d : ℝ)) * ((d : ℝ) + (d : ℝ))) :=
              mul_le_mul_of_nonneg_left hZZ (by norm_num)
          _ = 8 * (d : ℝ) * (d : ℝ) := by ring
      have h8n : k / 12 ≤ 8 * d * d := by exact_mod_cast h8
      have hk23 : k ≤ 23 * (k / 12) := by omega
      have hgoal : k < (14 * d + 1) * (14 * d + 1) := by
        have hexp : (14 * d + 1) * (14 * d + 1) = 196 * (d * d) + 28 * d + 1 := by
          ring
        rw [hexp]
        have h184 : 23 * (k / 12) ≤ 184 * (d * d) := by
          calc 23 * (k / 12) ≤ 23 * (8 * d * d) :=
              Nat.mul_le_mul_left (k := 23) h8n
            _ = 184 * (d * d) := by ring
        have hdd : 0 ≤ d * d := Nat.zero_le _
        linarith [hk23, h184, hdd]
      have hs5 : Nat.sqrt k < 14 * d + 1 :=
        (Nat.sqrt_lt (n := 14 * d + 1)).mpr hgoal
      omega

end DegreeControl

end Discrepancy
