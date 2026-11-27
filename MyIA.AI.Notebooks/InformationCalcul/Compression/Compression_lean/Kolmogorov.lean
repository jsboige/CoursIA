import Mathlib
import PrefixCodes

/-!
# Kolmogorov — complexité de Kolmogorov : le core combinatoire (pli 10, EPIC #18706)

Formalisation Lean du **cœur combinatoire** de la complexité de Kolmogorov,
telle que le carnet `Compression-06-MDL-Kolmogorov-Python.ipynb` la présente —
**sans** la couche de calculabilité (pas de machine de Turing, pas de
décidabilité) : on modélise une « machine de nommage » par un **code préfixe**
(ensemble de mots binaires, cf [PrefixCodes](PrefixCodes.lean)), et l'on montre
que l'inégalité de Kraft (déjà prouvée dans `PrefixCodes.kraft_le_one`) force
une **borne de comptage**, qui à son tour force l'**incompressibilité**.

La chaîne de résultats, du plus général au plus concret :

1. **Kraft → borne de comptage** (`kraft_short_count`) : dans un code préfixe,
   le nombre de mots de longueur ≤ `k` est ≤ `2 ^ k`. Chaque mot court
   consomme une part `2 ^ (- |w|) ≥ 2 ^ (- k)` du budget unitaire de Kraft.
2. **Nommage → borne de comptage des données** (`atMostK`) : le nombre de
   données nommables en ≤ `k` bits est ≤ `2 ^ k` — chaque mot court code au
   plus une donnée.
3. **Incompressibilité** (`incompressible`) : parmi `2 ^ n` données, au moins
   `2 ^ (n - 1)` exigent ≥ `n` bits — on ne peut pas tout compresser.
4. **La facture MDL** (`mdlCost`) : description du modèle + description des
   données ; quand les données grossissent à modèle fixé, la part du modèle
   dans la facture tend vers `0` (`mdlModelShareTendsToZero`).

Renvoi croisé (doctrine des lakes R4) : `PrefixCodes.kraft_le_one` est la
maison canonique de l'inégalité de Kraft ; ce module **l'importe** et s'en sert,
sans la redéfinir.

Énoncés et tactiques en anglais (compat Mathlib) ; docstrings en français
(convention i18n #4980).
-/

namespace CompressionLean

/-! ## La machine de nommage -/

variable {α : Type}

/-- Une **machine de nommage** : un arbre de code (donc un ensemble de mots
binaires **préfixe**, cf `leafWords_prefixFree`) muni d'une fonction de
décodage `decode : mot → donnée`. Seules les valeurs de `decode` **sur les mots
du code** comptent ; ailleurs elle est arbitraire. -/
structure NamingMachine (α : Type) where
  /-- L'arbre de code : les mots qui « nomment ». -/
  tree : CodeTree
  /-- Le décodage : un mot du code désigne une donnée. -/
  decode : List Bool → α

/-- `shortWords t k` : les mots du code de `t` de longueur ≤ `k`. -/
def shortWords (t : CodeTree) (k : ℕ) : Finset (List Bool) :=
  (leafWords t).toFinset.filter (fun w => w.length ≤ k)

/-! ## Les mots des feuilles sont tous distincts -/

/-- Les mots des feuilles d'un arbre de code sont **tous distincts** (chaque
mot est un chemin racine-feuille unique). C'est ce qui autorise à passer de la
liste `leafWords` à un `Finset` sans perte de cardinalité. -/
theorem leafWords_nodup (t : CodeTree) : (leafWords t).Nodup := by
  induction t with
  | leaf =>
      simp [leafWords]
  | node l r ihl ihr =>
      simp only [leafWords]
      apply List.Nodup.append
      · -- la moitié gauche est nodup
        apply List.Nodup.map (fun x x' h => by injection h)
        exact ihl
      · -- la moitié droite est nodup
        apply List.Nodup.map (fun x x' h => by injection h)
        exact ihr
      · -- les deux moitiés sont disjointes (premier bit distinct)
        intro w hw hw'
        simp only [List.mem_map] at hw hw'
        obtain ⟨a, _, ha⟩ := hw
        obtain ⟨b, _, hb⟩ := hw'
        subst ha
        injection hb with hb'
        cases hb'

/-- La somme de Kraft d'un arbre, vue comme somme sur le `Finset` des mots des
feuilles (les mots sont tous distincts, cf `leafWords_nodup`). -/
theorem kraftSum_toFinset (t : CodeTree) :
    ((leafWords t).toFinset).sum (fun w => (1 : ℚ) / 2 ^ w.length) = kraftSum t := by
  simp only [kraftSum]
  exact List.sum_toFinset (fun w => (1 : ℚ) / 2 ^ w.length) (leafWords_nodup t)

/-! ## Théorème 1 : Kraft → borne de comptage -/

/-- **Borne de comptage** : dans un code préfixe, le nombre de mots de longueur
≤ `k` est ≤ `2 ^ k`. C'est l'inégalité de Kraft (`kraft_le_one`) lue comme un
comptage : chaque mot court consomme au moins `2 ^ (- k)` du budget unitaire,
donc il y en a au plus `2 ^ k`. -/
theorem kraft_short_count (t : CodeTree) (k : ℕ) :
    (shortWords t k).card ≤ 2 ^ k := by
  set S := shortWords t k with hS
  have hSdef : S = (leafWords t).toFinset.filter (fun w => w.length ≤ k) := rfl
  -- chaque mot court pèse au moins 2 ^ (- k) dans la somme de Kraft
  have hpoint : ∀ w ∈ S, (1 : ℚ) / 2 ^ w.length ≥ (1 : ℚ) / 2 ^ k := by
    intro w hw
    rw [hSdef, Finset.mem_filter] at hw
    have hl : w.length ≤ k := hw.2
    have hpow : (2 : ℕ) ^ w.length ≤ (2 : ℕ) ^ k := pow_le_pow_right' (by norm_num) hl
    rw [ge_iff_le,
      one_div_le_one_div (by positivity : (0 : ℚ) < 2 ^ k)
        (by positivity : (0 : ℚ) < 2 ^ w.length)]
    exact_mod_cast hpow
  -- la somme sur les mots courts ≥ (nombre de mots courts) * 2 ^ (- k)
  have hlower : S.sum (fun w => (1 : ℚ) / 2 ^ w.length) ≥ (S.card : ℚ) * (1 : ℚ) / 2 ^ k := by
    calc
      S.sum (fun w => (1 : ℚ) / 2 ^ w.length)
          ≥ S.sum (fun _ => (1 : ℚ) / 2 ^ k) := by
            apply Finset.sum_le_sum
            intro w hw
            exact hpoint w hw
      _ = (S.card : ℚ) * (1 : ℚ) / 2 ^ k := by
            rw [Finset.sum_const, nsmul_eq_mul]
            field_simp
  -- et cette somme ≤ la somme de Kraft totale ≤ 1
  have hupper : S.sum (fun w => (1 : ℚ) / 2 ^ w.length) ≤ kraftSum t := by
    calc
      S.sum (fun w => (1 : ℚ) / 2 ^ w.length)
          = ((leafWords t).toFinset).sum (fun w => if w.length ≤ k then (1 : ℚ) / 2 ^ w.length else 0) := by
            rw [hSdef, Finset.sum_filter]
      _ ≤ ((leafWords t).toFinset).sum (fun w => (1 : ℚ) / 2 ^ w.length) := by
            apply Finset.sum_le_sum
            intro w _
            split_ifs <;> (try exact le_rfl); positivity
      _ = kraftSum t := kraftSum_toFinset t
  -- donc (nombre de mots courts) * 2 ^ (- k) ≤ 1
  have hfinal : (S.card : ℚ) * (1 : ℚ) / 2 ^ k ≤ 1 := by
    calc
      _ ≤ S.sum (fun w => (1 : ℚ) / 2 ^ w.length) := hlower
      _ ≤ kraftSum t := hupper
      _ ≤ 1 := kraft_le_one t
  -- d'où (nombre de mots courts) ≤ 2 ^ k
  have h2 : (S.card : ℚ) ≤ (2 : ℚ) ^ k := by
    have hdiv : (S.card : ℚ) / 2 ^ k ≤ 1 := by
      calc
        (S.card : ℚ) / 2 ^ k = (S.card : ℚ) * (1 : ℚ) / 2 ^ k := by field_simp
        _ ≤ 1 := hfinal
    rwa [div_le_one (by positivity : (0 : ℚ) < 2 ^ k)] at hdiv
  exact_mod_cast h2

/-! ## Théorème 2 : nommage → borne de comptage des données -/

/-- **Borne de comptage des données** : le nombre de **données** nommables en ≤
`k` bits (les images, par décodage, des mots courts) est ≤ `2 ^ k`. Chaque mot
court code au plus une donnée, donc les données nommables ne dépassent pas les
mots courts, bornés par `kraft_short_count`. -/
theorem atMostK [DecidableEq α] (m : NamingMachine α) (k : ℕ) :
    ((shortWords m.tree k).image m.decode).card ≤ 2 ^ k := by
  calc
    ((shortWords m.tree k).image m.decode).card
        ≤ (shortWords m.tree k).card := Finset.card_image_le
    _ ≤ 2 ^ k := kraft_short_count m.tree k

/-! ## Théorème 3 : incompressibilité -/

/-- `namedWithin m x k` : la donnée `x` est nommée par un mot du code de
longueur ≤ `k`. -/
abbrev namedWithin (m : NamingMachine α) (x : α) (k : ℕ) : Prop :=
  ∃ w ∈ (leafWords m.tree).toFinset, m.decode w = x ∧ w.length ≤ k

/-- **Incompressibilité** : soit `D` un ensemble de `2 ^ n` données. Alors au
moins `2 ^ (n - 1)` d'entre elles exigent ≥ `n` bits pour être nommées — on ne
peut pas tout compresser. Preuve : au plus `2 ^ (n - 1)` données sont
nommables en ≤ `n - 1` bits (`atMostK`), donc au moins la moitié de `D` ne
l'est pas. -/
theorem incompressible [DecidableEq α] (m : NamingMachine α) (n : ℕ) (hn : 0 < n)
    (D : Finset α) (hD : D.card = 2 ^ n) :
    (D.filter (fun x => ¬ namedWithin m x (n - 1))).card ≥ 2 ^ (n - 1) := by
  -- la partie « nommée en ≤ n-1 bits » est une sous-part de D
  have h2 : (D.filter (fun x => namedWithin m x (n - 1))).card ≤ 2 ^ (n - 1) := by
    have hsub : D.filter (fun x => namedWithin m x (n - 1))
        ⊆ (shortWords m.tree (n - 1)).image m.decode := by
      intro x hx
      have hnamed : namedWithin m x (n - 1) := by
        simpa [namedWithin] using (Finset.mem_filter.mp hx).2
      obtain ⟨w, hw, hdec, hlen⟩ := hnamed
      have hwshort : w ∈ shortWords m.tree (n - 1) := by
        simp only [shortWords, Finset.mem_filter]
        exact ⟨hw, hlen⟩
      rw [Finset.mem_image]
      exact ⟨w, hwshort, hdec⟩
    calc
      (D.filter (fun x => namedWithin m x (n - 1))).card
          ≤ ((shortWords m.tree (n - 1)).image m.decode).card := Finset.card_le_card hsub
      _ ≤ (shortWords m.tree (n - 1)).card := Finset.card_image_le
      _ ≤ 2 ^ (n - 1) := kraft_short_count m.tree (n - 1)
  -- le complément (les « incompressibles ») = D moins la partie nommée
  have h1 : (D.filter (fun x => ¬ namedWithin m x (n - 1))).card
      = D.card - (D.filter (fun x => namedWithin m x (n - 1))).card := by
    have hsub2 : D.filter (fun x => namedWithin m x (n - 1)) ⊆ D :=
        Finset.filter_subset (fun x => namedWithin m x (n - 1)) D
    rw [Finset.filter_not, Finset.card_sdiff]
    congr
    rw [Finset.inter_eq_left.mpr hsub2]
  calc
    (D.filter (fun x => ¬ namedWithin m x (n - 1))).card
        = D.card - (D.filter (fun x => namedWithin m x (n - 1))).card := h1
    _ ≥ D.card - 2 ^ (n - 1) := by
        apply Nat.sub_le_sub_left h2 D.card
    _ = 2 ^ n - 2 ^ (n - 1) := by rw [hD]
    _ = 2 ^ (n - 1) := by
        have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
          have hle : 1 ≤ n := Nat.succ_le_of_lt hn
          have h : n - 1 + 1 = n := Nat.sub_add_cancel hle
          calc
            2 ^ n = 2 ^ ((n - 1) + 1) := by
              conv in (2 ^ n) => rw [← h]
            _ = 2 ^ (n - 1) * 2 := by rw [Nat.pow_add, Nat.pow_one]
            _ = 2 * 2 ^ (n - 1) := by rw [Nat.mul_comm]
        rw [h2n, Nat.mul_comm, Nat.mul_two, Nat.add_sub_cancel]

/-! ## La facture MDL -/

/-- `mdlCost` : la **facture MDL** = description du modèle + description des
données (en bits). C'est la grandeur que le principe MDL minimise. -/
def mdlCost (modelBits dataBits : ℕ) : ℕ := modelBits + dataBits

/-- **Part du modèle → 0** : à modèle fixé (`m` bits), quand les données
grossissent, la part du modèle dans la facture MDL, `m / (m + n)`, devient
arbitrairement petite. Formellement : pour tout `k ≥ 1`, au-delà d'un certain
`N`, `m / (m + n) ≤ 1 / k`. -/
theorem mdlModelShareTendsToZero (m : ℕ) :
    ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ n ≥ N, (m : ℚ) / ((m : ℚ) + n) ≤ 1 / k := by
  intro k hk
  -- il suffit de prendre N = k * m + 1 : alors n ≥ N force k * m < m + n
  -- (le + 1 garantit m + n > 0, y compris dans le cas m = n = 0)
  use k * m + 1
  intro n hn
  have hnq : (n : ℚ) ≥ ((k : ℕ) * m + 1 : ℚ) := by
    exact_mod_cast hn
  have hpos : (0 : ℚ) < (m : ℚ) + n := by
    -- m + n ≥ n ≥ k * m + 1 ≥ 1 : strictement positif dans tous les cas
    have h1 : 1 ≤ n := Nat.le_trans (Nat.le_add_left 1 (k * m)) hn
    have : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast h1
    linarith
  have hcross : (k : ℚ) * (m : ℚ) ≤ (m : ℚ) + (n : ℚ) := by
    have : (k : ℚ) * (m : ℚ) + 1 ≤ (n : ℚ) := by
      have : ((k : ℕ) * m + 1 : ℚ) = (k : ℚ) * (m : ℚ) + 1 := by norm_cast
      rw [this] at hnq
      exact hnq
    linarith
  -- m / (m + n) ≤ 1 / k  se ramène à k * m ≤ m + n : `field_simp` multiplie
  -- par les dénominateurs positifs. (`div_le_div_iff'` ne sert pas : en v4.33.0
  -- c'est le lemme de groupe abélien ordonné, pas le lemme de corps.)
  have hkq : 0 < (k : ℚ) := by exact_mod_cast hk
  field_simp [hpos, hkq]
  nlinarith [hcross]

/-! ## Ancres numériques (exécutables) -/

-- Le code `sf4` (longueurs `[1, 2, 3, 3]`) : la borne de comptage en action.
#eval (leafWords sf4).map List.length  -- [1, 2, 3, 3]
#eval (shortWords sf4 1).card  -- 1
#eval (shortWords sf4 2).card  -- 2
#eval (shortWords sf4 3).card  -- 4
#eval (shortWords (full 3) 3).card  -- 8
#eval (shortWords (full 3) 2).card  -- 0 : tous les mots de `full 3` ont longueur 3

-- Les trois bornes, évaluées sur `sf4`.
example : (shortWords sf4 1).card ≤ 2 ^ 1 := kraft_short_count sf4 1
example : (shortWords sf4 2).card ≤ 2 ^ 2 := kraft_short_count sf4 2
example : (shortWords sf4 3).card ≤ 2 ^ 3 := kraft_short_count sf4 3

end CompressionLean
