/-
  Théorie des jeux coopératifs — Définitions de base
  ===================================================

  Ce fichier formalise les concepts de base de la théorie des jeux coopératifs :
  - Jeux TU (Transferable Utility Games, jeux à utilité transférable)
  - Coalitions et fonctions caractéristiques
  - Propriétés de superadditivité et convexité
  - Le noyau (Core) d'un jeu

  Référence : L.S. Shapley, « A Value for N-Person Games » (1953)

  Convention i18n (EPIC #4980, cycle 39, PR pilote) : FR-first appliqué sur les
  en-têtes, titres de section, et docstrings publics. Le code tactique et les
  commentaires intra-preuve restent en anglais (références Mathlib, notation
  formelle). Les blocs `/--  docstring EN  -/` qui auraient pu être préservés
  en companion `Basic.en.lean` pour publication externe ne sont PAS dupliqués
  dans cette PR pilote — voir convention §A dans `docs/lean/i18n-inventory-cycle-38.md`.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import CooperativeGames.ConeKernel

/-! ## Types de base -/

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ## Jeux TU (utilité transférable) -/

/-- Une coalition est un sous-ensemble de joueurs. -/
abbrev Coalition (N : Type*) := Finset N

/-- Un jeu TU (Transferable Utility, à utilité transférable) est défini par
    une fonction caractéristique v associant à chaque coalition une valeur
    réelle, avec la convention v(∅) = 0. -/
@[ext]
structure TUGame (N : Type*) [Fintype N] where
  /-- La fonction caractéristique : valeur de chaque coalition. -/
  v : Finset N → ℝ
  /-- La coalition vide a pour valeur 0. -/
  empty_zero : v ∅ = 0

namespace TUGame

variable (G : TUGame N)

/-! ## Propriétés structurelles -/

/-- Un jeu est superadditif si la coopération est profitable :
    v(S ∪ T) ≥ v(S) + v(T) pour S, T disjoints. -/
def Superadditive : Prop :=
  ∀ S T : Finset N, Disjoint S T →
    G.v (S ∪ T) ≥ G.v S + G.v T

/-- Un jeu est convexe (supermodulaire) si les contributions marginales
    sont croissantes : v(S ∪ {i}) - v(S) ≤ v(T ∪ {i}) - v(T) pour S ⊆ T, i ∉ T. -/
def Convex : Prop :=
  ∀ S T : Finset N, ∀ i : N,
    S ⊆ T → i ∉ T →
    G.v (S ∪ {i}) - G.v S ≤ G.v (T ∪ {i}) - G.v T

/-- Contribution marginale du joueur i à la coalition S. -/
def marginalContribution (i : N) (S : Finset N) : ℝ :=
  G.v (S ∪ {i}) - G.v S

/-! ## Exemples classiques -/

/-- Le jeu d'unanimité pour la coalition T (non vide) :
    v(S) = 1 si T ⊆ S, sinon 0. -/
def unanimityGame (T : Finset N) (hT : T.Nonempty) : TUGame N where
  v := fun S => if T ⊆ S then 1 else 0
  empty_zero := by
    simp only [Finset.subset_empty]
    simp [hT.ne_empty]

/-- Le jeu de majorité : v(S) = 1 si |S| > n/2, sinon 0. -/
def majorityGame : TUGame N where
  v := fun S => if 2 * S.card > Fintype.card N then 1 else 0
  empty_zero := by simp

/-! ## Le noyau (Core) -/

/-- Une allocation est une fonction associant un payoff à chaque joueur. -/
abbrev Allocation (N : Type*) := N → ℝ

/-- Le noyau (Core) : ensemble des allocations efficaces et stables. -/
def Core : Set (Allocation N) :=
  { x |
    -- Efficacité : la somme des payoffs vaut v(N)
    (∑ i : N, x i = G.v Finset.univ) ∧
    -- Rationalité collective : aucune coalition ne peut bloquer
    (∀ S : Finset N, ∑ i ∈ S, x i ≥ G.v S) }

/-- Le noyau peut être vide. -/
def CoreEmpty : Prop := G.Core = ∅

/-! ## Jeux balancés (balanced games) -/

/-- Une collection balancée de poids. -/
def BalancedWeights (weights : Finset N → ℝ) : Prop :=
  (∀ S, weights S ≥ 0) ∧
  (∀ i : N, ∑ S ∈ (Finset.univ.filter fun S => i ∈ S), weights S = 1)

/-- Un jeu est balancé si toute collection balancée vérifie l'inégalité. -/
def Balanced : Prop :=
  ∀ weights : Finset N → ℝ,
    BalancedWeights weights →
    ∑ S : Finset N, weights S * G.v S ≤ G.v Finset.univ

/-! ## Théorèmes clés -/

/-- Les jeux superadditifs ont une coalition grande de valeur non négative.
    Preuve : par induction sur les coalitions, en utilisant la superadditivité
    pour décomposer la grande coalition en singletons. Requiert v({i}) ≥ 0 pour
    chaque singleton, ce qui découle de v(∅) = 0 et de la superadditivité de
    {i} avec ∅.
    NOTE : la preuve décompose univ en singletons via superadditivité :
    v(univ) = v({i1} ∪ ... ∪ {in}) ≥ v({i1}) + ... + v({in}) ≥ 0.
    Chaque v({ik}) ≥ 0 car v({ik}) = v(∅ ∪ {ik}) ≥ v(∅) + v({ik}) = v({ik}),
    donc v({ik}) ≥ v({ik}) est trivialement vrai mais ne donne pas la non-négativité.
    En fait : v({i}) = v({i} ∪ ∅) ≥ v({i}) + v(∅) = v({i}), trivialement.
    L'approche correcte : par superadditivité, v(S ∪ T) ≥ v(S) + v(T).
    Par application répétée : v(univ) ≥ ∑ᵢ v({i}). Mais il faut v({i}) ≥ 0,
    ce qui découle de : v({i}) ≥ v(∅) + v({i})... non, cela donne v({i}) ≥ v({i}).
    INSIGHT CLÉ : par superadditivité avec S = ∅, T = ∅ : v(∅) ≥ 2·v(∅),
    donc v(∅) ≤ 0. Combiné avec v(∅) = 0, c'est cohérent.
    Pour les singletons : v({i}) peut être quelconque. Donc le théorème tel
    qu'énoncé est en fait FAUX sans hypothèses supplémentaires. Un contre-exemple :
    N = Fin 1, v(∅) = 0, v({0}) = -1.
    CORRECTIF : on prouve l'énoncé plus faible v(∅) ≥ 0 (trivial depuis empty_zero). -/
theorem superadditive_empty_nonneg (_h : G.Superadditive) :
    G.v ∅ ≥ 0 := by
  rw [G.empty_zero]

/-- Pour les jeux superadditifs dont tous les singletons ont une valeur non
    négative, la grande coalition a une valeur non négative. -/
theorem superadditive_grand_coalition_nonneg_of_nonneg_singletons
    (h : G.Superadditive) (hnn : ∀ i : N, G.v {i} ≥ 0) :
    G.v Finset.univ ≥ 0 := by
  -- Decompose univ into singletons via superadditivity
  have hsum : ∀ S : Finset N, G.v S ≥ ∑ i ∈ S, G.v ({i} : Finset N) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [G.empty_zero]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      have hsup : G.v (insert a S) ≥ G.v ({a} : Finset N) + G.v S := by
        rw [Finset.insert_eq]
        exact h {a} S (Finset.disjoint_singleton_left.mpr ha)
      linarith
  have h1 := hsum Finset.univ
  have h2 : (0 : ℝ) ≤ ∑ (i : N), G.v ({i} : Finset N) :=
    Finset.sum_nonneg (fun i _ => hnn i)
  linarith

/-- Sens direct de Bondareva-Shapley : noyau non vide implique balancé.
    Preuve : soit x ∈ Core. Pour des poids balancés w avec ∑_{S∋i} w(S) = 1 :
    ∑_S w(S)·v(S) ≤ ∑_S w(S)·(∑_{i∈S} x(i))   [rationalité collective]
                   = ∑_S ∑_{i∈S} w(S)·x(i)       [distributivité]
                   = ∑_i ∑_{S∋i} w(S)·x(i)       [Fubini, double somme]
                   = ∑_i x(i)·∑_{S∋i} w(S)       [factorisation par x(i)]
                   = ∑_i x(i)·1 = v(N)            [balancé + efficacité] -/
theorem bondareva_shapley_forward :
    G.Core.Nonempty → G.Balanced := by
  rintro ⟨x, ⟨hx_eff, hx_gr⟩⟩
  intro weights ⟨hw_pos, hw_bal⟩
  suffices h : ∑ S : Finset N, weights S * G.v S ≤ ∑ i : N, x i by rwa [hx_eff] at h
  -- Étape 1 : borne de rationalité collective
  have h_gr : ∑ S : Finset N, weights S * G.v S ≤
      ∑ S : Finset N, weights S * (∑ i ∈ S, x i) :=
    Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left (hx_gr S) (hw_pos S))
  -- Étape 2 : distribuer les poids dans la somme interne
  have h_dist : ∑ S : Finset N, weights S * (∑ i ∈ S, x i) =
      ∑ S : Finset N, ∑ i ∈ S, weights S * x i :=
    Finset.sum_congr rfl (fun S _ => by rw [Finset.mul_sum])
  -- Étape 3 : Fubini — échanger l'ordre de la double somme
  have h_fubini : ∑ S : Finset N, ∑ i ∈ S, weights S * x i =
      ∑ i : N, ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S * x i := by
    classical
    -- Étendre les sommes internes au type complet en utilisant des fonctions indicatrices
    have h1 (S : Finset N) : ∑ i ∈ S, weights S * x i =
        ∑ i : N, (if i ∈ S then weights S * x i else 0) := by
      trans ∑ i ∈ S, (if i ∈ S then weights S * x i else 0)
      · exact Finset.sum_congr rfl (fun i hi => (if_pos hi).symm)
      · exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => if_neg hi)
    -- Échanger l'ordre de sommation (Fubini pour types finis)
    have h2 : ∑ S : Finset N, ∑ i : N, (if i ∈ S then weights S * x i else 0) =
        ∑ i : N, ∑ S : Finset N, (if i ∈ S then weights S * x i else 0) := by
      exact Finset.sum_comm
    -- Reconvertir les sommes indicatrices en sommes filtrées
    have h3 (i : N) : ∑ S : Finset N, (if i ∈ S then weights S * x i else 0) =
        ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S * x i := by
      exact (Finset.sum_filter (fun S => i ∈ S) (fun S => weights S * x i)).symm
    -- Chain the three steps
    rw [Finset.sum_congr rfl (fun S _ => h1 S), h2,
        Finset.sum_congr rfl (fun i _ => h3 i)]
  -- Étape 4 : factoriser x(i) hors de chaque somme interne
  have h_factor : ∑ i : N, ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S * x i =
      ∑ i : N, x i * ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S :=
    Finset.sum_congr rfl (fun i _ => by
      rw [Finset.sum_congr rfl (fun S _ => mul_comm (weights S) (x i)),
          ← Finset.mul_sum])
  -- Étape 5 : appliquer la condition balancée
  have h_bal : ∑ i : N, x i * ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S =
      ∑ i : N, x i :=
    Finset.sum_congr rfl (fun i _ => by rw [hw_bal i, mul_one])
  -- Combiner
  calc ∑ S : Finset N, weights S * G.v S
      ≤ ∑ S : Finset N, weights S * (∑ i ∈ S, x i) := h_gr
    _ = ∑ S : Finset N, ∑ i ∈ S, weights S * x i := h_dist
    _ = ∑ i : N, ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S * x i := h_fubini
    _ = ∑ i : N, x i * ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), weights S := h_factor
    _ = ∑ i : N, x i := h_bal

/-! ## Pont cône-séparation (décodage du témoin Bondareva-Farkas)

Ces lemmes relient l'hypothèse `TUGame.Balanced` à la machinerie cône-TUGame-free
dans `CooperativeGames.ConeKernel` (`BondarevaCone.augCone` et le séparateur
`hyperplane_separation_point` de `Mathlib.Analysis.Convex.Cone.Dual`). Ils forment
la première moitié de la construction du témoin backward de Bondareva-Shapley :
depuis `hb : G.Balanced` on obtient un fonctionnel séparant, puis on le décode
en une pré-imputation. -/

open BondarevaCone

/-- Depuis `hb : G.Balanced` et `t > 0`, le point de test balanced-unit
    `balancedUnit (G.v univ + t)` est hors de `augCone G.v`. L'appartenance
    donnerait des poids non négatifs `w` avec `phiAugCont G.v w = balancedUnit ...` ;
    les coordonnées `some i` forcent `w` à être une collection balancée
    (`BalancedWeights`), tandis que la coordonnée `none` se lit
    `∑ S, w S * G.v S = G.v univ + t > G.v univ`, contredisant `hb`. -/
theorem balancedUnit_notIn_augCone (t : ℝ) (ht : 0 < t) (hb : G.Balanced) :
    balancedUnit (G.v Finset.univ + t) ∉ augCone G.v := by
  intro hmem
  rw [augCone_mem_iff] at hmem
  obtain ⟨w, hw, hwmem⟩ := hmem
  -- Coordonnée `some i` : ∑_{S ∋ i} w S = 1  (collection balancée).
  have hsome (i : N) :
      ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), w S = 1 := by
    have key := congr_fun hwmem (some i)
    simp only [balancedUnit] at key
    exact key
  -- Coordonnée `none` : ∑ S, w S * G.v S = G.v univ + t.
  have hnone : ∑ S : Finset N, w S * G.v S = G.v Finset.univ + t := by
    have key := congr_fun hwmem none
    simp only [balancedUnit] at key
    exact key
  -- `w` est balancé, donc `hb` borne la somme des valeurs par v(N) : contradiction.
  have hbnd := hb w ⟨hw, hsome⟩
  linarith

/-- Sens réciproque de Bondareva-Shapley : balancé implique noyau non vide.
    Stratégie (mise à jour v4.30) : `ProperCone.hyperplane_separation` est
    désormais disponible via `Mathlib.Analysis.Convex.Cone.Dual`. Cela donne :
    étant donnés un cône propre C et un compact convexe K avec K ∩ C = ∅,
    ∃ f, (∀ x ∈ C, 0 ≤ f x) ∧ ∀ x ∈ K, f x < 0.
    Esquisse de la preuve :
    1. Supposer balancé : ∀ weights, BalancedWeights weights → ∑_S w(S)·v(S) ≤ v(N).
    2. Définir l'ensemble polyédrique P = { x : N → ℝ | ∀ S, ∑_{i∈S} xᵢ ≥ v(S) }.
    3. Définir le rayon R = { t · 1_N | t ∈ ℝ, t ≤ v(N) } (valeurs grande coalition).
    4. Montrer que P ∩ cone(R) est non vide via la condition balancée (approche
       par contradiction) : si P ∩ { x | ∑ᵢ xᵢ < v(N) } = ∅, appliquer
       hyperplane_separation pour obtenir un hyperplan séparant témoignant d'un
       système de poids non balancé, contredisant l'hypothèse balancée.
    5. Extraire l'allocation du noyau depuis le point d'intersection. -/
theorem bondareva_shapley_backward :
    G.Balanced → G.Core.Nonempty := by
  intro hb
  -- On travaille dans l'espace vectoriel réel de dimension finie N → ℝ.
  -- La région réalisable : P = { x | ∀ S, ∑_{i∈S} xᵢ ≥ v(S) } (contraintes de coalition).
  -- On montre que P ∩ { x | ∑ᵢ xᵢ = v(N) } est non vide via séparation d'hyperplan.
  -- Étape 1 : définir l'ensemble de contraintes polyédrique P
  let P : Set (N → ℝ) := { x | ∀ S : Finset N, ∑ i ∈ S, x i ≥ G.v S }
  -- Étape 2 : montrer que P est convexe (intersection de demi-espaces, chacun convexe)
  have hP_conv : _root_.Convex ℝ P := by
    -- CIBLE DU PROVEUR : montrer que l'intersection de demi-espaces est convexe
    -- Chaque contrainte S est un demi-espace { x | ∑_{i∈S} xᵢ ≥ v(S) } qui est convexe.
    -- L'intersection d'ensembles convexes est convexe.
    intro x hx y hy a b ha hb hab S
    show ∑ i ∈ S, (a • x + b • y) i ≥ G.v S
    have h : ∀ i ∈ S, (a • x + b • y) i = a * x i + b * y i := by
      intro i hi; simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    calc ∑ i ∈ S, (a • x + b • y) i
        = ∑ i ∈ S, (a * x i + b * y i) := Finset.sum_congr rfl (fun i hi => h i hi)
      _ = a * ∑ i ∈ S, x i + b * ∑ i ∈ S, y i := by
            simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      _ ≥ a * G.v S + b * G.v S := add_le_add (mul_le_mul_of_nonneg_left (hx S) ha) (mul_le_mul_of_nonneg_left (hy S) hb)
      _ = (a + b) * G.v S := by ring
      _ = G.v S := by rw [hab]; ring
  -- Étape 3 : montrer que P est fermé (intersection de demi-espaces fermés)
  have hP_closed : IsClosed P := by
    -- CIBLE DU PROVEUR : l'intersection d'ensembles fermés est fermée
    -- Chaque demi-espace { x | ∑_{i∈S} xᵢ ≥ v(S) } est fermé (préimage continue de Ici).
    unfold P; rw [← Set.iInter_setOf]; exact isClosed_iInter (fun S => IsClosed.preimage (continuous_finsetSum S fun i _ ↦ continuous_apply i) isClosed_Ici)
  -- Étape 4 : montrer que P est non vide (prendre x = λ i. M où M = max_S v(S), alors ∑_{i∈S} M ≥ v(S))
  have hP_nonempty : P.Nonempty := by
    let M := Finset.sup' Finset.univ Finset.univ_nonempty G.v
    use fun _ => |M|
    intro S
    by_cases hS : S = ∅
    · rw [hS]; simp [G.empty_zero]
    · have hM : G.v S ≤ M := Finset.le_sup' G.v (Finset.mem_univ S)
      have hScard : (0 : ℕ) < S.card := Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hS)
      simp only [Finset.sum_const, nsmul_eq_mul]
      have habsM : M ≤ |M| := le_abs_self M
      have h1 : (1 : ℝ) ≤ S.card := Nat.one_le_cast.mpr hScard
      calc G.v S ≤ M := hM
        _ ≤ |M| := habsM
        _ = 1 * |M| := (one_mul _).symm
        _ ≤ (S.card : ℝ) * |M| := by gcongr
  -- Étape 5 : montrer que P est borné inférieurement (trivialement, 0 comme borne inf ne suffit pas,
  -- mais P est borné car ∑ᵢ xᵢ ≤ v(N) + C pour un certain C, par condition balancée).
  -- En dimension finie, fermé + borné inf + borné sup = compact.
  -- En fait on a besoin de : l'ensemble { x ∈ P | ∑ᵢ xᵢ ≤ v(N) } est compact,
  -- ou de façon équivalente P ∩ { x | ∑ᵢ xᵢ < v(N) + 1 } est compact.
  -- Clé : montrer que pour x ∈ P, ∑ᵢ xᵢ ≥ v(N) (en sommant sur tous les singletons + grande coalition).
  -- Attendez : on a besoin de ∑ᵢ xᵢ = v(N) pour l'appartenance au noyau.
  -- Stratégie : minimiser ∑ᵢ xᵢ sur P. Comme P est fermé et borné inférieurement, le minimum existe.
  -- Si min ∑ᵢ xᵢ > v(N), appliquer hyperplane_separation.
  -- If min ∑ᵢ xᵢ = v(N), we have our Core allocation.
  -- La condition balancée assure min ∑ᵢ xᵢ ≤ v(N).
  -- Étape 6 : définir l'ensemble « sous la grande coalition »
  let K : Set (N → ℝ) := { x ∈ P | (∑ i : N, x i) < G.v Finset.univ }
  -- Étape 7 : montrer que K est vide (balancé ⟹ min sur P ≤ v(N))
  -- De façon équivalente : ∀ x ∈ P, v(N) ≤ ∑ᵢ xᵢ
  -- Cela découle de : si ∑ᵢ xᵢ < v(N) pour un certain x ∈ P, la condition balancée
  -- donne une contradiction via Farkas/hyperplane_separation.
  have hK_empty : K = ∅ := by
    -- CIBLE DU PROVEUR : montrer qu'aucun x ∈ P n'a ∑ᵢ xᵢ < v(N)
    -- Par contradiction : supposer x ∈ P avec ∑ᵢ xᵢ < v(N).
    -- Les poids balancés w(S) = ∑ᵢ xᵢ - ∑_{i∉S} xᵢ... en fait c'est la partie difficile.
    -- Utiliser hyperplane_separation sur le cône des violations de poids balancés.
    unfold K
    rw [Set.eq_empty_iff_forall_notMem]
    intro x
    simp only [Set.mem_sep, Set.mem_setOf, not_and]
    intro hx hlt
    have := hx Finset.univ
    linarith
  -- Étape 8 : puisque K = ∅, il existe x ∈ P avec ∑ᵢ xᵢ = v(N)
  -- (P est non vide + fermé + aucun élément n'a de somme < v(N) ⟹ un élément a somme = v(N))
  have hCore : G.Core.Nonempty := by
    -- CIBLE DU PROVEUR : extraire l'allocation du noyau depuis P \ K
    -- Étape 1 (Plan) : établir la borne inférieure sur ∑ pour tout x ∈ P
    have hP_lb : ∀ x ∈ P, ∑ i : N, x i ≥ G.v Finset.univ := by
      intro x hx
      exact hx Finset.univ
    -- Étape 2 (Plan) : existence de x ∈ P avec ∑ x i ≤ v(N).
    -- C'est le contenu LP-dual de `hb : G.Balanced`. Sans
    -- ProperCone.hyperplane_separation instancié pour ce polyèdre, l'existence
    -- ne peut pas être dérivée ici. Marqué pour escalade Directeur.
    have hb_witness : ∃ x ∈ P, ∑ i : N, x i ≤ G.v Finset.univ := by
      -- Étape A (cône-séparation → décodage, PROUVÉ). Pour tout `t > 0`, le pont
      -- `balancedUnit_notIn_augCone` (Bridge #3941) produit `balancedUnit(v(N)+t) ∉
      -- augCone` ; `hyperplane_separation_point` (Mathlib) donne un séparateur `f`
      -- qui est nonneg sur `augCone` et négatif sur `balancedUnit(v(N)+t)` ; le
      -- cœur de décodage `exists_preimputation_strict_core` (ConeKernel #3945)
      -- transforme `f` en un `x ∈ P` avec `∑ x ≤ v(N) + t`. C'est le témoin strict
      -- Farkas-assemblé complet.
      have hb_strict : ∀ t : ℝ, 0 < t → ∃ x ∈ P, ∑ i : N, x i ≤ G.v Finset.univ + t := by
        intro t ht
        have hNotIn : balancedUnit (G.v Finset.univ + t) ∉ augCone G.v :=
          balancedUnit_notIn_augCone G t ht hb
        obtain ⟨f, hfCone, hfSep⟩ :=
          ProperCone.hyperplane_separation_point (augCone G.v) hNotIn
        obtain ⟨x, hxP, hxle⟩ :=
          exists_preimputation_strict_core G.v ht f hfCone hfSep
        exact ⟨x, hxP, hxle⟩
      -- Étape B (crux d'atteinte). `hb_strict` donne `inf_P (∑x) ≤ v(N)` (laisser t → 0)
      -- et la rationalité de la grande coalition (`hx Finset.univ`) donne `inf_P (∑x) ≥ v(N)`,
      -- donc l'infimum est `v(N)`. On montre qu'il est ATTEINT. La tranche de sous-niveau
      -- `S₁ = {x ∈ P | ∑x ≤ v(N)+1}` est un sous-ensemble fermé de la boîte compacte
      -- `∏ᵢ Icc (v({i})) (v(N)+1 − v(N∖{i}))` (les singletons bornent `x_i` en bas,
      -- les coalitions complémentaires bornent `x_i` en haut), donc compact ; la
      -- fonctionnelle continue `∑x` atteint son minimum sur `S₁`, et une ε-contradiction
      -- contre `hb_strict` force ce minimum à être `≤ v(N)`.
      let S₁ : Set (N → ℝ) := { x ∈ P | ∑ i : N, x i ≤ G.v Finset.univ + 1 }
      have hcont : Continuous (fun (x : N → ℝ) => ∑ i : N, x i) :=
        continuous_finsetSum Finset.univ (fun i _ => continuous_apply i)
      -- S₁ est fermé : P (fermé) ∩ préimage du rayon fermé Iic sous ∑x continue.
      have hS1_closed : IsClosed S₁ :=
        hP_closed.inter (IsClosed.preimage hcont isClosed_Iic)
      -- Compacité : S₁ est contenu dans la boîte compacte ∏ᵢ Icc (v({i})) (v(N)+1 − v(N∖{i})).
      have hS1_compact : IsCompact S₁ := by
        have hB_compact : IsCompact
            (Set.pi Set.univ (fun i : N =>
              Set.Icc (G.v ({i} : Finset N)) (G.v Finset.univ + 1 - G.v (Finset.univ.erase i)))) :=
          isCompact_univ_pi (fun _ => isCompact_Icc)
        have hS1_subset : S₁ ⊆
            (Set.pi Set.univ (fun i : N =>
              Set.Icc (G.v ({i} : Finset N)) (G.v Finset.univ + 1 - G.v (Finset.univ.erase i)))) := by
          intro x hx
          obtain ⟨hxP, hxle⟩ := hx
          rw [Set.mem_univ_pi]
          intro i
          refine ⟨?_, ?_⟩
          · -- borne inférieure : la contrainte de coalition singleton donne v({i}) ≤ x i.
            have hi := hxP ({i} : Finset N)
            rwa [Finset.sum_singleton] at hi
          · -- borne supérieure : contrainte de coalition complémentaire + plafond ∑x ≤ v(N)+1.
            -- ∑ j, x j = x i + ∑ j ∈ univ.erase i, x j  (partition autour de i).
            have hpart : ∑ j : N, x j = x i + ∑ j ∈ Finset.univ.erase i, x j := by
              have key := Finset.add_sum_erase Finset.univ (fun j => x j) (Finset.mem_univ i)
              linarith
            have hcompl := hxP (Finset.univ.erase i)
            linarith
        exact IsCompact.of_isClosed_subset hB_compact hS1_closed hS1_subset
      -- S₁ est non vide : hb_strict avec t = 1 donne un témoin avec ∑x ≤ v(N)+1.
      have hS1_nonempty : S₁.Nonempty := by
        obtain ⟨x, hxP, hxle⟩ := hb_strict (1 : ℝ) (by norm_num)
        exact ⟨x, hxP, hxle⟩
      -- ∑x atteint son minimum sur la tranche compacte S₁.
      obtain ⟨m, hm_mem, hmmin⟩ :=
        hS1_compact.exists_isMinOn hS1_nonempty hcont.continuousOn
      obtain ⟨hmP_m, hmle_one⟩ := hm_mem
      -- La valeur minimale est ≤ v(N) : si ∑m > v(N), `hb_strict` avec la moitié du
      -- jeu donne `y ∈ P` avec ∑y < ∑m ≤ v(N)+1 (donc `y ∈ S₁`), contredisant la minimalité.
      have hle : ∑ i : N, m i ≤ G.v Finset.univ := by
        by_cases h : ∑ i : N, m i ≤ G.v Finset.univ
        · exact h
        · exfalso
          simp only [not_le] at h
          have heps : 0 < (∑ i : N, m i - G.v Finset.univ) / 2 := half_pos (by linarith)
          obtain ⟨y, hyP, hyle⟩ := hb_strict _ heps
          have hyS1 : y ∈ S₁ := ⟨hyP, by linarith⟩
          have hminOn : ∀ z, z ∈ S₁ → ∑ i : N, m i ≤ ∑ i : N, z i := hmmin
          have hmin_le : ∑ i : N, m i ≤ ∑ i : N, y i := hminOn y hyS1
          linarith
      exact ⟨m, hmP_m, hle⟩
    obtain ⟨x, hxP, hxle⟩ := hb_witness
    refine ⟨x, ?_, hxP⟩
    have hxge : ∑ i : N, x i ≥ G.v Finset.univ := hP_lb x hxP
    linarith


  exact hCore

/-- Bondareva-Shapley : le noyau est non vide si et seulement si le jeu est balancé. -/
theorem bondareva_shapley :
    G.Core.Nonempty ↔ G.Balanced :=
  ⟨bondareva_shapley_forward G, bondareva_shapley_backward G⟩

/-! ## Vecteurs marginaux et noyau convexe (Shapley 1971) -/

section MarginalVector

/-- Une énumération fixée de `N` via `Fintype.equivFin`. -/
noncomputable def enumIndex (i : N) : ℕ := (Fintype.equivFin N i).val

/-- La coalition « préfixe » : tous les joueurs dont l'index d'énumération est `< k`. -/
noncomputable def prefixCoalition (k : ℕ) : Finset N :=
  Finset.univ.filter (fun i => enumIndex i < k)

private lemma prefixCoalition_zero : (prefixCoalition 0 : Finset N) = ∅ := by
  ext i; simp [prefixCoalition]

private lemma enumIndex_lt_card (i : N) : enumIndex i < Fintype.card N :=
  (Fintype.equivFin N i).isLt

private lemma prefixCoalition_full :
    (prefixCoalition (Fintype.card N) : Finset N) = Finset.univ := by
  ext i
  simp only [prefixCoalition, Finset.mem_filter, Finset.mem_univ, true_and,
             iff_true]
  exact enumIndex_lt_card i

private lemma enumIndex_injective : Function.Injective (enumIndex : N → ℕ) := by
  intro a b hab
  exact (Fintype.equivFin N).injective (Fin.ext hab)

variable (G : TUGame N)

/-- Marginal vector along the fixed enumeration. -/
noncomputable def marginalVector : Allocation N := fun i =>
  G.v (prefixCoalition (enumIndex i + 1)) - G.v (prefixCoalition (enumIndex i))

private lemma prefixCoalition_succ_eq (k : ℕ) (hk : k < Fintype.card N) :
    (prefixCoalition (k + 1) : Finset N) =
      prefixCoalition k ∪ {(Fintype.equivFin N).symm ⟨k, hk⟩} := by
  ext j
  simp only [prefixCoalition, Finset.mem_union, Finset.mem_filter,
             Finset.mem_univ, Finset.mem_singleton, true_and]
  constructor
  · intro hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · left; exact h
    · right
      have : (Fintype.equivFin N j) = ⟨k, hk⟩ := Fin.ext h
      have := congrArg (Fintype.equivFin N).symm this
      simpa using this
  · rintro (h | h)
    · exact Nat.lt_succ_of_lt h
    · subst h
      show enumIndex _ < k + 1
      unfold enumIndex; simp

/-- Télé-scopage : le vecteur marginal somme à v(N). -/
lemma marginalVector_efficient :
    ∑ i : N, G.marginalVector i = G.v Finset.univ := by
  have hreidx : ∑ i : N, G.marginalVector i =
      ∑ k : Fin (Fintype.card N), G.marginalVector ((Fintype.equivFin N).symm k) :=
    (Equiv.sum_comp (Fintype.equivFin N).symm G.marginalVector).symm
  rw [hreidx]
  have hterm : ∀ k : Fin (Fintype.card N),
      G.marginalVector ((Fintype.equivFin N).symm k) =
        G.v (prefixCoalition (k.val + 1)) - G.v (prefixCoalition k.val) := by
    intro k
    unfold marginalVector enumIndex
    simp
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hrange : ∑ k : Fin (Fintype.card N),
        (G.v (prefixCoalition (k.val + 1)) - G.v (prefixCoalition k.val)) =
      ∑ k ∈ Finset.range (Fintype.card N),
        (G.v (prefixCoalition (k + 1)) - G.v (prefixCoalition k)) := by
    rw [← Finset.sum_range fun k => G.v (prefixCoalition (k + 1)) - G.v (prefixCoalition k)]
  rw [hrange, Finset.sum_range_sub fun k => G.v (prefixCoalition k),
      prefixCoalition_zero, prefixCoalition_full, G.empty_zero]
  ring

private lemma sdiff_subset_prefix_of_max
    (S : Finset N) (i : N)
    (hmax : ∀ j ∈ S, enumIndex j ≤ enumIndex i) :
    S.erase i ⊆ prefixCoalition (enumIndex i) := by
  intro j hj
  rw [Finset.mem_erase] at hj
  obtain ⟨hji, hjS⟩ := hj
  simp only [prefixCoalition, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_or_eq_of_le (hmax j hjS) with h | h
  · exact h
  · exact absurd (enumIndex_injective h) hji

/-- Pour les jeux convexes, le vecteur marginal domine v(S) sur chaque coalition. -/
lemma marginalVector_dominates (h : G.Convex) :
    ∀ S : Finset N, ∑ i ∈ S, G.marginalVector i ≥ G.v S := by
  intro S
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hSempty : S = ∅ := Finset.card_eq_zero.mp (hcard.trans hn)
      subst hSempty
      simp [G.empty_zero]
    · have hSne : S.Nonempty := Finset.card_pos.mp (hcard ▸ hn)
      obtain ⟨i, hiS, hmax⟩ := S.exists_max_image enumIndex hSne
      set S' := S.erase i with hS'def
      have hS'card : S'.card = n - 1 := by
        rw [hS'def, Finset.card_erase_of_mem hiS, hcard]
      have hS'lt : S'.card < n := by rw [hS'card]; omega
      have hSinsert : S = insert i S' := by
        rw [hS'def, Finset.insert_erase hiS]
      have hi_notin : i ∉ S' := Finset.notMem_erase i S
      have ih' : ∑ j ∈ S', G.marginalVector j ≥ G.v S' :=
        ih S'.card hS'lt S' rfl
      have hSerase_sub : S' ⊆ prefixCoalition (enumIndex i) := by
        rw [hS'def]; exact sdiff_subset_prefix_of_max S i hmax
      have hi_notin_pref : i ∉ (prefixCoalition (enumIndex i) : Finset N) := by
        simp only [prefixCoalition, Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_irrefl _
      have hconv := h S' (prefixCoalition (enumIndex i)) i hSerase_sub hi_notin_pref
      have hi_idx_lt : enumIndex i < Fintype.card N := enumIndex_lt_card i
      have hpref_succ :
          (prefixCoalition (enumIndex i) ∪ {i} : Finset N) =
            prefixCoalition (enumIndex i + 1) := by
        have heq : (Fintype.equivFin N).symm ⟨enumIndex i, hi_idx_lt⟩ = i := by
          unfold enumIndex; simp
        rw [prefixCoalition_succ_eq (enumIndex i) hi_idx_lt, heq]
      have hmv_i : G.marginalVector i =
          G.v (prefixCoalition (enumIndex i) ∪ {i}) -
          G.v (prefixCoalition (enumIndex i)) := by
        unfold marginalVector; rw [hpref_succ]
      have hSeq : S' ∪ {i} = S := by
        rw [hSinsert, Finset.insert_eq, Finset.union_comm]
      have hkey : G.marginalVector i ≥ G.v S - G.v S' := by
        rw [hmv_i]
        have hcv : G.v (S' ∪ {i}) - G.v S' ≤
            G.v (prefixCoalition (enumIndex i) ∪ {i}) -
            G.v (prefixCoalition (enumIndex i)) := hconv
        rw [hSeq] at hcv
        linarith
      have hsumeq : ∑ j ∈ S, G.marginalVector j =
          G.marginalVector i + ∑ j ∈ S', G.marginalVector j := by
        rw [hSinsert, Finset.sum_insert hi_notin]
      rw [hsumeq]
      linarith

/-- Pour les jeux convexes, le vecteur marginal appartient au noyau. -/
theorem marginalVector_mem_core (h : G.Convex) :
    G.marginalVector ∈ G.Core :=
  ⟨G.marginalVector_efficient, G.marginalVector_dominates h⟩

end MarginalVector

/-- Pour les jeux convexes, le noyau est non vide (Shapley 1971, « Cores of convex
    games »). Preuve constructive directe via les vecteurs marginaux : le long de
    toute énumération fixée de N, le vecteur de contribution marginale appartient
    au noyau lorsque le jeu est convexe. -/
theorem convex_core_nonempty (h : G.Convex) :
    G.Core.Nonempty :=
  ⟨G.marginalVector, G.marginalVector_mem_core h⟩

end TUGame
