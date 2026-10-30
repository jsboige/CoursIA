/-
  Mécanismes de Groves et pivot de Clarke — Compagnon Lean
  =======================================================

  Généralisation du certificat `SocialChoice.MechanismDesign` : là où le bloc
  `VCGCombinatorial` calcule à la main les paiements du pivot de Clarke sur
  DEUX témoins (2 et 3 enchérisseurs) et délègue chaque valeur à `decide`, ce
  module prouve le théorème qui les engendre — le **théorème de Groves**
  (Groves, 1973) et l'admissibilité individuelle du **pivot de Clarke**
  (Clarke, 1971) — sur un domaine ABSTRAIT : un nombre quelconque d'agents,
  un espace de types fini et un ensemble d'issues fini quelconques.

  Cadre (quasi-linéaire, stratégies dominantes) :

  * `v i (θ i) a` : valorisation de l'agent `i` de type `θ i` pour l'issue `a` ;
  * `aStar θ` : règle d'allocation, supposée maximiser le bien-être **reporté** ;
  * transferts de Groves : `p i θ = Σ_{j≠i} v j (θ j) (aStar θ) + g i θ`,
    où le terme `g i θ` ne dépend pas du report de `i` lui-même.

  Résultats prouvés :

  1. `groves_DSIC` — tout mécanisme de Groves est **DSIC** : dire la vérité
     est une stratégie dominante pour chaque agent ;
  2. `clarke_DSIC` — le pivot de Clarke (`g i θ = − max_a Σ_{j≠i} v j (θ j) a`)
     est une instance de Groves, donc DSIC lui aussi ;
  3. `clarke_IR` — sous valorisations positives, le pivot de Clarke est
     **individuellement rationnel** : participer rapporte au moins 0 ;
  4. `badAlloc_violates_DSIC` — **témoin négatif** : sans maximalité du
     bien-être, le même schéma de transferts cesse d'être DSIC (utilité
     sincère 0, utilité de la déviation 2).

  Ce que ce module NE prouve PAS (portée honnête) : la version bayésienne
  (BIC), l'optimalité en revenu (Myerson-Satterthwaite / équivalence de
  revenu), l'équilibre budgétaire, ni la sélection d'équilibre. `aStar` est
  une **hypothèse** du théorème, pas un calcul : le moteur de synthèse reste
  hors Lean (#22381 jalon 1, `amd_synthesis.py`) ; ce module certifie le
  schéma d'incitations, pas les instances que le solveur énumère.

  Références : T. Groves, « Incentives in Teams » (Econometrica, 1973) ;
  E. H. Clarke, « Multipart Pricing of Public Goods » (1971) ;
  Maschler, Solan & Zamir, *Game Theory*, ch. 10 (Vickrey-Clarke-Groves).

  Voir #22381 (jalon 2, extension formelle nommée par le critère 6),
  #12205 (chaîne Loi II), #4980 (convention i18n FR/EN).
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace SocialChoice.Groves

open Finset

variable {N A T : Type*} [Fintype N] [DecidableEq N]

/-! ## Cadre : valorisations, bien-être, profil reporté

  Un **profil reporté** `θ : N → T` associe à chaque agent le type qu'il
  annonce. `N` = agents, `T` = espace de types (un seul espace, symétrique),
  `A` = ensemble des issues (allocation, projet public, etc.). -/

/-- Bien-être social du profil reporté `θ` à l'issue `a`. -/
def welfare (v : N → T → A → ℤ) (θ : N → T) (a : A) : ℤ := ∑ j, v j (θ j) a

/-- Bien-être des agents **autres que `i`** au profil reporté `θ`, issue `a`. -/
def othersWelfare (v : N → T → A → ℤ) (θ : N → T) (a : A) (i : N) : ℤ :=
  ∑ j ∈ univ.erase i, v j (θ j) a

/-- Transfert de **Groves** : la part de l'agent `i` au bien-être des autres
    dans l'issue retenue, plus un terme additif `g i θ` qui ne doit dépendre
    que du report des **autres** agents (hypothèse `hg` du théorème). -/
def grovesPayment (v : N → T → A → ℤ) (aStar : (N → T) → A) (g : N → (N → T) → ℤ)
    (θ : N → T) (i : N) : ℤ :=
  othersWelfare v θ (aStar θ) i + g i θ

/-- Gain de l'agent `i`, de **type vrai** `t`, quand le profil reporté est `rep`.
    C'est l'utilité quasi-linéaire : valorisation de l'issue moins ce que
    l'agent paie, soit ici valorisation plus transfert reçu. -/
def payoff (v : N → T → A → ℤ) (aStar : (N → T) → A) (g : N → (N → T) → ℤ)
    (i : N) (t : T) (rep : N → T) : ℤ :=
  v i t (aStar rep) + grovesPayment v aStar g rep i

/-! ## Deux lemmes de structure

  Le premier est le seul point où le bien-être total se scinde en « les
  autres » plus « soi-même » ; le second dit que la part des autres est
  insensible au report propre. -/

/-- Le bien-être total se scinde en part des autres et part propre. -/
lemma othersWelfare_add_own (v : N → T → A → ℤ) (θ : N → T) (a : A) (i : N) :
    othersWelfare v θ a i + v i (θ i) a = welfare v θ a := by
  unfold othersWelfare welfare
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

/-- La part des autres agents ne dépend pas du report de `i`. -/
lemma othersWelfare_update (v : N → T → A → ℤ) (θ : N → T) (i : N) (t' : T) (a : A) :
    othersWelfare v (Function.update θ i t') a i = othersWelfare v θ a i := by
  unfold othersWelfare
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mem_erase] at hj
  rw [Function.update_apply, if_neg hj.1]

/-! ## Théorème de Groves — tout mécanisme de Groves est DSIC

  L'argument tient en une ligne : l'utilité de `i` vaut le bien-être total du
  profil vrai **plus** une constante indépendante de son report ; comme
  `aStar` maximise le bien-être, dévier ne peut que le diminuer. C'est
  exactement ce que le calcul ci-dessous reproduit. -/

/-- **Théorème de Groves.** Si `aStar` maximise le bien-être reporté et si le
    terme `g i ·` ne dépend pas du report de `i`, alors aucun agent n'a
    intérêt à dévier unilatéralement du report sincère. -/
theorem groves_DSIC
    (v : N → T → A → ℤ) (aStar : (N → T) → A)
    (hStar : ∀ θ a, welfare v θ a ≤ welfare v θ (aStar θ))
    (g : N → (N → T) → ℤ)
    (hg : ∀ (i : N) (θ θ' : N → T), (∀ j, j ≠ i → θ j = θ' j) → g i θ = g i θ')
    (i : N) (θ : N → T) (t' : T) :
    payoff v aStar g i (θ i) θ ≥ payoff v aStar g i (θ i) (Function.update θ i t') := by
  have hg' : g i (Function.update θ i t') = g i θ :=
    hg i _ θ (fun j hj => by rw [Function.update_apply, if_neg hj])
  have hothers := othersWelfare_update v θ i t' (aStar (Function.update θ i t'))
  have hstar := hStar θ (aStar (Function.update θ i t'))
  have e1 := othersWelfare_add_own v θ (aStar (Function.update θ i t')) i
  have e2 := othersWelfare_add_own v θ (aStar θ) i
  rw [← e1, ← e2] at hstar
  unfold payoff grovesPayment
  rw [hothers, hg']
  linarith

/-! ## Pivot de Clarke — la part des autres au maximum

  Le choix canonique de `g` est l'opposé du bien-être maximal des autres :
  l'agent paie exactement l'externalité qu'il impose. `A` doit être non vide
  (sinon le maximum n'a pas de sens) et fini (sinon il n'est pas atteint). -/

variable [Fintype A] [Nonempty A]

/-- Bien-être maximal des agents autres que `i`, au profil reporté `θ`.
    Atteint : `A` est fini et non vide. -/
noncomputable def othersMax (v : N → T → A → ℤ) (θ : N → T) (i : N) : ℤ :=
  (univ : Finset A).sup' Finset.univ_nonempty (fun a => othersWelfare v θ a i)

/-- Transferts du **pivot de Clarke** : l'agent `i` reçoit l'opposé de
    l'externalité qu'il impose aux autres agents. -/
noncomputable def clarkeTransfer (v : N → T → A → ℤ) : N → (N → T) → ℤ :=
  fun i θ => - othersMax v θ i

/-- Le maximum des autres ne dépend pas du report de `i`. -/
lemma othersMax_congr (v : N → T → A → ℤ) (i : N) {θ θ' : N → T}
    (h : ∀ j, j ≠ i → θ j = θ' j) : othersMax v θ i = othersMax v θ' i := by
  unfold othersMax
  have hfun : (fun a => othersWelfare v θ a i) = (fun a => othersWelfare v θ' a i) := by
    funext a
    unfold othersWelfare
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_erase] at hj
    rw [h j hj.1]
  rw [hfun]

/-- Le maximum des autres **majore** la part de tout autre agent. -/
lemma othersWelfare_le_othersMax (v : N → T → A → ℤ) (θ : N → T) (i : N) (a : A) :
    othersWelfare v θ a i ≤ othersMax v θ i := by
  unfold othersMax
  exact Finset.le_sup' (fun a => othersWelfare v θ a i) (Finset.mem_univ a)

/-- Le maximum des autres est **atteint** par une issue. -/
lemma exists_othersMax (v : N → T → A → ℤ) (θ : N → T) (i : N) :
    ∃ a : A, othersMax v θ i = othersWelfare v θ a i := by
  unfold othersMax
  obtain ⟨a, -, ha⟩ :=
    Finset.exists_mem_eq_sup' (s := (univ : Finset A)) (H := Finset.univ_nonempty)
      (f := fun a => othersWelfare v θ a i)
  exact ⟨a, ha⟩

/-- **Pivot de Clarke : DSIC.** Instance directe du théorème de Groves. -/
theorem clarke_DSIC
    (v : N → T → A → ℤ) (aStar : (N → T) → A)
    (hStar : ∀ θ a, welfare v θ a ≤ welfare v θ (aStar θ))
    (i : N) (θ : N → T) (t' : T) :
    payoff v aStar (clarkeTransfer v) i (θ i) θ
      ≥ payoff v aStar (clarkeTransfer v) i (θ i) (Function.update θ i t') := by
  refine groves_DSIC v aStar hStar (clarkeTransfer v) ?_ i θ t'
  intro i θ θ' h
  unfold clarkeTransfer
  rw [othersMax_congr v i h]

/-- **Pivot de Clarke : rationalité individuelle.** Sous valorisations
    positives, participer rapporte au moins 0 : l'agent ne paie jamais plus
    que ce que l'issue retenue lui rapporte, puisque le maximum des autres est
    majoré par le bien-être total qu'il atteint lui-même. -/
theorem clarke_IR
    (v : N → T → A → ℤ) (aStar : (N → T) → A)
    (hStar : ∀ θ a, welfare v θ a ≤ welfare v θ (aStar θ))
    (hv : ∀ (i : N) (t : T) (a : A), 0 ≤ v i t a)
    (i : N) (θ : N → T) :
    0 ≤ payoff v aStar (clarkeTransfer v) i (θ i) θ := by
  obtain ⟨a0, ha0⟩ := exists_othersMax v θ i
  have hstar := hStar θ a0
  have e1 := othersWelfare_add_own v θ a0 i
  have e2 := othersWelfare_add_own v θ (aStar θ) i
  rw [← e1, ← e2] at hstar
  have hnonneg := hv i (θ i) a0
  unfold payoff grovesPayment clarkeTransfer
  rw [ha0]
  linarith

/-! ## Témoin négatif — la maximalité du bien-être est indispensable

  Deux agents, types booléens, issue booléenne, valorisation 1 si le type
  vaut `true` ET l'issue vaut `true`. L'allocation `badAlloc` ignore le second
  agent : elle rend l'issue = `¬ (report du premier)`. Les transferts gardent
  la forme de Groves, mais comme `badAlloc` ne maximise plus le bien-être,
  l'agent 0 préfère mentir : sincère il obtient 0, en déviant il obtient 2. -/

namespace Counterexample

/-- Valorisation : 1 si le type et l'issue valent `true`, 0 sinon. -/
def val (_i : Bool) (t : Bool) (a : Bool) : ℤ := if t && a then 1 else 0

/-- Allocation **non efficace** : l'issue est la négation du report de l'agent 0. -/
def badAlloc (θ : Bool → Bool) : Bool := !(θ false)

/-- Transfert additionnel nul (on isole l'effet de l'allocation). -/
def zeroTransfer (_ : Bool) (_ : Bool → Bool) : ℤ := 0

/-- Sur deux agents, la part des autres pour l'agent `false` est le terme `true`. -/
lemma othersWelfare_false (v : Bool → Bool → Bool → ℤ) (θ : Bool → Bool) (a : Bool) :
    othersWelfare v θ a false = v true (θ true) a := by
  unfold othersWelfare
  have h : (univ : Finset Bool).erase false = {true} := by decide
  rw [h, Finset.sum_singleton]

/-- Sur deux agents, la part des autres pour l'agent `true` est le terme `false`. -/
lemma othersWelfare_true (v : Bool → Bool → Bool → ℤ) (θ : Bool → Bool) (a : Bool) :
    othersWelfare v θ a true = v false (θ false) a := by
  unfold othersWelfare
  have h : (univ : Finset Bool).erase true = {false} := by decide
  rw [h, Finset.sum_singleton]

/-- L'allocation `badAlloc` ne maximise pas le bien-être : au profil où les
    deux agents ont le type `true`, elle rend `false` alors que `true` ferait
    strictement mieux. C'est la prémisse du théorème de Groves qui échoue. -/
theorem badAlloc_not_efficient :
    ¬ ∀ θ a, welfare val θ a ≤ welfare val θ (badAlloc θ) := by
  intro h
  have hbad : badAlloc (fun _ : Bool => true) = false := by simp [badAlloc]
  have hw1 : welfare val (fun _ : Bool => true) true = 2 := by
    unfold welfare
    have hsplit : (univ : Finset Bool) = insert true ({false} : Finset Bool) := by decide
    rw [hsplit, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [val]
  have hw0 : welfare val (fun _ : Bool => true) false = 0 := by
    unfold welfare
    have hsplit : (univ : Finset Bool) = insert true ({false} : Finset Bool) := by decide
    rw [hsplit, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [val]
  have h0 := h (fun _ => true) true
  rw [hbad, hw1, hw0] at h0
  omega

/-- **Témoin négatif** : sans maximalité du bien-être, les transferts de
    Groves ne sont plus DSIC. L'agent 0, de type vrai `true`, obtient 0 en
    rapportant sincèrement et 2 en déviant vers `false`. -/
theorem badAlloc_violates_DSIC :
    ∃ (i : Bool) (θ : Bool → Bool) (t' : Bool),
      payoff val badAlloc zeroTransfer i (θ i) θ
        < payoff val badAlloc zeroTransfer i (θ i) (Function.update θ i t') := by
  refine ⟨false, fun _ => true, false, ?_⟩
  have htruth : payoff val badAlloc zeroTransfer false true (fun _ => true) = 0 := by
    rw [payoff, grovesPayment, othersWelfare_false]
    simp [val, badAlloc, zeroTransfer]
  have hdev :
      payoff val badAlloc zeroTransfer false true (Function.update (fun _ => true) false false) = 2 := by
    rw [payoff, grovesPayment, othersWelfare_false]
    simp [val, badAlloc, zeroTransfer, Function.update]
  rw [htruth, hdev]
  norm_num

end Counterexample

end SocialChoice.Groves
