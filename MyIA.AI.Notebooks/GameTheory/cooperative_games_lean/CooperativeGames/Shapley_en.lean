/-
  Shapley Value — Axiomatic Characterization
  ==========================================

  This file formalizes the Shapley axiomatic approach to fair division:
  - The four Shapley axioms (Efficiency, Symmetry, Null Player, Additivity)
  - The Shapley value formula
  - The uniqueness theorem

  Reference: L.S. Shapley, "A Value for N-Person Games" (1953)

  i18n convention (cycle 39 ratified, see `docs/lean/i18n-inventory-cycle-38.md`):
  headers, sections, docstrings and intra-proof comments in English;
  the Lean tactical code (symbol names, Mathlib references, lemma statements,
  proofs) stays in English to preserve Mathlib compatibility.

  EN sibling (`Shapley_en.lean`) of the FR canonical (`Shapley.lean`), per
  EPIC #4980 Lean FR+EN i18n convention (See #4980). Code tactique byte-identique
  modulo namespace wrap (`CooperativeGames_en` anti-collision) and cross-namespace
  import (`import CooperativeGames.Basic_en` instead of `CooperativeGames.Basic`).
  Lean tactical code 100% byte-identical between siblings.
-/

import CooperativeGames.Basic_en
import Mathlib.Data.Nat.Choose.Sum

open TUGame

namespace CooperativeGames_en

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ## Solutions and axioms -/

/-- Un concept de solution associe à chaque jeu un vecteur de paiements -/
def Solution (N : Type*) [Fintype N] := TUGame N → (N → ℝ)

namespace Solution

variable (φ : Solution N)

/-! ## The four Shapley axioms -/

/-- Axiome 1 : Efficience
    Les paiements s'additionnent pour donner la valeur de la grande coalition -/
def Efficiency : Prop :=
  ∀ G : TUGame N, ∑ i : N, φ G i = G.v Finset.univ

/-- Two players are symmetric in G if they bring equal contributions -/
def SymmetricPlayers (G : TUGame N) (i j : N) : Prop :=
  ∀ S : Finset N, i ∉ S → j ∉ S →
    G.v (S ∪ {i}) = G.v (S ∪ {j})

/-- Axiome 2 : Symétrie
    Des joueurs symétriques reçoivent des paiements égaux -/
def Symmetry : Prop :=
  ∀ G : TUGame N, ∀ i j : N,
    SymmetricPlayers G i j → φ G i = φ G j

/-- A player i is null if they bring no value to any coalition -/
def NullPlayer (G : TUGame N) (i : N) : Prop :=
  ∀ S : Finset N, i ∉ S →
    G.v (S ∪ {i}) = G.v S

/-- Axiome 3 : Joueur nul
    Un joueur sans contribution marginale reçoit 0 -/
def NullPlayerAxiom : Prop :=
  ∀ G : TUGame N, ∀ i : N,
    NullPlayer G i → φ G i = 0

/-- Somme de deux jeux TU -/
def AddGames (G H : TUGame N) : TUGame N where
  v := fun S => G.v S + H.v S
  empty_zero := by simp [G.empty_zero, H.empty_zero]

/-- Axiome 4 : Additivité
    La solution d'une somme de jeux est la somme des solutions -/
def Additivity : Prop :=
  ∀ G H : TUGame N, ∀ i : N,
    φ (AddGames G H) i = φ G i + φ H i

end Solution

/-! ## The Shapley value -/

/-- Le coefficient de Shapley pour une coalition de taille s dans un jeu à n joueurs :
    c(s,n) = s! * (n - s - 1)! / n! -/
noncomputable def shapleyCoef (n s : ℕ) : ℝ :=
  (Nat.factorial s * Nat.factorial (n - s - 1)) / Nat.factorial n

/-- The Shapley value: average marginal contribution over all orderings -/
noncomputable def shapleyValue (G : TUGame N) (i : N) : ℝ :=
  ∑ S ∈ (Finset.univ.filter fun S => i ∉ S),
    shapleyCoef (Fintype.card N) S.card * G.marginalContribution i S

/-- Le concept de solution de Shapley -/
noncomputable def shapleySolution : Solution N :=
  fun G i => shapleyValue G i

/-! ## Characterization via unanimity games (any axiomatic solution) -/

/-- Toute solution efficiente, symétrique et respectant le joueur nul donne 1/|T|
    aux joueurs de T et 0 aux joueurs hors de T dans le jeu d'unanimité u_T.
    Utilise directement les trois axiomes (efficience, symétrie, joueur nul). -/
private theorem phi_unanimity (φ : Solution N)
    (h_eff : φ.Efficiency)
    (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (T : Finset N) (hT : T.Nonempty) (i : N) :
    φ (TUGame.unanimityGame T hT) i =
    if i ∈ T then (1 : ℝ) / T.card else 0 := by
  classical
  split_ifs with hiT
  · -- Cas i ∈ T : par symétrie tous les j ∈ T obtiennent la même valeur, par efficience somme = 1
    -- Étape 1 : Par symétrie, tous les j ∈ T ont la même valeur que i
    have h_eq : ∀ j ∈ T, φ (unanimityGame T hT) j = φ (unanimityGame T hT) i := by
      intro j hjT
      by_cases hij : j = i; · subst hij; rfl
      · apply h_sym
        intro S hiS hjS
        simp only [unanimityGame]
        have hni : ¬(T ⊆ S ∪ {i}) := by
          intro h
          have := h hjT
          simp only [Finset.mem_union, Finset.mem_singleton] at this
          tauto
        have hnj : ¬(T ⊆ S ∪ {j}) := by
          intro h
          have := h hiT
          simp only [Finset.mem_union, Finset.mem_singleton] at this
          tauto
        rw [if_neg hni, if_neg hnj]
    -- Étape 2 : Les joueurs hors de T sont nuls
    have h_null_out : ∀ j, j ∉ T → φ (unanimityGame T hT) j = 0 := by
      intro j hjT'
      apply h_null
      intro S hjS
      simp only [unanimityGame]
      have hto : T ⊆ S ∪ {j} → T ⊆ S := fun h k hk => by
        have hk' := h hk
        simp only [Finset.mem_union, Finset.mem_singleton] at hk'
        rcases hk' with hk' | hk'
        · exact hk'
        · subst hk'; exact absurd hk hjT'
      split_ifs
      · rfl
      · exfalso; exact ‹¬T ⊆ S› (hto ‹T ⊆ S ∪ {j}›)
      · exfalso; exact ‹¬T ⊆ S ∪ {j}› (fun k hk => Finset.mem_union_left {j} (‹T ⊆ S› hk))
      · rfl
    -- Étape 3 : Efficience : somme = v(univ) = 1
    have h_sum_one : ∑ j, φ (unanimityGame T hT) j = 1 := by
      have := h_eff (unanimityGame T hT)
      simp only [unanimityGame, if_pos (Finset.subset_univ T)] at this
      exact this
    -- Étape 4 : ∑_{∈T} = 1 (car ∑_{∉T} = 0)
    have h_sum_T : ∑ j ∈ T, φ (unanimityGame T hT) j = 1 := by
      have h_out_sum : ∑ j ∈ Finset.filter (fun j => j ∉ T) Finset.univ,
          φ (unanimityGame T hT) j = 0 :=
        Finset.sum_eq_zero (fun j hj => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact h_null_out j hj)
      have h_split : ∑ j ∈ T, φ (unanimityGame T hT) j +
          ∑ j ∈ Finset.filter (fun j => j ∉ T) Finset.univ,
          φ (unanimityGame T hT) j = ∑ j, φ (unanimityGame T hT) j := by
        have : Finset.filter (fun j => j ∉ T) Finset.univ = Tᶜ := by
          ext j; simp
        rw [this]
        rw [Finset.sum_add_sum_compl T (fun j => φ (unanimityGame T hT) j)]
      linarith
    -- Étape 5 : Tous égaux dans T, donc T.card * φ G i = 1
    have h_card : (T.card : ℝ) * φ (unanimityGame T hT) i = 1 := by
      have : ∑ _ ∈ T, φ (unanimityGame T hT) i = (T.card : ℝ) * φ (unanimityGame T hT) i := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [← this]
      exact (Finset.sum_congr rfl (fun j hj => (h_eq j hj).symm)).trans h_sum_T
    -- Étape 6 : Donc φ G i = 1 / T.card
    have hT0 : (T.card : ℝ) ≠ 0 := by
      have hcp : 0 < T.card := Finset.Nonempty.card_pos hT
      norm_cast
      omega
    field_simp
    linarith
  · -- Cas i ∉ T : i est un joueur nul dans unanimityGame T
    apply h_null
    intro S hiS
    simp only [TUGame.unanimityGame]
    have hto : T ⊆ S ∪ {i} → T ⊆ S := fun h j hj => by
      obtain hks | hki := Finset.mem_union.mp (h hj)
      · exact hks
      · exact absurd (Finset.mem_singleton.mp hki) (fun heq => hiT (heq ▸ hj))
    split_ifs <;> try rfl
    · exfalso; exact ‹¬T ⊆ S› (hto ‹T ⊆ S ∪ {i}›)
    · exfalso; exact ‹¬T ⊆ S ∪ {i}› (fun j hj => Finset.mem_union_left {i} (‹T ⊆ S› hj))

/-! ## Key properties -/

namespace ShapleyValue

/-- The Shapley value satisfies the null-player axiom -/
theorem shapley_null_player (G : TUGame N) (i : N)
    (h : Solution.NullPlayer G i) : shapleyValue G i = 0 := by
  unfold shapleyValue
  apply Finset.sum_eq_zero
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  have hmc : G.marginalContribution i S = 0 := by
    unfold TUGame.marginalContribution
    rw [h S hS]
    ring
  simp [hmc]

/-- Valeur de Shapley pour les jeux d'unanimité :
    φᵢ(uₜ) = 1/|T| si i ∈ T, sinon 0
    SCHÉMA DE PREUVE :
    Cas i ∉ T : i est un joueur nul dans u_T, donc φᵢ = 0 par `shapley_null_player`.
      Preuve de joueur nul : v(S∪{i}) = (si T⊆S∪{i} alors 1 sinon 0).
      Puisque i ∉ T, T⊆S∪{i} ↔ T⊆S. Donc v(S∪{i}) = v(S).
    Cas i ∈ T : par symétrie (`shapley_symmetric`), tous les j ∈ T ont la même valeur.
      Par efficience (`shapley_efficient`), la somme vaut v(univ) = 1.
      Donc chacun obtient 1/|T|.
      Argument direct : `marginalContribution i S = 1` ssi T\{i} ⊆ S et i ∉ S.
      Comptage de tels S de taille s : C(n-|T|-1+1, s-|T|+1) ... donne 1/|T|. -/

private theorem shapleyCoef_shift (n s : ℕ) (hs : s + 2 ≤ n) :
    (s + 1 : ℝ) * shapleyCoef n s = (n - s - 1 : ℝ) * shapleyCoef n (s + 1) := by
  unfold shapleyCoef
  rw [← mul_div_assoc, ← mul_div_assoc]
  congr 1
  rw [show n - (s + 1) - 1 = n - s - 2 from by omega]
  rw [Nat.factorial_succ s]
  have hm : n - s - 1 = (n - s - 2) + 1 := by omega
  rw [hm, Nat.factorial_succ (n - s - 2)]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  -- Convertir ↑(n - s - 2) en ↑n - ↑s - 2 via les lemmes de cast pour la soustraction dans ℕ
  rw [Nat.cast_sub (by omega : (2 : ℕ) ≤ n - s)]
  rw [Nat.cast_sub (by omega : (s : ℕ) ≤ n)]
  ring

private theorem shapleyCoef_top (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * shapleyCoef n (n - 1) = 1 := by
  unfold shapleyCoef
  have h1 : n - (n - 1) - 1 = 0 := by omega
  simp only [h1, Nat.factorial_zero, Nat.cast_one, mul_one]
  -- Objectif : ↑n * (↑(n-1).factorial / ↑n.factorial) = 1
  have hfact : (n : ℝ) * ↑(Nat.factorial (n - 1)) = ↑(Nat.factorial n) := by
    have hsucc : n = (n - 1) + 1 := by omega
    rw [hsucc, Nat.factorial_succ]
    simp [Nat.cast_mul]
  rw [← mul_div_assoc, hfact, div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]

private theorem pos_term_eq (G : TUGame N) :
    (∑ S, shapleyCoef (Fintype.card N) S.card * ∑ i ∈ Finset.univ \ S, G.v (S ∪ {i})) =
    (∑ T, (T.card : ℝ) * shapleyCoef (Fintype.card N) (T.card - 1) * G.v T) := by
  classical
  -- Étape 1 : Faire passer le coefficient dans la somme interne à gauche
  simp only [Finset.mul_sum]
  -- Étape 2 : Prouver ponctuellement : ↑|T| * c * v = ∑ j ∈ T, c * v
  have hT (T : Finset N) :
      (T.card : ℝ) * shapleyCoef (Fintype.card N) (T.card - 1) * G.v T =
      ∑ j ∈ (T : Finset N), shapleyCoef (Fintype.card N) (T.card - 1) * G.v T := by
    rw [mul_assoc, ← nsmul_eq_mul, ← Finset.sum_const]
  -- Étape 3 : Réécrire le membre de droite via hT ponctuellement
  rw [Finset.sum_congr rfl (fun T _ => hT T)]
  -- Étape 4 : Aplatir les deux côtés en sommes sigma, puis appliquer la bijection
  -- MGD : ∑ x, ∑ i ∈ univ\x, f(x,i) → ∑ p ∈ univ.sigma(fun x => univ\x), f(p.1,p.2)
  rw [Finset.sum_sigma']
  -- MHD : ∑ T, ∑ j ∈ T, g(T,j) → ∑ p ∈ univ.sigma(fun T => T), g(p.1,p.2)
  rw [Finset.sum_sigma']
  -- Maintenant bijection sur les types sigma : (S, i) avec i∉S ↦ (S∪{i}, i)
  -- f : (S, i) ↦ (S∪{i}, i), g : (T, j) ↦ (T\{j}, j)
  refine Finset.sum_bij' (fun p _ => ⟨p.1 ∪ {p.2}, p.2⟩)
      (fun p _ => ⟨p.1 \ {p.2}, p.2⟩) ?_ ?_ ?_ ?_ ?_
  -- f dans le range : p.2 ∈ p.1 ∪ {p.2}
  · intro p hp
    simp only [Finset.mem_sigma] at hp ⊢
    exact ⟨Finset.mem_univ _, by
      rw [Finset.union_comm]
      exact Finset.mem_insert_self _ _⟩
  -- g dans le range : p.2 ∈ univ \ (p.1 \ {p.2}) (i.e. p.2 ∉ p.1 \ {p.2})
  · intro p hp
    simp only [Finset.mem_sigma] at hp ⊢
    exact ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      intro h
      exact Finset.notMem_sdiff_of_mem_right (Finset.mem_singleton_self _) h⟩⟩
  -- g∘f = id : (S∪{i})\{i} = S quand i∉S
  · intro p hp
    simp only [Finset.mem_sigma] at hp
    have hni : p.2 ∉ p.1 := (Finset.mem_sdiff.mp hp.2).2
    simp only
    -- but : ⟨(p.fst ∪ {p.snd}) \ {p.snd}, p.snd⟩ = p
    ext1
    · exact Finset.union_sdiff_cancel_right (Finset.disjoint_singleton_right.mpr hni)
    · rfl
  -- f∘g = id : (T\{j})∪{j} = T quand j∈T
  · intro p hp
    simp only [Finset.mem_sigma] at hp
    simp only
    ext1
    · rw [Finset.union_comm, ← Finset.insert_eq,
        (Finset.insert_sdiff_self_of_mem hp.2)]
    · rfl
  -- valeurs cohérentes : c(|S|) * v(S∪{i}) = c(|S∪{i}|-1) * v(S∪{i})
  · intro p hp
    simp only [Finset.mem_sigma] at hp
    have hni : p.2 ∉ p.1 := (Finset.mem_sdiff.mp hp.2).2
    have : p.1.card = (p.1 ∪ {p.2}).card - 1 := by
      rw [Finset.union_comm, ← Finset.insert_eq,
        Finset.card_insert_of_notMem hni, Nat.add_sub_cancel]
    simp only [this]

/-- La valeur de Shapley vérifie l'efficience.
    SCHÉMA DE PREUVE :
    ∑ᵢ φᵢ(G) = ∑ᵢ ∑_{S:i∉S} c(|S|,n) · [v(S∪{i}) - v(S)]
    On échange l'ordre des sommations :
    = ∑_S ∑_{i∉S} c(|S|,n) · [v(S∪{i}) - v(S)]
    = ∑_S c(|S|,n) · ∑_{i∉S} [v(S∪{i}) - v(S)]
    Chaque i ∉ S apporte sa valeur marginale à S.
    Télescopage : ∑_{i∉S} v(S∪{i}) - (n-|S|)·v(S)
    Après réarrangement sur tous les S, les termes s'annulent pour laisser
    v(univ) - v(∅) = v(univ).
    Identité clé : chaque v(S) apparaît comme +v(S) avec coefficient c(|S|-1,n)
    et comme -v(S) avec coefficient c(|S|,n)·(n-|S|), qui s'annulent. -/
theorem shapley_efficient (G : TUGame N) :
    ∑ i : N, shapleyValue G i = G.v Finset.univ := by
  classical
  unfold shapleyValue TUGame.marginalContribution
  -- Échange : ∑ᵢ ∑_{S:i∉S} f(i,S) = ∑_S ∑_{i:i∉S} f(i,S)
  have hswap :
    (∑ i ∈ Finset.univ, ∑ S ∈ Finset.univ.filter (fun S => i ∉ S),
        shapleyCoef (Fintype.card N) S.card * (G.v (S ∪ {i}) - G.v S)) =
    (∑ S ∈ Finset.univ, ∑ i ∈ Finset.univ.filter (fun i => i ∉ S),
        shapleyCoef (Fintype.card N) S.card * (G.v (S ∪ {i}) - G.v S)) :=
    Finset.sum_comm' (fun i S => by simp)
  rw [hswap]
  -- Factoriser shapleyCoef hors de la somme interne
  simp only [← Finset.mul_sum]
  -- Séparer la soustraction dans les sommes internes : ∑ (a - b) = ∑ a - ∑ b
  simp only [Finset.sum_sub_distrib]
  -- Distribuer mul_sub à l'intérieur de la somme
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  -- Simplifier le terme négatif : v(x) constant en x_1, somme = (n - |x|) • v(x)
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp only [← Finset.sdiff_eq_filter, Finset.card_univ_diff]
  -- Réindexer le terme positif : ∑ S ∑_{i∉S} c(|S|)*v(S∪{i}) = ∑ T, |T|*c(|T|-1)*v(T)
  rw [pos_term_eq]
  -- Combiner en une seule somme de différences
  rw [← Finset.sum_sub_distrib]
  -- Isoler le terme univ : tous les T ≠ univ ont un coefficient nul (shapleyCoef_shift)
  have : ∑ x ∈ Finset.univ,
      (↑x.card * shapleyCoef (Fintype.card N) (x.card - 1) * G.v x -
        shapleyCoef (Fintype.card N) x.card * (↑(Fintype.card N - x.card) * G.v x)) =
      (↑(Finset.univ : Finset N).card *
        shapleyCoef (Fintype.card N) ((Finset.univ : Finset N).card - 1) * G.v Finset.univ -
        shapleyCoef (Fintype.card N) (Finset.univ : Finset N).card *
          (↑(Fintype.card N - (Finset.univ : Finset N).card) * G.v Finset.univ)) :=
    Finset.sum_eq_single (Finset.univ : Finset N)
      (fun T _ hT => by
        have hcard : T.card < (Finset.univ : Finset N).card :=
          Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hT)
        simp only [Finset.card_univ] at hcard
        rw [sub_eq_zero]
        by_cases hT0 : T.card = 0
        · -- T = ∅ : les deux termes s'annulent car v(∅) = 0
          have : T = ∅ := Finset.card_eq_zero.mp hT0
          simp [this, G.empty_zero]
        · -- T ≠ ∅ : le décalage de coefficient s'applique
          have hTcard : 1 ≤ T.card := Nat.pos_of_ne_zero hT0
          have hshift := shapleyCoef_shift (Fintype.card N) (T.card - 1) (by omega)
          have h1 : (↑(T.card - 1) + 1 : ℝ) = ↑T.card := by
            norm_cast; exact Nat.sub_add_cancel hTcard
          have h2 : (T.card - 1 + 1 : ℕ) = T.card := Nat.sub_add_cancel hTcard
          have h3 : (↑(Fintype.card N) - ↑(T.card - 1) - 1 : ℝ) = ↑(Fintype.card N - T.card) := by
            have hle : T.card ≤ Fintype.card N := Finset.card_le_univ T
            rw [Nat.cast_sub hle, ← h1]
            ring
          rw [h1, h2, h3] at hshift
          rw [hshift]
          ring)
      (fun h => (h (Finset.mem_univ _)).elim)
  rw [this]
  -- Simplifier : n - card univ = 0, donc le terme négatif s'annule
  simp only [Finset.card_univ, tsub_self, Nat.cast_zero]
  -- Terme positif : n * c(n,n-1) * v(univ) = v(univ) car n * c(n,n-1) = 1
  by_cases hN : IsEmpty N
  · -- Cas vide : les deux côtés se réduisent à 0
    simp [G.empty_zero]
  · -- Cas non vide : shapleyCoef_top s'applique
    haveI : Nonempty N := not_isEmpty_iff.mp hN
    have hn : 0 < Fintype.card N := Fintype.card_pos_iff.mpr ⟨Classical.arbitrary N⟩
    rw [shapleyCoef_top (Fintype.card N) hn, one_mul]
    simp only [zero_mul, mul_zero, sub_zero]

/-- La valeur de Shapley vérifie la symétrie.
    SCHÉMA DE PREUVE (bijection par échange) :
    Définir f : {S | i ∉ S} → {T | j ∉ T} par :
    - f(S) = S                  si j ∉ S (les deux i,j absents)
    - f(S) = (S\{j})∪{i}        si j ∈ S (échanger j avec i)

    Propriétés :
    (1) |f(S)| = |S|, donc shapleyCoef n |f(S)| = shapleyCoef n |S|
    (2) v(f(S)∪{j}) - v(f(S)) = v(S∪{i}) - v(S) :
      - Cas j ∉ S : f(S)=S, marginalContribution j S = v(S∪{j})-v(S) = v(S∪{i})-v(S)
        (par h avec i,j tous deux ∉ S)
      - Cas j ∈ S : f(S)=(S\{j})∪{i}, f(S)∪{j}=S∪{i}, et
        v(f(S)) = v((S\{j})∪{i}) = v((S\{j})∪{j}) = v(S)
        (par h appliqué à S' = S\{j}, puisque i∉S\{j} et j∉S\{j})
    (3) f est une bijection (inverse : échanger i↔j)

    Utiliser Finset.sum_bij pour conclure ∑_S g(S) = ∑_T g'(T). -/
theorem shapley_symmetric (G : TUGame N) (i j : N)
    (h : Solution.SymmetricPlayers G i j) :
    shapleyValue G i = shapleyValue G j := by
  classical
  by_cases heq : i = j
  · subst heq; rfl
  -- Preuve de bijection d'échange utilisant Finset.sum_bij
  -- La fonction directe envoie {S | i ∉ S} → {T | j ∉ T} en échangeant j↔i
  unfold shapleyValue TUGame.marginalContribution
  set src := Finset.univ.filter (fun S : Finset N => i ∉ S)
  set tgt := Finset.univ.filter (fun S : Finset N => j ∉ S)
  have hmem_src {S} : S ∈ src ↔ i ∉ S := by simp [src]
  have hmem_tgt {T} : T ∈ tgt ↔ j ∉ T := by simp [tgt]
  -- Définir les applications directe et inverse séparément pour qu'elles se réduisent correctement
  let fwd (S : Finset N) (_ : S ∈ src) : Finset N :=
    if hSj : j ∈ S then (S.erase j) ∪ {i} else S
  let inv (T : Finset N) (_ : T ∈ tgt) : Finset N :=
    if hTi : i ∈ T then (T.erase i) ∪ {j} else T
  refine Finset.sum_bij' fwd inv ?fwd_mem ?inv_mem ?left_inv ?right_inv ?hfg
  case fwd_mem =>
    intro S hS
    rw [hmem_src] at hS
    rw [hmem_tgt]
    -- Goal: j ∉ fwd S hS✝ where fwd S _ = if j ∈ S then (S.erase j) ∪ {i} else S
    simp only [fwd]
    split_ifs with hSj
    · -- fwd = (S.erase j) ∪ {i}, prove j ∉ (S.erase j) ∪ {i}
      rw [Finset.mem_union]
      intro h
      rcases h with h | h
      · exact Finset.notMem_erase j S h
      · exact heq (Finset.mem_singleton.mp h).symm
    · exact hSj
  case inv_mem =>
    intro T hT
    rw [hmem_tgt] at hT
    rw [hmem_src]
    simp only [inv]
    split_ifs with hTi
    · -- inv = (T.erase i) ∪ {j}, prove i ∉ (T.erase i) ∪ {j}
      rw [Finset.mem_union]
      intro h
      rcases h with h | h
      · exact Finset.notMem_erase i T h
      · exact heq (Finset.mem_singleton.mp h)
    · exact hTi
  case left_inv =>
    intro S hS
    rw [hmem_src] at hS
    dsimp only [fwd, inv]
    split_ifs with hSj hTi
    · -- j ∈ S, i ∈ (S.erase j) ∪ {i}: the real case
      have hnI : i ∉ S.erase j := fun h' => hS (Finset.mem_of_mem_erase h')
      have : ((S.erase j) ∪ {i}).erase i = S.erase j := by
        rw [Finset.erase_union_distrib]
        simp [Finset.erase_eq_self.mpr hnI]
      rw [this, Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hSj]
    · -- j ∈ S, i ∉ (S.erase j) ∪ {i}: impossible
      exact absurd (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))) hTi
    · -- j ∉ S: fwd(S) = S, inner condition i ∈ S auto-closed by hS, identity
      rfl
  case right_inv =>
    intro T hT
    rw [hmem_tgt] at hT
    dsimp only [fwd, inv]
    split_ifs with hSj hTi
    · -- hSj : i ∈ T, hTi : j ∈ T.erase i ∪ {j}: the real case
      have hnJ : j ∉ T.erase i := fun h => hT (Finset.mem_of_mem_erase h)
      have : ((T.erase i) ∪ {j}).erase j = T.erase i := by
        rw [Finset.erase_union_distrib]
        simp [Finset.erase_eq_self.mpr hnJ]
      rw [this, Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hSj]
    · -- hSj : i ∈ T, hTi : j ∉ T.erase i ∪ {j}: impossible
      exact absurd (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))) hTi
    · -- i ∉ T: inv(T) = T, inner condition j ∈ T auto-closed by hT, identity
      rfl
  case hfg =>
    intro S hS
    rw [hmem_src] at hS
    dsimp only [fwd]
    split_ifs with hSj
    · -- j ∈ S: fwd(S) = (S.erase j) ∪ {i}
      have hnI : i ∉ S.erase j := fun h' => hS (Finset.mem_of_mem_erase h')
      have hcard : ((S.erase j) ∪ {i} : Finset N).card = S.card := by
        have hge : 0 < S.card := Finset.card_pos.mpr ⟨j, hSj⟩
        rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hnI),
          Finset.card_erase_of_mem hSj, Finset.card_singleton]
        omega
      simp only [hcard]
      have hv1 : G.v (S ∪ {i}) = G.v ((S.erase j) ∪ {i} ∪ {j}) := by
        congr 1
        rw [Finset.union_assoc, Finset.union_comm {i} {j}, ← Finset.union_assoc,
          Finset.union_comm (S.erase j) {j}, ← Finset.insert_eq,
          Finset.insert_erase hSj]
      have hv2 : G.v S = G.v ((S.erase j) ∪ {i}) := by
        have hsym := h (S.erase j) hnI (Finset.notMem_erase j S)
        rw [hsym]
        congr 1
        rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hSj]
      rw [hv1, hv2]
    · -- j ∉ S: fwd(S) = S
      have hsym := h S hS hSj
      rw [hsym]

/-- Shapley value on unanimity games: each player in T gets 1/|T| -/
theorem shapley_unanimity (T : Finset N) (hT : T.Nonempty) (i : N) :
    shapleyValue (TUGame.unanimityGame T hT) i =
    if i ∈ T then (1 : ℝ) / T.card else 0 := by
  classical
  split_ifs with hiT
  · -- Cas i ∈ T : par symétrie tous les j ∈ T obtiennent la même valeur, par efficience la somme vaut 1
    have h : shapleySolution (TUGame.unanimityGame T hT) i =
        if i ∈ T then (1 : ℝ) / T.card else 0 :=
      phi_unanimity (φ := shapleySolution)
        shapley_efficient shapley_symmetric
        (fun G i => shapley_null_player G i) T hT i
    simp only [shapleySolution, if_pos hiT] at h
    exact h
  · -- Cas i ∉ T : i est un joueur nul dans le jeu d'unanimité T
    apply shapley_null_player
    intro S hiS
    simp only [TUGame.unanimityGame]
    have hto : T ⊆ S ∪ {i} → T ⊆ S := fun h j hj => by
      obtain hj' | hj' := Finset.mem_union.mp (h hj)
      · exact hj'
      · exact absurd (Finset.mem_singleton.mp hj') (fun heq => hiT (heq ▸ hj))
    split_ifs
    · rfl
    · exfalso; exact ‹¬T ⊆ S› (hto ‹T ⊆ S ∪ {i}›)
    · exfalso; exact ‹¬T ⊆ S ∪ {i}› (fun j hj => Finset.mem_union_left {i} (‹T ⊆ S› hj))
    · rfl

/-- The Shapley value satisfies additivity -/
theorem shapley_additive (G H : TUGame N) (i : N) :
    shapleyValue (Solution.AddGames G H) i =
    shapleyValue G i + shapleyValue H i := by
-- Linearity of summation
  unfold shapleyValue Solution.AddGames TUGame.marginalContribution
  simp only
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

end ShapleyValue

/-! ## Scalar multiplication and finite sums of games -/

namespace Solution

/-- Scalar multiplication of a TU game by a real number -/
def SmulGame (c : ℝ) (G : TUGame N) : TUGame N where
  v := fun S => c * G.v S
  empty_zero := by simp [G.empty_zero]

/-- The zero TU game -/
def zeroGame : TUGame N where
  v := fun _ => 0
  empty_zero := rfl

/-- phi of the zero game is 0 (every player is null) -/
theorem phi_zero_game (φ : Solution N) (h_null : φ.NullPlayerAxiom) (i : N) :
    φ zeroGame i = 0 :=
  h_null zeroGame i (fun S _ => rfl)

/-- Sum of games indexed by a Finset -/
noncomputable def finsetSumGames {ι : Type*} (s : Finset ι) (f : ι → TUGame N) : TUGame N where
  v := fun S => ∑ j ∈ s, (f j).v S
  empty_zero := Finset.sum_eq_zero (fun j _ => (f j).empty_zero)

/-- Inserting into finsetSumGames gives AddGames -/
theorem finsetSumGames_insert {ι : Type*} [DecidableEq ι] {j : ι} {s : Finset ι}
    (f : ι → TUGame N) (hjs : j ∉ s) :
    finsetSumGames (insert j s) f = AddGames (finsetSumGames s f) (f j) := by
  ext S
  simp only [finsetSumGames, AddGames, Finset.sum_insert hjs]
  ring

end Solution

/-! ## Finite additivity for the Shapley value -/

namespace ShapleyValue

/-- shapleyValue is homogeneous: shapleyValue (SmulGame c G) i = c * shapleyValue G i -/
theorem shapley_smulGame (c : ℝ) (G : TUGame N) (i : N) :
    shapleyValue (Solution.SmulGame c G) i = c * shapleyValue G i := by
  have hSmul : (Solution.SmulGame c G).v = fun S => c * G.v S := rfl
  unfold shapleyValue TUGame.marginalContribution
  rw [hSmul]
  have hLHS : (fun S => shapleyCoef (Fintype.card N) S.card *
        (c * G.v (S ∪ {i}) - c * G.v S)) =
      (fun S => c * (shapleyCoef (Fintype.card N) S.card *
        (G.v (S ∪ {i}) - G.v S))) := by
    funext S; ring
  simp only [hLHS]
  rw [Finset.mul_sum]

/-- The Shapley value is additive -/
theorem shapley_addGames (G H : TUGame N) (i : N) :
    shapleyValue (Solution.AddGames G H) i = shapleyValue G i + shapleyValue H i := by
  unfold shapleyValue TUGame.marginalContribution
  simp only [Solution.AddGames]
  have h_key (S : Finset N) :
      shapleyCoef (Fintype.card N) S.card * (G.v (S ∪ {i}) + H.v (S ∪ {i}) - (G.v S + H.v S))
      = shapleyCoef (Fintype.card N) S.card * (G.v (S ∪ {i}) - G.v S)
        + shapleyCoef (Fintype.card N) S.card * (H.v (S ∪ {i}) - H.v S) := by ring
  rw [Finset.sum_congr rfl (fun S _ => h_key S), Finset.sum_add_distrib]

end ShapleyValue

/-! ## Mobius inversion (Harsanyi dividends) -/

namespace Mobius

/-- Le coefficient de Mobius (dividende de Harsanyi) du jeu G pour la coalition T :
    a_T = Σ_{R ⊆ T} (-1)^{|T|-|R|} * G.v(R)
    Cela capture la valeur « pure » de la coalition T au-delà de ses sous-ensembles. -/
noncomputable def mobiusCoeff (G : TUGame N) (T : Finset N) : ℝ :=
  ∑ R ∈ Finset.univ.filter (fun R => R ⊆ T),
    ((-1 : ℝ) ^ (T.card - R.card)) * G.v R

/-- A game built from a weighted unanimity game -/
noncomputable def weightedUnanimity (c : ℝ) (T : Finset N) (hT : T.Nonempty) : TUGame N where
  v := fun S => c * (if T ⊆ S then (1 : ℝ) else 0)
  empty_zero := by
    simp only [Finset.subset_empty, if_neg hT.ne_empty, mul_zero]

/-- The Mobius reconstruction of G: G = sum_{T nonempty} a_T * u_T -/
noncomputable def mobiusReconstruction (G : TUGame N) : TUGame N where
  v := fun S => ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S),
      mobiusCoeff G T
  empty_zero := by
    classical
    apply Finset.sum_eq_zero
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨hne, hsub⟩ := hT
    have : T = ∅ := Finset.subset_empty.mp hsub
    rw [this] at hne
    exact absurd rfl hne.ne_empty

/-- Lemme : pour R ⊂ S, la somme alternée sur les sur-ensembles T de R contenus dans S est nulle.
    Σ_{T : R ⊆ T ⊆ S} (-1)^(|T|-|R|) = (1-1)^|S\R| = 0 quand S\R est non vide.
    Preuve : bijection T ↦ T \ R vers (S \ R).powerset, puis sum_powerset_neg_one_pow_card. -/
private theorem mobius_inner_sum_zero (S R : Finset N) (hR : R ⊆ S) (hne : R ≠ S) :
    ∑ T ∈ Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S),
        ((-1 : ℝ) ^ (T.card - R.card)) = 0 := by
  classical
  have hSR_ne : (S \ R).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    have h_sub : S ⊆ R := Finset.sdiff_eq_empty_iff_subset.mp h_empty
    exact hne (subset_antisymm hR h_sub)
  -- Réindexer via la bijection T ↦ T \ R vers (S \ R).powerset
  have h_eq :
    ∑ T ∈ Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S),
        ((-1 : ℝ) ^ (T.card - R.card)) =
    ∑ m ∈ (S \ R).powerset, ((-1 : ℝ) ^ m.card) := by
    refine Finset.sum_bij' (fun T _ => T \ R) (fun m _ => R ∪ m) ?_ ?_ ?_ ?_ ?_
    -- hi: forward map lands in target
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      obtain ⟨hRT, hTS⟩ := hT
      rw [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff hTS (Finset.Subset.refl R)
    -- hj: backward map lands in source
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Finset.mem_powerset] at hm
      exact ⟨Finset.subset_union_left,
             Finset.union_subset hR (hm.trans Finset.sdiff_subset)⟩
    -- left_inv: R ∪ (T \ R) = T
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      obtain ⟨hRT, _⟩ := hT
      show R ∪ (T \ R) = T
      rw [Finset.union_comm R (T \ R), Finset.sdiff_union_of_subset hRT]
    -- right_inv: (R ∪ m) \ R = m
    · intro m hm
      simp only [Finset.mem_powerset] at hm
      show (R ∪ m) \ R = m
      have h_disj : Disjoint R m := (Finset.subset_sdiff.mp hm).2.symm
      exact Finset.union_sdiff_cancel_left h_disj
    -- h: summand equality via card_sdiff_of_subset
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      obtain ⟨hRT, _⟩ := hT
      congr 1
      exact (Finset.card_sdiff_of_subset hRT).symm
  rw [h_eq]
  -- Rewrite: ∑ m ∈ powerset, (-1 : ℝ)^m.card = ↑(∑ m, (-1 : ℤ)^m.card)
  rw [show (∑ m ∈ (S \ R).powerset, ((-1 : ℝ) ^ m.card)) =
        ↑(∑ m ∈ (S \ R).powerset, ((-1 : ℤ) ^ m.card)) from by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun m _hm => ?_)
    have h_neg_one : (-1 : ℝ) = ↑(-1 : ℤ) := by rw [Int.cast_neg, Int.cast_one]
    rw [h_neg_one]
    exact (Int.cast_pow (-1 : ℤ) m.card).symm]
  rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty hSR_ne, Int.cast_zero]

/-- Lemma: for R = S, the inner sum equals 1 (the singleton {S} contributes (-1)^0 = 1) -/
private theorem mobius_inner_sum_self (S R : Finset N) (_hR : R ⊆ S) (hRS : R = S) :
    ∑ T ∈ Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S),
        ((-1 : ℝ) ^ (T.card - R.card)) = 1 := by
  rw [hRS]
  have hSingleton : Finset.univ.filter (fun T => S ⊆ T ∧ T ⊆ S) = {S} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨hle, hge⟩ => le_antisymm hge hle,
           fun h => by rw [h]; exact ⟨Finset.Subset.refl S, Finset.Subset.refl S⟩⟩
  rw [hSingleton, Finset.sum_singleton, Nat.sub_self, pow_zero]

/-- Inversion de Mobius : v(S) = Σ_{∅≠T⊆S} a_T
    Tout jeu se décompose de manière unique en somme de jeux d'unanimité pondérés
    (dividendes de Harsanyi).
    Preuve : inclusion-exclusion sur le treillis des sous-ensembles.
    Σ_{T: ∅≠T⊆S} a_T = Σ_T Σ_{R⊆T} (-1)^(|T|-|R|) · v(R)
    Après échange des sommes : Σ_R v(R) · Σ_{T: R⊆T⊆S} (-1)^(|T|-|R|) = Σ_R v(R)·δ_{R,S} = v(S). -/
private theorem mobius_decomposition_axiom (G : TUGame N) (S : Finset N) :
    G.v S = ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S),
        mobiusCoeff G T := by
  classical
  simp only [mobiusCoeff]
  -- Échanger l'ordre de sommation
  have h_comm :
      ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S),
          ∑ R ∈ Finset.univ.filter (fun R => R ⊆ T),
            ((-1 : ℝ) ^ (T.card - R.card)) * G.v R =
      ∑ R ∈ (Finset.univ : Finset (Finset N)),
          ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ R ⊆ T ∧ T ⊆ S),
            ((-1 : ℝ) ^ (T.card - R.card)) * G.v R :=
    Finset.sum_comm' (s := Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S))
      (t := fun T => Finset.univ.filter (fun R => R ⊆ T))
      (t' := (Finset.univ : Finset (Finset N)))
      (s' := fun R => Finset.univ.filter (fun T => T.Nonempty ∧ R ⊆ T ∧ T ⊆ S))
      (fun T R => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact ⟨⟨h.1.1, h.2, h.1.2⟩, trivial⟩
        · intro h
          exact ⟨⟨h.1.1, h.1.2.2⟩, h.1.2.1⟩)
  rw [h_comm]
  -- Maintenant montrer que chaque R contribue soit G.v R (si R = S) soit 0 (sinon)
  suffices h : ∀ R ∈ (Finset.univ : Finset (Finset N)),
      ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ R ⊆ T ∧ T ⊆ S),
          ((-1 : ℝ) ^ (T.card - R.card)) * G.v R =
        if R = S then G.v R else 0 by
    simp only [Finset.mem_univ, forall_true_left] at h
    simp_rw [h]
    -- ∑ R : Finset N, if R = S then G.v R else 0 = G.v S
    exact (Fintype.sum_ite_eq' S (fun R => G.v R)).symm
  intro R _hR
  by_cases hRS : R = S
  -- Cas R = S
  · rw [if_pos hRS, hRS]
    by_cases hSe : S = ∅
    -- S = ∅ : le filtre est vide, la somme vaut 0 = G.v ∅
    · rw [hSe]
      have hFilter : (Finset.univ : Finset (Finset N)).filter
          (fun T => T.Nonempty ∧ (∅ : Finset N) ⊆ T ∧ T ⊆ (∅ : Finset N)) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem (fun T hT => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
        have hTe : T = ∅ := (Finset.subset_empty).mp hT.2.2
        subst hTe
        exact Finset.not_nonempty_empty hT.1
      rw [G.empty_zero, hFilter, Finset.sum_empty]
    -- S ≠ ∅ : le filtre vaut {S}, la somme vaut 1 * G.v S
    · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSe
      have hSingleton : Finset.univ.filter (fun T => T.Nonempty ∧ S ⊆ T ∧ T ⊆ S) = {S} := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun ⟨_, hST, hTS⟩ => le_antisymm hTS hST,
               fun h => by subst h; exact ⟨hSne, Finset.Subset.refl _, Finset.Subset.refl _⟩⟩
      rw [hSingleton, Finset.sum_singleton, Nat.sub_self, pow_zero, one_mul]
  -- Cas R ≠ S
  · rw [if_neg hRS]
    by_cases hRsub : R ⊆ S
    -- Sous-cas R ⊆ S, R ≠ S
    · by_cases hRe : R = ∅
      -- R = ∅ : G.v ∅ = 0
      · rw [hRe]
        simp [G.empty_zero]
      -- R ≠ ∅, R ⊆ S, R ≠ S
      · have hRne := Finset.nonempty_iff_ne_empty.mpr hRe
        have hfilter : Finset.univ.filter (fun T => T.Nonempty ∧ R ⊆ T ∧ T ⊆ S) =
            Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S) := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun ⟨hTne, hRT, hTS⟩ => ⟨hRT, hTS⟩,
                 fun ⟨hRT, hTS⟩ => ⟨hRne.mono hRT, hRT, hTS⟩⟩
        rw [hfilter]
        have : ∑ T ∈ Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S),
            ((-1 : ℝ) ^ (T.card - R.card)) * G.v R =
          (∑ T ∈ Finset.univ.filter (fun T => R ⊆ T ∧ T ⊆ S),
              ((-1 : ℝ) ^ (T.card - R.card))) * G.v R := by
          rw [Finset.sum_mul]
        rw [this, mobius_inner_sum_zero S R hRsub hRS, zero_mul]
    -- Sous-cas R ⊄ S : aucun T ne satisfait R ⊆ T ⊆ S
    · have hfilter : Finset.univ.filter (fun T => T.Nonempty ∧ R ⊆ T ∧ T ⊆ S) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem (fun T hT => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
        obtain ⟨_, hRT, hTS⟩ := hT
        exact hRsub (hRT.trans hTS)
      rw [hfilter, Finset.sum_empty]

theorem mobius_decomposition (G : TUGame N) (S : Finset N) :
    G.v S = ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S),
        mobiusCoeff G T :=
  mobius_decomposition_axiom G S

end Mobius

/-! ## Uniqueness theorem -/

/- Théorème d'unicité de Shapley :
    La valeur de Shapley est l'unique solution satisfaisant les quatre axiomes.
    Stratégie de preuve : montrer que toute solution axiomatique φ coïncide avec
    `shapleyValue` sur les jeux d'unanimité (phi_unanimity + phi_eq_shapley),
    puis étendre à tous les jeux via la décomposition de Mobius et l'additivité. -/

/-- phi coincides with shapleyValue on unanimity games -/
private theorem phi_eq_shapley (φ : Solution N)
    (h_eff : φ.Efficiency)
    (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (T : Finset N) (hT : T.Nonempty) (i : N) :
    φ (TUGame.unanimityGame T hT) i = shapleyValue (TUGame.unanimityGame T hT) i := by
  rw [phi_unanimity φ h_eff h_sym h_null T hT i,
      ShapleyValue.shapley_unanimity T hT i]

/-- Symmetry of players in T within SmulGame c u_T -/
private theorem sym_in_smulUnanimity (φ : Solution N)
    (h_sym : φ.Symmetry)
    (c : ℝ) (T : Finset N) (hT : T.Nonempty) (i j : N) (hiT : i ∈ T) (hjT : j ∈ T) (hij : i ≠ j) :
    φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i =
    φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j := by
  apply h_sym
  intro S hiS hjS
  simp only [Solution.SmulGame, TUGame.unanimityGame]
  have hni : ¬(T ⊆ S ∪ {i}) := by
    intro h; have := h hjT
    simp only [Finset.mem_union, Finset.mem_singleton] at this; tauto
  have hnj : ¬(T ⊆ S ∪ {j}) := by
    intro h; have := h hiT
    simp only [Finset.mem_union, Finset.mem_singleton] at this; tauto
  rw [if_neg hni, if_neg hnj]

/-- Null players outside T in SmulGame c u_T -/
private theorem null_outside_smulUnanimity (φ : Solution N)
    (h_null : φ.NullPlayerAxiom)
    (c : ℝ) (T : Finset N) (hT : T.Nonempty) (k : N) (hkT : k ∉ T) :
    φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) k = 0 :=
  h_null (Solution.SmulGame c (TUGame.unanimityGame T hT)) k
    (fun S _ => by
      simp only [Solution.SmulGame, TUGame.unanimityGame]
      have hto : T ⊆ S ∪ {k} → T ⊆ S := fun h m hm => by
        obtain hms | hmk := Finset.mem_union.mp (h hm)
        · exact hms
        · exact absurd (Finset.mem_singleton.mp hmk) (fun heq => hkT (heq ▸ hm))
      split_ifs <;> try rfl
      · exfalso; exact ‹¬T ⊆ S› (hto ‹T ⊆ S ∪ {k}›)
      · exfalso; exact ‹¬T ⊆ S ∪ {k}› (fun m hm => Finset.mem_union_left {k} (‹T ⊆ S› hm)))

/-- φ sur un jeu d'unanimité pondéré : φ(SmulGame c u_T, i) = c * φ(u_T, i).
    Démontré directement à partir des axiomes, sans multiplication scalaire générale. -/
private theorem phi_weightedUnanimity (φ : Solution N)
    (h_eff : φ.Efficiency)
    (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (c : ℝ) (T : Finset N) (hT : T.Nonempty) (i : N) :
    φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i = c * φ (TUGame.unanimityGame T hT) i := by
  classical
  rw [phi_unanimity φ h_eff h_sym h_null T hT i]
  split_ifs with hiT
  -- Cas i ∈ T
  · -- Efficience : Σ_j φ(H, j) = H.v(univ) = c
    have h_eff_T : ∑ j : N, φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j = c := by
      have h_val : (Solution.SmulGame c (TUGame.unanimityGame T hT)).v Finset.univ = c := by
        simp [Solution.SmulGame, TUGame.unanimityGame]
      exact (h_eff (Solution.SmulGame c (TUGame.unanimityGame T hT))).trans h_val
-- Players outside T contribute 0
    have h_null_out : ∀ j, j ∉ T →
        φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j = 0 :=
      fun j hj => null_outside_smulUnanimity φ h_null c T hT j hj
-- The sum over the complement of T is 0
    have h_out_sum : ∑ j ∈ Tᶜ, φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j = 0 :=
      Finset.sum_eq_zero (fun j hj => by
        simp only [Finset.mem_compl] at hj
        exact h_null_out j hj)
    -- ∑_{j∈T} φ(j) = c
    have h_sum_T : ∑ j ∈ T, φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j = c := by
      have h_split := Finset.sum_add_sum_compl T
          (fun j => φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j)
      linarith
-- All players in T get the same value
    have h_eq : ∀ j ∈ T,
        φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) j =
        φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i := by
      intro j hjT
      by_cases hij : j = i; · subst hij; rfl
      exact (sym_in_smulUnanimity φ h_sym c T hT i j hiT hjT (Ne.symm hij)).symm
-- T.card * phi(H, i) = c
    have h_card : (T.card : ℝ) * φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i = c := by
      have : ∑ _ ∈ T, φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i =
          (T.card : ℝ) * φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [← this]
      exact (Finset.sum_congr rfl (fun j hj => (h_eq j hj).symm)).trans h_sum_T
    have hT0 : (T.card : ℝ) ≠ 0 := by
      have hcp : 0 < T.card := Finset.Nonempty.card_pos hT
      norm_cast; omega
    field_simp; linarith
  -- Cas i ∉ T
  · rw [null_outside_smulUnanimity φ h_null c T hT i hiT]; ring

/-- Any axiomatic phi coincides with shapleyValue on SmulGame c u_T -/
private theorem phi_eq_shapley_weighted (φ : Solution N)
    (h_eff : φ.Efficiency) (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (c : ℝ) (T : Finset N) (hT : T.Nonempty) (i : N) :
    φ (Solution.SmulGame c (TUGame.unanimityGame T hT)) i =
    shapleyValue (Solution.SmulGame c (TUGame.unanimityGame T hT)) i := by
  rw [phi_weightedUnanimity φ h_eff h_sym h_null c T hT i,
      ShapleyValue.shapley_smulGame c (TUGame.unanimityGame T hT) i,
      phi_eq_shapley φ h_eff h_sym h_null T hT i]

/-- phi distributes over finite sums (from binary additivity by induction) -/
private theorem phi_finsetSumGames (φ : Solution N)
    (h_null : φ.NullPlayerAxiom) (h_add : φ.Additivity)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → TUGame N) (i : N) :
    φ (Solution.finsetSumGames s f) i = ∑ j ∈ s, φ (f j) i := by
  induction s using Finset.induction with
  | empty =>
    have h : Solution.finsetSumGames (∅ : Finset ι) f = Solution.zeroGame := by
      ext S; simp [Solution.finsetSumGames, Solution.zeroGame]
    simp [h, Solution.phi_zero_game φ h_null i]
  | insert j s hjs ih =>
    rw [Solution.finsetSumGames_insert f hjs, h_add, ih, Finset.sum_insert hjs]; ring

/-- The Shapley value distributes over finite sums -/
private theorem shapley_finsetSumGames {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → TUGame N) (i : N) :
    shapleyValue (Solution.finsetSumGames s f) i = ∑ j ∈ s, shapleyValue (f j) i := by
  induction s using Finset.induction with
  | empty =>
    have h : Solution.finsetSumGames (∅ : Finset ι) f = Solution.zeroGame := by
      ext S; simp [Solution.finsetSumGames, Solution.zeroGame]
    rw [h]
    exact ShapleyValue.shapley_null_player Solution.zeroGame i (fun S _ => rfl)
  | insert j s hjs ih =>
    rw [Solution.finsetSumGames_insert f hjs, ShapleyValue.shapley_addGames, ih,
      Finset.sum_insert hjs]; ring

/-- Le jeu G est égal au finsetSumGames de ses termes de décomposition de Mobius.
    G = ∑_{T≠∅} SmulGame (mobiusCoeff G T) (unanimityGame T) -/
private theorem game_eq_mobius_sum (G : TUGame N) :
    G = Solution.finsetSumGames
      (Finset.univ.filter Finset.Nonempty)
      (fun T => if hT : T.Nonempty then
        Solution.SmulGame (Mobius.mobiusCoeff G T) (TUGame.unanimityGame T hT)
      else Solution.zeroGame) := by
  ext S
  simp only [Solution.finsetSumGames]
  classical
  -- Étape 1 : Pour T ∈ filtre Nonempty, f(T).v S = mobiusCoeff G T * (if T⊆S then 1 else 0)
  have h_term (T : Finset N) (hT : T ∈ Finset.univ.filter Finset.Nonempty) :
      (if hT' : T.Nonempty then
        Solution.SmulGame (Mobius.mobiusCoeff G T) (TUGame.unanimityGame T hT')
      else (Solution.zeroGame : TUGame N)).v S =
        Mobius.mobiusCoeff G T * (if T ⊆ S then (1 : ℝ) else 0) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    rw [dif_pos hT]
    simp only [Solution.SmulGame, TUGame.unanimityGame]
  -- Étape 2 : a * (if p then 1 else 0) = if p then a else 0
  have h_mul (T : Finset N) :
      Mobius.mobiusCoeff G T * (if T ⊆ S then (1 : ℝ) else 0) =
      (if T ⊆ S then Mobius.mobiusCoeff G T else (0 : ℝ)) := by
    split_ifs <;> ring
  -- Étape 3 : enchaîner les égalités pour obtenir la somme filtrée
  have h_rhs :
      ∑ T ∈ Finset.univ.filter Finset.Nonempty,
        (if hT : T.Nonempty then
          Solution.SmulGame (Mobius.mobiusCoeff G T) (TUGame.unanimityGame T hT)
        else (Solution.zeroGame : TUGame N)).v S =
      ∑ T ∈ Finset.univ.filter (fun T => T.Nonempty ∧ T ⊆ S),
        Mobius.mobiusCoeff G T := by
    rw [Finset.sum_congr rfl h_term, Finset.sum_congr rfl (fun T _ => h_mul T)]
    rw [← Finset.sum_filter, Finset.filter_filter]
  exact (Mobius.mobius_decomposition_axiom G S).trans h_rhs.symm

/-- Unicité de la valeur de Shapley : toute solution axiomatique est égale à la valeur de Shapley.
    Stratégie : décomposer G = ∑_{T≠∅} a_T · u_T via Mobius, puis φ et shapleyValue se
    distribuent sur la somme et coïncide sur chaque terme via phi_eq_shapley_weighted. -/
theorem shapley_uniqueness (φ : Solution N)
    (h_eff : φ.Efficiency)
    (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (h_add : φ.Additivity) :
    ∀ G : TUGame N, ∀ i : N, φ G i = shapleyValue G i := by
  intro G i
  classical
  let idx : Finset (Finset N) := Finset.univ.filter Finset.Nonempty
  let g : Finset N → TUGame N := fun T =>
    if hT : T.Nonempty then
      Solution.SmulGame (Mobius.mobiusCoeff G T) (TUGame.unanimityGame T hT)
    else Solution.zeroGame
  have hG : G = Solution.finsetSumGames idx g := game_eq_mobius_sum G
  rw [hG, phi_finsetSumGames φ h_null h_add, shapley_finsetSumGames]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, idx] at hT
  simp only [g, dif_pos hT]
  exact phi_eq_shapley_weighted φ h_eff h_sym h_null (Mobius.mobiusCoeff G T) T hT i

/-! ## Voting games -/

/-- A weighted voting game [q; w_1, ..., w_n] with positive quota -/
noncomputable def WeightedVotingGame (weights : N → ℝ) (quota : ℝ) (hquota : 0 < quota) : TUGame N where
  v := fun S => if ∑ i ∈ S, weights i ≥ quota then 1 else 0
  empty_zero := by simp [hquota]

/-! ## Jeux simples

Un *jeu simple* est un jeu à utilité transférable dont la fonction caractéristique ne prend
que les valeurs `0` (coalition perdante) et `1` (coalition gagnante). C'est le cadre naturel
des notions de pouvoir de vote : `VetoPlayer`, `Dictator`, `Critical`, et les indices de
Banzhaf n'ont de sens que sous cette contrainte (sinon `v S ∈ {0, 1}` échoue et la
normalisation de Banzhaf `2 ^ (|N| - 1)` ne correspond plus à l'étendue de `v`).

Le prédicat `SimpleGame G` encapsule la contrainte `v ∈ {0, 1}` que les axiomes
Veto/Dictator (greenlight architectural, cycle 73) supposeront. -/
def SimpleGame (G : TUGame N) : Prop :=
  ∀ S : Finset N, G.v S = 0 ∨ G.v S = 1

/-- Un `WeightedVotingGame` est simple : sa fonction caractéristique est un `if … then 1 else 0`,
donc la valeur de chaque coalition est `0` ou `1`. -/
theorem weighted_voting_game_simple (weights : N → ℝ) (quota : ℝ) (hquota : 0 < quota) :
    SimpleGame (WeightedVotingGame weights quota hquota) := by
  intro S
  simp only [WeightedVotingGame]
  by_cases h : ∑ i ∈ S, weights i ≥ quota
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

namespace SimpleGame

/-- Dans un jeu simple, une valeur différente de `0` doit être `1`. C'est la lecture par
    contraposée utilisée par les théorèmes Veto/Dictator pour promouvoir `v S ≠ 0` en `v S = 1`. -/
theorem eq_one_of_ne_zero {G : TUGame N} (hG : SimpleGame G) (S : Finset N)
    (hne : G.v S ≠ 0) : G.v S = 1 :=
  (hG S).resolve_left hne

/-- In a simple game, a value different from `1` must be `0`. Symmetric reading. -/
theorem eq_zero_of_ne_one {G : TUGame N} (hG : SimpleGame G) (S : Finset N)
    (hne : G.v S ≠ 1) : G.v S = 0 :=
  (hG S).resolve_right hne

end SimpleGame

/-! ## Jeux forts

Un jeu *fort* (à utilité transférable) est le dual d'un jeu propre : une coalition et son
complément ne peuvent être toutes deux perdantes — `v S = 0 → v Sᶜ = 1`. Pour un jeu simple,
cela signifie que le complément d'une coalition perdante est gagnant. Avec `ProperGame`,
`StrongGame` définit un jeu de vote simple *auto-dual* (propre et fort). Un jeu de vote
pondéré est fort dès que le quota ne dépasse pas la moitié du poids total. -/
def StrongGame (G : TUGame N) : Prop :=
  ∀ ⦃S : Finset N⦄, G.v S = 0 → G.v Sᶜ = 1

namespace StrongGame

/-- In a strong game, the complement of a losing coalition is winning. -/
theorem complement_wins {G : TUGame N} (hG : StrongGame G) {S : Finset N}
    (hlose : G.v S = 0) : G.v Sᶜ = 1 :=
  hG hlose

end StrongGame

/-- Un jeu de vote pondéré dont le quota ne dépasse pas la moitié du poids total est fort : si
    le poids d'une coalition est inférieur au quota, le poids de la coalition complémentaire
    l'atteint (les deux poids complémentaires somment au total, qui vaut au moins `2 * quota`),
    donc le complément gagne. Aucune hypothèse de signe sur les poids n'est nécessaire — c'est
    une conséquence pure du rapport quota/total. -/
theorem weighted_voting_game_strong (weights : N → ℝ) (quota : ℝ) (hquota : 0 < quota)
    (hstrong : 2 * quota ≤ ∑ i, weights i) :
    StrongGame (WeightedVotingGame weights quota hquota) := by
  intro S hlose
  simp only [WeightedVotingGame] at hlose ⊢
  -- Decode `S` losing into its weight falling short of the quota: if it reached the quota the
  -- `if` would evaluate to `1`, contradicting `hlose : … = 0`.
  have hS : ∑ i ∈ S, weights i < quota := by
    by_contra hge
    push_neg at hge
    rw [if_pos hge] at hlose
    linarith
  -- Le poids de la coalition complémentaire vaut `total − ∑_S`, donc `≥ quota`.
  have hSc : ∑ i ∈ Sᶜ, weights i = ∑ i, weights i - ∑ i ∈ S, weights i := by
    rw [← Finset.sum_add_sum_compl S weights]; ring
  have hSc_ge : ∑ i ∈ Sᶜ, weights i ≥ quota := by rw [hSc]; linarith
  -- Le complément atteint le quota, donc sa valeur vaut `1`.
  exact if_pos hSc_ge

/-- Un jeu fort a une grande coalition gagnante.

    La coalition vide est toujours perdante (`TUGame.empty_zero`), et son complément est la
    grande coalition `Finset.univ`. La propriété forte (`v S = 0 → v Sᶜ = 1`) appliquée à
    `S = ∅` force donc `v univ = 1` : un jeu fort est non dégénéré au sens où la grande
    coalition gagne. -/
theorem strong_grand_wins {G : TUGame N} (hG : StrongGame G) : G.v Finset.univ = 1 := by
  have hcomp : (∅ : Finset N)ᶜ = Finset.univ := by simp
  have := hG G.empty_zero
  rwa [hcomp] at this

/-! ## Jeux monotones

Un jeu *monotone* (à utilité transférable) est un jeu où élargir une coalition ne diminue
jamais sa valeur : `S ⊆ T → v S ≤ v T`. Pour un jeu simple, cela se spécialise en la
propriété d'up-set des coalitions gagnantes — `S` gagnant et `S ⊆ T` implique `T` gagnant
— la caractéristique définitoire d'un jeu de vote simple *propre*.

Avec `SimpleGame`, `MonotoneGame` encapsule les hypothèses que les théorèmes d'indice de
pouvoir Veto/Dictator supposent (greenlight architectural, ai-01 cycle 75→76). -/
def MonotoneGame (G : TUGame N) : Prop :=
  ∀ ⦃S T : Finset N⦄, S ⊆ T → G.v S ≤ G.v T

namespace MonotoneGame

/-- In a monotone game, a larger coalition has at least as large a value. -/
theorem le_of_subset {G : TUGame N} (hG : MonotoneGame G) {S T : Finset N}
    (h : S ⊆ T) : G.v S ≤ G.v T :=
  hG h

/-- Les coalitions gagnantes d'un jeu simple monotone forment un up-set : élargir une
    coalition gagnante la maintient gagnante.

    La monotonicité donne `v S ≤ v T` pour `S ⊆ T` ; puisque `v S = 1` et que `SimpleGame`
    force `v T ∈ {0, 1}`, cela élimine `v T = 0`, laissant `v T = 1`. C'est la propriété
    définitoire d'un jeu de vote simple *propre* et le pont entre `MonotoneGame` et la
    théorie du veto. -/
theorem winning_upward_closed {G : TUGame N} (hG : MonotoneGame G) (hG' : SimpleGame G)
    {S T : Finset N} (hST : S ⊆ T) (hwin : G.v S = 1) : G.v T = 1 := by
  -- Monotonicity: `v S ≤ v T`, and `v S = 1` so `1 ≤ v T`; with `v T ∈ {0,1}` this
  -- rules out `v T = 0`, hence `v T = 1`.
  apply SimpleGame.eq_one_of_ne_zero hG' T
  intro hzero
  have : (1 : ℝ) ≤ G.v T := hwin ▸ hG hST
  linarith

end MonotoneGame

/-- Les coalitions perdantes d'un jeu simple monotone forment un down-set : rétrécir une
    coalition perdante la maintient perdante. Le dual de la propriété d'up-set des
    coalitions gagnantes : la monotonicité donne `v S ≤ v T`, et `v T = 0` force
    `v S ≤ 0 < 1` ; `SimpleGame` élimine alors `v S = 1`, laissant `v S = 0`. -/
theorem losing_downward_closed {G : TUGame N} (hG : MonotoneGame G) (hG' : SimpleGame G)
    {S T : Finset N} (hST : S ⊆ T) (hlose : G.v T = 0) : G.v S = 0 := by
  -- Monotonicity: `v S ≤ v T = 0`, so `v S ≤ 0 < 1`; `SimpleGame` then rules out `v S = 1`.
  apply SimpleGame.eq_zero_of_ne_one hG' S
  intro hone
  have : G.v S ≤ G.v T := MonotoneGame.le_of_subset hG hST
  linarith

/-- Un jeu de vote pondéré à poids non négatifs est monotone : élargir une coalition ajoute
    du poids non négatif, donc la somme des poids ne peut qu'augmenter, et `v` (un
    `if sum ≥ quota then 1 else 0`) ne peut pas diminuer. -/
theorem weighted_voting_game_monotone (weights : N → ℝ) (quota : ℝ) (hquota : 0 < quota)
    (hw : ∀ i, 0 ≤ weights i) :
    MonotoneGame (WeightedVotingGame weights quota hquota) := by
  intro S T hST
  have hsum : ∑ i ∈ S, weights i ≤ ∑ i ∈ T, weights i :=
    Finset.sum_le_sum_of_subset_of_nonneg hST (fun i _ _ => hw i)
  simp only [WeightedVotingGame]
  split_ifs with h₁ h₂
  · exact le_refl _                                   -- both reach quota: 1 ≤ 1
  · exact absurd (le_trans h₁ hsum) h₂               -- S reaches, T does not: impossible
  · exact zero_le_one                                 -- S does not, T does: 0 ≤ 1
  · exact le_refl _                                   -- neither: 0 ≤ 0

/-! ## Jeux propres

Un jeu *propre* (à utilité transférable) est un jeu où une coalition et son complément ne
peuvent être tous deux gagnants : `v S = 1 → v Sᶜ = 0`. Pour un jeu simple, c'est la
propriété standard « deux coalitions complémentaires ne gagnent pas toutes deux » d'un
jeu de vote simple propre (le complément d'une coalition gagnante est perdant). Un jeu de
vote pondéré est propre dès que le quota dépasse strictement la moitié du poids total, car
les poids de coalitions complémentaires somment au total. -/
def ProperGame (G : TUGame N) : Prop :=
  ∀ ⦃S : Finset N⦄, G.v S = 1 → G.v Sᶜ = 0

namespace ProperGame

/-- In a proper game, the complement of a winning coalition is losing. -/
theorem complement_loses {G : TUGame N} (hG : ProperGame G) {S : Finset N}
    (hwin : G.v S = 1) : G.v Sᶜ = 0 :=
  hG hwin

end ProperGame

/-- Un jeu de vote pondéré dont le quota dépasse strictement la moitié du poids total est
    propre : si le poids d'une coalition atteint le quota, le poids de la coalition
    complémentaire lui est strictement inférieur (les deux poids complémentaires somment au
    total, qui vaut moins que `2 * quota`), donc le complément perd. Aucune hypothèse de
    signe sur les poids n'est nécessaire — c'est une conséquence pure du rapport quota/total. -/
theorem weighted_voting_game_proper (weights : N → ℝ) (quota : ℝ) (hquota : 0 < quota)
    (hproper : 2 * quota > ∑ i, weights i) :
    ProperGame (WeightedVotingGame weights quota hquota) := by
  intro S hwin
  simp only [WeightedVotingGame] at hwin ⊢
  -- Decode `S` winning into its weight reaching the quota.
  have hS : ∑ i ∈ S, weights i ≥ quota := by
    split_ifs at hwin with h
    · exact h
    · linarith
  -- Le poids de la coalition complémentaire vaut `total − ∑_S`, donc `< quota`.
  have hSc : ∑ i ∈ Sᶜ, weights i = ∑ i, weights i - ∑ i ∈ S, weights i := by
    rw [← Finset.sum_add_sum_compl S weights]; ring
  have hSc_lt : ∑ i ∈ Sᶜ, weights i < quota := by rw [hSc]; linarith
  -- Le complément n'atteint pas le quota, donc sa valeur vaut `0`.
  split_ifs with h
  · linarith
  · rfl

/-! ## Jeux auto-duaux

Un jeu *auto-dual* (à utilité transférable) est un jeu qui est simultanément *propre* (une
coalition et son complément ne peuvent tous deux gagner) et *fort* (ils ne peuvent tous
deux perdre). Pour un jeu simple, c'est le jeu de vote canonique « décisif » / auto-dual :
pour toute coalition, exactement l'une d'elle et de son complément gagne. -/
def SelfDualGame (G : TUGame N) : Prop :=
  ProperGame G ∧ StrongGame G

namespace SelfDualGame

/-- A self-dual game is proper. -/
theorem proper (G : TUGame N) (hG : SelfDualGame G) : ProperGame G := hG.1

/-- A self-dual game is strong. -/
theorem strong (G : TUGame N) (hG : SelfDualGame G) : StrongGame G := hG.2

/-- Dans un jeu simple auto-dual, exactement l'une d'une coalition et de son complément gagne :
    `v S = 1` force `v Sᶜ = 0` (propre), et `v S = 0` force `v Sᶜ = 1` (fort). -/
theorem complement_flip {G : TUGame N} (hG : SelfDualGame G) {S : Finset N}
    (hS : G.v S = 1 ∨ G.v S = 0) : G.v Sᶜ = 0 ∨ G.v Sᶜ = 1 := by
  rcases hS with h1 | h0
  · exact Or.inl (hG.1 h1)
  · exact Or.inr (hG.2 h0)

end SelfDualGame

/-- Player i is critical in coalition S if removing them makes S lose -/
def Critical (G : TUGame N) (i : N) (S : Finset N) : Prop :=
  i ∈ S ∧ G.v S = 1 ∧ G.v (S.erase i) = 0

/-- Un joueur critique doit être membre de la coalition : `Critical G i S` se déplie en
    `i ∈ S ∧ …`, donc l'appartenance est la première conjonction. Cible BG-prover échauffement
    (#1453) : extraction de conjonction triviale, exerce le harnais sur une seconde cible réelle
    maintenant que le format bullet-sorry stub corrige GoalExtract (cycle 63). -/
theorem critical_implies_mem (G : TUGame N) (i : N) (S : Finset N) :
    Critical G i S → i ∈ S := by
  intro h
  exact h.1

/-- `Critical G i` est décidable via raisonnement classique (les comparaisons `TUGame.v` sont
    des réels non calculables). Promu en instance globale pour que `BanzhafRaw` et tout théorème
    le concernant synthétisent la MÊME instance, évitant le piège du mismatch opaque
    `Classical.decPred`. -/
noncomputable instance criticalDecidable (G : TUGame N) (i : N) :
    DecidablePred (fun S : Finset N => Critical G i S) := Classical.decPred _

/-- Raw Banzhaf index: number of coalitions where i is critical. -/
noncomputable def BanzhafRaw (G : TUGame N) (i : N) : ℕ :=
  (Finset.univ.filter fun S => Critical G i S).card

/-- `BanzhafRaw G i` est borné par le nombre total de coalitions (`2^|N|`) :
    les coalitions critiques sont un sous-ensemble de `Finset.univ`. Première cible réellement
    prouvable, non-smoke, pour le prover BG (#1453). -/
theorem banzhaf_raw_le_univ (G : TUGame N) (i : N) :
    BanzhafRaw G i ≤ (Finset.univ : Finset (Finset N)).card := by
  unfold BanzhafRaw
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Player with veto power -/
def VetoPlayer (G : TUGame N) (i : N) : Prop :=
  ∀ S : Finset N, G.v S = 1 → i ∈ S

/-- Dictator: can win alone and possesses the veto -/
def Dictator (G : TUGame N) (i : N) : Prop :=
  G.v {i} = 1 ∧ VetoPlayer G i

/-- Un jeu a au plus un dictateur.

    Si à la fois `i` et `j` sont dictateurs, alors `j` est un joueur veto (seconde conjonction
    de `Dictator`) et `i` gagne seul (`v {i} = 1`, première conjonction de `Dictator i`).
    Appliquer la propriété de veto de `j` à la coalition gagnante `{i}` force `j ∈ {i}`,
    c'est-à-dire `j = i`. -/
theorem dictator_unique (G : TUGame N) (i j : N) (hi : Dictator G i) (hj : Dictator G j) :
    i = j := by
-- `j` is a veto player (second conjunction of `Dictator`) and `i` wins alone
-- (`v {i} = 1`, first conjunction), so the veto property forces `j in {i}`, i.e. `j = i`.
  exact (Finset.mem_singleton.mp (hj.2 {i} hi.1)).symm

/-- Un dictateur a un indice brut de Banzhaf strictement positif. Le pendant positif de
    `dummy_banzhaf_raw_zero` : un joueur muet ne change jamais la valeur d'une coalition
    (BanzhafRaw = 0), alors qu'un dictateur gagne seul (`v {i} = 1`, première conjonction
    de `Dictator`) et que la coalition vide a pour valeur `0` (`TUGame.empty_zero`), donc
    `{i}` est une coalition critique (`i ∈ {i}`, `v {i} = 1`, `v ({i}.erase i) = v ∅ = 0`).
    Ainsi le filtre des coalitions critiques est non vide et sa cardinalité est positive. -/
theorem dictator_banzhaf_pos (G : TUGame N) (i : N) (h : Dictator G i) :
    0 < BanzhafRaw G i := by
  have hcrit : Critical G i ({i} : Finset N) := by
    refine ⟨?_, ?_, ?_⟩
    · simp
    · exact h.1
    · have herase : ({i} : Finset N).erase i = ∅ := by simp
      rw [herase]
      exact G.empty_zero
  simp only [BanzhafRaw]
  exact Finset.card_pos.mpr ⟨{i}, Finset.mem_filter.2 ⟨Finset.mem_univ _, hcrit⟩⟩

/-- Un joueur veto rend perdante toute coalition à laquelle il **n'appartient** pas.

    La contraposée de la propriété de veto : `VetoPlayer G i` force `i ∈ S` pour toute coalition
    gagnante `S`, donc `i ∉ S` élimine `v S = 1` ; combiné avec `SimpleGame` (qui force
    `v S ∈ {0, 1}`), cela laisse `v S = 0`. Le pendant « coalition perdante » de
    `veto_critical_of_winning` (où ce résultat montre qu'un joueur veto est critique dans
    toute coalition *gagnante*, celui-ci montre que toute coalition *sans* le joueur veto
    est perdante). -/
theorem veto_losing_without {G : TUGame N} (hG : SimpleGame G) {i : N}
    (hv : VetoPlayer G i) {S : Finset N} (hni : i ∉ S) : G.v S = 0 := by
  apply SimpleGame.eq_zero_of_ne_one hG S
  intro hone
  exact absurd (hv S hone) hni

/-- Un joueur veto est critique dans la grande coalition, à condition que la grande coalition
    gagne.

    `VetoPlayer G i` force `i ∈ S` pour toute coalition gagnante `S`. Appliqué à
    `S = univ.erase i`, si `v (univ.erase i) = 1` alors `i ∈ univ.erase i`, contredisant
    `i ∉ univ.erase i` ; donc `v (univ.erase i) ≠ 1`, et `SimpleGame` force
    `v (univ.erase i) = 0`. Avec `v univ = 1` (`hwin`) et `i ∈ univ`, cela fait de `univ`
    une coalition critique pour `i`. -/
theorem veto_critical_in_grand {G : TUGame N} (hG : SimpleGame G) {i : N}
    (hv : VetoPlayer G i) (hwin : G.v Finset.univ = 1) :
    Critical G i Finset.univ := by
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.mem_univ i
  · exact hwin
  · apply SimpleGame.eq_zero_of_ne_one hG (Finset.univ.erase i)
    intro heq
    have hni : i ∉ Finset.univ.erase i := by simp [Finset.mem_erase]
    exact hni (hv (Finset.univ.erase i) heq)

/-- Un joueur veto est critique dans *toute* coalition gagnante.

    La forme générale dont `veto_critical_in_grand` est l'instance grande-coalition :
    spécialiser `S` à `Finset.univ` la récupère. `VetoPlayer G i` force `i ∈ S` pour toute
    coalition gagnante `S`. Pour montrer que `i` est critique dans une coalition gagnante
    `S`, il nous faut `v (S.erase i) = 0` : si `v (S.erase i) = 1`, la propriété de veto
    forcerait `i ∈ S.erase i`, contredisant `i ∉ S.erase i` ; donc `v (S.erase i) ≠ 1`,
    et `SimpleGame` force `v (S.erase i) = 0`. Avec `v S = 1` (`hwin`) et `i ∈ S`, cela
    fait de `S` une coalition critique pour `i`. -/
theorem veto_critical_of_winning {G : TUGame N} (hG : SimpleGame G) {i : N}
    (hv : VetoPlayer G i) {S : Finset N} (hwin : G.v S = 1) :
    Critical G i S := by
  refine ⟨?_, ?_, ?_⟩
  · exact hv S hwin
  · exact hwin
  · apply SimpleGame.eq_zero_of_ne_one hG (S.erase i)
    intro heq
    have hni : i ∉ S.erase i := by simp [Finset.mem_erase]
    exact hni (hv (S.erase i) heq)

/-- Un joueur est veto si et seulement s'il est critique dans toute coalition gagnante.

    La réciproque de `veto_critical_of_winning` : être joueur veto est *équivalent* à être
    critique dans toute coalition gagnante. Le sens direct est `veto_critical_of_winning` (un
    joueur veto appartient à toute coalition gagnante et son retrait la fait perdre) ; le sens
    inverse est immédiat car la criticité `Critical G i S` inclut l'appartenance `i ∈ S`,
    donc être critique dans toute coalition gagnante retrouve `VetoPlayer G i`
    (`∀ coalition gagnante S, i ∈ S`). La caractérisation est significative en non-dégénérescence
    (existence d'au moins une coalition gagnante) ; dans le cas pleinement dégénéré (aucune
    coalition gagnante) les deux côtés sont vacuoment vrais. -/
theorem veto_iff_critical_of_winning {G : TUGame N} (hG : SimpleGame G) (i : N) :
    VetoPlayer G i ↔ ∀ S : Finset N, G.v S = 1 → Critical G i S := by
  constructor
  · exact fun hv S hS => veto_critical_of_winning hG hv hS
  · intro h S hS
    exact (h S hS).1

/-- Une *coalition gagnante minimale* : `S` est gagnante, mais tout sous-ensemble propre est
    perdant.

    Les coalitions gagnantes minimales sont les éléments minimaux de l'up-set des coalitions
    gagnantes ; elles forment les coalitions « clés » irréductibles dont le poids atteint
    tout juste le quota dans un jeu de vote pondéré. Un joueur veto, qui appartient à toute
    coalition gagnante, appartient en particulier à toute coalition gagnante minimale. -/
def MinimalWinning (G : TUGame N) (S : Finset N) : Prop :=
  G.v S = 1 ∧ ∀ T ⊂ S, G.v T = 0

/-- Un joueur veto appartient à toute coalition gagnante minimale.

    Une coalition gagnante minimale est en particulier gagnante, donc la propriété de veto
    (`∀ coalition gagnante S, i ∈ S`) force l'appartenance. -/
theorem veto_mem_minimal_winning {G : TUGame N} (i : N) (hv : VetoPlayer G i)
    {S : Finset N} (hmin : MinimalWinning G S) : i ∈ S :=
  hv S hmin.1

/-- Tout membre d'une coalition gagnante minimale est critique.

    La minimalité dit que tout sous-ensemble propre perd, donc retirer tout membre `i ∈ S`
    (ce qui donne le sous-ensemble propre `S.erase i`) rend `S` perdant : `v (S.erase i) = 0`.
    Avec `v S = 1` et `i ∈ S`, c'est exactement `Critical G i S`. Aucune hypothèse
    `SimpleGame` n'est requise — cela tient pour toute coalition `MinimalWinning` (qui force
    déjà `v S = 1`). -/
theorem critical_of_minimal_winning {G : TUGame N} {S : Finset N}
    (hmin : MinimalWinning G S) {i : N} (himem : i ∈ S) : Critical G i S := by
  refine ⟨himem, hmin.1, ?_⟩
-- `S.erase i` is a proper subset of `S` since `i in S`, so minimality makes it losing.
  exact hmin.2 (S.erase i) (Finset.erase_ssubset himem)

/-- Le support d'un jeu : l'intersection de toutes ses coalitions gagnantes.

    En théorie du vote, le *support* est l'ensemble des joueurs qui appartiennent à toute
    coalition gagnante. Par la définition de `VetoPlayer`, l'appartenance au support coïncide
    exactement avec le fait d'être joueur veto (voir `mem_carrier_iff_veto`). La notion est
    définie pour tout jeu ; elle est non triviale précisément en non-dégénérescence
    (l'existence d'au moins une coalition gagnante), auquel cas le support est l'ensemble des
    joueurs veto. -/
def carrier (G : TUGame N) : Set N :=
  ⋂₀ { S : Set N | ∃ t : Finset N, (t : Set N) = S ∧ G.v t = 1 }

/-- Un joueur appartient au support (l'intersection de toutes les coalitions gagnantes) si et
    seulement si c'est un joueur veto. Les deux directions sont les dépliages de l'intersection
    (`Set.mem_sInter`, l'appartenance à une intersection arbitraire est l'appartenance à
    chaque composante) et de `VetoPlayer` (un joueur veto réside dans toute coalition gagnante). -/
theorem mem_carrier_iff_veto (G : TUGame N) (i : N) :
    i ∈ carrier G ↔ VetoPlayer G i := by
  constructor
  · intro hi t ht
    exact Finset.mem_coe.mp (Set.mem_sInter.mp hi (t : Set N) ⟨t, rfl, ht⟩)
  · intro hv
    apply Set.mem_sInter.mpr
    rintro S ⟨t, rfl, ht⟩
    exact Finset.mem_coe.mpr (hv t ht)

/-- Un joueur veto a un indice brut de Banzhaf strictement positif quand la grande coalition gagne.

    Le pendant veto de `dummy_banzhaf_raw_zero` (un joueur muet a `BanzhafRaw = 0`) : un joueur
    veto est critique dans la grande coalition (`veto_critical_in_grand`, utilisant `SimpleGame`),
    donc le filtre des coalitions critiques est non vide et sa cardinalité est positive. Notez
    que, contrairement à `dictator_banzhaf_pos`, ceci nécessite l'hypothèse « la grande coalition
    gagne » `hwin` : sans aucune coalition gagnante un joueur est vacuoment veto mais a
    `BanzhafRaw = 0`. -/
theorem veto_banzhaf_raw_pos (G : TUGame N) (hG : SimpleGame G) (i : N)
    (hv : VetoPlayer G i) (hwin : G.v Finset.univ = 1) :
    0 < BanzhafRaw G i := by
  have hcrit : Critical G i Finset.univ := veto_critical_in_grand hG hv hwin
  simp only [BanzhafRaw]
  exact Finset.card_pos.mpr ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hcrit⟩⟩

/-- Tout coefficient de Shapley `s! * (n - s - 1)! / n!` est strictement positif, étant un ratio
    de factorielles strictement positives (`0! = 1`). -/
private theorem shapleyCoef_pos (n s : ℕ) : 0 < shapleyCoef n s := by
  unfold shapleyCoef
  exact div_pos (by exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
    (by exact_mod_cast Nat.factorial_pos _)

/-- Un joueur veto a une valeur de Shapley strictement positive quand la grande coalition gagne.

    Le pendant Shapley de `dummy_shapley_zero` (un joueur muet a une valeur de Shapley `0`) et
    l'analogue de `veto_banzhaf_raw_pos` pour la valeur de Shapley. La valeur de Shapley est la
    somme pondérée des contributions marginales de `i` sur toutes les coalitions précédentes `S`
    (avec `i ∉ S`). Pour un joueur veto dans un jeu simple, chaque tel ensemble précédent est
    perdant (`v S = 0` par `veto_losing_without`), donc chaque contribution marginale est
    `v (S ∪ {i}) ∈ {0, 1} ≥ 0`, et chaque terme de la somme est non négatif (coefficient positif
    fois contribution non négative). La grande coalition privée de `i` est un tel ensemble
    précédent ; sa contribution marginale est `v univ - v (univ \ {i}) = 1 - 0 = 1` (par `hwin`),
    pondérée par le coefficient de Shapley strictement positif, ce qui donne un terme strictement
    positif. La somme entière est au moins ce terme positif unique, donc strictement positive.

    Comme pour `veto_banzhaf_raw_pos`, l'hypothèse de non-dégénérescence `hwin` est essentielle :
    sans aucune coalition gagnante un joueur est vacuoment veto mais a une valeur de Shapley `0`. -/
theorem veto_shapley_pos (G : TUGame N) (hG : SimpleGame G) (i : N)
    (hv : VetoPlayer G i) (hwin : G.v Finset.univ = 1) :
    0 < shapleyValue G i := by
-- The grand coalition deprived of i is a preceding set of i whose marginal
-- contribution is `1`.
  set T := (Finset.univ \ ({i} : Finset N)) with hTdef
  have hTni : i ∉ T := by simp [hTdef]
  have hTuni : T ∪ ({i} : Finset N) = Finset.univ :=
    Finset.sdiff_union_of_subset (Finset.subset_univ _)
  have hvT : G.v T = 0 := veto_losing_without hG hv hTni
-- Each term of the Shapley sum is nonneg: `v S = 0` (veto, `i not in S`),
  -- donc la contribution marginale est `v (S ∪ {i}) ∈ {0, 1}` et le coefficient est > 0.
  have hnonneg : ∀ S ∈ Finset.univ.filter fun S => i ∉ S,
      0 ≤ shapleyCoef (Fintype.card N) S.card * G.marginalContribution i S := by
    rintro S hS
    obtain ⟨-, hni⟩ := Finset.mem_filter.mp hS
    have hvS : G.v S = 0 := veto_losing_without hG hv hni
    have hmc : G.marginalContribution i S = G.v (S ∪ {i}) := by
      show G.v (S ∪ {i}) - G.v S = G.v (S ∪ {i})
      rw [hvS, sub_zero]
    rw [hmc]
    have hvSi : 0 ≤ G.v (S ∪ {i}) := by
      rcases hG (S ∪ {i}) with h | h <;> rw [h] <;> norm_num
    exact mul_nonneg (shapleyCoef_pos _ _).le hvSi
-- The term indexed by `T` is strictly positive: marginal `= 1`, coefficient `> 0`.
  have hTin : T ∈ Finset.univ.filter fun S => i ∉ S := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hTni
  have hmcT : G.marginalContribution i T = 1 := by
    show G.v (T ∪ {i}) - G.v T = 1
    rw [hTuni, hvT, sub_zero]; exact hwin
  have htermT :
      0 < shapleyCoef (Fintype.card N) T.card * G.marginalContribution i T := by
    rw [hmcT]; exact mul_pos (shapleyCoef_pos _ _) zero_lt_one
-- The sum over the whole filter is at least this unique positive term indexed by `T`.
  have hle :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.singleton_subset_iff.mpr hTin)
      (fun S hSF _ => hnonneg S hSF)
  rw [Finset.sum_singleton] at hle
  exact htermT.trans_le hle

/-- Dummy player: adds no value. -/
def DummyPlayer (G : TUGame N) (i : N) : Prop :=
  ∀ S : Finset N, i ∉ S → G.v (S ∪ {i}) = G.v S

/-- Dummy players have a zero Shapley value. -/
theorem dummy_shapley_zero (G : TUGame N) (i : N) (h : DummyPlayer G i) :
    shapleyValue G i = 0 :=
  ShapleyValue.shapley_null_player G i h

/-- Les joueurs muets ne sont critiques dans aucune coalition, donc ont un indice brut de
    Banzhaf nul.

    Un joueur muet ne change jamais la valeur d'une coalition, donc il ne peut jamais se
    produire que `v S = 1` tandis que `v (S.erase i) = 0` : l'hypothèse de muet force
    `v S = v (S.erase i)`, contredisant la criticalité. -/
theorem dummy_banzhaf_raw_zero (G : TUGame N) (i : N) (h : DummyPlayer G i) :
    BanzhafRaw G i = 0 := by
-- A dummy player is critical in no coalition: criticality requires `v S = 1`
-- and `v (S.erase i) = 0`, but `DummyPlayer` gives `v S = v (S.erase i)`.
  have hneq : ∀ S, Critical G i S → False := by
    rintro S ⟨hmem, hone, hzero⟩
    have hni : i ∉ S.erase i := by simp [Finset.mem_erase]
    -- `S = (S.erase i) ∪ {i}` puisque `i ∈ S`.
    have hS_eq : S = (S.erase i) ∪ {i} := by
      ext j
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · intro hj
        by_cases heq : j = i
        · exact Or.inr heq
        · exact Or.inl ⟨heq, hj⟩
      · rintro (⟨_, hj⟩ | hj)
        · exact hj
        · rw [hj]; exact hmem
    have hdummy := h (S.erase i) hni
    rw [← hS_eq] at hdummy
    rw [hdummy] at hone
    linarith
-- `BanzhafRaw` = cardinality of the filter of critical coalitions (instance now
-- consistent via `criticalDecidable`); the filter is empty since `hneq` refutes all criticality.
  simp only [BanzhafRaw]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun S _ hcrit => hneq S hcrit

/-- Un joueur veto n'est jamais un joueur muet, pourvu que la grande coalition gagne.

    Le pendant veto de `dictator_not_dummy` : les deux rôles sont mutuellement exclusifs. Un
    joueur muet ne change jamais la valeur d'une coalition ; appliqué à `Finset.univ.erase i`
    (dont `i` est absent), ceci donne `v (univ.erase i ∪ {i}) = v (univ.erase i)`, i.e.
    `v univ = v (univ.erase i)`. Mais un joueur veto force `v (univ.erase i) = 0` (via
    `veto_losing_without`, puisque `i ∉ univ.erase i`), tandis que l'hypothèse de non-dégénérescence
    `hwin : v univ = 1` donne `v univ = 1`. L'égalité `1 = 0` est une contradiction. -/
theorem veto_not_dummy (G : TUGame N) (hG : SimpleGame G) (i : N) (hv : VetoPlayer G i)
    (hwin : G.v Finset.univ = 1) : ¬ DummyPlayer G i := by
  intro hd
-- A dummy never changes the value of a coalition; applied to `univ.erase i`
-- (which excludes `i`):
  have hni : i ∉ Finset.univ.erase i := by simp [Finset.mem_erase]
  have hdummy := hd (Finset.univ.erase i) hni
-- `univ.erase i union {i} = univ` (the absence then the addition of the player restore the universe).
  have huniv : Finset.univ.erase i ∪ ({i} : Finset N) = Finset.univ := by
    ext j; simp [Finset.mem_univ]
  rw [huniv] at hdummy
-- A veto player forces `v (univ.erase i) = 0` (they are absent from this coalition).
  rw [veto_losing_without hG hv hni] at hdummy
-- `hdummy : v univ = 0` contradicts `hwin : v univ = 1`.
  rw [hdummy] at hwin
  linarith

/-- Un dictateur n'est jamais un joueur muet.

    Les deux rôles extrêmes de joueur sont mutuellement exclusifs. Un joueur muet n'ajoute
    aucune valeur à toute coalition dont il est absent ; appliqué à la coalition vide, ceci
    donne `v (∅ ∪ {i}) = v ∅`, i.e. `v {i} = 0` (via `TUGame.empty_zero`). Mais un dictateur
    gagne seul (`v {i} = 1`, premier conjunct de `Dictator`), contradiction. C'est l'analogue
    par type de joueur du dédoublement de signe pour BanzhafRaw (`dictator_banzhaf_pos` : `> 0`,
    `dummy_banzhaf_raw_zero` : `= 0`). -/
theorem dictator_not_dummy (G : TUGame N) (i : N) (h : Dictator G i) :
    ¬ DummyPlayer G i := by
  intro hd
-- The dummy hypothesis on the empty coalition gives `v {i} = v empty = 0`.
  have hdummy : G.v ({i} : Finset N) = 0 := by
    have hni : (i : N) ∉ (∅ : Finset N) := by simp
    have heq := hd ∅ hni
    rw [Finset.empty_union, G.empty_zero] at heq
    exact heq
  linarith [h.1]

/-- Échange coalitional utilisé par `banzhaf_raw_symmetric`. Dans une coalition `S`, remplace
    l'unique membre de `{i, j}` par l'autre (si `S` contient exactement un de `i, j`) ; les
    coalitions contenant les deux ou aucun sont fixées. C'est une involution qui préserve la
    valeur du jeu dès lors que `i, j` sont symétriques dans `G`. -/
private def banzhafSwap (i j : N) (S : Finset N) : Finset N :=
  if i ∈ S ∧ j ∉ S then (S.erase i) ∪ {j}
  else if j ∈ S ∧ i ∉ S then (S.erase j) ∪ {i}
  else S

/-- **Symétrie de l'indice brut de Banzhaf.**

    Les joueurs symétriques (interchangeables) sont critiques dans le même nombre de coalitions,
    donc ont des indices bruts de Banzhaf égaux. C'est l'analogue Banzhaf de `shapley_symmetric` :
    l'axiome de symétrie est partagé par tout indice de pouvoir raisonnable (Banzhaf autant que
    Shapley), même si seul le paquet complet des quatre axiomes caractérise Shapley de manière
    unique.

    La bijection `banzhafSwap i j` échange `i ↔ j` dans chaque coalition. C'est une involution,
    préserve la valeur du jeu (par `SymmetricPlayers`, après une séparation de cas sur
    `S ∩ {i, j}`), et échange « critique pour `i` » avec « critique pour `j` » (l'appartenance
    s'échange, la valeur est invariante, et `(σ S) \ {j} = σ (S \ {i})`). Les deux filtres de
    coalitions critiques sont donc en bijection, et leurs cardinalités — les indices bruts de
    Banzhaf — coïncident. -/
theorem banzhaf_raw_symmetric (G : TUGame N) (i j : N)
    (h : Solution.SymmetricPlayers G i j) :
    BanzhafRaw G i = BanzhafRaw G j := by
  classical
  by_cases heq : i = j
  · subst heq; rfl
  -- L'hypothèse est symétrique en `i, j`.
  have hsymm : Solution.SymmetricPlayers G j i := fun S hj hi => (h S hi hj).symm
  -- Identité `(S.erase k) ∪ {k} = S` pour `k ∈ S`.
  have aux_readd (k : N) {S : Finset N} (hk : k ∈ S) : (S.erase k) ∪ {k} = S := by
    rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hk]
-- Behavior of `banzhafSwap i j` in each of the four membership cases.
  have swap_both {S : Finset N} (hSi : i ∈ S) (hSj : j ∈ S) : banzhafSwap i j S = S := by
    simp only [banzhafSwap]
    rw [if_neg (fun H => H.2 hSj), if_neg (fun H => H.2 hSi)]
  have swap_neither {S : Finset N} (hni : i ∉ S) (hnj : j ∉ S) : banzhafSwap i j S = S := by
    simp only [banzhafSwap]
    rw [if_neg (fun H => hni H.1), if_neg (fun H => hnj H.1)]
  have swap_i_only {S : Finset N} (hSi : i ∈ S) (hnj : j ∉ S) :
      banzhafSwap i j S = (S.erase i) ∪ {j} := by
    simp only [banzhafSwap]; rw [if_pos ⟨hSi, hnj⟩]
  have swap_j_only {S : Finset N} (hni : i ∉ S) (hSj : j ∈ S) :
      banzhafSwap i j S = (S.erase j) ∪ {i} := by
    simp only [banzhafSwap]
    rw [if_neg (fun H => hni H.1), if_pos ⟨hSj, hni⟩]
-- (1) Involution: `banzhafSwap i j (banzhafSwap i j S) = S`.
  have hinv : ∀ S : Finset N, banzhafSwap i j (banzhafSwap i j S) = S := by
    intro S
    by_cases hSi : i ∈ S <;> by_cases hSj : j ∈ S
    · rw [swap_both hSi hSj, swap_both hSi hSj]
    · -- i ∈ S, j ∉ S : σ S = (S.erase i) ∪ {j}, qui contient j, mais pas i.
      have hσ : banzhafSwap i j S = (S.erase i) ∪ {j} := swap_i_only hSi hSj
      rw [hσ]
      have hmem_j : j ∈ (S.erase i) ∪ ({j} : Finset N) :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      have hni_mem : i ∉ (S.erase i) ∪ ({j} : Finset N) := by
        rw [Finset.mem_union, Finset.mem_singleton]
        rintro (h | hij)
        · exact absurd h (Finset.notMem_erase i S)
        · exact absurd hij heq
      rw [swap_j_only hni_mem hmem_j]
      -- ((S.erase i) ∪ {j}).erase j ∪ {i} = S
      have hnj_erase : j ∉ S.erase i :=
        fun Hh => hSj (Finset.mem_of_mem_erase Hh)
      rw [Finset.erase_union_distrib, Finset.erase_singleton,
          Finset.erase_eq_self.mpr hnj_erase, Finset.union_empty, aux_readd i hSi]
    · -- i ∉ S, j ∈ S : symétrique du cas précédent.
      have hσ : banzhafSwap i j S = (S.erase j) ∪ {i} := swap_j_only hSi hSj
      rw [hσ]
      have hmem_i : i ∈ (S.erase j) ∪ ({i} : Finset N) :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      have hnj_mem : j ∉ (S.erase j) ∪ ({i} : Finset N) := by
        rw [Finset.mem_union, Finset.mem_singleton]
        rintro (h | hji)
        · exact absurd h (Finset.notMem_erase j S)
        · exact heq hji.symm
      rw [swap_i_only hmem_i hnj_mem]
      have hni_erase : i ∉ S.erase j :=
        fun Hh => hSi (Finset.mem_of_mem_erase Hh)
      rw [Finset.erase_union_distrib, Finset.erase_singleton,
          Finset.erase_eq_self.mpr hni_erase, Finset.union_empty, aux_readd j hSj]
    · rw [swap_neither hSi hSj, swap_neither hSi hSj]
-- (2) Value invariance: `G.v (banzhafSwap i j S) = G.v S`.
  have hval : ∀ S : Finset N, G.v (banzhafSwap i j S) = G.v S := by
    intro S
    by_cases hSi : i ∈ S <;> by_cases hSj : j ∈ S
    · -- tous deux dedans : σ S = S.
      rw [swap_both hSi hSj]
    · -- i dedans, j dehors : σ S = (S.erase i) ∪ {j} ; valeur = v S par symétrie sur S.erase i.
      have hσ : banzhafSwap i j S = (S.erase i) ∪ {j} := swap_i_only hSi hSj
      rw [hσ]
      have hjni : j ∉ S.erase i := fun Hh => hSj (Finset.mem_of_mem_erase Hh)
      have hT := h (S.erase i) (Finset.notMem_erase i S) hjni
      rw [aux_readd i hSi] at hT
      exact hT.symm
    · -- i dehors, j dedans : σ S = (S.erase j) ∪ {i}.
      have hσ : banzhafSwap i j S = (S.erase j) ∪ {i} := swap_j_only hSi hSj
      rw [hσ]
      have hini : i ∉ S.erase j := fun Hh => hSi (Finset.mem_of_mem_erase Hh)
      have hT := hsymm (S.erase j) (Finset.notMem_erase j S) hini
      rw [aux_readd j hSj] at hT
      exact hT.symm
    · rw [swap_neither hSi hSj]
-- `hkey`: when i, j are both in S, symmetry on S \ {i, j} identifies the
-- two erased values.
  have hkey : ∀ S : Finset N, i ∈ S → j ∈ S →
      G.v (S.erase j) = G.v (S.erase i) := by
    intro S hSi hSj
-- Erasing i then j equals erasing j then i.
    have erase_erase_comm : (S.erase i).erase j = (S.erase j).erase i := by
      ext x
      simp only [Finset.mem_erase]
      tauto
    set T := (S.erase j).erase i
    have hTni : i ∉ T := Finset.notMem_erase i (S.erase j)
    have hTnj : j ∉ T := fun Hh => Finset.notMem_erase j S (Finset.mem_of_mem_erase Hh)
    have h1 : T ∪ ({i} : Finset N) = S.erase j :=
      aux_readd i (Finset.mem_erase.mpr ⟨heq, hSi⟩)
    have h2 : T ∪ ({j} : Finset N) = S.erase i := by
      rw [show T = (S.erase i).erase j from by rw [erase_erase_comm]]
      exact aux_readd j (Finset.mem_erase.mpr ⟨fun hj => heq hj.symm, hSj⟩)
    rw [← h1, ← h2]
    exact h T hTni hTnj
  -- Identité : effacer j de (S.erase i) ∪ {j} donne S.erase i.
  have aux_erase_lone (S : Finset N) (hnj : j ∉ S.erase i) :
      ((S.erase i) ∪ ({j} : Finset N)).erase j = S.erase i := by
    rw [Finset.erase_union_distrib, Finset.erase_singleton,
        Finset.erase_eq_self.mpr hnj, Finset.union_empty]
-- (3) 'Critical for i' <-> 'critical for j (after the swap)'.
  have hiff : ∀ S : Finset N, Critical G i S ↔ Critical G j (banzhafSwap i j S) := by
    intro S
    by_cases hSi : i ∈ S <;> by_cases hSj : j ∈ S
    · -- tous deux dedans : σ S = S ; relier v(S.erase i) et v(S.erase j) via `hkey`.
      rw [swap_both hSi hSj]
      refine ⟨fun ⟨_, h1, h0⟩ => ⟨hSj, h1, by rw [hkey S hSi hSj]; exact h0⟩,
              fun ⟨_, h1, h0⟩ => ⟨hSi, h1, by rw [← hkey S hSi hSj]; exact h0⟩⟩
    · -- i dedans, j dehors : σ S = (S.erase i) ∪ {j}.
      have hσ : banzhafSwap i j S = (S.erase i) ∪ {j} := swap_i_only hSi hSj
      rw [hσ]
      have hnj_ei : j ∉ S.erase i := fun Hh => hSj (Finset.mem_of_mem_erase Hh)
      have hval' : G.v ((S.erase i) ∪ {j}) = G.v S := by
        rw [← hσ]; exact hval S
      refine ⟨fun ⟨_, h1, h0⟩ =>
                ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)),
                 hval'.trans h1,
                 by rw [aux_erase_lone S hnj_ei]; exact h0⟩,
              fun ⟨_, h1, h0⟩ =>
                ⟨hSi, hval'.symm.trans h1,
                 by rw [aux_erase_lone S hnj_ei] at h0; exact h0⟩⟩
    · -- i dehors, j dedans : σ S = (S.erase j) ∪ {i}. Les deux côtés sont faux.
      have hσ : banzhafSwap i j S = (S.erase j) ∪ {i} := swap_j_only hSi hSj
      rw [hσ]
-- j not in (S.erase j) union {i} (j was erased, j != i), so `Critical G j (sigma S)` is false;
-- `Critical G i S` is also false since i not in S.
      have hnjs : j ∉ (S.erase j) ∪ ({i} : Finset N) := by
        rw [Finset.mem_union, Finset.mem_singleton]
        rintro (h | hji)
        · exact absurd h (Finset.notMem_erase j S)
        · exact heq hji.symm
      exact ⟨fun Hh => absurd Hh.1 hSi, fun Hh => absurd Hh.1 hnjs⟩
    · -- aucun : σ S = S ; les deux côtés sont faux (i, j ∉ S).
      rw [swap_neither hSi hSj]
      exact ⟨fun Hh => absurd Hh.1 hSi, fun Hh => absurd Hh.1 hSj⟩
-- (4) The swap is an involution hence injective; the j-critical filter is exactly
-- the image of the i-critical filter by the swap, so the two cardinals coincide.
  show BanzhafRaw G i = BanzhafRaw G j
  simp only [BanzhafRaw]
  have hσ_inj : Function.Injective (banzhafSwap i j) := by
    intros a b hab
    have h2 : banzhafSwap i j (banzhafSwap i j a) = banzhafSwap i j (banzhafSwap i j b) :=
      congr_arg (banzhafSwap i j) hab
    rw [hinv, hinv] at h2
    exact h2
  have himage : (Finset.univ.filter fun S => Critical G j S) =
      Finset.image (banzhafSwap i j) (Finset.univ.filter fun S => Critical G i S) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hT
      refine ⟨banzhafSwap i j T, ?_, hinv T⟩
      have key : Critical G j (banzhafSwap i j (banzhafSwap i j T)) := by
        rw [hinv T]; exact hT
      exact (hiff (banzhafSwap i j T)).mpr key
    · rintro ⟨S, hS, hseq⟩
      have hcj := (hiff S).mp hS
      rwa [hseq] at hcj
  have hcard : (Finset.image (banzhafSwap i j)
        (Finset.univ.filter fun S => Critical G i S)).card =
      (Finset.univ.filter fun S => Critical G i S).card :=
    Finset.card_image_of_injective _ hσ_inj
  rw [himage, hcard]

/-! ## Normalized Banzhaf index -/

/-- L'indice de pouvoir normalisé (Penrose-Banzhaf absolu) : le compte brut de Banzhaf divisé
    par `2 ^ (n - 1)`, le nombre de coalitions qui contiennent le joueur (chacun des autres
    `n - 1` joueurs est indépendamment dedans ou dehors). Équivalent à la probabilité que `i`
    soit pivot quand une coalition contenant `i` est tirée uniformément au hasard. La
    normalisation rend l'indice comparable entre des ensembles de joueurs de tailles différentes. -/
noncomputable def BanzhafIndex (G : TUGame N) (i : N) : ℝ :=
  (BanzhafRaw G i : ℝ) / (2 : ℝ) ^ (Fintype.card N - 1)

/-- **Symétrie de l'indice de Banzhaf normalisé.** Les joueurs symétriques (interchangeables)
    ont des indices de Banzhaf normalisés égaux : ils ont les mêmes comptes bruts
    (`banzhaf_raw_symmetric`) et partagent le même dénominateur de normalisation. C'est le pendant
    de `shapley_symmetric` : l'axiome de symétrie est partagé par tout indice de pouvoir raisonnable. -/
theorem banzhaf_index_symmetric (G : TUGame N) (i j : N)
    (h : Solution.SymmetricPlayers G i j) :
    BanzhafIndex G i = BanzhafIndex G j := by
  simp only [BanzhafIndex]
  rw [banzhaf_raw_symmetric G i j h]

/-- Un joueur muet a un indice de Banzhaf normalisé nul : il n'est pivot dans aucune coalition,
    donc son compte brut (et par suite sa part normalisée) est nul. -/
theorem banzhaf_index_dummy_zero (G : TUGame N) (i : N)
    (h : DummyPlayer G i) : BanzhafIndex G i = 0 := by
  simp only [BanzhafIndex, dummy_banzhaf_raw_zero G i h, Nat.cast_zero, zero_div]

/-- L'indice de Banzhaf normalisé est non négatif : `BanzhafRaw` est un compte naturel
    (≥ 0 quand transtypé vers ℝ) et le dénominateur normalisateur `2 ^ (card N - 1) > 0`.
    Cible réelle du prouveur BG (#1453, cycle 65), enchaîne sur #4071 (déf. BanzhafIndex).
    Légèrement plus dur que les échauffements : nécessite `div_nonneg` plus un argument
    de positivité sur le dénominateur. -/
theorem banzhaf_index_nonneg (G : TUGame N) (i : N) : 0 ≤ BanzhafIndex G i := by
  simp only [BanzhafIndex]
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · exact pow_nonneg (by norm_num) _

/-- L'indice de Banzhaf normalisé est nul si et seulement si l'indice brut de Banzhaf est
    nul : `BanzhafIndex = BanzhafRaw / 2^(card N - 1)` et le dénominateur normalisateur
    `2 ^ (card N - 1)` est strictement positif (donc la division par lui est fidèle). Ceci
    renforce `banzhaf_index_dummy_zero` (un sens) en une caractérisation structurelle nette.
    Cible BG-prover (#1453, cycle 66, item 4) ; preuve iff `div_eq_zero_iff₀`. -/
theorem banzhaf_index_eq_zero_iff (G : TUGame N) (i : N) :
    BanzhafIndex G i = 0 ↔ BanzhafRaw G i = 0 := by
  simp [BanzhafIndex]

/-- L'indice de Banzhaf normalisé est positif si et seulement si l'indice brut de Banzhaf
    est positif : le dual `>0` de `banzhaf_index_eq_zero_iff`. Ensemble, les deux
    théorèmes iff donnent une caractérisation fidèle — le normalisateur `2 ^ (card N - 1)`
    est strictement positif, donc positivité et nullité sont toutes deux préservées par la
    division. Cible BG-prover (#1453, cycle 67, item 5) ; iff de positivité. -/
theorem banzhaf_index_pos_iff (G : TUGame N) (i : N) :
    0 < BanzhafIndex G i ↔ 0 < BanzhafRaw G i := by
  simp only [BanzhafIndex]
  have hden : 0 < (2 : ℝ) ^ (Fintype.card N - 1) := pow_pos (by norm_num) _
  constructor
  · intro h
    have hnumreal : 0 < (BanzhafRaw G i : ℝ) := (div_pos_iff_of_pos_right hden).mp h
    exact_mod_cast hnumreal
  · intro h
    exact div_pos (by exact_mod_cast h) hden

/-- L'indice de Banzhaf normalisé vaut au plus 2 : `BanzhafRaw` compte les coalitions
    critiques, bornées par le nombre total de coalitions `2 ^ card N` (voir
    `banzhaf_raw_le_univ`) ; normaliser par `2 ^ (card N - 1)` laisse un quotient d'au
    plus 2. Le joueur `i : N` force `0 < card N`, donc la soustraction Nat `card N - 1`
    ne déborde pas.
    Cible BG-prover (#1453, cycle 66, item 3) ; enchaîne `banzhaf_raw_le_univ`. -/
theorem banzhaf_index_le_two (G : TUGame N) (i : N) : BanzhafIndex G i ≤ 2 := by
  have hn : 0 < Fintype.card N := Fintype.card_pos_iff.mpr ⟨i⟩
  have hdenom : 0 < (2 : ℝ) ^ (Fintype.card N - 1) := pow_pos (by norm_num) _
  rw [BanzhafIndex, div_le_iff₀ hdenom]
  have hcard : (Finset.univ : Finset (Finset N)).card = 2 ^ Fintype.card N := by
    rw [Finset.card_univ, Fintype.card_finset]
  have h2 : (2 : ℝ) ^ Fintype.card N = 2 * (2 : ℝ) ^ (Fintype.card N - 1) := by
    have hkey : Fintype.card N = Fintype.card N - 1 + 1 := by omega
    conv_lhs => rw [hkey, pow_add, pow_one]
    ring
  calc (BanzhafRaw G i : ℝ)
      ≤ ((Finset.univ : Finset (Finset N)).card : ℝ) := by exact_mod_cast banzhaf_raw_le_univ G i
    _ = (2 ^ Fintype.card N : ℝ) := by rw [hcard]; norm_cast
    _ = 2 * (2 : ℝ) ^ (Fintype.card N - 1) := by rw [h2]

/-- L'indice de Banzhaf normalisé vaut au plus 1 : le compte brut `BanzhafRaw` n'enregistre
    que les coalitions où `i` est critique, et un joueur critique doit être membre
    (`critical_implies_mem`), donc le filtre des coalitions critiques est contenu dans le
    filtre des coalitions *contenant* `i`. Il y a exactement `2 ^ (card N - 1)` telles
    coalitions (bijection insertion/effacement avec les sous-ensembles de `N \ {i}` : chacun
    des autres `card N - 1` joueurs est dedans ou dehors, et `i` est forcé dedans).
    Normaliser `BanzhafRaw ≤ 2 ^ (card N - 1)` par `2 ^ (card N - 1)` laisse un quotient d'au
    plus 1 — l'indice de Penrose-Banzhaf est une quantité de type probabilité dans `[0, 1]`.
    Ceci resserre `banzhaf_index_le_two` (qui utilisait la borne plus grossière
    `banzhaf_raw_le_univ ≤ 2 ^ card N`) et s'apparie avec `banzhaf_index_nonneg` pour
    épingler l'indice dans `[0, 1]`. Le joueur `i : N` force `0 < card N`, donc la
    soustraction Nat `card N - 1` ne déborde pas. -/
theorem banzhaf_index_le_one (G : TUGame N) (i : N) : BanzhafIndex G i ≤ 1 := by
  have hn : 0 < Fintype.card N := Fintype.card_pos_iff.mpr ⟨i⟩
  have hdenom : 0 < (2 : ℝ) ^ (Fintype.card N - 1) := pow_pos (by norm_num) _
  -- une coalition critique doit contenir i, donc le filtre critique ⊆ le filtre d'appartenance
  have hsubset :
      (Finset.univ.filter fun S => Critical G i S) ⊆
        (Finset.univ : Finset (Finset N)).filter (fun S => i ∈ S) :=
    fun S hS =>
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, critical_implies_mem G i S (Finset.mem_filter.mp hS).2⟩
  -- coalitions contenant i ↔ sous-ensembles de (univ.erase i) via insertion/effacement (bijection)
  have hmemcard :
      ((Finset.univ : Finset (Finset N)).filter (fun S => i ∈ S)).card =
        2 ^ (Fintype.card N - 1) := by
    have heq :
        (Finset.univ : Finset (Finset N)).filter (fun S => i ∈ S) =
          ((Finset.univ : Finset N).erase i).powerset.image (insert i) := by
      ext S
      constructor
      · intro h
        obtain ⟨-, hmem⟩ := Finset.mem_filter.mp h
        refine Finset.mem_image.mpr ⟨S.erase i, ?_, ?_⟩
        · exact Finset.mem_powerset.mpr (Finset.erase_subset_erase i (Finset.subset_univ S))
        · rw [Finset.insert_erase hmem]
      · intro h
        obtain ⟨T, hT, hST⟩ := Finset.mem_image.mp h
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [← hST]; exact Finset.mem_insert_self i T
    rw [heq]
    have hinj :
        Set.InjOn (insert i)
          (((Finset.univ : Finset N).erase i).powerset : Set (Finset N)) := by
      intros T₁ hT₁ T₂ hT₂ heq
      have hsub₁ : T₁ ⊆ (Finset.univ : Finset N).erase i :=
        Finset.mem_powerset.mp (Finset.mem_coe.mp hT₁)
      have hsub₂ : T₂ ⊆ (Finset.univ : Finset N).erase i :=
        Finset.mem_powerset.mp (Finset.mem_coe.mp hT₂)
      have hi₁ : i ∉ T₁ := fun h => by simpa using hsub₁ h
      have hi₂ : i ∉ T₂ := fun h => by simpa using hsub₂ h
      have hstrip : (insert i T₁).erase i = (insert i T₂).erase i := by rw [heq]
      rwa [Finset.erase_insert hi₁, Finset.erase_insert hi₂] at hstrip
    have herase : ((Finset.univ : Finset N).erase i).card = Fintype.card N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ (i : N)), Finset.card_univ]
    rw [Finset.card_image_of_injOn hinj, Finset.card_powerset, herase]
  rw [BanzhafIndex, div_le_iff₀ hdenom, one_mul]
  unfold BanzhafRaw
  exact_mod_cast (Finset.card_le_card hsubset).trans hmemcard.le

/-- Cas d'égalité de `banzhaf_index_le_one` : un dictateur atteint l'indice de Banzhaf
    maximal `1`. Dans un jeu simple monotone, un dictateur `i` est critique dans *toute*
    coalition qui le contient — la monotonicité fait que toute telle coalition gagne (puisque
    `{i}` gagne), et la propriété de veto fait que son retrait perd — donc `i` est critique
    dans exactement les `2^(|N|-1)` coalitions qui le contiennent, ce qui donne
    `BanzhafIndex G i = 2^(|N|-1) / 2^(|N|-1) = 1`. Ceci caractérise l'atteinte de la
    borne supérieure prouvée par `banzhaf_index_le_one`. -/
theorem dictator_banzhaf_index_eq_one (G : TUGame N) (i : N)
    (hG : SimpleGame G) (hM : MonotoneGame G) (h : Dictator G i) :
    BanzhafIndex G i = 1 := by
  have hn : 0 < Fintype.card N := Fintype.card_pos_iff.mpr ⟨i⟩
  have hdenom : 0 < (2 : ℝ) ^ (Fintype.card N - 1) := pow_pos (by norm_num) _
-- For a dictator, i is critical in S iff i in S.
  have hcrit_iff : ∀ S : Finset N, Critical G i S ↔ i ∈ S := by
    intro S
    refine ⟨fun hcrit => hcrit.1, fun hmem => ?_⟩
    refine ⟨hmem, ?_, ?_⟩
    · -- v S = 1 : {i} ⊆ S, monotonicité donne v {i} ≤ v S, et v {i} = 1
      have hsub : ({i} : Finset N) ⊆ S := Finset.singleton_subset_iff.mpr hmem
      have hle : G.v ({i} : Finset N) ≤ G.v S := MonotoneGame.le_of_subset hM hsub
      apply SimpleGame.eq_one_of_ne_zero hG S
      intro h0
      rw [h.1] at hle
      linarith
    · -- v (S.erase i) = 0 : i ∉ S.erase i, donc la propriété de veto le fait perdre
      exact veto_losing_without hG h.2 (by simp)
-- Hence the critical filter equals the membership filter.
  have hfilter_eq :
      (Finset.univ.filter fun S => Critical G i S) =
        (Finset.univ : Finset (Finset N)).filter (fun S => i ∈ S) := by
    ext S
    rw [Finset.mem_filter, Finset.mem_filter]
    refine ⟨fun h => ⟨Finset.mem_univ _, (hcrit_iff S).mp h.2⟩,
      fun h => ⟨Finset.mem_univ _, (hcrit_iff S).mpr h.2⟩⟩
-- The membership filter has cardinal 2^(|N|-1) (insert/erase bijection).
  have hmemcard :
      ((Finset.univ : Finset (Finset N)).filter (fun S => i ∈ S)).card =
        2 ^ (Fintype.card N - 1) := by
    have heq :
        (Finset.univ : Finset (Finset N)).filter (fun S => i ∈ S) =
          ((Finset.univ : Finset N).erase i).powerset.image (insert i) := by
      ext S
      constructor
      · intro h
        obtain ⟨-, hmem⟩ := Finset.mem_filter.mp h
        refine Finset.mem_image.mpr ⟨S.erase i, ?_, ?_⟩
        · exact Finset.mem_powerset.mpr (Finset.erase_subset_erase i (Finset.subset_univ S))
        · rw [Finset.insert_erase hmem]
      · intro h
        obtain ⟨T, hT, hST⟩ := Finset.mem_image.mp h
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [← hST]; exact Finset.mem_insert_self i T
    rw [heq]
    have hinj :
        Set.InjOn (insert i)
          (((Finset.univ : Finset N).erase i).powerset : Set (Finset N)) := by
      intros T₁ hT₁ T₂ hT₂ heq
      have hsub₁ : T₁ ⊆ (Finset.univ : Finset N).erase i :=
        Finset.mem_powerset.mp (Finset.mem_coe.mp hT₁)
      have hsub₂ : T₂ ⊆ (Finset.univ : Finset N).erase i :=
        Finset.mem_powerset.mp (Finset.mem_coe.mp hT₂)
      have hi₁ : i ∉ T₁ := fun h => by simpa using hsub₁ h
      have hi₂ : i ∉ T₂ := fun h => by simpa using hsub₂ h
      have hstrip : (insert i T₁).erase i = (insert i T₂).erase i := by rw [heq]
      rwa [Finset.erase_insert hi₁, Finset.erase_insert hi₂] at hstrip
    have herase : ((Finset.univ : Finset N).erase i).card = Fintype.card N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ (i : N)), Finset.card_univ]
    rw [Finset.card_image_of_injOn hinj, Finset.card_powerset, herase]
  rw [BanzhafIndex, div_eq_iff hdenom.ne', one_mul]
  unfold BanzhafRaw
  rw [hfilter_eq]
  exact_mod_cast hmemcard


end CooperativeGames_en