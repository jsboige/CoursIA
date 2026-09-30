import Mathlib

/-!
# InfoBits — b = log₂(n!/|Aut G|) : contenu informationnel d'une structure

Tranche **R06** de l'arc « théorie effective » (#16741, issue #16752) :
*Baek, Liu & Tegmark, GenEFT* (arXiv:2402.05916). Le papier mesure le contenu
informationnel `b` d'une structure à `n` nœuds par
`b = log₂(n! / |Aut G|)` : il faut `log₂ n!` bits pour étiqueter `n` nœuds,
moins `log₂ |Aut G|` bits offerts par les symétries du groupe d'automorphismes.

Contenu formalisé :

1. **Définition** — `infoBits G := log₂ (n! / |MulAut G|)` pour un groupe
   fini `G`.
2. **Ancres concrètes** (l'issue demande « des groupes d'automorphismes
   concrets ») :
   - `infoBits_trivial` : groupe trivial, `b = log₂(1/1) = 0` — aucune
     information requise, aucune symétrie à monnayer ;
   - `infoBits_card_two` : tout groupe à deux éléments, `b = log₂(2/1) = 1`
     bit — le groupe d'automorphismes est trivial (`card_mulAut_eq_one` :
     un automorphisme fixe `1`, et l'unique autre élément n'a nulle part où
     aller), donc aucune symétrie : l'étiquetage d'un nœud coûte exactement
     1 bit ;
   - `infoBits_cyclicSeven` : le cyclique `C₇` (compagnon du module
     `CircleOfDays`, dont la rotation des jours est la représentation de ce
     groupe), `b = log₂(7!/6) = log₂ 840` — les automorphismes d'un cyclique
     d'ordre `n` sont au nombre de φ(n) (`IsCyclic.card_mulAut`), donc les
     6 rotations de C₇ rabattent l'étiquetage de log₂ 6 ≈ 2,58 bits.
3. **Statics sur graphes — Section III de GenEFT** : le re-labellage des
   `n` nœuds d'un graphe est l'action naturelle de `Equiv.Perm (Fin n)` sur
   `SimpleGraph (Fin n)` (instances `permSmul`, `MulAction`) ; le pont
   `mem_aut_iff` identifie le stabilisateur au groupe d'automorphismes
   usuels (préservation de l'adjacence dans les deux sens) ;
   **orbit-stabilizer** `card_orbit_mul_card_aut` donne `|orbite| · |Aut G|
   = n!`, d'où la longueur de description `descLength G = log₂ |orbite|` et
   sa forme quotient `descLength_eq` : `b = log₂ (n! / |Aut G|)` (éq. 4 du
   papier) — la contrepartie « graphe » de la définition `infoBits` groupe.
   Migration depuis le module dissous `GenEFT.lean` (#17480, arbitrage
   c.38 : dissolution, pas de module parallèle).

Dépendances : Mathlib uniquement (`MulAut`, `Fintype.card`, `Real.log2`,
`SimpleGraph`, `MulAction`, `Real.logb`).
-/

namespace LearningTheory.EffectiveTheory

/-- Contenu informationnel d'une structure groupe finie (R06) :
`b = log₂(n! / |Aut G|)` — bits d'un étiquetage brut `n!` moins les bits
offerts par les symétries `|Aut G|`. -/
noncomputable def infoBits (G : Type*) [Group G] [Fintype G] [DecidableEq G] : ℝ :=
  Real.logb 2 ((Nat.factorial (Fintype.card G) : ℝ) / ((Fintype.card (MulAut G)) : ℝ))

/-- **Groupe trivial** : `b = log₂(1!/1) = 0` — un seul étiquetage, une seule
symétrie, aucun bit d'information. -/
theorem infoBits_trivial (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G = 1) :
    infoBits G = 0 := by
  have hAut : Fintype.card (MulAut G) = 1 := by
    have hsub : Subsingleton G := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    haveI : Inhabited (MulAut G) := ⟨1⟩
    haveI : Unique (MulAut G) :=
      ⟨⟨1⟩, fun f => MulEquiv.ext fun x => hsub.elim (f x) x⟩
    simp [Fintype.card_unique]
  simp [infoBits, hG, hAut, Real.logb_one]

/-- **Groupe à deux éléments** : son groupe d'automorphismes est trivial.
Un automorphisme fixe `1` ; l'unique élément `a ≠ 1` ne peut pas y aller
(injectivité), donc tout automorphisme est l'identité. -/
theorem card_mulAut_eq_one {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G = 2) :
    Fintype.card (MulAut G) = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : G, a ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : Fintype.card G = 1 :=
      (Fintype.card_eq_one_iff.mpr ⟨(1 : G), fun y => hcon y⟩)
    omega
  have hcov : ∀ x : G, x = 1 ∨ x = a := by
    intro x
    by_contra hx
    push_neg at hx
    have hm1 : (1 : G) ∉ ({a, x} : Finset G) := by simp [ha.symm, (hx.1).symm]
    have hm2 : a ∉ ({x} : Finset G) := by simp [(hx.2).symm]
    have h3 : ({1, a, x} : Finset G).card = 3 := by
      rw [Finset.card_insert_of_notMem hm1, Finset.card_insert_of_notMem hm2,
        Finset.card_singleton]
    have hle : ({1, a, x} : Finset G).card ≤ Fintype.card G :=
      Finset.card_le_card (Finset.subset_univ _)
    omega
  haveI : Unique (MulAut G) :=
    ⟨⟨1⟩, fun f => MulEquiv.ext fun x => by
      show f x = x
      rcases hcov x with hx | hx
      · rw [hx, map_one]
      · rw [hx]
        have hfa : f a ≠ 1 := fun h =>
          ha (f.injective (by rw [h, map_one]))
        rcases hcov (f a) with h | h
        · exact absurd h hfa
        · rw [h]⟩
  simp [Fintype.card_unique]

/-- **Tout groupe à deux éléments** : `b = log₂(2!/1) = 1` bit exactement —
aucune symétrie ne rabat le coût de l'étiquetage. -/
theorem infoBits_card_two {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G = 2) :
    infoBits G = 1 := by
  have hAut := card_mulAut_eq_one hG
  simp only [infoBits, hG, hAut]
  norm_num

/-- **Groupe cyclique C₇** : le groupe d'automorphismes d'un cyclique d'ordre
`n` a φ(n) éléments (`IsCyclic.card_mulAut` — les images du générateur sont
exactement ses puissances inversibles), donc `|Aut C₇| = φ(7) = 6` et
`b = log₂(7!/6) = log₂ 840 ≈ 9{,}71` bits : les 6 rotations rabattent
l'étiquetage de log₂ 6 ≈ 2,58 bits. Compagnon du module `CircleOfDays`
(la rotation des jours y est la représentation de ce C₇). -/
theorem infoBits_cyclicSeven :
    infoBits (Multiplicative (ZMod 7)) = Real.logb 2 840 := by
  have hcard : Fintype.card (Multiplicative (ZMod 7)) = 7 := by norm_num
  have h1 : Nat.card (Multiplicative (ZMod 7)) = 7 := by
    rw [Nat.card_eq_fintype_card]; exact hcard
  have hAut : Fintype.card (MulAut (Multiplicative (ZMod 7))) = 6 := by
    have h := IsCyclic.card_mulAut (Multiplicative (ZMod 7))
    rw [h1, Nat.totient_prime (by norm_num : (7 : ℕ).Prime)] at h
    rw [Nat.card_eq_fintype_card] at h
    exact h
  have hd : ((7 : ℕ).factorial : ℝ) / ((6 : ℕ) : ℝ) = 840 := by norm_num
  simp only [infoBits, hcard, hAut, hd]

/-! ## Statics sur graphes — re-labellage, automorphismes, description length

Section III de GenEFT : le re-labellage des `n` nœuds d'un graphe est l'action
naturelle de `Equiv.Perm (Fin n)` sur `SimpleGraph (Fin n)` ; les graphes « de
même structure » sont exactement l'orbite, et orbit-stabilizer donne
`|orbite| · |Aut G| = n!` — encoder `G` revient à choisir un point dans une
orbite de taille `n! / |Aut G|`, d'où `b = log₂ (n! / |Aut G|)`. Migré du
module dissous `GenEFT.lean` (#17480). -/

section Statics

variable {n : ℕ}

/-- Le **re-labellage** d'un graphe par une permutation `σ` des sommets :
l'arête `i—j` existe dans `σ • G` ssi `σ⁻¹ i — σ⁻¹ j` existe dans `G`.
C'est l'action naturelle du groupe symétrique sur les structures de graphe. -/
instance permSmul : SMul (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) where
  smul σ G :=
    { Adj := fun i j => G.Adj (σ.symm i) (σ.symm j)
      symm := by
        apply Std.Symm.mk
        intro i j h
        exact G.symm.symm (σ.symm i) (σ.symm j) h
      loopless := by
        apply Std.Irrefl.mk
        intro i h
        exact G.loopless.irrefl (σ.symm i) h }

/-- `Equiv.Perm (Fin n)` agit sur les graphes sur `Fin n` par re-labellage :
le groupe symétrique effectue les renommages de sommets. -/
instance : MulAction (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) where
  one_smul G := by
    ext i j
    have hone : ∀ x, (1 : Equiv.Perm (Fin n)).symm x = x := by
      intro x
      rw [show ((1 : Equiv.Perm (Fin n)).symm) = 1 from inv_one]
      exact Equiv.Perm.one_apply x
    show G.Adj ((1 : Equiv.Perm (Fin n)).symm i) ((1 : Equiv.Perm (Fin n)).symm j) ↔ G.Adj i j
    rw [hone i, hone j]
  mul_smul σ τ G := by
    ext i j
    have hst : ∀ x, (σ * τ).symm x = τ.symm (σ.symm x) := by
      intro x
      rw [show (σ * τ).symm = τ.symm * σ.symm from mul_inv_rev σ τ]
      simp [Equiv.Perm.mul_apply]
    show G.Adj ((σ * τ).symm i) ((σ * τ).symm j) ↔
      G.Adj (τ.symm (σ.symm i)) (τ.symm (σ.symm j))
    rw [hst i, hst j]

/-- **Pont avec la définition usuelle** : une permutation est dans le
stabilisateur (l'« automate » du graphe, `Aut G`) **ssi** elle préserve
l'adjacence dans les deux sens — le stabilisateur du re-labellage EST le
groupe d'automorphismes du graphe. -/
theorem mem_aut_iff {G : SimpleGraph (Fin n)} (σ : Equiv.Perm (Fin n)) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) G ↔
      ∀ i j, G.Adj i j ↔ G.Adj (σ i) (σ j) := by
  constructor
  · intro h i j
    have hsmul : σ • G = G := h
    constructor
    · intro hij
      have h3 : (σ • G).Adj (σ i) (σ j) := by
        show G.Adj (σ.symm (σ i)) (σ.symm (σ j))
        simpa using hij
      rw [hsmul] at h3
      exact h3
    · intro hij
      -- l'égalité de graphes σ • G = G transportée au couple (σ i, σ j)
      have hAdjeq : (σ • G).Adj = G.Adj := SimpleGraph.ext_iff.mp hsmul
      have h4 : (σ • G).Adj (σ i) (σ j) := by rw [hAdjeq]; exact hij
      have h5 : (σ • G).Adj (σ i) (σ j) ↔ G.Adj i j := by
        show G.Adj (σ.symm (σ i)) (σ.symm (σ j)) ↔ G.Adj i j
        simp
      exact h5.mp h4
  · intro h
    show σ • G = G
    ext i j
    show G.Adj (σ.symm i) (σ.symm j) ↔ G.Adj i j
    simpa using h (σ.symm i) (σ.symm j)

/-- **Orbit-stabilizer pour les graphes** (Section III du papier) : le nombre
de graphes de même structure que `G` (son orbite sous re-labellage) fois le
nombre d'automorphismes de `G` (son stabilisateur) égale `n!`. Encoder la
structure, c'est choisir un point de l'orbite. -/
theorem card_orbit_mul_card_aut (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)]
    [Fintype ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) G)] :
    Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G) *
      Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) =
        Fintype.card (Equiv.Perm (Fin n)) := by
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (G := Equiv.Perm (Fin n)) G

/-- La **longueur de description** du graphe `G` (éq. 4 du papier) : le log
en base 2 de la taille de l'orbite de re-labellage, `b = log₂ (n! / |Aut G|)`.
C'est le nombre de bits du « plus court programme » qui produit `G` à
structure près. -/
noncomputable def descLength (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)] : ℝ :=
  Real.logb 2 (Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G))

/-- `descLength` sous forme de quotient : `b = log₂ (n! / |Aut G|)` — la
forme utilisée dans le papier (Section III). -/
theorem descLength_eq (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)]
    [Fintype ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) G)] :
    descLength G =
      Real.logb 2 (Fintype.card (Equiv.Perm (Fin n)) /
        Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G)) := by
  have h := card_orbit_mul_card_aut G
  -- le stabilisateur contient l'identité, donc est non vide et de cardinal > 0
  have hcardpos : 0 < Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) :=
    Fintype.card_pos_iff.2 ⟨⟨1, one_smul _ G⟩⟩
  have haut : (Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast hcardpos)
  unfold descLength
  congr 1
  rw [eq_div_iff haut]
  exact_mod_cast h

end Statics

end LearningTheory.EffectiveTheory
