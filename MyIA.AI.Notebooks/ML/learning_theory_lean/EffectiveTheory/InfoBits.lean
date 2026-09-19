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

Dépendances : Mathlib uniquement (`MulAut`, `Fintype.card`, `Real.log2`).
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

end LearningTheory.EffectiveTheory
