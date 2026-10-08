import Sensitivity.Fourier
import Mathlib.Tactic.FinCases

/-!
# Sensibilité et sensibilité de bloc : définitions et premières séparations

Ce fichier est un **ajout additif** au lac `sensitivity_lean` (Epic Origami
#19898, Pli 2, sous-grain #19908) : il ne modifie aucun énoncé existant du
théorème de Huang. Il définit la sensibilité locale et la sensibilité de bloc
locale d'une fonction booléenne `F` sur l'hypercube `Q n`, établit l'inégalité
fondamentale `sensitivity ≤ blockSensitivity`, et produit une **séparation
stricte explicite** en dimension 4 : la disjonction de deux conjonctions
possède un point de sensibilité nulle mais de sensibilité de bloc non nulle.

Les quantités ici sont *locales* (en un sommet `x`) : c'est le grain fin de la
littérature (Nisan, Huang), et le socle sur lequel le carnet
`ANALYSE-06-Sensibilite-2026` construit les variantes globales.
-/

namespace Sensitivity

open Bool Finset Fintype

/-- Sensibilité locale de `F` en `x` : nombre de coordonnées dont le
retournement (une à une) change la valeur de `F`. -/
def sensitivity {n : ℕ} (F : Q n → Bool) (x : Q n) : ℕ :=
  (Finset.univ.filter fun i => F (flip x i) ≠ F x).card

/-- Retournement simultané d'un **bloc** `S` de coordonnées de `x`. -/
def flipBlock {n : ℕ} (x : Q n) (S : Finset (Fin n)) : Q n :=
  fun j => if j ∈ S then !(x j) else x j

/-- Sensibilité de bloc locale de `F` en `x` : nombre de blocs **non vides** de
coordonnées dont le retournement simultané change la valeur de `F`. Le bloc
vide est exclu : il laisserait `x` invariant et compterait pour rien. -/
def blockSensitivity {n : ℕ} (F : Q n → Bool) (x : Q n) : ℕ :=
  (Finset.univ.filter fun S : Finset (Fin n) => S.Nonempty ∧ F (flipBlock x S) ≠ F x).card

/-!
### Lemmes de calcul sur `flipBlock`
-/

@[simp] lemma flipBlock_empty {n : ℕ} (x : Q n) : flipBlock x ∅ = x := by
  funext j
  simp [flipBlock]

/-- Retourner le singleton `{i}` revient au retournement d'une coordonnée. -/
lemma flipBlock_singleton {n : ℕ} (x : Q n) (i : Fin n) :
    flipBlock x {i} = flip x i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [flipBlock]
  · simp only [flipBlock, Finset.mem_singleton, if_neg h]
    exact (flip_apply_ne x i h).symm

/-!
### Bornes triviales
-/

/-- La sensibilité locale est majorée par la dimension. -/
theorem sensitivity_le {n : ℕ} (F : Q n → Bool) (x : Q n) : sensitivity F x ≤ n := by
  simp only [sensitivity]
  calc (Finset.univ.filter fun i => F (flip x i) ≠ F x).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- La sensibilité de bloc locale est majorée par le nombre de blocs, `2 ^ n`. -/
theorem blockSensitivity_le {n : ℕ} (F : Q n → Bool) (x : Q n) :
    blockSensitivity F x ≤ 2 ^ n := by
  simp only [blockSensitivity]
  calc (Finset.univ.filter fun S : Finset (Fin n) => S.Nonempty ∧ F (flipBlock x S) ≠ F x).card
      ≤ (Finset.univ : Finset (Finset (Fin n))).card := Finset.card_filter_le _ _
    _ = 2 ^ n := by simp

/-!
### L'inégalité fondamentale : chaque singleton est un bloc
-/

/-- `sensitivity ≤ blockSensitivity` : les singletons sont des blocs non vides,
donc chaque voisin sensible est en particulier un bloc sensible. C'est la
direction triviale de l'écart entre les deux quantités ; la conjecture de
sensibilité (résolue par Huang) porte sur la direction inverse. -/
theorem sensitivity_le_blockSensitivity {n : ℕ} (F : Q n → Bool) (x : Q n) :
    sensitivity F x ≤ blockSensitivity F x := by
  classical
  have hsub : ((Finset.univ.filter fun i => F (flip x i) ≠ F x).image
      fun i => ({i} : Finset (Fin n))) ⊆
      Finset.univ.filter fun S : Finset (Fin n) => S.Nonempty ∧ F (flipBlock x S) ≠ F x := by
    intro S hS
    simp only [Finset.mem_image] at hS
    obtain ⟨i, hi, rfl⟩ := hS
    simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and] at hi ⊢
    exact ⟨Finset.singleton_nonempty i, by rw [flipBlock_singleton]; exact hi⟩
  have hinj : Set.InjOn (fun i => ({i} : Finset (Fin n)))
      (↑(Finset.univ.filter fun i => F (flip x i) ≠ F x) : Set (Fin n)) := by
    intro a _ b _ hab
    exact Finset.singleton_inj.1 hab
  simp only [sensitivity, blockSensitivity]
  calc (Finset.univ.filter fun i => F (flip x i) ≠ F x).card
      = ((Finset.univ.filter fun i => F (flip x i) ≠ F x).image
          fun i => ({i} : Finset (Fin n))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ.filter fun S : Finset (Fin n) => S.Nonempty ∧ F (flipBlock x S) ≠ F x).card :=
        Finset.card_le_card hsub

/-!
### Une séparation stricte explicite en dimension 4

La disjonction de deux conjonctions `(x₀ ∧ x₁) ∨ (x₂ ∧ x₃)` possède, au sommet
nul, une sensibilité **nulle** (aucun retournement d'une seule coordonnée ne
l'allume) mais une sensibilité de bloc **non nulle** (retourner le bloc
`{0, 1}` l'allume). La sensibilité de bloc peut donc dépasser strictement la
sensibilité — dès la dimension 4, sur un exemple calculable de bout en bout.
-/

/-- Exemple explicite de dimension 4 : disjonction de deux conjonctions. -/
def orOfAnds (x : Q 4) : Bool := (x 0 && x 1) || (x 2 && x 3)

/-- Au sommet nul, aucune coordonnée seule ne change la valeur de `orOfAnds` :
la sensibilité locale y est **nulle**. -/
theorem orOfAnds_sensitivity_zero :
    sensitivity orOfAnds (fun _ => false) = 0 := by
  classical
  have key : ∀ i : Fin 4, orOfAnds (flip (fun _ => false) i) = false := by
    intro i
    fin_cases i <;> simp [orOfAnds, flip]
  have hset : (Finset.univ.filter
      fun i => orOfAnds (flip (fun _ => false) i) ≠ orOfAnds (fun _ => false)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _ h
    have h0 : orOfAnds (fun _ => false) = false := by simp [orOfAnds]
    rw [key i, h0] at h
    exact absurd rfl h
  simp only [sensitivity, hset, Finset.card_empty]

/-- Retourner le bloc `{0, 1}` au sommet nul allume `orOfAnds` : la sensibilité
de bloc locale y est **non nulle**. -/
theorem orOfAnds_blockSensitivity_pos :
    0 < blockSensitivity orOfAnds (fun _ => false) := by
  classical
  have hval : orOfAnds (flipBlock (fun _ => false) ({0, 1} : Finset (Fin 4))) = true := by
    simp [orOfAnds, flipBlock]
  have hmem : ({0, 1} : Finset (Fin 4)) ∈ Finset.univ.filter
      fun S : Finset (Fin 4) => S.Nonempty ∧
        orOfAnds (flipBlock (fun _ => false) S) ≠ orOfAnds (fun _ => false) := by
    simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and]
    refine ⟨⟨0, by simp⟩, ?_⟩
    rw [hval]
    simp [orOfAnds]
  simp only [blockSensitivity]
  exact Finset.card_pos.2 ⟨_, hmem⟩

/-- **Séparation stricte** : `sensitivity < blockSensitivity` atteint par
l'exemple `orOfAnds` en dimension 4. -/
theorem orOfAnds_strict_separation :
    sensitivity orOfAnds (fun _ => false) < blockSensitivity orOfAnds (fun _ => false) := by
  rw [orOfAnds_sensitivity_zero]
  exact orOfAnds_blockSensitivity_pos

end Sensitivity
