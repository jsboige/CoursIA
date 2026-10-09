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

La sensibilité de bloc suit la **définition standard** (Nisan–Szegedy) : le
**maximum, sur les familles de blocs non vides, sensibles et deux à deux
disjoints, du cardinal de la famille** — et non le compte de tous les blocs
sensibles. Le témoin `or3_blockSensitivity` exécute la différence : pour OR
sur trois coordonnées au sommet nul, les sept blocs non vides sont tous
sensibles (`or3_sensitive_blocks_card`), mais la sensibilité de bloc vaut
**3** — les trois singletons — et ne dépasse jamais la dimension
(`blockSensitivity_le`).

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

/-- Sensibilité de bloc locale de `F` en `x` — **définition standard**
(Nisan–Szegedy) : le **maximum du nombre de blocs sensibles deux à deux
disjoints**, c'est-à-dire le cardinal maximal d'une famille de blocs **non
vides** dont le retournement simultané change la valeur de `F`, et dont deux
membres distincts sont toujours d'intersection vide.

Ce n'est **pas** le compte de tous les blocs sensibles : au sommet nul de `or3`,
les sept blocs non vides sont tous sensibles, mais la valeur standard est 3 —
les trois singletons (`or3_blockSensitivity`). La disjonction borne la quantité
par la dimension (`blockSensitivity_le`), quand un compte brut de blocs
sensibles atteindrait jusqu'à `2 ^ n - 1`. La famille vide est admissible (de
cardinal nul) : le maximum existe toujours et vaut au moins `0`. -/
def blockSensitivity {n : ℕ} (F : Q n → Bool) (x : Q n) : ℕ :=
  (Finset.univ.filter fun 𝓑 : Finset (Finset (Fin n)) =>
      (∀ B ∈ 𝓑, B.Nonempty ∧ F (flipBlock x B) ≠ F x) ∧
      (∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, B₁ ≠ B₂ → (B₁ ∩ B₂ : Finset (Fin n)) = ∅)).sup
    Finset.card

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

/-- **La sensibilité de bloc est majorée par la dimension** : les blocs d'une
famille admissible sont non vides et deux à deux disjoints, donc l'application
« plus petit élément d'un bloc » est injective sur la famille, dont le cardinal
ne peut pas dépasser `n`. Un compte brut de blocs sensibles, lui, atteindrait
jusqu'à `2 ^ n - 1`. -/
theorem blockSensitivity_le {n : ℕ} (F : Q n → Bool) (x : Q n) :
    blockSensitivity F x ≤ n := by
  classical
  refine Finset.sup_le ?_
  intro 𝓑 h𝓑
  have hmem : ∀ B ∈ 𝓑, B.Nonempty := fun B hB =>
    ((Finset.mem_filter.1 h𝓑).2.1 B hB).1
  have hdisj : ∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, B₁ ≠ B₂ → (B₁ ∩ B₂ : Finset (Fin n)) = ∅ :=
    fun B₁ hB₁ B₂ hB₂ hne => (Finset.mem_filter.1 h𝓑).2.2 B₁ hB₁ B₂ hB₂ hne
  have hinj : Set.InjOn (fun p : {B : Finset (Fin n) // B ∈ 𝓑} =>
      p.1.min' (hmem p.1 p.2)) (↑𝓑.attach : Set {B : Finset (Fin n) // B ∈ 𝓑}) := by
    intro p _ q _ hpq
    by_contra hpne
    have hBne : p.1 ≠ q.1 := fun h => hpne (Subtype.ext h)
    have hp : p.1.min' (hmem p.1 p.2) ∈ p.1 := Finset.min'_mem _ _
    have hq : q.1.min' (hmem q.1 q.2) ∈ q.1 := Finset.min'_mem _ _
    have hboth : p.1.min' (hmem p.1 p.2) ∈ q.1 := by
      rw [show p.1.min' (hmem p.1 p.2) = q.1.min' (hmem q.1 q.2) from hpq]
      exact hq
    have hinter : p.1.min' (hmem p.1 p.2) ∈ (p.1 ∩ q.1 : Finset (Fin n)) :=
      Finset.mem_inter.2 ⟨hp, hboth⟩
    rw [hdisj p.1 p.2 q.1 q.2 hBne] at hinter
    simp at hinter
  calc 𝓑.card = 𝓑.attach.card := Finset.card_attach.symm
    _ = (𝓑.attach.image
          fun p : {B : Finset (Fin n) // B ∈ 𝓑} => p.1.min' (hmem p.1 p.2)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

/-!
### L'inégalité fondamentale : les singletons forment une famille disjointe
-/

/-- `sensitivity ≤ blockSensitivity` : les singletons des coordonnées
sensibles forment une famille admissible — des singletons distincts sont
d'intersection vide — donc leur cardinal, qui est celui des coordonnées
sensibles, minore le maximum. C'est la direction triviale de l'écart entre les
deux quantités ; la conjecture de sensibilité (résolue par Huang) porte sur la
direction inverse. -/
theorem sensitivity_le_blockSensitivity {n : ℕ} (F : Q n → Bool) (x : Q n) :
    sensitivity F x ≤ blockSensitivity F x := by
  classical
  have hfam : ∀ B ∈ (Finset.univ.filter fun i => F (flip x i) ≠ F x).image
      fun i => ({i} : Finset (Fin n)), B.Nonempty ∧ F (flipBlock x B) ≠ F x := by
    intro B hB
    simp only [Finset.mem_image] at hB
    obtain ⟨i, hi, rfl⟩ := hB
    exact ⟨Finset.singleton_nonempty i, by
      rw [flipBlock_singleton]; exact (Finset.mem_filter.1 hi).2⟩
  have hpair : ∀ B₁ ∈ (Finset.univ.filter fun i => F (flip x i) ≠ F x).image
      fun i => ({i} : Finset (Fin n)), ∀ B₂ ∈
      (Finset.univ.filter fun i => F (flip x i) ≠ F x).image
        fun i => ({i} : Finset (Fin n)), B₁ ≠ B₂ →
      (B₁ ∩ B₂ : Finset (Fin n)) = ∅ := by
    intro B₁ hB₁ B₂ hB₂ hne
    simp only [Finset.mem_image] at hB₁ hB₂
    obtain ⟨i, -, rfl⟩ := hB₁
    obtain ⟨j, -, rfl⟩ := hB₂
    have hij : i ≠ j := fun h => hne (Finset.singleton_inj.2 h)
    ext a
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · intro h
      exact absurd (h.1.symm.trans h.2) hij
    · intro h
      simp at h
  have hinj : Set.InjOn (fun i => ({i} : Finset (Fin n)))
      (↑(Finset.univ.filter fun i => F (flip x i) ≠ F x) : Set (Fin n)) := by
    intro a _ b _ hab
    exact Finset.singleton_inj.1 hab
  calc sensitivity F x
      = ((Finset.univ.filter fun i => F (flip x i) ≠ F x).image
          fun i => ({i} : Finset (Fin n))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ blockSensitivity F x := by
        refine Finset.le_sup ?_
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hfam, hpair⟩⟩

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

/-- Retourner le bloc `{0, 1}` au sommet nul allume `orOfAnds` : la famille
singleton `{{0, 1}}` est admissible, donc la sensibilité de bloc locale y est
**non nulle**. -/
theorem orOfAnds_blockSensitivity_pos :
    0 < blockSensitivity orOfAnds (fun _ => false) := by
  classical
  have hval : orOfAnds (flipBlock (fun _ => false) ({0, 1} : Finset (Fin 4))) = true := by
    simp [orOfAnds, flipBlock]
  have hfalse : orOfAnds (fun _ => false) = false := by simp [orOfAnds]
  have hfam : ∀ B ∈ ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))),
      B.Nonempty ∧ orOfAnds (flipBlock (fun _ => false) B) ≠ orOfAnds (fun _ => false) := by
    intro B hB
    simp only [Finset.mem_singleton] at hB
    subst hB
    exact ⟨⟨0, by simp⟩, by simp [hval, hfalse]⟩
  have hpair : ∀ B₁ ∈ ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))),
      ∀ B₂ ∈ ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))), B₁ ≠ B₂ →
      (B₁ ∩ B₂ : Finset (Fin 4)) = ∅ := by
    intro B₁ hB₁ B₂ hB₂ hne
    simp only [Finset.mem_singleton] at hB₁ hB₂
    rw [hB₁, hB₂] at hne
    exact absurd rfl hne
  have hone : ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))).card ≤
      blockSensitivity orOfAnds (fun _ => false) := by
    refine Finset.le_sup ?_
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hfam, hpair⟩⟩
  have h1 : ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))).card = 1 := by simp
  rw [h1] at hone
  exact hone

/-- **Séparation stricte** : `sensitivity < blockSensitivity` atteint par
l'exemple `orOfAnds` en dimension 4. -/
theorem orOfAnds_strict_separation :
    sensitivity orOfAnds (fun _ => false) < blockSensitivity orOfAnds (fun _ => false) := by
  rw [orOfAnds_sensitivity_zero]
  exact orOfAnds_blockSensitivity_pos

/-!
### Le témoin OR₃ : trois, pas sept

Au sommet nul de OR₃, **tous** les blocs non vides sont sensibles — il y en a
sept. Une définition qui compterait les blocs sensibles lirait donc 7 ; la
définition standard lit **3**, le cardinal maximal d'une famille disjointe
(les trois singletons), borné par la dimension. C'est le témoin qui distingue
les deux lectures de la définition.
-/

/-- OR sur les trois coordonnées de `Q 3`. -/
def or3 (x : Q 3) : Bool := x 0 || x 1 || x 2

/-- Au sommet nul, les **sept** blocs non vides de `Fin 3` sont tous sensibles
pour `or3` : c'est le compte que lirait une définition énumérant les blocs
sensibles. -/
theorem or3_sensitive_blocks_card :
    (Finset.univ.filter fun S : Finset (Fin 3) =>
       S.Nonempty ∧ or3 (flipBlock (fun _ => false) S) ≠ or3 (fun _ => false)).card = 7 := by
  decide

/-- **Témoin de la définition standard** : la sensibilité de bloc de `or3` au
sommet nul vaut **3**, et non 7, bien que les sept blocs non vides soient
sensibles (`or3_sensitive_blocks_card`). La majoration vient de la dimension
(`blockSensitivity_le`) ; la minoration, de la famille admissible des trois
singletons. -/
theorem or3_blockSensitivity :
    blockSensitivity or3 (fun _ => false) = 3 := by
  apply Nat.le_antisymm ?_ ?_
  · exact blockSensitivity_le or3 (fun _ => false)
  · have hzero : or3 (fun _ => false) = false := by simp [or3]
    have hsens : ∀ i : Fin 3, or3 (flip (fun _ => false) i) = true := by
      intro i
      fin_cases i <;> simp [or3, flip]
    have hfam : ∀ B ∈ (Finset.univ : Finset (Fin 3)).image
        fun i => ({i} : Finset (Fin 3)),
        B.Nonempty ∧ or3 (flipBlock (fun _ => false) B) ≠ or3 (fun _ => false) := by
      intro B hB
      simp only [Finset.mem_image] at hB
      obtain ⟨i, -, rfl⟩ := hB
      exact ⟨Finset.singleton_nonempty i, by simp [flipBlock_singleton, hsens i, hzero]⟩
    have hpair : ∀ B₁ ∈ (Finset.univ : Finset (Fin 3)).image
        fun i => ({i} : Finset (Fin 3)), ∀ B₂ ∈ (Finset.univ : Finset (Fin 3)).image
        fun i => ({i} : Finset (Fin 3)), B₁ ≠ B₂ →
        (B₁ ∩ B₂ : Finset (Fin 3)) = ∅ := by
      intro B₁ hB₁ B₂ hB₂ hne
      simp only [Finset.mem_image] at hB₁ hB₂
      obtain ⟨i, -, rfl⟩ := hB₁
      obtain ⟨j, -, rfl⟩ := hB₂
      have hij : i ≠ j := fun h => hne (Finset.singleton_inj.2 h)
      ext a
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · intro h
        exact absurd (h.1.symm.trans h.2) hij
      · intro h
        simp at h
    have hcard : ((Finset.univ : Finset (Fin 3)).image
        fun i => ({i} : Finset (Fin 3))).card = 3 := by
      rw [Finset.card_image_of_injOn]
      · simp
      · intro a _ b _ hab
        exact Finset.singleton_inj.1 hab
    calc 3 = ((Finset.univ : Finset (Fin 3)).image
          fun i => ({i} : Finset (Fin 3))).card := hcard.symm
      _ ≤ blockSensitivity or3 (fun _ => false) := by
          refine Finset.le_sup ?_
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hfam, hpair⟩⟩

end Sensitivity
