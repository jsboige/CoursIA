import Mathlib

/-!
# Planning.Strips — modèle STRIPS : fluents, états, actions, transitions

**STRIPS** (STanford Research Institute Problem Solver) est le formalisme canonique de
la planification classique. On modélise :

- un **fluent** (fait atomique) `F` comme un type quelconque (décidablement égalable,
  pour les opérations ensemblistes) ;
- un **état** `s : Finset F` comme l'ensemble des fluents vrais ;
- une **action** STRIPS `a = (pre, add, del)` :
  - `pre a` : préconditions (fluents requis),
  - `add a` : effets additifs (fluents devenant vrais),
  - `del a` : effets de *deletion* (fluents devenant faux).

Une action `a` est **applicable** dans l'état `s` quand `pre a ⊆ s`. La **transition
réelle** applique add ET del : `step a s = (s \ del a) ∪ add a`. La **transition
relaxée** (sans-delete, cœur de h⁺) ignore les deletions : `stepR a s = s ∪ add a`.

Cette relaxation rend l'atteignabilité **monotone** : l'état relaxé ne fait que croître,
ce qui rend le calcul du plan relaxé polynomial et garantit l'**admissibilité** h⁺ ≤ h*
(prouvée dans `Admissibility.lean`). Voir l'issue #4053.
-/

namespace PlanningLean

/-- Un **état** STRIPS = l'ensemble des fluents actuellement vrais. -/
abbrev State (F : Type) := Finset F

/-- Une **action** STRIPS : préconditions, effets additifs, effets de deletion. -/
structure Action (F : Type) where
  /-- Préconditions : fluents requis pour que l'action soit applicable. -/
  pre : Finset F
  /-- Effets additifs : fluents devenant vrais après l'action. -/
  add : Finset F
  /-- Effets de deletion : fluents devenant faux après l'action (ignorés par la relaxation). -/
  del : Finset F

variable {F : Type} [DecidableEq F]

/-- Une action est **applicable** dans `s` quand ses préconditions sont satisfaites. -/
def applicable (a : Action F) (s : State F) : Prop := a.pre ⊆ s

/-- La **transition réelle** : on retire les deletions puis on ajoute les add.
    `step a s = (s \ a.del) ∪ a.add`. -/
def step (a : Action F) (s : State F) : State F := (s \ a.del) ∪ a.add

/-- La **transition relaxée** (sans-delete) : on ignore les deletions.
    `stepR a s = s ∪ a.add`. C'est le cœur de la relaxation h⁺. -/
def stepR (a : Action F) (s : State F) : State F := s ∪ a.add

/-- Le but `g` est **atteint** par l'état `s` quand tous les fluents du but sont présents. -/
def goalSatisfied (g s : State F) : Prop := g ⊆ s

/-- Lemme clé : la transition réelle est incluse dans la transition relaxée.
    `step a s ⊆ stepR a s` car `s \ a.del ⊆ s`. -/
lemma step_subset_stepR (a : Action F) (s : State F) : step a s ⊆ stepR a s := by
  rw [Finset.subset_iff]
  intro x hx
  unfold step at hx
  unfold stepR
  simp only [Finset.mem_union, Finset.mem_sdiff] at hx ⊢
  rcases hx with h | h
  · exact Or.inl h.1
  · exact Or.inr h

/-- La transition réelle est **monotone** en l'état : `s ⊆ s'` entraîne `step a s ⊆ step a s'`. -/
lemma step_mono (a : Action F) {s s' : State F} (h : s ⊆ s') : step a s ⊆ step a s' := by
  rw [Finset.subset_iff]
  intro x hx
  unfold step at hx ⊢
  simp only [Finset.mem_union, Finset.mem_sdiff] at hx ⊢
  rcases hx with hs | ha
  · exact Or.inl ⟨h hs.1, hs.2⟩
  · exact Or.inr ha

/-- La transition relaxée est **monotone** en l'état : `s ⊆ s'` entraîne `stepR a s ⊆ stepR a s'`. -/
lemma stepR_mono (a : Action F) {s s' : State F} (h : s ⊆ s') : stepR a s ⊆ stepR a s' := by
  rw [Finset.subset_iff]
  intro x hx
  unfold stepR at hx ⊢
  simp only [Finset.mem_union] at hx ⊢
  rcases hx with hs | ha
  · exact Or.inl (h hs)
  · exact Or.inr ha

end PlanningLean
