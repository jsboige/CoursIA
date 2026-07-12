import Mathlib

/-!
# Sudoku.Basic — structure de contraintes, solutions, paires

Formalisation abstraite d'un Sudoku (plus généralement : tout problème de satisfaction
de contraintes « à portées toutes-distinctes »). Un Sudoku 9×9 concret est une instance
de ce cadre : les **portées** (`scopes`) sont ses 27 familles (9 lignes, 9 colonnes,
9 blocs), chacune devant porter des valeurs **toutes distinctes**.

L'abstraction est délibérée : les théorèmes de soundness de la propagation
(`Propagation.lean`) sont valables pour **toute** structure de ce type, pas seulement
le 9×9. C'est le bon niveau de formalisation — la logique de la propagation ne dépend
pas du fait qu'il y ait 9 valeurs ou des blocs 3×3, mais seulement de l'invariant
« toutes-distinctes par portée ».

Référence croisée : la série `Sudoku` (backtracking, OR-Tools, .NET, Infer.NET) dont ce
lake fonde formellement les solveurs par propagation. Voir issue #4055.
-/

namespace Sudoku

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- La structure de contraintes d'un Sudoku : un ensemble fini de **portées** (chacune
    un `Finset` de cellules) devant porter des valeurs toutes distinctes. -/
abbrev Scopes (ι : Type*) := Finset (Finset ι)

/-- Une affectation complète : une valeur par cellule. -/
abbrev Solution (ι V : Type*) := ι → V

/-- `σ` est **toutes-distinctes sur `s`** si deux cellules distinctes de `s` ne portent
    jamais la même valeur (injectivité de `σ` sur `s`). -/
def AllDistinctOn (σ : Solution ι V) (s : Finset ι) : Prop :=
  ∀ ⦃c c'⦄, c ∈ s → c' ∈ s → σ c = σ c' → c = c'

/-- `σ` est une **solution** de la structure `scopes` si elle est toutes-distinctes sur
    chacune des portées. C'est l'invariant fondamental du Sudoku (chaque ligne, colonne
    et bloc contient chaque valeur au plus une fois). -/
def IsSolution (scopes : Scopes ι) (σ : Solution ι V) : Prop :=
  ∀ s ∈ scopes, AllDistinctOn σ s

/-- `σ` **concorde** avec une affectation partielle `a` partout où `a` est définie. -/
def AgreesWith (σ : Solution ι V) (a : ι → Option V) : Prop :=
  ∀ i, ∀ v, a i = some v → σ i = v

/-- `c'` est une **paire** de `c` (anglais : *peer*) si elles sont distinctes et
    partagent au moins une portée. Deux cellules paires ne peuvent porter la même
    valeur dans une solution. -/
def IsPeer (scopes : Scopes ι) (c c' : ι) : Prop :=
  c ≠ c' ∧ ∃ s ∈ scopes, c ∈ s ∧ c' ∈ s

/-- Une valeur `v` est **présente dans la portée `s`** si quelque cellule de `s` la
    porte. Pour une portée « pleine maison » (|s| = |V|) d'une solution, toute valeur y
    est présente (lemme de la maison pleine). -/
def PresentIn (σ : Solution ι V) (s : Finset ι) (v : V) : Prop :=
  ∃ c ∈ s, σ c = v

/-- **Lemme de la maison pleine.** Si une portée `s` contient autant de cellules que de
    valeurs possibles (`s.card = card V`) et qu'une affectation `σ` est toutes-distinctes
    sur `s`, alors **toute** valeur `v` est présente dans `s`.

    C'est l'argument de pigeonhole : `σ` restreinte à `s` est injective, donc son image
    a `card s = card V` éléments distincts — soit la totalité de `V` — donc toute valeur
    y apparaît. Ce lemme rend automatique l'hypothèse `PresentIn σ s v` du « hidden single »
    (`Propagation.hidden_single_sound`) dans le cas plein-maison (cf #4055). -/
theorem full_house_present {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
    [DecidableEq V] (σ : Solution ι V) (s : Finset ι) (v : V)
    (hcard : s.card = Fintype.card V) (hAD : AllDistinctOn σ s) : PresentIn σ s v := by
  -- `AllDistinctOn σ s` ⟺ `Set.InjOn σ s` (même forme, Finset/Set membership defeq)
  have hinj : Set.InjOn σ s := by
    intros c hc c' hc' heq
    exact hAD hc hc' heq
  -- L'image `σ '' s` a même cardinalité que `s` (injectivité)
  have hcard_img : (Finset.image σ s).card = s.card := Finset.card_image_of_injOn hinj
  -- `σ '' s ⊆ univ`, de même cardinalité que `univ` (= card V) ⟹ `σ '' s = univ`
  have hsub : Finset.image σ s ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
  have heq_img : Finset.image σ s = (Finset.univ : Finset V) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard_img, hcard]; simp
  -- `v ∈ σ '' s` (= univ), puis `mem_image` ⟺ `∃ c ∈ s, σ c = v` = `PresentIn`
  have hmem : v ∈ Finset.image σ s := heq_img ▸ Finset.mem_univ v
  rw [Finset.mem_image] at hmem
  exact hmem

end Sudoku
