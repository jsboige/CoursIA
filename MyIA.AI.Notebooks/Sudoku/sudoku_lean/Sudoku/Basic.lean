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

---

**English — Constraint structure, solutions, peers.**

Abstract formalisation of a Sudoku (more generally: any constraint-satisfaction problem
with "all-distinct scopes"). A concrete 9×9 Sudoku is one instance of this framework: the
**scopes** are its 27 families (9 rows, 9 columns, 9 blocks), each of which must carry
**all-distinct** values.

The abstraction is deliberate: the soundness theorems of propagation (`Propagation.lean`)
hold for **every** structure of this kind, not only the 9×9 grid. This is the right level
of formalisation — the logic of propagation does not depend on there being 9 values or
3×3 blocks, only on the "all-distinct per scope" invariant.

Cross-reference: the `Sudoku` series (backtracking, OR-Tools, .NET, Infer.NET), whose
propagation-based solvers this lake formally grounds. See issue #4055.
-/

namespace Sudoku

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- La structure de contraintes d'un Sudoku : un ensemble fini de **portées** (chacune
    un `Finset` de cellules) devant porter des valeurs toutes distinctes.

    The constraint structure of a Sudoku: a finite set of **scopes** (each a `Finset` of
    cells) that must carry all-distinct values. -/
abbrev Scopes (ι : Type*) := Finset (Finset ι)

/-- Une affectation complète : une valeur par cellule.

    A complete assignment: one value per cell. -/
abbrev Solution (ι V : Type*) := ι → V

/-- `σ` est **toutes-distinctes sur `s`** si deux cellules distinctes de `s` ne portent
    jamais la même valeur (injectivité de `σ` sur `s`).

    `σ` is **all-distinct on `s`** if two distinct cells of `s` never carry the same
    value (injectivity of `σ` on `s`). -/
def AllDistinctOn (σ : Solution ι V) (s : Finset ι) : Prop :=
  ∀ ⦃c c'⦄, c ∈ s → c' ∈ s → σ c = σ c' → c = c'

/-- `σ` est une **solution** de la structure `scopes` si elle est toutes-distinctes sur
    chacune des portées. C'est l'invariant fondamental du Sudoku (chaque ligne, colonne
    et bloc contient chaque valeur au plus une fois).

    `σ` is a **solution** of the structure `scopes` if it is all-distinct on every scope.
    This is the fundamental Sudoku invariant (each row, column and block contains each
    value at most once). -/
def IsSolution (scopes : Scopes ι) (σ : Solution ι V) : Prop :=
  ∀ s ∈ scopes, AllDistinctOn σ s

/-- `σ` **concorde** avec une affectation partielle `a` partout où `a` est définie.

    `σ` **agrees** with a partial assignment `a` wherever `a` is defined. -/
def AgreesWith (σ : Solution ι V) (a : ι → Option V) : Prop :=
  ∀ i, ∀ v, a i = some v → σ i = v

/-- `c'` est une **paire** de `c` (anglais : *peer*) si elles sont distinctes et
    partagent au moins une portée. Deux cellules paires ne peuvent porter la même
    valeur dans une solution.

    `c'` is a **peer** of `c` if they are distinct and share at least one scope. Two peer
    cells cannot carry the same value in a solution. -/
def IsPeer (scopes : Scopes ι) (c c' : ι) : Prop :=
  c ≠ c' ∧ ∃ s ∈ scopes, c ∈ s ∧ c' ∈ s

/-- Une valeur `v` est **présente dans la portée `s`** si quelque cellule de `s` la
    porte. Pour une portée « pleine maison » (|s| = |V|) d'une solution, toute valeur y
    est présente (lemme de la maison pleine).

    A value `v` is **present in the scope `s`** if some cell of `s` carries it. For a
    "full house" scope (|s| = |V|) of a solution, every value is present there (full-house
    lemma). -/
def PresentIn (σ : Solution ι V) (s : Finset ι) (v : V) : Prop :=
  ∃ c ∈ s, σ c = v

/-- **Lemme de la maison pleine.** Si une portée `s` contient autant de cellules que de
    valeurs possibles (`s.card = card V`) et qu'une affectation `σ` est toutes-distinctes
    sur `s`, alors **toute** valeur `v` est présente dans `s`.

    C'est l'argument de pigeonhole : `σ` restreinte à `s` est injective, donc son image
    a `card s = card V` éléments distincts — soit la totalité de `V` — donc toute valeur
    y apparaît. Ce lemme rend automatique l'hypothèse `PresentIn σ s v` du « hidden single »
    (`Propagation.hidden_single_sound`) dans le cas plein-maison (cf #4055).

    **Full-house lemma.** If a scope `s` contains as many cells as there are possible
    values (`s.card = card V`) and an assignment `σ` is all-distinct on `s`, then
    **every** value `v` is present in `s`.

    This is the pigeonhole argument: `σ` restricted to `s` is injective, so its image has
    `card s = card V` distinct elements — i.e. all of `V` — hence every value appears
    there. This lemma makes the hypothesis `PresentIn σ s v` of the "hidden single"
    (`Propagation.hidden_single_sound`) automatic in the full-house case (cf. #4055). -/
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
