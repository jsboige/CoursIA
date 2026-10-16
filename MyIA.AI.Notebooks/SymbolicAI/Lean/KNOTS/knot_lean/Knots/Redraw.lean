/-
Module maillon 6 (#2874) : la relation de redraw d'un code PD.

Un code PD est une présentation : l'ORDRE de la liste des croisements et les
NOMS des étiquettes d'arêtes ne portent aucune information de dessin. Deux
diagrammes différant par ces deux seuls choix représentent le même dessin
plan. Ce module formalise cette relation (`Redraws`) comme brique du
maillon 6 : relier le certificat de redraw du maillon 5
(`conway_sphereMutate_redraws_kinoshitaTerasaka`, Conway.lean) à
l'équivalence exigée par `AreMutants` (Mutation.lean).

Le docstring de `Knot` (Basic.lean) nomme l'équivalence visée — « modulo les
mouvements de Reidemeister ET l'isotopie planaire » — et note que la seconde
n'est pas encore reliée. `Redraws` en est la brique combinatoire.

Tranche 2 : le témoin de renommage est une bijection `Nat ≃ Nat` (les deux
clauses de fenêtre portent l'aller ET le retour — symétrie sans argument de
cardinalité finie), et la direction du `List.Perm` est celle du certificat
du maillon 5 : `relabelCrossings f (ktRedrawOrder d₁) = d₂`.
-/
import Knots.Basic
import Knots.Reidemeister

/-!
# Redraw d'un code PD (maillon 6)

`Redraws d₁ d₂` : `d₂` s'obtient de `d₁` en permutant la liste des croisements
et en renommant les étiquettes par une bijection qui échange les fenêtres
`edges` des deux diagrammes. C'est l'incarnation formelle du
« réordonnancement + renommage » du certificat de redraw du maillon 5.

## État et écart restant (NOTE MAJ)

Trois voies pour fermer `AreMutants conwayKnot kinoshitaTerasakaKnot` :

1. **Congruence forte** : prouver `Redraws d₁ d₂ → ReidemeisterEquiv d₁ d₂`.
   Mathématiquement vraie (le redraw est une isotopie planaire, et
   l'isotopie planaire est engendrée par les mouvements de Reidemeister),
   mais exige des chaînes explicites de chirurgies — coût élevé, la
   décomposition d'un renommage global en pas R1/R2/R3 conservateurs n'est
   pas triviale (chaque pas R1/R2 change `numEdges`, R3 ne permute que les
   slots de trois croisements).
2. **Amendement définitionnel** : quantifier dans `AreMutants` sur des
   représentants à redraw près. Fidèle au docstring (« diagrammes des mêmes
   classes d'isotopie »), mais affaiblit l'énoncé — décision de design à
   instruire avec le coordinateur (EPIC #2874).
3. **Équivalence composée** : introduire `SameKnot d₁ d₂ := ∃ m₁ m₂,
   Redraws d₁ m₁ ∧ Redraws d₂ m₂ ∧ ReidemeisterEquiv m₁ m₂` et l'utiliser
   dans l'assemblage du maillon 6 sans toucher `AreMutants` (variante de 2).

Tranches posées : définition + équivalence `refl`/`symm`/`trans` (ce
fichier). Tranches suivantes : transfert de `wf`, lemme `List.Perm` pour
`ktRedrawOrder`, pont depuis `conway_sphereMutate_redraws_kinoshitaTerasaka`,
puis le choix de voie.
-/

namespace Knots

/-- Renommage d'un croisement par une fonction sur les étiquettes.
Version par croisement de `relabelCrossings` (Conway.lean, maillon 5) :
`relabelCrossings f cs = cs.map (PDCrossing.relabel f)`. -/
def PDCrossing.relabel (f : Nat → Nat) (c : PDCrossing) : PDCrossing where
  e1 := f c.e1
  e2 := f c.e2
  e3 := f c.e3
  e4 := f c.e4

/-- Redraw : `d₂` s'obtient de `d₁` par un renommage bijectif des étiquettes
qui échange les fenêtres `edges` (donc `numEdges`), et une permutation de la
liste des croisements — la liste de `d₂` est une permutation de la liste de
`d₁` renommée. C'est la direction du certificat du maillon 5 :
`relabelCrossings f (ktRedrawOrder d₁.crossings) = d₂.crossings`. -/
def Redraws (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.numEdges = d₂.numEdges ∧
  ∃ e : Nat ≃ Nat,
    (∀ k ∈ d₁.edges, e k ∈ d₂.edges) ∧
    (∀ k ∈ d₂.edges, e.symm k ∈ d₁.edges) ∧
    d₂.crossings.Perm (d₁.crossings.map (PDCrossing.relabel e))

/-! ### Lemmes auxiliaires : renommage et structure de liste. -/

/-- Le renommage par l'identité est l'identité, par croisement. -/
theorem relabel_equiv_refl (c : PDCrossing) :
    PDCrossing.relabel (Equiv.refl Nat) c = c := rfl

/-- Le renommage par l'identité est l'identité, par liste. -/
theorem map_relabel_equiv_refl (cs : List PDCrossing) :
    cs.map (PDCrossing.relabel (Equiv.refl Nat)) = cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih => rw [List.map_cons, ih, relabel_equiv_refl]

/-- Le renommage compose comme les fonctions : `relabel g ∘ relabel f =
relabel (g ∘ f)`. C'est ce qui rend la transitivité du redraw immédiate. -/
theorem relabel_comp_apply (g f : Nat → Nat) (c : PDCrossing) :
    PDCrossing.relabel g (PDCrossing.relabel f c) = PDCrossing.relabel (g ∘ f) c := rfl

/-- Le renommage par la bijection inverse annule le renommage direct,
par croisement. -/
theorem relabel_symm_apply (e : Nat ≃ Nat) (c : PDCrossing) :
    PDCrossing.relabel e.symm (PDCrossing.relabel e c) = c := by
  simp [PDCrossing.relabel, Equiv.symm_apply_apply]

/-- Le renommage composé s'écrit avec `Equiv.trans` : `relabel e₂ ∘
relabel e₁ = relabel (e₁.trans e₂)` (la convention `Equiv.trans` applique
`e₁` puis `e₂`). -/
theorem relabel_trans_eq (e₁ e₂ : Nat ≃ Nat) :
    (PDCrossing.relabel e₂) ∘ (PDCrossing.relabel e₁) = PDCrossing.relabel (e₁.trans e₂) := by
  funext c
  simp [PDCrossing.relabel, Equiv.trans_apply]

/-! ### Structure : `Redraws` est une équivalence. -/

/-- Réflexivité du redraw : bijection identité, permutation identité. -/
theorem Redraws.refl (d : KnotDiagram) : Redraws d d := by
  refine ⟨rfl, Equiv.refl Nat, fun _ hk => hk, fun _ hk => hk, ?_⟩
  rw [map_relabel_equiv_refl]

/-- Symétrie du redraw : la bijection inverse `e.symm` échange les fenêtres
dans l'autre sens, et l'annulation `e.symm ∘ e = id` ramène la liste
renommée à la liste de départ. -/
theorem Redraws.symm {d₁ d₂ : KnotDiagram} (h : Redraws d₁ d₂) : Redraws d₂ d₁ := by
  obtain ⟨hne, e, hw₁, hw₂, hperm⟩ := h
  refine ⟨hne.symm, e.symm, fun k hk => hw₂ k hk, fun k hk => hw₁ k hk, ?_⟩
  -- De hperm : d₂ ~ d₁.map (relabel e), on mappe par (relabel e.symm) :
  -- d₂.map (relabel e.symm) ~ (d₁.map (relabel e)).map (relabel e.symm)
  --   = d₁.map (relabel e.symm ∘ relabel e) = d₁.map id = d₁,
  -- puis symétrie de la permutation.
  have hmap := List.Perm.map (PDCrossing.relabel e.symm) hperm
  rw [List.map_map] at hmap
  have hfn : (PDCrossing.relabel e.symm) ∘ (PDCrossing.relabel e) = id := by
    funext c
    simpa using relabel_symm_apply e c
  rw [hfn, List.map_id] at hmap
  exact hmap.symm

/-- Transitivité du redraw : les bijections se composent par `Equiv.trans`
(la convention applique `e₁` puis `e₂`, qui est exactement l'ordre de
composition des renommages), et les permutations se chaînent. -/
theorem Redraws.trans {d₁ d₂ d₃ : KnotDiagram} (h₁ : Redraws d₁ d₂) (h₂ : Redraws d₂ d₃) :
    Redraws d₁ d₃ := by
  obtain ⟨hne₁, e₁, hw₁₁, hw₁₂, hp₁⟩ := h₁
  obtain ⟨hne₂, e₂, hw₂₁, hw₂₂, hp₂⟩ := h₂
  refine ⟨hne₁.trans hne₂, e₁.trans e₂, ?_, ?_, ?_⟩
  · intro k hk
    rw [Equiv.trans_apply]
    exact hw₂₁ (e₁ k) (hw₁₁ k hk)
  · intro k hk
    rw [Equiv.symm_trans_apply]
    exact hw₁₂ (e₂.symm k) (hw₂₂ k hk)
  · -- d₃ ~ d₂.map (relabel e₂) [hp₂] et
    -- d₂.map (relabel e₂) ~ d₁.map (relabel (e₁.trans e₂)) [mapping de hp₁].
    have hmap := List.Perm.map (PDCrossing.relabel e₂) hp₁
    rw [List.map_map, relabel_trans_eq] at hmap
    exact hp₂.trans hmap

end Knots
