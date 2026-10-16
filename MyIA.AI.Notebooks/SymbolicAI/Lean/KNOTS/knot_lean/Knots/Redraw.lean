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
-/
import Knots.Basic
import Knots.Reidemeister

/-!
# Redraw d'un code PD (maillon 6)

`Redraws d₁ d₂` : `d₂` s'obtient de `d₁` en permutant la liste des croisements
et en renommant les étiquettes par une fonction injective qui préserve la
fenêtre d'étiquettes. C'est l'incarnation formelle du « réordonnancement +
renommage » du certificat de redraw du maillon 5.

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

Ce module livre le socle commun aux trois voies : la définition, sa
réflexivité, et (tranches suivantes) symétrie, transitivité, transfert de
`wf`, lemme de permutation pour `ktRedrawOrder`, et le pont depuis le
certificat du maillon 5.
-/

namespace Knots

/-- Renommage d'un croisement par une fonction sur les étiquettes.
Version par croisement de `relabelCrossings` (Conway.lean, maillon 5). -/
def PDCrossing.relabel (f : Nat → Nat) (c : PDCrossing) : PDCrossing where
  e1 := f c.e1
  e2 := f c.e2
  e3 := f c.e3
  e4 := f c.e4

/-- Redraw : `d₂` s'obtient de `d₁` par une permutation de la liste des
croisements et un renommage injectif des étiquettes préservant la fenêtre
`edges` (donc `numEdges`). L'injectivité garantit que deux étiquettes
distinctes de `d₁` restent distinctes dans `d₂` — condition minimale pour
que le renommage ne fusionne pas deux arêtes du dessin. -/
def Redraws (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.numEdges = d₂.numEdges ∧
  ∃ f : Nat → Nat,
    Function.Injective f ∧
    (∀ k ∈ d₁.edges, f k ∈ d₂.edges) ∧
    d₁.crossings.Perm (d₂.crossings.map (PDCrossing.relabel f))

/-- Réflexivité du redraw : identité sur les étiquettes, permutation
identité sur la liste. -/
theorem Redraws.refl (d : KnotDiagram) : Redraws d d := by
  refine ⟨rfl, id, Function.injective_id, fun k hk => hk, ?_⟩
  have hmap : d.crossings.map (PDCrossing.relabel id) = d.crossings := by
    induction d.crossings with
    | nil => rfl
    | cons c cs ih =>
      rw [List.map_cons, ih]
      rfl
  rw [hmap]

end Knots
