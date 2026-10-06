/-
  Knots.Mutation — Mutation de Conway
  ====================================

  Une mutation de Conway prend un nœud K muni d'une sphère de Conway (rencontre K
  en 4 points), le découpe le long de la sphère, effectue une rotation de 180°,
  puis recolle. La mutation préserve le polynôme d'Alexander et le polynôme de
  Jones — c'est le socle de la paire Conway / Kinoshita-Terasaka (§2-3 du
  monolithe historique, désormais `Knots.ConwayPD`).

  Extrait de `Knots.Conway` (tranche 2 du split #18397, tranche 1 = `Knots.Slice`
  en #18528). Epic #2874.
-/

import Knots.Basic
import Knots.Reidemeister

namespace Knots

/-! ## 1. Mutation de Conway

Une mutation de Conway prend un nœud K muni d'une sphère de Conway (rencontre K
en 4 points), le découpe le long de la sphère, effectue une rotation de 180°,
puis recolle. La mutation préserve :
- le polynôme d'Alexander
- le polynôme de Jones
- le genre du nœud

Le nœud de Conway et le nœud de Kinoshita-Terasaka sont reliés par mutation.
-/

/-- Une sphère de Conway : une S² rencontrant le nœud transversalement en 4 points. -/
structure ConwaySphere where
  -- The 4 intersection points on the knot
  points : Fin 4 → Nat
  -- TODO: proper geometric definition

/-! ### Traduction combinatoire de la mutation au niveau des codes PD

La mutation est géométrique (découper le long d'une sphère de Conway, tourner
de 180°, recoller), mais la topologie PL — recollement de variétés à bord —
est hors de portée de Mathlib. La traduction combinatoire retenue : la rotation
de 180° d'un tangle à 2 brins agit sur ses 4 points de bord comme un élément
du groupe de Klein {id, (12)(34), (13)(24), (14)(23)} — les trois demi-tours
et l'identité. Au niveau des codes PD, muter une fenêtre de croisements =
permuter les positions des étiquettes dans chaque croisement de la fenêtre.

La mutation préserve le nombre de croisements (lemme `mutateWindow_length`) —
c'est ce qui rend le contrôle négatif ci-dessous décidable.
-/

/-- Rotations de 180° d'un tangle à 2 brins : le groupe de Klein sur les
quatre points de bord {id, (12)(34), (13)(24), (14)(23)}. Chaque élément est
son propre inverse. -/
inductive KleinRot where
  | id : KleinRot
  | r12 : KleinRot
  | r13 : KleinRot
  | r14 : KleinRot

/-- Action d'une rotation de Klein sur un croisement PD : les étiquettes
(valeurs) sont préservées, leurs positions sont permutées. -/
def KleinRot.apply (ρ : KleinRot) (c : PDCrossing) : PDCrossing :=
  match ρ with
  | .id => c
  | .r12 => ⟨c.e2, c.e1, c.e4, c.e3⟩
  | .r13 => ⟨c.e3, c.e4, c.e1, c.e2⟩
  | .r14 => ⟨c.e4, c.e3, c.e2, c.e1⟩

theorem KleinRot.apply_involutive (ρ : KleinRot) (c : PDCrossing) :
    ρ.apply (ρ.apply c) = c := by
  cases ρ <;> cases c <;> rfl

/-- Mutation d'une fenêtre [i, j) de la liste de croisements : les croisements
hors de la fenêtre sont inchangés, ceux de la fenêtre sont rotés par ρ.
Fenêtre vide (j ≤ i) : identité. Fenêtre pleine : tout le diagramme. -/
def mutateWindow : List PDCrossing → Nat → Nat → KleinRot → List PDCrossing
  | [], _, _, _ => []
  | c :: cs', 0, 0, _ => c :: cs'
  | c :: cs', 0, j+1, ρ => ρ.apply c :: mutateWindow cs' 0 j ρ
  | c :: cs', _+1, 0, _ => c :: cs'
  | c :: cs', i+1, j+1, ρ => c :: mutateWindow cs' i j ρ

/-- La mutation préserve le nombre de croisements. -/
theorem mutateWindow_length (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot) :
    (mutateWindow cs i j ρ).length = cs.length := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, _+1 => simp [mutateWindow, ih]
    | _+1, 0 => rfl
    | _+1, _+1 => simp [mutateWindow, ih]

/-- La mutation est involutive : muter deux fois la même fenêtre avec la même
rotation redonne la liste initiale (chaque élément de Klein est son propre
inverse). -/
theorem mutateWindow_involutive (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot) :
    mutateWindow (mutateWindow cs i j ρ) i j ρ = cs := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    match i, j with
    | 0, 0 => rfl
    | 0, j+1 =>
      simp only [mutateWindow]
      rw [ih 0 j, KleinRot.apply_involutive]
    | _+1, 0 => rfl
    | _+1, _+1 => simp only [mutateWindow, ih _ _]

/-- Deux diagrammes sont mutants s'il existe une fenêtre et une rotation de
Klein envoyant la liste de croisements de l'un sur celle de l'autre. -/
def AreMutantDiagrams (d₁ d₂ : KnotDiagram) : Prop :=
  ∃ (i j : Nat) (ρ : KleinRot), mutateWindow d₁.crossings i j ρ = d₂.crossings

/-- Deux nœuds sont mutants s'ils possèdent des diagrammes représentants (au
sens de Reidemeister) mutants. Le quantificateur existentiel sur les
représentants est essentiel : la mutation ne s'applique pas nécessairement
aux diagrammes désignés, mais à des diagrammes des mêmes classes d'isotopie. -/
def AreMutants (k₁ k₂ : Knot) : Prop :=
  ∃ (d₁ d₂ : KnotDiagram),
    ReidemeisterEquiv k₁.diagram d₁ ∧
    ReidemeisterEquiv k₂.diagram d₂ ∧
    AreMutantDiagrams d₁ d₂

/-! ### Théorie élémentaire : réflexivité et symétrie

Réflexivité : fenêtre vide. Symétrie : involutivité de `mutateWindow`
(chaque rotation de Klein est son propre inverse). La transitivité est
fausse en général pour la mutation (composer deux mutations sur des fenêtres
différentes n'est pas une mutation one-shot) — ce n'est PAS une relation
d'équivalence, et c'est correct : c'est le phénomène biologique des enzymes
de restriction, pas une identité. -/
/- NOTE : pas de transitivité affirmée — la mutation compose des rotations sur
des fenêtres potentiellement différentes, qui n'est pas une rotation one-shot. -/

/-- Fenêtre vide : la mutation y est l'identité, pour toute liste. -/
theorem mutateWindow_zero_window (cs : List PDCrossing) (ρ : KleinRot) :
    mutateWindow cs 0 0 ρ = cs := by
  cases cs with
  | nil => rfl
  | cons _ _ => rfl

theorem AreMutantDiagrams.refl (d : KnotDiagram) : AreMutantDiagrams d d :=
  ⟨0, 0, .id, mutateWindow_zero_window d.crossings .id⟩

theorem AreMutantDiagrams.symm {d₁ d₂ : KnotDiagram} (h : AreMutantDiagrams d₁ d₂) :
    AreMutantDiagrams d₂ d₁ := by
  obtain ⟨i, j, ρ, hmut⟩ := h
  refine ⟨i, j, ρ, ?_⟩
  rw [← hmut]
  exact mutateWindow_involutive d₁.crossings i j ρ

theorem AreMutants.refl (k : Knot) : AreMutants k k :=
  ⟨k.diagram, k.diagram, ReidemeisterEquiv.refl k.diagram,
    ReidemeisterEquiv.refl k.diagram, AreMutantDiagrams.refl k.diagram⟩

theorem AreMutants.symm {k₁ k₂ : Knot} (h : AreMutants k₁ k₂) : AreMutants k₂ k₁ := by
  obtain ⟨d₁, d₂, hd₁, hd₂, hmut⟩ := h
  exact ⟨d₂, d₁, hd₂, hd₁, AreMutantDiagrams.symm hmut⟩

/-! ### Contrôles : la définition discrimine

Une définition qui n'attraperait ni paire mutante ni contre-exemple serait un
`True` déguisé et le retrait du `sorry` serait cosmétique. Deux contrôles :

- NÉGATIF (`not_areMutantDiagrams_trefoil_unknot`) : la mutation préserve le
  nombre de croisements, donc le trèfle (3 croisements) et le nœud trivial
  (0) ne sont pas mutants — au niveau des diagrammes désignés.
- POSITIF (`areMutants_trefoil_mutant`) : une mutation non triviale (fenêtre
  pleine, rotation r12) est capturée par la définition.

NOTE (limite du témoin canonique) : les diagrammes désignés
`conwayKnotDiagram` et `kinoshitaTerasakaDiagram` (codes PD census corrigés,
cf. §2) partagent leurs cinq premiers croisements et diffèrent aux
croisements 6 à 11 — aucun envoi one-shot ne les superpose.
`AreMutants conwayKnot kinoshitaTerasakaKnot` exigera un diagramme
intermédiaire (isotopie de Reidemeister) — sous-grain ultérieur.
-/

/-- Contrôle négatif : trèfle et nœud trivial ne sont pas mutants (la
mutation préserve le nombre de croisements). -/
theorem not_areMutantDiagrams_trefoil_unknot :
    ¬ AreMutantDiagrams trefoilDiagram unknotDiagram := by
  intro ⟨i, j, ρ, hmut⟩
  have hlen := mutateWindow_length trefoilDiagram.crossings i j ρ
  simp only [unknotDiagram] at hmut
  rw [hmut] at hlen
  simp [trefoilDiagram] at hlen

/-- Le mutant du trèfle par r12 sur la fenêtre pleine. -/
def trefoilMutantDiagram : KnotDiagram where
  crossings := mutateWindow trefoilDiagram.crossings 0 3 KleinRot.r12
  numEdges := 6

def trefoilMutant : Knot where
  diagram := trefoilMutantDiagram

/-- Contrôle positif : la définition attrape une mutation non triviale
(fenêtre pleine, rotation non identique). -/
theorem areMutantDiagrams_trefoil_mutant :
    AreMutantDiagrams trefoilDiagram trefoilMutantDiagram :=
  ⟨0, 3, .r12, rfl⟩

theorem areMutants_trefoil_mutant : AreMutants trefoil trefoilMutant :=
  ⟨trefoilDiagram, trefoilMutantDiagram, ReidemeisterEquiv.refl _,
    ReidemeisterEquiv.refl _, areMutantDiagrams_trefoil_mutant⟩


end Knots
