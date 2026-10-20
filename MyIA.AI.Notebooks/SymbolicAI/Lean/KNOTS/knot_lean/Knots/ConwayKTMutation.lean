/-
  Knots.ConwayKTMutation — Mutants combinatoires de Conway et frontière one-shot
  =============================================================================

  Tranche 1 de la case « construction de Conway et Kinoshita-Terasaka par
  mutation » de l'EPIC #2874. Le chantier complet — prouver
  `AreMutants conwayKnot kinoshitaTerasakaKnot` — exige un diagramme
  intermédiaire (NOTE de `Knots.Mutation`, §Contrôles) ; le présent module
  consolide le socle mesurable de ce chantier :

  1. Les trois mutants combinatoires du nœud de Conway sur la fenêtre 5-11
     (croisements 6 à 11, la partie divergente du code PD entre 11n34 et
     11n42), avec `wf` prouvé et `AreMutantDiagrams` par construction.
  2. Des lemmes de normalisation des fenêtres (`mutateWindow_empty_window`,
     `mutateWindow_take`, `mutateWindow_ge_length_right`), réutilisables pour
     toute preuve négative `¬ AreMutantDiagrams` future.
  3. Le théorème d'impossibilité one-shot
     `not_areMutantDiagrams_conway_kt` : AUCUNE fenêtre et AUCUNE rotation de
     Klein n'envoie le code PD désigné de Conway sur celui de
     Kinoshita-Terasaka — la NOTE informelle de `Knots.Mutation` devient une
     preuve par énumération exhaustive vérifiée par le noyau.

  Limite assumée du modèle (héritée de `Knots.Mutation`) : la « fenêtre » est
  combinatoire (une plage d'indices de la liste de croisements), pas une
  sphère de Conway géométrique — la définition géométrique reste un TODO du
  lake (`ConwaySphere`). Les mutants ci-dessous sont les mutants du modèle
  combinatoire, à examiner comme tels.
-/

import Knots.Basic
import Knots.Mutation
import Knots.ConwayPD

namespace Knots

/-! ## 1. Normalisation des fenêtres

Trois faits structurels de `mutateWindow`, utilisés par l'impossibilité
one-shot du §3. Ils bornent l'espace des fenêtres utiles : une fenêtre vide
(`j ≤ i`) est l'identité, les positions avant `i` sont inchangées, et une
borne droite au-delà de la liste se clampe à sa longueur. -/

/-- Fenêtre vide (`j ≤ i`) : la mutation est l'identité. Le cas
`c :: cs', _+1, 0` du match rend la queue intacte, et chaque pas récursif
préserve la vacuité relative de la fenêtre. -/
theorem mutateWindow_empty_window (cs : List PDCrossing) (i j : Nat)
    (ρ : KleinRot) (hij : j ≤ i) : mutateWindow cs i j ρ = cs := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' => omega
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' => simp [mutateWindow, ih i' j' (by omega)]

/-- Les positions strictement avant la fenêtre sont inchangées (pour une
fenêtre non vide `i ≤ j`). -/
theorem mutateWindow_take (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot)
    (hij : i ≤ j) : (mutateWindow cs i j ρ).take i = cs.take i := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' => simp [mutateWindow, ih i' j' (by omega)]

/-- Borne droite au-delà de la liste : muter avec `j ≥ length cs` revient à
muter jusqu'au bout de la liste. -/
theorem mutateWindow_ge_length_right (cs : List PDCrossing) (i j : Nat)
    (ρ : KleinRot) (hj : cs.length ≤ j) :
    mutateWindow cs i j ρ = mutateWindow cs i cs.length ρ := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    simp only [List.length_cons] at hj ⊢
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' => simp [mutateWindow, ih 0 j' (by omega)]
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' => simp [mutateWindow, ih i' j' (by omega)]

/-! ## 2. Les mutants combinatoires du nœud de Conway

Les croisements 6 à 11 (indices 5 à 10) sont la partie du code PD où 11n34
et 11n42 divergent — les cinq premiers croisements sont communs. La fenêtre
5-11 est donc la fenêtre de mutation naturelle du modèle. Les trois rotations
non triviales du groupe de Klein donnent les trois mutants combinatoires. -/

/-- Le mutant de Conway par `r12` sur la fenêtre 5-11 (croisements 6 à 11). -/
def conwayMutantR12Diagram : KnotDiagram where
  crossings := mutateWindow conwayKnotDiagram.crossings 5 11 KleinRot.r12
  numEdges := 22

/-- Le mutant de Conway par `r13` sur la fenêtre 5-11. -/
def conwayMutantR13Diagram : KnotDiagram where
  crossings := mutateWindow conwayKnotDiagram.crossings 5 11 KleinRot.r13
  numEdges := 22

/-- Le mutant de Conway par `r14` sur la fenêtre 5-11. -/
def conwayMutantR14Diagram : KnotDiagram where
  crossings := mutateWindow conwayKnotDiagram.crossings 5 11 KleinRot.r14
  numEdges := 22

/-- `wf` du mutant r12 : `KleinRot.apply` permute les étiquettes dans chaque
croisement, le multi-ensemble global des 22 arêtes est inchangé — la parité
`wf` passe (contrôle par le noyau, style `conway_wf`). -/
theorem conwayMutantR12_wf : conwayMutantR12Diagram.wf = true := by decide

/-- `wf` du mutant r13. -/
theorem conwayMutantR13_wf : conwayMutantR13Diagram.wf = true := by decide

/-- `wf` du mutant r14. -/
theorem conwayMutantR14_wf : conwayMutantR14Diagram.wf = true := by decide

/-- Chaque mutant est mutant de Conway par construction (fenêtre 5-11,
rotation désignée) — le témoin `rfl` est la définition même. -/
theorem areMutantDiagrams_conway_conwayMutantR12 :
    AreMutantDiagrams conwayKnotDiagram conwayMutantR12Diagram :=
  ⟨5, 11, .r12, rfl⟩

theorem areMutantDiagrams_conway_conwayMutantR13 :
    AreMutantDiagrams conwayKnotDiagram conwayMutantR13Diagram :=
  ⟨5, 11, .r13, rfl⟩

theorem areMutantDiagrams_conway_conwayMutantR14 :
    AreMutantDiagrams conwayKnotDiagram conwayMutantR14Diagram :=
  ⟨5, 11, .r14, rfl⟩

/-- Les trois mutants comme nœuds (diagramme désigné = le mutant). -/
def conwayMutantR12 : Knot where diagram := conwayMutantR12Diagram
def conwayMutantR13 : Knot where diagram := conwayMutantR13Diagram
def conwayMutantR14 : Knot where diagram := conwayMutantR14Diagram

/-- Relation de mutation au niveau des nœuds, témoins désignés. -/
theorem areMutants_conway_conwayMutantR12 :
    AreMutants conwayKnot conwayMutantR12 :=
  ⟨conwayKnotDiagram, conwayMutantR12Diagram, ReidemeisterEquiv.refl _,
    ReidemeisterEquiv.refl _, areMutantDiagrams_conway_conwayMutantR12⟩

theorem areMutants_conway_conwayMutantR13 :
    AreMutants conwayKnot conwayMutantR13 :=
  ⟨conwayKnotDiagram, conwayMutantR13Diagram, ReidemeisterEquiv.refl _,
    ReidemeisterEquiv.refl _, areMutantDiagrams_conway_conwayMutantR13⟩

theorem areMutants_conway_conwayMutantR14 :
    AreMutants conwayKnot conwayMutantR14 :=
  ⟨conwayKnotDiagram, conwayMutantR14Diagram, ReidemeisterEquiv.refl _,
    ReidemeisterEquiv.refl _, areMutantDiagrams_conway_conwayMutantR14⟩

/-! ## 3. Impossibilité one-shot : les codes désignés ne sont pas mutants

La NOTE de `Knots.Mutation` (§Contrôles) constate qu'aucun envoi one-shot ne
superpose les codes PD désignés de 11n34 et 11n42. Le théorème ci-dessous le
prouve : pour TOUTE fenêtre et TOUTE rotation de Klein,
`mutateWindow conwayKnotDiagram.crossings i j ρ ≠ kinoshitaTerasakaDiagram.crossings`.

La preuve borne l'espace par les lemmes du §1 (fenêtre vide = identité ;
positions avant `i` inchangées ; borne droite clampée), puis énumère les cas
restants — chaque branche est close par le noyau (`decide` sur des listes
littérales). La borne `i ≤ 5` vient du croisement 6 : les codes divergent dès
l'index 5 (`⟨16, 9, 15, 8⟩` contre `⟨17, 9, 18, 8⟩`), toute fenêtre
commençant après laisse les six premières positions inchangées.

Conséquence pour le chantier : la jonction `AreMutants conwayKnot
kinoshitaTerasakaKnot` passe nécessairement par un diagramme intermédiaire
dans la classe de Reidemeister de l'un des deux — c'est le sous-grain
ultérieur. -/

/-- Les codes PD désignés de Conway et Kinoshita-Terasaka diffèrent (contrôle
par le noyau). -/
theorem conway_designated_ne_kt :
    conwayKnotDiagram.crossings ≠ kinoshitaTerasakaDiagram.crossings := by
  decide

/-- Ils diffèrent déjà sur les six premiers croisements. -/
theorem conway_designated_take6_ne_kt :
    conwayKnotDiagram.crossings.take 6 ≠
      kinoshitaTerasakaDiagram.crossings.take 6 := by
  decide

/-- **Impossibilité one-shot** : aucune fenêtre ni rotation de Klein n'envoie
le code PD désigné du nœud de Conway sur celui de Kinoshita-Terasaka. -/
theorem not_areMutantDiagrams_conway_kt :
    ¬ AreMutantDiagrams conwayKnotDiagram kinoshitaTerasakaDiagram := by
  rintro ⟨i, j, ρ, h⟩
  by_cases hij : j ≤ i
  · rw [mutateWindow_empty_window _ i j ρ hij] at h
    exact conway_designated_ne_kt h
  · by_cases hi6 : 6 ≤ i
    · have h6 := congrArg (List.take 6) h
      have htake := mutateWindow_take conwayKnotDiagram.crossings i j ρ
        (by omega)
      have hmin : min 6 i = 6 := Nat.min_eq_left (by omega)
      have hstep : (mutateWindow conwayKnotDiagram.crossings i j ρ).take 6
          = ((mutateWindow conwayKnotDiagram.crossings i j ρ).take i).take 6 := by
        rw [List.take_take, hmin]
      rw [hstep, htake, List.take_take, hmin] at h6
      exact conway_designated_take6_ne_kt h6
    · have hlen : conwayKnotDiagram.crossings.length = 11 := by decide
      have hi5 : i ≤ 5 := by omega
      by_cases hj11 : 11 ≤ j
      · rw [mutateWindow_ge_length_right _ i j ρ (by rw [hlen]; omega)] at h
        interval_cases i <;> cases ρ <;> exact absurd h (by decide)
      · have hj10 : j ≤ 10 := by omega
        interval_cases i <;> interval_cases j <;> cases ρ <;>
          exact absurd h (by decide)

end Knots
