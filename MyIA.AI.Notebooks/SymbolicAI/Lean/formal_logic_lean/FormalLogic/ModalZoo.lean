/-
Zoo modal certifié (tranche G de l'EPIC #15066).

Un « zoo » de logiques modales est une carte : quels systèmes sont plus forts que
quels autres. Ce module en extrait un sous-graphe borné, le sous-cube des huit
systèmes normaux qu'un cours rencontre d'abord (`K`, `KD`, `KT`, `KTB`, `K4`,
`S4`, `KD45`, `S5`), et certifie **toute** la relation d'ordre entre eux, pas
seulement les arêtes que l'on dessine.

Le résultat central est `weakerThan_iff_profile` : pour ces huit systèmes,
`L₁ ⪯ L₂` (tout théorème de `L₁` est théorème de `L₂`) équivaut à l'inclusion des
**profils**, c'est-à-dire des schémas `D`, `T`, `B`, `4`, `5` que chacun prouve. Les
deux sens ont une nature différente :

- le sens « profil inclus ⇒ plus faible » passe par les axiomes de Hilbert : un
  système est engendré par des schémas de son profil, qu'un système de profil plus
  grand prouve ;
- le sens « plus faible ⇒ profil inclus » exige de savoir qu'un schéma n'est **pas**
  prouvable. Chacune des 22 cases négatives du tableau des profils se ramène à
  l'un de huit contre-modèles de Kripke finis (au plus trois mondes). La
  correction de Kripke vient de `ModalLogic` ; les cinq correspondances qu'elle
  demande (sérialité ↦ `D`, réflexivité ↦ `T`, symétrie ↦ `B`, transitivité ↦ `4`,
  euclidianité ↦ `5`) sont prouvées ici.

L'ordre étant décidé par une inclusion de listes, le diagramme de Hasse (arêtes
de couverture) et les paires incomparables sont **calculés** par `decide`, puis
transportés en énoncés `⪱` et `¬ ⪯` sur les vrais systèmes de Hilbert. Une paire
absente du dessin est ainsi aussi certifiée qu'une arête présente : `KTB` et `S4`
sont incomparables, et le module le prouve.

Aucun module upstream n'est vendu ou adapté : on consomme `ModalLogic` au pin du
lakefile, et seulement trois couches : les systèmes de Hilbert `Modal.K`…
`Modal.S5`, les dérivations génériques (`Entailment.S4`, `Entailment.S5`) et la
correction de Kripke sur un cadre (`Kripke.Hilbert`). Les modules
`Kripke/Logic/*`, qui portent les classes de cadres et les complétudes, ne sont
pas importés : ils dépendent tous de `ModalLogicArchive.Modal.Tableau`, qui ne
compile pas au pin du fork sous Lean 4.33.1 (six erreurs, mesurées le 2026-09-23).
Ce module d'archive est hors des `defaultTargets` du fork (`Fin74`, `Neighborhood`),
donc hors de sa CI : ce n'est pas une régression du fork, c'est une couche qu'il ne
construit pas. Le tableau des profils, les correspondances et les contre-modèles
sont les nôtres.
-/

import ModalLogicArchive.Modal.Kripke.Hilbert
import ModalLogicArchive.Modal.Entailment.S4
import ModalLogicArchive.Modal.Entailment.S5

namespace FormalLogic.ModalZoo

open LO LO.Entailment LO.Modal LO.Modal.Entailment LO.Modal.Kripke LO.Modal.Formula.Kripke

/-! ## Les cinq schémas et les huit systèmes -/

/-- Les cinq schémas qui séparent les systèmes du sous-cube, instanciés sur
l'atome `0` : `D` (□p → ◇p), `T` (□p → p), `B` (p → □◇p), `4` (□p → □□p),
`5` (◇p → □◇p). -/
inductive Ax
  | D | T | B | four | five
  deriving DecidableEq, Repr

namespace Ax

/-- Les cinq schémas, dans l'ordre d'affichage. -/
def all : List Ax := [D, T, B, four, five]

/-- La formule de `ModalLogic` correspondant au schéma. -/
abbrev formula : Ax → Formula ℕ
  | D => Axioms.D (.atom 0)
  | T => Axioms.T (.atom 0)
  | B => Axioms.B (.atom 0)
  | four => Axioms.Four (.atom 0)
  | five => Axioms.Five (.atom 0)

/-- Le nom usuel du schéma. -/
def name : Ax → String
  | D => "D" | T => "T" | B => "B" | four => "4" | five => "5"

end Ax

/-- Les huit systèmes du sous-cube. -/
inductive Sys
  | K | KD | KT | KTB | K4 | S4 | KD45 | S5
  deriving DecidableEq, Repr

namespace Sys

/-- Les huit systèmes, dans l'ordre d'affichage. -/
def all : List Sys := [K, KD, KT, KTB, K4, S4, KD45, S5]

theorem mem_all (s : Sys) : s ∈ all := by cases s <;> decide

/-- Les axiomes de Hilbert du système, tels que `ModalLogic` les déclare. -/
abbrev axioms : Sys → Axiom ℕ
  | K => Modal.K.axioms
  | KD => Modal.KD.axioms
  | KT => Modal.KT.axioms
  | KTB => Modal.KTB.axioms
  | K4 => Modal.K4.axioms
  | S4 => Modal.S4.axioms
  | KD45 => Modal.KD45.axioms
  | S5 => Modal.S5.axioms

/-- Le système de Hilbert normal engendré par ces axiomes : `Sys.KD.logic` est
définitionnellement `Modal.KD`. -/
abbrev logic (s : Sys) : Logic ℕ := Hilbert.Normal s.axioms

/-- Les schémas qui engendrent le système (en plus de l'axiome `K`). -/
def gens : Sys → List Ax
  | K => [] | KD => [.D] | KT => [.T] | KTB => [.T, .B] | K4 => [.four]
  | S4 => [.T, .four] | KD45 => [.D, .four, .five] | S5 => [.T, .five]

/-- Le **profil** : les schémas parmi `D`, `T`, `B`, `4`, `5` que le système
prouve. Le profil contient les générateurs, mais pas seulement : `KT` prouve `D`,
et `S5` prouve `B` et `4` sans les avoir pour axiomes. Que ce tableau soit exact,
cases positives et négatives, est le théorème `provable_iff_mem_profile`. -/
def profile : Sys → List Ax
  | K => [] | KD => [.D] | KT => [.D, .T] | KTB => [.D, .T, .B] | K4 => [.four]
  | S4 => [.D, .T, .four] | KD45 => [.D, .four, .five] | S5 => [.D, .T, .B, .four, .five]

/-- Le nom usuel du système. -/
def name : Sys → String
  | K => "K" | KD => "KD" | KT => "KT" | KTB => "KTB" | K4 => "K4"
  | S4 => "S4" | KD45 => "KD45" | S5 => "S5"

theorem gens_subset_profile (s : Sys) : ∀ a ∈ s.gens, a ∈ s.profile := by
  cases s <;> decide

/-- Tout axiome de Hilbert du système est l'axiome `K` ou un générateur. -/
theorem mem_axioms {s : Sys} {φ : Formula ℕ} (h : φ ∈ s.axioms) :
    φ = Axioms.K (.atom 0) (.atom 1) ∨ ∃ a ∈ s.gens, φ = a.formula := by
  cases s <;> simp [gens] at h ⊢ <;> tauto

end Sys

/-! ## Cases positives du tableau : ce que chaque système prouve

Les générateurs sont des axiomes. Les six autres cases positives sont dérivées :
`D` découle de `T` (`□p → p → ◇p`), et `KT` est inclus dans `KTB`, `S4` et `S5`
puisque ses axiomes en font partie ; `B` et `4` se dérivent dans `S5` à partir de
`T` et de `5`. -/

theorem KT_D : Modal.KT ⊢ Axioms.D (.atom 0) := axiomD!

theorem KT_weakerThan_KTB : Modal.KT ⪯ Modal.KTB :=
  Hilbert.Normal.weakerThan_of_subset_axioms (by grind)

theorem KT_weakerThan_S4 : Modal.KT ⪯ Modal.S4 :=
  Hilbert.Normal.weakerThan_of_subset_axioms (by grind)

theorem KT_weakerThan_S5 : Modal.KT ⪯ Modal.S5 :=
  Hilbert.Normal.weakerThan_of_subset_axioms (by grind)

theorem KTB_D : Modal.KTB ⊢ Axioms.D (.atom 0) := KT_weakerThan_KTB.wk KT_D

theorem S4_D : Modal.S4 ⊢ Axioms.D (.atom 0) := KT_weakerThan_S4.wk KT_D

theorem S5_D : Modal.S5 ⊢ Axioms.D (.atom 0) := KT_weakerThan_S5.wk KT_D

/-- `B` dans `S5` : `p → ◇p` (dual de `T`), puis `◇p → □◇p` (`5`). -/
theorem S5_B : Modal.S5 ⊢ Axioms.B (.atom 0) := ⟨C_trans diaTc axiomFive⟩

/-- `4` dans `S5` : `□p → ◇□p` (dual de `T`), `◇□p → □◇□p` (`5`), puis
`□◇□p → □□p`, par nécessitation de `◇□p → □p`, théorème de `S5`. -/
theorem S5_four : Modal.S5 ⊢ Axioms.Four (.atom 0) :=
  ⟨C_trans diaTc (C_trans axiomFive (implyBoxDistribute' diabox_box))⟩

/-- Chaque schéma du profil est prouvable (les 18 cases positives). -/
theorem provable_of_mem_profile {s : Sys} {a : Ax} (h : a ∈ s.profile) :
    s.logic ⊢ a.formula := by
  cases s <;> cases a <;> simp [Sys.profile] at h
  case KD.D => exact (axiomD! : Modal.KD ⊢ _)
  case KT.D => exact KT_D
  case KT.T => exact (axiomT! : Modal.KT ⊢ _)
  case KTB.D => exact KTB_D
  case KTB.T => exact (axiomT! : Modal.KTB ⊢ _)
  case KTB.B => exact (axiomB! : Modal.KTB ⊢ _)
  case K4.four => exact (axiomFour! : Modal.K4 ⊢ _)
  case S4.D => exact S4_D
  case S4.T => exact (axiomT! : Modal.S4 ⊢ _)
  case S4.four => exact (axiomFour! : Modal.S4 ⊢ _)
  case KD45.D => exact (axiomD! : Modal.KD45 ⊢ _)
  case KD45.four => exact (axiomFour! : Modal.KD45 ⊢ _)
  case KD45.five => exact (axiomFive! : Modal.KD45 ⊢ _)
  case S5.D => exact S5_D
  case S5.T => exact (axiomT! : Modal.S5 ⊢ _)
  case S5.B => exact S5_B
  case S5.four => exact S5_four
  case S5.five => exact (axiomFive! : Modal.S5 ⊢ _)

/-- Le sens « profil inclus ⇒ plus faible », par les axiomes de Hilbert : les
axiomes de `s` sont `K` et des schémas de son profil, donc de celui de `t`. -/
theorem weakerThan_of_profile_subset {s t : Sys}
    (h : ∀ a ∈ s.profile, a ∈ t.profile) : s.logic ⪯ t.logic := by
  apply Hilbert.Normal.weakerThan_of_provable_axioms
  intro φ hφ
  rcases Sys.mem_axioms hφ with rfl | ⟨a, ha, rfl⟩
  · cases t <;> exact axiomK!
  · exact provable_of_mem_profile (h a (s.gens_subset_profile a ha))

/-! ## Correspondances : une propriété du cadre valide un schéma

La correction de Kripke (`Kripke.soundness_of_frame_validates_axioms`) dit qu'un
cadre qui valide les axiomes d'un système valide tous ses théorèmes. Il reste à
savoir quels cadres valident quels schémas : ce sont les cinq correspondances
classiques, dans le sens « propriété ⇒ validité », prouvées ici. -/

section Correspondence

variable {F : Kripke.Frame}

/-- Un cadre sériel (tout monde a un successeur) valide `D`. -/
theorem valid_D (h : ∀ x : F.World, ∃ y, F.Rel x y) : F ⊧ Axioms.D (.atom 0) := by
  intro V x
  apply Satisfies.imp_def.mpr
  intro hbox
  obtain ⟨y, hy⟩ := h x
  exact Satisfies.dia_def.mpr ⟨y, hy, Satisfies.box_def.mp hbox y hy⟩

/-- Un cadre réflexif valide `T`. -/
theorem valid_T (h : ∀ x : F.World, F.Rel x x) : F ⊧ Axioms.T (.atom 0) := by
  intro V x
  apply Satisfies.imp_def.mpr
  intro hbox
  exact Satisfies.box_def.mp hbox x (h x)

/-- Un cadre symétrique valide `B`. -/
theorem valid_B (h : ∀ x y : F.World, F.Rel x y → F.Rel y x) :
    F ⊧ Axioms.B (.atom 0) := by
  intro V x
  apply Satisfies.imp_def.mpr
  intro hp
  exact Satisfies.box_def.mpr fun y hy => Satisfies.dia_def.mpr ⟨x, h x y hy, hp⟩

/-- Un cadre transitif valide `4`. -/
theorem valid_four (h : ∀ x y z : F.World, F.Rel x y → F.Rel y z → F.Rel x z) :
    F ⊧ Axioms.Four (.atom 0) := by
  intro V x
  apply Satisfies.imp_def.mpr
  intro hbox
  exact Satisfies.box_def.mpr fun y hy => Satisfies.box_def.mpr fun z hz =>
    Satisfies.box_def.mp hbox z (h x y z hy hz)

/-- Un cadre euclidien (deux successeurs d'un même monde se voient) valide `5`. -/
theorem valid_five (h : ∀ x y z : F.World, F.Rel x y → F.Rel x z → F.Rel z y) :
    F ⊧ Axioms.Five (.atom 0) := by
  intro V x
  apply Satisfies.imp_def.mpr
  intro hdia
  obtain ⟨y, hy, hp⟩ := Satisfies.dia_def.mp hdia
  exact Satisfies.box_def.mpr fun z hz => Satisfies.dia_def.mpr ⟨y, h x y z hy hz, hp⟩

/-- Un cadre qui valide les générateurs d'un système valide tous ses axiomes
(l'axiome `K` étant valide sur tout cadre). -/
theorem validates_axioms {s : Sys} (h : ∀ a ∈ s.gens, F ⊧ a.formula) :
    F ⊧* s.axioms := by
  constructor
  intro φ hφ
  rcases Sys.mem_axioms hφ with rfl | ⟨a, ha, rfl⟩
  · exact ValidOnFrame.axiomK
  · exact h a ha

/-- **Contre-modèle.** Si un cadre valide les générateurs de `s` et qu'un de ses
mondes falsifie `φ` sous une valuation, alors `s` ne prouve pas `φ`. -/
theorem unprovable_of_countermodel {s : Sys} {φ : Formula ℕ} (F : Kripke.Frame)
    (hF : ∀ a ∈ s.gens, F ⊧ a.formula) (V : Kripke.Valuation F) (x : F.World)
    (hx : ¬ Satisfies ⟨F, V⟩ x φ) : s.logic ⊬ φ := by
  intro h
  exact hx (Kripke.soundness_of_frame_validates_axioms (validates_axioms hF) h V x)

end Correspondence

/-! ## Huit contre-modèles : ce que chaque système ne prouve pas

Quatre cadres finis suffisent, chacun avec une ou deux valuations :

| cadre | mondes | relation | propriétés | ce qu'il réfute |
|---|---|---|---|---|
| vide | 1 | aucune flèche | transitif, non sériel | `D`, `T` dans `K4` |
| étoile | 3 | 0 voit tout ; 1 voit 0, 1 ; 2 voit 0, 2 | réflexif, symétrique, non transitif | `4`, `5` dans `KTB` |
| puits | 2 | tout monde voit 1 | sériel, transitif, euclidien, non réflexif | `T`, `B` dans `KD45` |
| chaîne | 2 | `x ≤ y` | réflexif, transitif, non symétrique | `B`, `5` dans `S4` |
-/

/-- Cadre vide : un monde sans successeur. -/
abbrev emptyFrame : Kripke.Frame := ⟨Fin 1, fun _ _ => False⟩

/-- Étoile : 0 voit tout, 1 voit 0 et 1, 2 voit 0 et 2. -/
abbrev starFrame : Kripke.Frame :=
  ⟨Fin 3, fun x y => x = 0 ∨ (x = 1 ∧ y ≠ 2) ∨ (x = 2 ∧ y ≠ 1)⟩

/-- Puits : tout monde voit le monde 1, et lui seul. -/
abbrev sinkFrame : Kripke.Frame := ⟨Fin 2, fun _ y => y = 1⟩

/-- Chaîne : `0 ≤ 1`, préordre non symétrique. -/
abbrev chainFrame : Kripke.Frame := ⟨Fin 2, fun x y => x ≤ y⟩

theorem emptyFrame_gens_K4 : ∀ a ∈ Sys.K4.gens, emptyFrame ⊧ a.formula := by
  intro a ha
  simp only [Sys.gens, List.mem_singleton] at ha
  subst ha
  exact valid_four fun _ _ _ h _ => h

theorem starFrame_gens_KTB : ∀ a ∈ Sys.KTB.gens, starFrame ⊧ a.formula := by
  intro a ha
  simp only [Sys.gens, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact valid_T (by decide)
  · exact valid_B (by decide)

theorem sinkFrame_gens_KD45 : ∀ a ∈ Sys.KD45.gens, sinkFrame ⊧ a.formula := by
  intro a ha
  simp only [Sys.gens, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact valid_D fun _ => ⟨1, rfl⟩
  · exact valid_four fun _ _ _ _ h => h
  · exact valid_five fun _ _ _ h _ => h

theorem chainFrame_gens_S4 : ∀ a ∈ Sys.S4.gens, chainFrame ⊧ a.formula := by
  intro a ha
  simp only [Sys.gens, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact valid_T (by decide)
  · exact valid_four (by decide)

/-- Cadre vide : `□p` est vrai sans successeur, `◇p` est faux. -/
theorem K4_not_D : Modal.K4 ⊬ Axioms.D (.atom 0) := by
  refine unprovable_of_countermodel (s := .K4) emptyFrame emptyFrame_gens_K4
    (fun _ _ => False) 0 fun h => ?_
  obtain ⟨_, hy, _⟩ := Satisfies.dia_def.mp
    (Satisfies.imp_def.mp h (Satisfies.box_def.mpr fun _ hy => hy.elim))
  exact hy

/-- Cadre vide : `□p` est vrai sans successeur, `p` est faux. -/
theorem K4_not_T : Modal.K4 ⊬ Axioms.T (.atom 0) := by
  refine unprovable_of_countermodel (s := .K4) emptyFrame emptyFrame_gens_K4
    (fun _ _ => False) 0 fun h => ?_
  exact Satisfies.atom_def.mp
    (Satisfies.imp_def.mp h (Satisfies.box_def.mpr fun _ hy => hy.elim))

/-- Étoile : `p` vrai en 0 et 1. En 1, `□p` tient (1 voit 0 et 1), mais 0 voit 2
où `p` est faux, donc `□□p` échoue en 1. -/
theorem KTB_not_four : Modal.KTB ⊬ Axioms.Four (.atom 0) := by
  refine unprovable_of_countermodel (s := .KTB) starFrame starFrame_gens_KTB
    (fun _ w => w ≠ 2) 1 fun h => ?_
  have key : ∀ y : Fin 3,
      ((1 : Fin 3) = 0 ∨ ((1 : Fin 3) = 1 ∧ y ≠ 2) ∨ ((1 : Fin 3) = 2 ∧ y ≠ 1)) → y ≠ 2 := by
    decide
  have hbox := Satisfies.imp_def.mp h
    (Satisfies.box_def.mpr fun y hy => Satisfies.atom_def.mpr (key y hy))
  have h0 := Satisfies.box_def.mp hbox 0 (by decide)
  exact Satisfies.atom_def.mp (Satisfies.box_def.mp h0 2 (by decide)) rfl

/-- Étoile : `p` vrai en 1 seulement. `◇p` tient en 0 (0 voit 1), mais 0 voit 2,
qui ne voit aucun monde où `p` est vrai. -/
theorem KTB_not_five : Modal.KTB ⊬ Axioms.Five (.atom 0) := by
  refine unprovable_of_countermodel (s := .KTB) starFrame starFrame_gens_KTB
    (fun _ w => w = 1) 0 fun h => ?_
  have hdia : Satisfies (⟨starFrame, fun _ w => w = 1⟩ : Kripke.Model) 0 (◇(.atom 0)) :=
    Satisfies.dia_def.mpr ⟨1, by decide, Satisfies.atom_def.mpr rfl⟩
  have h2 := Satisfies.box_def.mp (Satisfies.imp_def.mp h hdia) 2 (by decide)
  obtain ⟨y, hy, hp⟩ := Satisfies.dia_def.mp h2
  have hy1 : y = 1 := Satisfies.atom_def.mp hp
  subst hy1
  exact absurd hy (by decide)

/-- Puits : `p` vrai en 1 seulement. En 0, `□p` tient (0 ne voit que 1) mais `p`
est faux. -/
theorem KD45_not_T : Modal.KD45 ⊬ Axioms.T (.atom 0) := by
  refine unprovable_of_countermodel (s := .KD45) sinkFrame sinkFrame_gens_KD45
    (fun _ w => w = 1) 0 fun h => ?_
  have hp := Satisfies.imp_def.mp h
    (Satisfies.box_def.mpr fun _ hy => Satisfies.atom_def.mpr hy)
  exact absurd (Satisfies.atom_def.mp hp) (by decide)

/-- Puits : `p` vrai en 0 seulement. En 0, `p` tient, mais 0 ne voit que 1, qui
ne voit que lui-même, où `p` est faux. -/
theorem KD45_not_B : Modal.KD45 ⊬ Axioms.B (.atom 0) := by
  refine unprovable_of_countermodel (s := .KD45) sinkFrame sinkFrame_gens_KD45
    (fun _ w => w = 0) 0 fun h => ?_
  have h1 := Satisfies.box_def.mp
    (Satisfies.imp_def.mp h (Satisfies.atom_def.mpr rfl)) 1 rfl
  obtain ⟨y, hy, hp⟩ := Satisfies.dia_def.mp h1
  have hy0 : y = 0 := Satisfies.atom_def.mp hp
  subst hy0
  exact absurd hy (by decide)

/-- Chaîne `0 ≤ 1` : `p` vrai en 0 seulement. En 0, `p` tient, mais 0 voit 1, qui
ne voit que lui-même, où `p` est faux. -/
theorem S4_not_B : Modal.S4 ⊬ Axioms.B (.atom 0) := by
  refine unprovable_of_countermodel (s := .S4) chainFrame chainFrame_gens_S4
    (fun _ w => w = 0) 0 fun h => ?_
  have h1 := Satisfies.box_def.mp
    (Satisfies.imp_def.mp h (Satisfies.atom_def.mpr rfl)) 1 (by decide)
  obtain ⟨y, hy, hp⟩ := Satisfies.dia_def.mp h1
  have hy0 : y = 0 := Satisfies.atom_def.mp hp
  subst hy0
  exact absurd hy (by decide)

/-- Chaîne `0 ≤ 1` : `p` vrai en 0 seulement. `◇p` tient en 0 (0 se voit), mais
`◇p` échoue en 1. -/
theorem S4_not_five : Modal.S4 ⊬ Axioms.Five (.atom 0) := by
  refine unprovable_of_countermodel (s := .S4) chainFrame chainFrame_gens_S4
    (fun _ w => w = 0) 0 fun h => ?_
  have hdia : Satisfies (⟨chainFrame, fun _ w => w = 0⟩ : Kripke.Model) 0 (◇(.atom 0)) :=
    Satisfies.dia_def.mpr ⟨0, by decide, Satisfies.atom_def.mpr rfl⟩
  have h1 := Satisfies.box_def.mp (Satisfies.imp_def.mp h hdia) 1 (by decide)
  obtain ⟨y, hy, hp⟩ := Satisfies.dia_def.mp h1
  have hy0 : y = 0 := Satisfies.atom_def.mp hp
  subst hy0
  exact absurd hy (by decide)

/-! ## Cases négatives du tableau

Si `L₁ ⪯ L₂` et que `L₂` ne prouve pas `φ`, alors `L₁` non plus. Chaque case
négative descend ainsi, par une arête du cube, vers l'un des huit contre-modèles. -/

theorem unprovable_of_weakerThan {L₁ L₂ : Logic ℕ} {φ : Formula ℕ}
    (h : L₁ ⪯ L₂) (h₂ : L₂ ⊬ φ) : L₁ ⊬ φ :=
  fun h₁ => h₂ (h.wk h₁)

/-- Un pas le long d'une arête du cube, l'inclusion des profils étant vérifiée
par `decide`. -/
theorem down {s t : Sys} (h : ∀ a ∈ s.profile, a ∈ t.profile) {φ : Formula ℕ}
    (h₂ : t.logic ⊬ φ) : s.logic ⊬ φ :=
  unprovable_of_weakerThan (weakerThan_of_profile_subset h) h₂

theorem KT_not_B : Modal.KT ⊬ Axioms.B (.atom 0) :=
  down (s := .KT) (t := .S4) (by decide) S4_not_B
theorem KT_not_four : Modal.KT ⊬ Axioms.Four (.atom 0) :=
  down (s := .KT) (t := .KTB) (by decide) KTB_not_four
theorem KT_not_five : Modal.KT ⊬ Axioms.Five (.atom 0) :=
  down (s := .KT) (t := .KTB) (by decide) KTB_not_five
theorem K4_not_B : Modal.K4 ⊬ Axioms.B (.atom 0) :=
  down (s := .K4) (t := .S4) (by decide) S4_not_B
theorem K4_not_five : Modal.K4 ⊬ Axioms.Five (.atom 0) :=
  down (s := .K4) (t := .S4) (by decide) S4_not_five
theorem KD_not_T : Modal.KD ⊬ Axioms.T (.atom 0) :=
  down (s := .KD) (t := .KD45) (by decide) KD45_not_T
theorem KD_not_B : Modal.KD ⊬ Axioms.B (.atom 0) :=
  down (s := .KD) (t := .KT) (by decide) KT_not_B
theorem KD_not_four : Modal.KD ⊬ Axioms.Four (.atom 0) :=
  down (s := .KD) (t := .KT) (by decide) KT_not_four
theorem KD_not_five : Modal.KD ⊬ Axioms.Five (.atom 0) :=
  down (s := .KD) (t := .KT) (by decide) KT_not_five
theorem K_not_D : Modal.K ⊬ Axioms.D (.atom 0) :=
  down (s := .K) (t := .K4) (by decide) K4_not_D
theorem K_not_T : Modal.K ⊬ Axioms.T (.atom 0) :=
  down (s := .K) (t := .K4) (by decide) K4_not_T
theorem K_not_B : Modal.K ⊬ Axioms.B (.atom 0) :=
  down (s := .K) (t := .KD) (by decide) KD_not_B
theorem K_not_four : Modal.K ⊬ Axioms.Four (.atom 0) :=
  down (s := .K) (t := .KD) (by decide) KD_not_four
theorem K_not_five : Modal.K ⊬ Axioms.Five (.atom 0) :=
  down (s := .K) (t := .KD) (by decide) KD_not_five

/-- Les 22 cases négatives. -/
theorem unprovable_of_not_mem_profile {s : Sys} {a : Ax} (h : a ∉ s.profile) :
    s.logic ⊬ a.formula := by
  cases s <;> cases a <;> simp [Sys.profile] at h
  case K.D => exact K_not_D
  case K.T => exact K_not_T
  case K.B => exact K_not_B
  case K.four => exact K_not_four
  case K.five => exact K_not_five
  case KD.T => exact KD_not_T
  case KD.B => exact KD_not_B
  case KD.four => exact KD_not_four
  case KD.five => exact KD_not_five
  case KT.B => exact KT_not_B
  case KT.four => exact KT_not_four
  case KT.five => exact KT_not_five
  case KTB.four => exact KTB_not_four
  case KTB.five => exact KTB_not_five
  case K4.D => exact K4_not_D
  case K4.T => exact K4_not_T
  case K4.B => exact K4_not_B
  case K4.five => exact K4_not_five
  case S4.B => exact S4_not_B
  case S4.five => exact S4_not_five
  case KD45.T => exact KD45_not_T
  case KD45.B => exact KD45_not_B

/-- **Le tableau des profils est exact** : ses 40 cases, positives et négatives. -/
theorem provable_iff_mem_profile (s : Sys) (a : Ax) :
    s.logic ⊢ a.formula ↔ a ∈ s.profile := by
  constructor
  · intro h
    by_contra hn
    exact unprovable_of_not_mem_profile hn h
  · exact provable_of_mem_profile

/-! ## L'ordre du sous-cube est décidé par les profils -/

/-- La relation « plus faible ou égal », calculée sur les profils. -/
def le (s t : Sys) : Bool := s.profile.all (· ∈ t.profile)

theorem le_iff (s t : Sys) : le s t = true ↔ ∀ a ∈ s.profile, a ∈ t.profile := by
  simp [le]

/-- **Théorème central.** Pour les huit systèmes du sous-cube, `s ⪯ t` si et
seulement si le profil de `s` est inclus dans celui de `t`. -/
theorem weakerThan_iff_profile (s t : Sys) :
    s.logic ⪯ t.logic ↔ ∀ a ∈ s.profile, a ∈ t.profile := by
  constructor
  · intro h a ha
    exact (provable_iff_mem_profile t a).mp (h.wk ((provable_iff_mem_profile s a).mpr ha))
  · exact weakerThan_of_profile_subset

theorem weakerThan_iff_le (s t : Sys) : s.logic ⪯ t.logic ↔ le s t = true := by
  rw [weakerThan_iff_profile, le_iff]

/-! ## Le diagramme de Hasse, calculé puis certifié -/

/-- Les arêtes de couverture : `s` est strictement sous `t`, sans système du
sous-cube entre les deux. -/
def isCover (s t : Sys) : Bool :=
  le s t && !le t s && Sys.all.all (fun u => !(le s u && le u t) || u == s || u == t)

/-- Les onze arêtes du diagramme de Hasse, écrites à la main. -/
def covers : List (Sys × Sys) :=
  [(.K, .KD), (.K, .K4), (.KD, .KT), (.KD, .KD45), (.K4, .S4), (.K4, .KD45),
   (.KT, .KTB), (.KT, .S4), (.KTB, .S5), (.S4, .S5), (.KD45, .S5)]

/-- La liste écrite à la main est exactement la relation de couverture calculée. -/
theorem mem_covers_iff (s t : Sys) : (s, t) ∈ covers ↔ isCover s t = true := by
  cases s <;> cases t <;> decide

/-- Les sept paires incomparables, écrites à la main. -/
def incomparables : List (Sys × Sys) :=
  [(.KD, .K4), (.KT, .K4), (.KT, .KD45), (.KTB, .K4), (.KTB, .S4), (.KTB, .KD45),
   (.S4, .KD45)]

/-- Une paire non ordonnée est dans la liste si et seulement si ni `le s t` ni
`le t s`. -/
theorem incomparables_complete (s t : Sys) :
    ((s, t) ∈ incomparables ∨ (t, s) ∈ incomparables) ↔
      (le s t = false ∧ le t s = false) := by
  cases s <;> cases t <;> decide

/-- Chaque arête dessinée est une inclusion **stricte** entre systèmes de Hilbert. -/
theorem strict_of_mem_covers {s t : Sys} (h : (s, t) ∈ covers) : s.logic ⪱ t.logic := by
  have hc := (mem_covers_iff s t).mp h
  simp only [isCover, Bool.and_eq_true, Bool.not_eq_true'] at hc
  refine ⟨(weakerThan_iff_le s t).mpr hc.1.1, fun h' => ?_⟩
  have := (weakerThan_iff_le t s).mp h'
  simp_all

/-- Chaque paire de la liste est certifiée incomparable, dans les deux sens. -/
theorem incomparable_of_mem {s t : Sys} (h : (s, t) ∈ incomparables) :
    ¬ s.logic ⪯ t.logic ∧ ¬ t.logic ⪯ s.logic := by
  have := (incomparables_complete s t).mp (Or.inl h)
  rw [weakerThan_iff_le, weakerThan_iff_le]
  simp [this.1, this.2]

/-! ## Énoncés vitrines -/

theorem KD_lt_KD45 : Modal.KD ⪱ Modal.KD45 :=
  strict_of_mem_covers (s := .KD) (t := .KD45) (by decide)

theorem K4_lt_S4 : Modal.K4 ⪱ Modal.S4 :=
  strict_of_mem_covers (s := .K4) (t := .S4) (by decide)

/-- `T` et `4` sont indépendants : ni `KT` ni `K4` ne contient l'autre. -/
theorem KT_incomparable_K4 : ¬ Modal.KT ⪯ Modal.K4 ∧ ¬ Modal.K4 ⪯ Modal.KT :=
  incomparable_of_mem (s := .KT) (t := .K4) (by decide)

/-- La symétrie (`B`) et la transitivité (`4`) ne se déduisent pas l'une de
l'autre, même sur les cadres réflexifs. -/
theorem KTB_incomparable_S4 : ¬ Modal.KTB ⪯ Modal.S4 ∧ ¬ Modal.S4 ⪯ Modal.KTB :=
  incomparable_of_mem (s := .KTB) (t := .S4) (by decide)

/-- La logique usuelle de la croyance (`KD45`) et `S4`, souvent retenue pour la
connaissance, sont incomparables : `KD45` ne prouve pas `T` (une croyance peut
être fausse), et `S4` ne prouve pas `5` (introspection négative). -/
theorem S4_incomparable_KD45 : ¬ Modal.S4 ⪯ Modal.KD45 ∧ ¬ Modal.KD45 ⪯ Modal.S4 :=
  incomparable_of_mem (s := .S4) (t := .KD45) (by decide)

/-! ## Export des données certifiées

`toJson` sérialise les nœuds (nom, profil), les arêtes de couverture et les paires
incomparables. Ces trois listes sont celles que les théorèmes ci-dessus certifient :
un rendu qui lit ce JSON dessine une carte dont chaque trait, et chaque absence de
trait, a sa preuve. -/

private def jsonStr (s : String) : String := "\"" ++ s ++ "\""

private def jsonList (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

/-- Le sous-cube certifié, au format JSON. -/
def toJson : String :=
  let node (s : Sys) : String :=
    "{\"name\": " ++ jsonStr s.name ++ ", \"profile\": " ++
      jsonList (s.profile.map (jsonStr ∘ Ax.name)) ++ "}"
  let pair (p : Sys × Sys) : String := jsonList [jsonStr p.1.name, jsonStr p.2.name]
  "{\"axioms\": " ++ jsonList (Ax.all.map (jsonStr ∘ Ax.name)) ++
    ", \"nodes\": " ++ jsonList (Sys.all.map node) ++
    ", \"covers\": " ++ jsonList (covers.map pair) ++
    ", \"incomparables\": " ++ jsonList (incomparables.map pair) ++ "}"

end FormalLogic.ModalZoo
