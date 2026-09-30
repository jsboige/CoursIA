/-
Pont modal Tweety <-> FFL ModalLogic (tranche C de l'EPIC #15066).

Consomme `ModalLogic` au pin exact du lakefile (pilote d'integration mesure) :
- `ModalLogicArchive.Modal.Kripke` (namespace `LO.Modal.Kripke`) : cadres de Kripke
  GENERIQUES, sans aucune contrainte de reflexivite/transitivite — le bon substrat
  pour discriminer K, T, K4, S5 ;
- `Fin74.Kripke` (definitions a la racine) : cadres reflexifs et transitifs
  (S4 par construction), semantique de forcing `x ⊩ A`.

Aucun module upstream n'est vendu ou adapte ici : ce fichier ne fait qu'importer,
definir nos propres temoins finis et les certifier par le kernel.

Plan de la tranche C :
1. `K` (distribution) est valide sur tout cadre — la normalite semantique ;
2. `T` (□p → p), `4` (□p → □□p) et `5` (◇p → □◇p) ECHOUENT chacun sur un cadre
   temoin qui viole exactement sa condition frame (irreflexif, non transitif,
   non euclidien) — contre-modeles certifies par le kernel ;
3. sur les cadres `Fin74` (reflexifs et transitifs par construction), les duaux
   diamant de `T` et `4` sont des theoremes — la structure du cadre les donne.

Choix d'ingenierie : les cadres temoins vivent sur `World := ℕ` et la relation
n'atteint que les mondes 0/1/2 — le contre-modele est le sous-cadre fini
{0,1} ou {0,1,2}, les autres mondes sont isoles (aucun arc). Frames et modeles
sont des `abbrev` (definitions reducibles) : l'elaboration des numeraux
`(0 : model.World)` traverse alors la projection `Model.World` jusqu'a `Nat.OfNat`,
ce qu'un `def` (semi-reductible) refuse. Les eonces portent `Satisfies model x φ`
(forme explicite) : la notation `x ⊧ φ` est polymorphe et ne resout pas le modele
depuis le seul type de `x`. Les deux packages declarent des types distincts
(`LO.Modal.Formula` vs `Formula` racine) : chaque section qualifie explicitement.
-/

import ModalLogicArchive.Modal.Kripke.Basic
import Fin74.Kripke.Basic

namespace FormalLogic.ModalBridge

/-! ## Cadres generiques (`LO.Modal.Kripke`) : ce qui ECHOUE

Un cadre de l'Archive est `<World, Rel>` sans aucune contrainte : on peut y elire
un monde irreflexif, une chaine non transitive, un eventail non euclidien. -/

section GenericFrames

variable {M : LO.Modal.Kripke.Model} {x : M.World} {φ ψ : LO.Modal.Formula ℕ}

/-- `K` (axiome de distribution) : valide sur tout cadre, sans hypothese de structure.
C'est la part de la logique modale que la semantique de Kripke donne gratuitement. -/
theorem forces_kdist (hpq : x ⊧ □(φ 🡒 ψ)) (hp : x ⊧ □φ) : x ⊧ □ψ := by
  intro y hxy
  exact hpq y hxy (hp y hxy)

/-- Cadre temoin de l'echec de `T` : relation `0 ≺ 1` uniquement (mondes sur ℕ,
les autres isoles). Le monde 0 est irreflexif : `□p` y est vrai (l'unique
successeur 1 verify p) mais `p` y est faux. -/
abbrev frameT : LO.Modal.Kripke.Frame := ⟨ℕ, fun a b => a = 0 ∧ b = 1⟩

abbrev modelT : LO.Modal.Kripke.Model := ⟨frameT, fun a w => a = 0 ∧ w = 1⟩

theorem T_invalid :
    ¬ (LO.Modal.Formula.Kripke.Satisfies modelT (0 : modelT.World) ((□(.atom 0)) 🡒 (.atom 0))) := by
  intro h
  have hp : LO.Modal.Formula.Kripke.Satisfies modelT (0 : modelT.World) (□(.atom 0)) :=
    fun _ hy => hy
  exact absurd (h hp).2 (by decide)

/-- Cadre temoin de l'echec de `4` : chaine `0 ≺ 1 ≺ 2` sans arc `0 ≺ 2`.
Au monde 0, l'unique successeur 1 verify p donc `□p` ; mais 1 a pour successeur 2
ou p echoue, donc `¬□p` en 1, donc `¬□□p` en 0. -/
abbrev frame4 : LO.Modal.Kripke.Frame := ⟨ℕ, fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)⟩

abbrev model4 : LO.Modal.Kripke.Model := ⟨frame4, fun a w => a = 0 ∧ w = 1⟩

theorem four_invalid :
    ¬ (LO.Modal.Formula.Kripke.Satisfies model4 (0 : model4.World) ((□(.atom 0)) 🡒 (□□(.atom 0)))) := by
  intro h
  have hp : LO.Modal.Formula.Kripke.Satisfies model4 (0 : model4.World) (□(.atom 0)) := by
    intro y hy
    rcases hy with ⟨_, hy1⟩ | ⟨h01, _⟩
    · exact ⟨rfl, hy1⟩
    · exact absurd h01 (by decide)
  have hbad : LO.Modal.Formula.Kripke.Satisfies model4 (1 : model4.World) (□(.atom 0)) → False := by
    intro h2
    exact absurd (h2 (2 : model4.World) (Or.inr ⟨rfl, rfl⟩)).2 (by decide)
  exact hbad (h hp (1 : model4.World) (Or.inl ⟨rfl, rfl⟩))

/-- Cadre temoin de l'echec de `5` : eventail `0 ≺ 1`, `0 ≺ 2` (non euclidien).
Au monde 0 : `◇p` via le successeur 1 ; mais le successeur 2 n'a aucun successeur,
donc `¬◇p` en 2, donc `¬□◇p` en 0. -/
abbrev frame5 : LO.Modal.Kripke.Frame := ⟨ℕ, fun a b => a = 0 ∧ (b = 1 ∨ b = 2)⟩

abbrev model5 : LO.Modal.Kripke.Model := ⟨frame5, fun a w => a = 0 ∧ w = 1⟩

theorem five_invalid :
    ¬ (LO.Modal.Formula.Kripke.Satisfies model5 (0 : model5.World) ((◇(.atom 0)) 🡒 (□◇(.atom 0)))) := by
  intro h
  -- `◇` n'est PAS definitionnellement un `∃` dans l'Archive : `Satisfies M x (◇φ)` se
  -- reduit en `∼□∼φ`, une fleche. Toute destruction de `◇` passe par `dia_def`.
  have hdia : LO.Modal.Formula.Kripke.Satisfies model5 (0 : model5.World) (◇(.atom 0)) :=
    LO.Modal.Formula.Kripke.Satisfies.dia_def.mpr
      ⟨(1 : model5.World), ⟨rfl, Or.inl rfl⟩, ⟨rfl, rfl⟩⟩
  have hbad : LO.Modal.Formula.Kripke.Satisfies model5 (2 : model5.World) (◇(.atom 0)) → False := by
    intro h2
    obtain ⟨y, hy, _⟩ := LO.Modal.Formula.Kripke.Satisfies.dia_def.mp h2
    exact absurd hy.1 (by decide)
  exact hbad (h hdia (2 : model5.World) ⟨rfl, Or.inr rfl⟩)

end GenericFrames

/-! ## Cadres S4 (`Fin74.Kripke`, definitions racine) : ce que la structure DONNE

Un cadre `Frame` de Fin74 porte `rel_refl` et `rel_trans` comme champs de donnees :
reflexivite et transitivite ne sont pas des hypotheses, elles sont le cadre.
Les duaux diamant de `T` (`A → ◇A`) et de `4` (`◇◇A → ◇A`) s'y derivent
en une ligne chacun. -/

section S4Frames

variable {κ : Type} {M : Model κ ℕ} {x : M.World} {A : Formula ℕ}

/-- Dual diamant de `T` : la reflexivite du cadre donne `A → ◇A`. -/
theorem forces_dia_of_refl (hA : x ⊩ A) : x ⊩ ◇A :=
  ⟨x, M.rel_refl x, hA⟩

/-- Dual diamant de `4` : la transitivite du cadre donne `◇◇A → ◇A`. -/
theorem forces_dia_dia (h : x ⊩ ◇◇A) : x ⊩ ◇A := by
  obtain ⟨y, xy, ⟨z, yz, hz⟩⟩ := h
  exact ⟨z, M.rel_trans xy yz, hz⟩

end S4Frames

end FormalLogic.ModalBridge
