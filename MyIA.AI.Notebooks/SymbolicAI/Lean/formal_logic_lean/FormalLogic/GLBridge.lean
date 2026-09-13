import ProvabilityLogic.Logic.GL.Basic
import ProvabilityLogic.Logic.GL.Fixedpoint
import ProvabilityLogic.ProvabilityLogic.GL.Basic

/-!
# Pont vers la logique de prouvabilité GL

Ce module consomme directement la bibliothèque `ProvabilityLogic` à un commit
épinglé. Il expose dans CoursIA des témoins vérifiés par le noyau pour le schéma
de Löb, la décidabilité de GL et le théorème de point fixe de de Jongh–Sambin,
sans redéclarer ces résultats comme axiomes locaux.
-/

open FFL.FirstOrder.ProvabilityAbstraction

namespace FormalLogic.GLBridge

/-- Le schéma modal de Löb comme formule inductive, nommé explicitement pour ne
pas le confondre avec les connecteurs arithmétiques génériques de FFL. -/
def loebFormula (A : _root_.Formula ℕ) : _root_.Formula ℕ :=
  .imp (.box (.imp (.box A) A)) (.box A)

/-- La formule modale de cohérence `¬□⊥`. -/
def consistencyFormula : _root_.Formula ℕ :=
  .neg (.box .bot)

/-- Corps modal `□p → ⊥` utilisé pour spécialiser le théorème de point fixe. -/
def goedelBody : _root_.Formula ℕ :=
  .imp (.box (.atom 0)) .bot

/-- Le schéma modal de Löb est dérivable dans le calcul de Hilbert GL. -/
theorem loeb_schema {A : _root_.Formula ℕ} :
    ⊢ʰ[GL] loebFormula A :=
  LogicGL.ProvableHilbert.modalL

/-- Le membership de toute formule naturelle dans GL est une proposition décidable.
La réduction par `decide` de l'instance concrète ci-dessous dépasse toutefois la
réduction noyau ; ce module n'emploie donc pas `native_decide`. -/
def membership_decidable (A : _root_.Formula ℕ) : Decidable (A ∈ @LogicGL ℕ) :=
  inferInstance

/-- Une instance concrète du schéma de Löb appartient à GL, via sa dérivation de
Hilbert plutôt que par une réduction native non certifiée. -/
theorem loeb_bot_mem :
    loebFormula (.bot : _root_.Formula ℕ) ∈ @LogicGL ℕ :=
  LogicGL.iff_provableHilbert.mpr LogicGL.ProvableHilbert.modalL

/-- Modèle GL enraciné à un monde, relation d'accessibilité vide et valuation
constamment fausse. -/
abbrev onePointModel : RootedModel (Fin 1) ℕ where
  toModel := Model.pointModel fun _ => False
  root := ⟨0, fun x hx => absurd (Fin.fin_one_eq_zero x) hx⟩

/-- Le modèle à un point hérite de la transitivité, de l'irréflexivité et de la
finitude requises par les modèles GL finis. -/
instance : onePointModel.IsFiniteGL := inferInstance

/-- Contrôle négatif certifié : la formule de cohérence `¬□⊥` n'est pas un
théorème de GL. Le modèle fini explicite ci-dessus la falsifie à sa racine. -/
theorem consistency_not_mem :
    consistencyFormula ∉ @LogicGL ℕ :=
  LogicGL.not_mem_of_concrete_root_not_forces onePointModel (by
    intro h
    exact Model.World.forces_neg.mp h (by
      intro y hy
      exact False.elim hy))

/-- Spécialisation du théorème de point fixe de de Jongh–Sambin à la formule
`□p → ⊥`. Le témoin est construit en amont et son équivalence est prouvée dans
GL ; il n'est pas introduit comme axiome local. -/
theorem goedel_fixedpoint :
    ∃ D : _root_.Formula ℕ,
      D.atoms ⊆ goedelBody.atoms \ {0} ∧
      (_root_.Formula.iff
        (goedelBody.subst (_root_.Formula.Substitution.single 0 D)) D ∈
        @LogicGL ℕ) := by
  obtain ⟨D, hAtoms, hFixed, _⟩ := LogicGL.fixpointTheorem
    (A := goedelBody)
    (p := 0)
    (q := 1)
    (by decide)
    (by simp [goedelBody, _root_.Formula.ModalizedIn])
    (by decide)
  exact ⟨D, hAtoms, hFixed⟩

/-- Toute réalisation arithmétique du schéma concret de Löb est prouvable dans
la théorie de base d'un prédicat de prouvabilité satisfaisant les conditions de
Hilbert–Bernays–Löb. -/
theorem loeb_arithmetically_sound
    {L : FFL.FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
    {T U : FFL.FirstOrder.Theory L} [Diagonalization T] [T ⪯ U]
    {𝔅 : Provability T U} [𝔅.HBL]
    (f : Realization ℕ L) :
    T ⊢ (loebFormula (.bot : _root_.Formula ℕ)).interpret f 𝔅 :=
  LogicGL.arithmetical_soundness loeb_bot_mem

end FormalLogic.GLBridge
