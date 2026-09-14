import Foundation.Propositional.Formula.Basic
import Foundation.Propositional.Boolean.Basic
import Foundation.Propositional.Entailment.Cl

import Mathlib.Tactic.FinCases

/-!
# Pont execution ↔ certification (Tranche A, EPIC #15066)

Ce module est le versant Lean du notebook `Lean-3b-Formalized-Formal-Logic.ipynb` :
les formules definies ici sont **les memes** que celles executees par le raisonneur
Tweety dans le notebook (fragment fini a deux atomes, syntaxe commune serialisable).
Le notebook fabrique ses tables de verite par execution ; ici, chaque ligne de table
est un petit theoreme evalue par le noyau (semantique FFL Prop-valuee :
`Valuation α := α → Prop`), la validite est un theoreme, et le contre-modele est un
temoin exhibe.

Anchors metatheoriques cites (aucune redemonstration) :
- `Foundation.Propositional.Boolean.Tait.soundness` : `T ⊢ φ → T ⊨[Valuation α] φ` ;
- `Foundation.Propositional.Boolean.Tait.completeness!` : `T ⊨[Valuation α] φ → T ⊢ φ` ;
- `FFL.Entailment.peirce` (module `Foundation.Propositional.Entailment.Cl`) : le
  schéma de Peirce est derivable dans tout systeme classique (`HasAxiomPeirce`).

Verdict d'integration : CONSUMER_PINNE au commit `81810b9f` (pilote #15520).
-/

open FFL.Propositional
open FFL.Propositional.Formula

namespace FormalLogic.Bridge

/-- Fragment fini commun : deux atomes, `p := (0 : Fin 2)` et `q := (1 : Fin 2)`. -/
abbrev Atom := Fin 2

/-- La formule temoin 1 : le schema de Peirce `((p → q) → p) → p`.
Tautologie classique ; valide sur les quatre valuations, non prouvable
en logique intuitionniste — c'est le discriminant execute cote Tweety. -/
def φPeirce : Formula Atom :=
  ((Formula.atom 0 🡒 Formula.atom 1) 🡒 Formula.atom 0) 🡒 Formula.atom 0

/-- La formule temoin 2 : `p ∨ q`. Satisfiable mais non valide — le controle negatif
exige par la Tranche A : un meme objet peut etre l'un sans etre l'autre. -/
def φOr : Formula Atom := Formula.atom 0 ⋎ Formula.atom 1

/-! ## Les quatre valuations, comme lignes de la table de verite

Une `Valuation` FFL est une fonction `Atom → Prop`. Sur `Fin 2`, toute valuation
est l'une des quatre lignes de la table (preuve ci-dessous) : la table de verite
du notebook et l'enumeration ci-dessous couvrent exactement les memes cas. -/

/-- Ligne `p ↦ V, q ↦ V`. -/
def valTT : FFL.Propositional.Boolean.Valuation Atom := fun _ => True
/-- Ligne `p ↦ V, q ↦ F`. -/
def valTF : FFL.Propositional.Boolean.Valuation Atom := fun a => a = 0
/-- Ligne `p ↦ F, q ↦ V`. -/
def valFT : FFL.Propositional.Boolean.Valuation Atom := fun a => a = 1
/-- Ligne `p ↦ F, q ↦ F`. -/
def valFF : FFL.Propositional.Boolean.Valuation Atom := fun _ => False

/-- **Exhaustivite de la table** : sur `Fin 2`, toute valuation est l'une des
quatre lignes. C'est ce theoreme qui transforme une table de verite finie en
preuve de validite universelle. -/
theorem valuations_exhaustive (v : FFL.Propositional.Boolean.Valuation Atom) :
    v = valTT ∨ v = valTF ∨ v = valFT ∨ v = valFF := by
  by_cases h0 : v 0 <;> by_cases h1 : v 1
  · exact Or.inl (by funext a; fin_cases a <;> simp [valTT, h0, h1])
  · exact Or.inr (Or.inl (by funext a; fin_cases a <;> simp [valTF, h0, h1]))
  · exact Or.inr (Or.inr (Or.inl (by funext a; fin_cases a <;> simp [valFT, h0, h1])))
  · exact Or.inr (Or.inr (Or.inr (by funext a; fin_cases a <;> simp [valFF, h0, h1])))

/-! ## Lignes de table, evaluees par le noyau

La semantique FFL est Prop-valuee (`Valuation α := α → Prop`, `val` recursif
sur les connecteurs), donc chaque ligne de table est un **petit theoreme**
prouve par evaluation propositionnelle — `simp [models_iff_val, val]` deplie
la formule temoin et la valuation, puis evalue les connecteurs — pas un
`decide` : la table de verite n'est pas une image, ce sont quatre preuves
verifiees par le noyau. -/

@[simp] theorem peirce_row_TT : valTT ⊧ φPeirce := by
  simp [FFL.Propositional.Formula.Boolean.models_iff_val,
        FFL.Propositional.Formula.Boolean.val, φPeirce, valTT]
@[simp] theorem peirce_row_TF : valTF ⊧ φPeirce := by
  simp [FFL.Propositional.Formula.Boolean.models_iff_val,
        FFL.Propositional.Formula.Boolean.val, φPeirce, valTF]
@[simp] theorem peirce_row_FT : valFT ⊧ φPeirce := by
  simp [FFL.Propositional.Formula.Boolean.models_iff_val,
        FFL.Propositional.Formula.Boolean.val, φPeirce, valFT]
@[simp] theorem peirce_row_FF : valFF ⊧ φPeirce := by
  simp [FFL.Propositional.Formula.Boolean.models_iff_val,
        FFL.Propositional.Formula.Boolean.val, φPeirce, valFF]

/-- **Validite de Peirce** : vrai pour toute valuation — la tautologie constatee
cote Tweety devient un theoreme, par exhaustivite de la table. -/
theorem peirce_valid : ∀ v : FFL.Propositional.Boolean.Valuation Atom, v ⊧ φPeirce := by
  intro v
  rcases valuations_exhaustive v with rfl | rfl | rfl | rfl
  · exact peirce_row_TT
  · exact peirce_row_TF
  · exact peirce_row_FT
  · exact peirce_row_FF

/-- **Contre-modele de `p ∨ q`** : la ligne `p ↦ F, q ↦ F` le falsifie.
C'est le contre-modele *calcule* cote Tweety, devenu temoin certifie. -/
theorem or_not_valid : valFF ⊧ φOr ↔ False := by
  simp [FFL.Propositional.Formula.Boolean.models_iff_val,
        FFL.Propositional.Formula.Boolean.val, φOr, valFF]

/-! ## Les trois verdicts distincts sur les memes formules

`satisfiable`, `valid`, `provable` ne disent pas la meme chose : `φOr` le montre
sur un seul objet — satisfiable (ligne `TT`), non valide (ligne `FF`). -/

/-- `p ∨ q` est satisfiable : temoin `p ↦ V, q ↦ V`. -/
theorem or_satisfiable : ∃ v : FFL.Propositional.Boolean.Valuation Atom, v ⊧ φOr :=
  ⟨valTT, by simp [FFL.Propositional.Formula.Boolean.models_iff_val,
                   FFL.Propositional.Formula.Boolean.val, φOr, valTT]⟩

/-- `p ∨ q` n'est PAS valide : temoin falsifiant `p ↦ F, q ↦ F`.
Le controle negatif exige par la Tranche A : satisfiable sans etre valide. -/
theorem or_not_universally_valid :
    ¬ (∀ v : FFL.Propositional.Boolean.Valuation Atom, v ⊧ φOr) := by
  intro h
  exact or_not_valid.mp (h valFF)

/-! ## Versant preuve : Peirce est derivable, pas seulement vrai

`Entailment.Cl.peirce` (FFL) donne la derivation de Hilbert du meme schema dans
tout systeme portant l'axiome de Peirce ; `Tait.completeness!` garantit que tout
ce qui est semantiquement entail (comme `peirce_valid` ci-dessus, via `T = ∅`)
est derivable. Execution et derivation se rejoignent — c'est le point de l'arc. -/

section PeirceProvable

variable {S F : Type*} [FFL.LogicalConnective F] [FFL.Entailment S F] {𝓢 : S}
variable [FFL.LogicalNeutral F] [FFL.Entailment.HasAxiomPeirce 𝓢]
variable (φ ψ : F)

/-- Le schema de Peirce est derivable : reprise directe de `FFL.Entailment.peirce`
(`Entailment/Cl.lean`), rappele ici pour que le notebook cite le versant preuve
sur la meme formule que le versant table. -/
theorem peirce_provable : 𝓢 ⊢ ((φ 🡒 ψ) 🡒 φ) 🡒 φ := FFL.Entailment.peirce

end PeirceProvable

end FormalLogic.Bridge
