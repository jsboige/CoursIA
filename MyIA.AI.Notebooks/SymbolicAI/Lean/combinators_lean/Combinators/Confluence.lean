/-
Confluence du systeme S/K/I — invocation de l'organe Mathlib.

Pli 4 de l'Epic Origami #19742 (grain B, #25061) : la confluence est
demontree en invoquant l'organe formel du depot, `Relation.church_rosser`
(Mathlib/Logic/Relation.lean, l.896 au pin v4.33.0) — forme de
Hindley-Rosen : un losange local pour une relation intermediaire
entraine la confluence de sa cloture reflexive-transitive.

Le pont entre `step` et sa cloture `ReflTransGen step` passe par la
reduction parallele `par` :

  - `step ⊆ par` (lemme `step_par`) ;
  - `par ⊆ ReflTransGen step` (lemme `par_step`) ;
  - `diamond` (`Combinators.Parallel`) fournit exactement l'hypotenuse
    `h` que `church_rosser` exige.

Corollaire pedagogique (`unique_normal_form`) : deux reductions
exhaustives d'un meme terme aboutissent au meme resultat — c'est la
propriete qui fonde la reduction a une forme close, le geste central
du calcul symbolique (pont avec la question de veille de l'Epic : la
confluence est la condition sous laquelle reduire « jusqu'au bout » a
un sens).
-/

import Combinators.Parallel
import Mathlib.Logic.Relation

namespace Combinators

open Term Relation

/-! ### Pont entre `step` et `par` -/

/-- Toute reduction a un pas est une reduction parallele. -/
theorem step_par {a b : Term} (h : step a b) : par a b := by
  induction h with
  | S x y z => exact par.S (par.refl x) (par.refl y) (par.refl z)
  | K x y => exact par.K (par.refl x) (par.refl y)
  | I x => exact par.I (par.refl x)
  | @app_l x x' y _ ih => exact par.congr ih (par.refl y)
  | @app_r x y y' _ ih => exact par.congr (par.refl x) ih

/-- Lever une suite de reductions dans le trou gauche d'une application. -/
theorem rtg_app_l {x x' y : Term} (h : ReflTransGen step x x') :
    ReflTransGen step (x ⊙ y) (x' ⊙ y) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (step.app_l hs)

/-- Lever une suite de reductions dans le trou droit d'une application. -/
theorem rtg_app_r {x y y' : Term} (h : ReflTransGen step y y') :
    ReflTransGen step (x ⊙ y) (x ⊙ y') := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (step.app_r hs)

/-- Transfert de la cloture : `step ⊆ par` s'etend a `ReflTransGen`. -/
theorem rtg_step_par {a b : Term} (h : ReflTransGen step a b) :
    ReflTransGen par a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (step_par hs)

/-- Toute reduction parallele est une suite de reductions a un pas :
chaque jambe applique les reductions des sous-termes dans le contexte.
La regle S duplique son troisieme argument, d'ou les deux passages
`rtg_app_r ihz` (occurrence gauche puis occurrence droite du rejoint). -/
theorem par_step {a b : Term} (h : par a b) : ReflTransGen step a b := by
  induction h with
  | refl t => exact ReflTransGen.refl
  | @congr x x' y y' _ _ ihx ihy =>
      exact (rtg_app_l ihx).trans (rtg_app_r ihy)
  | @S x x' y y' z z' _ _ _ ihx ihy ihz =>
      -- a = S ⊙ x ⊙ y ⊙ z ; apres contraction, x est en gauche-gauche,
      -- y en droite-gauche, z apparait a gauche et a droite.
      exact (ReflTransGen.single (step.S x y z)).trans
        ((rtg_app_l (rtg_app_l ihx)).trans
          ((rtg_app_l (rtg_app_r ihz)).trans
            ((rtg_app_r (rtg_app_l ihy)).trans
              (rtg_app_r (rtg_app_r ihz)))))
  | @K x x' y y' _ _ ihx _ =>
      -- a = K ⊙ x ⊙ y ; apres contraction, x est a la racine.
      exact (ReflTransGen.single (step.K x y)).trans ihx
  | @I x x' _ ihx =>
      -- a = I ⊙ x ; apres contraction, x est a la racine.
      exact (ReflTransGen.single (step.I x)).trans ihx

/-- Transfert reciproque : `par ⊆ step*` s'etend a `ReflTransGen`. -/
theorem rtg_par_step {a b : Term} (h : ReflTransGen par a b) :
    ReflTransGen step a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hs ih => exact ih.trans (par_step hs)

/-! ### Confluence -/

/-- **Confluence du systeme S/K/I** : toute paire de reductions
`step*` issues d'un meme terme se rejoint. Demontree par invocation
de l'organe `Relation.church_rosser` sur la reduction parallele,
puis transfert par `ReflTransGen step = ReflTransGen par`. -/
theorem confluence {a b c : Term}
    (hb : ReflTransGen step a b) (hc : ReflTransGen step a c) :
    ∃ d, ReflTransGen step b d ∧ ReflTransGen step c d := by
  have hbp : ReflTransGen par a b := rtg_step_par hb
  have hcp : ReflTransGen par a c := rtg_step_par hc
  obtain ⟨d, hd₁, hd₂⟩ := Relation.church_rosser (r := par)
    (fun _ _ _ e₁ e₂ =>
      let ⟨f, hf₁, hf₂⟩ := diamond' _ _ _ e₁ e₂
      ⟨f, ReflGen.single hf₁, ReflTransGen.single hf₂⟩)
    hbp hcp
  exact ⟨d, rtg_par_step hd₁, rtg_par_step hd₂⟩

/-! ### Corollaire : unicite de la forme normale -/

/-- Un terme irreductible : aucune regle S, K ou I ne s'applique
nulle part. C'est la « forme close » du geste symbolique. -/
def Irreducible (t : Term) : Prop := ∀ u, ¬ step t u

/-- Une suite de reductions issue d'un terme irreductible est vide. -/
theorem eq_of_rtg_irreducible {a b : Term} (h : ReflTransGen step a b)
    (ha : Irreducible a) : b = a := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      subst ih
      exact absurd hs (ha _)

/-- **Unicite de la forme normale** : deux reductions exhaustives d'un
meme terme aboutissent au meme terme irreductible. Corollaire direct de
la confluence — c'est la reponse que le systeme S/K/I apporte a
l'irreductibilite : quand une forme normale existe, elle est unique,
meme si le chemin pour l'atteindre ne l'est pas. -/
theorem unique_normal_form {a b c : Term}
    (hb : ReflTransGen step a b) (hc : ReflTransGen step a c)
    (hbi : Irreducible b) (hci : Irreducible c) : b = c := by
  obtain ⟨d, hd₁, hd₂⟩ := confluence hb hc
  have e₁ : b = d := (eq_of_rtg_irreducible hd₁ hbi).symm
  have e₂ : c = d := (eq_of_rtg_irreducible hd₂ hci).symm
  exact e₁.trans e₂.symm

end Combinators