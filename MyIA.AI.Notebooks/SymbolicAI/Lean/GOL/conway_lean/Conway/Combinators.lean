import Mathlib.Logic.Relation

/-!
# Pics de réduction des combinateurs

Le moteur `ict/combinators.py` représente les constantes S, K et I par des
variables de noms correspondants. Ici, `Step` autorise une contraction à la
racine ou dans l'une des deux branches d'une application, indépendamment de la
stratégie choisie par le moteur. `Relation.ReflTransGen` et `Relation.Join`
sont les organes Mathlib employés pour les réductions et leur jonction ;
`Relation.church_rosser` donne un cadre pour une preuve générale ultérieure.

Les pics ci-dessous ne prouvent pas la confluence générale de SKI. Ils isolent
l'effacement par K et la duplication par S, deux cas à traiter dans une telle
preuve. Source : Stephen Wolfram, *Combinators: A Centennial View* (2020),
https://writings.stephenwolfram.com/2020/12/combinators-a-centennial-view/.
-/
namespace Conway.Combinators

/-- Termes du moteur : variables nommées et application binaire. -/
inductive Term where
  | var : String → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

abbrev S : Term := .var "S"
abbrev K : Term := .var "K"
abbrev I : Term := .var "I"

/-- Une contraction SKI, éventuellement dans une branche d'application. -/
inductive Step : Term → Term → Prop where
  | s (f g x : Term) : Step (.app (.app (.app S f) g) x) (.app (.app f x) (.app g x))
  | k (x y : Term) : Step (.app (.app K x) y) x
  | i (x : Term) : Step (.app I x) x
  | left {f f' : Term} (x : Term) : Step f f' → Step (.app f x) (.app f' x)
  | right (f : Term) {x x' : Term} : Step x x' → Step (.app f x) (.app f x')

abbrev Steps := Relation.ReflTransGen Step

/-- Une réduction multi-pas se transporte à gauche d'une application. -/
theorem steps_left {f f' : Term} (h : Steps f f') (x : Term) :
    Steps (.app f x) (.app f' x) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (Step.left x h)

/-- Une réduction multi-pas se transporte à droite d'une application. -/
theorem steps_right (f : Term) {x x' : Term} (h : Steps x x') :
    Steps (.app f x) (.app f x') := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (Step.right f h)

/-- K efface son second argument, même si celui-ci a déjà fait un pas. -/
theorem k_erasure_peak (x : Term) {y y' : Term} (_h : Step y y') :
    Relation.Join Steps x (.app (.app K x) y') := by
  exact ⟨x, .refl, .single (Step.k x y')⟩

/-- Réduire le premier argument de K avant ou après la racine mène au même terme. -/
theorem k_retained_peak {x x' : Term} (h : Step x x') (y : Term) :
    Relation.Join Steps x (.app (.app K x') y) := by
  exact ⟨x', .single h, .single (Step.k x' y)⟩

/-- Après la contraction de S, les deux copies de l'argument peuvent réduire. -/
theorem s_duplication_peak (f g : Term) {x x' : Term} (h : Step x x') :
    Relation.Join Steps (.app (.app f x) (.app g x))
      (.app (.app (.app S f) g) x') := by
  refine ⟨.app (.app f x') (.app g x'), ?_, .single (Step.s f g x')⟩
  exact (Relation.ReflTransGen.single (Step.left (.app g x) (Step.right f h))).tail
    (Step.right (.app f x') (Step.right g h))

/-- Témoins fermés : l’argument `I K` se réduit en `K`. -/
example : Relation.Join Steps I (.app (.app K I) K) :=
  k_erasure_peak I (Step.i K)

example : Relation.Join Steps (.app (.app I (.app I K)) (.app K (.app I K)))
    (.app (.app (.app S I) K) K) :=
  s_duplication_peak I K (Step.i K)

end Conway.Combinators
