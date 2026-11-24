import Mathlib.Logic.Relation

/-!
# Combinator reduction peaks

The `ict/combinators.py` engine represents S, K and I as variables with those
names. `Step` permits contraction at the root or in either branch of an
application, independently of the engine's chosen strategy. Mathlib's
`Relation.ReflTransGen` and `Relation.Join` express reductions and joins;
`Relation.church_rosser` provides a framework for a future general proof.

These peaks do not prove general confluence of SKI. They isolate erasure by K
and duplication by S, two cases for such a proof. Source: Stephen Wolfram,
*Combinators: A Centennial View* (2020),
https://writings.stephenwolfram.com/2020/12/combinators-a-centennial-view/.
-/
namespace Conway.Combinators_en

/-- Engine terms: named variables and binary application. -/
inductive Term where
  | var : String → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

abbrev S : Term := .var "S"
abbrev K : Term := .var "K"
abbrev I : Term := .var "I"

/-- One SKI contraction, possibly in an application branch. -/
inductive Step : Term → Term → Prop where
  | s (f g x : Term) : Step (.app (.app (.app S f) g) x) (.app (.app f x) (.app g x))
  | k (x y : Term) : Step (.app (.app K x) y) x
  | i (x : Term) : Step (.app I x) x
  | left {f f' : Term} (x : Term) : Step f f' → Step (.app f x) (.app f' x)
  | right (f : Term) {x x' : Term} : Step x x' → Step (.app f x) (.app f x')

abbrev Steps := Relation.ReflTransGen Step

/-- A multi-step reduction lifts to the left of an application. -/
theorem steps_left {f f' : Term} (h : Steps f f') (x : Term) :
    Steps (.app f x) (.app f' x) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (Step.left x h)

/-- A multi-step reduction lifts to the right of an application. -/
theorem steps_right (f : Term) {x x' : Term} (h : Steps x x') :
    Steps (.app f x) (.app f x') := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (Step.right f h)

/-- K erases its second argument even if it has already taken a step. -/
theorem k_erasure_peak (x : Term) {y y' : Term} (_h : Step y y') :
    Relation.Join Steps x (.app (.app K x) y') := by
  exact ⟨x, .refl, .single (Step.k x y')⟩

/-- Reducing K's first argument before or after the root reaches the same term. -/
theorem k_retained_peak {x x' : Term} (h : Step x x') (y : Term) :
    Relation.Join Steps x (.app (.app K x') y) := by
  exact ⟨x', .single h, .single (Step.k x' y)⟩

/-- After contracting S, both copies of the argument can reduce. -/
theorem s_duplication_peak (f g : Term) {x x' : Term} (h : Step x x') :
    Relation.Join Steps (.app (.app f x) (.app g x))
      (.app (.app (.app S f) g) x') := by
  refine ⟨.app (.app f x') (.app g x'), ?_, .single (Step.s f g x')⟩
  exact (Relation.ReflTransGen.single (Step.left (.app g x) (Step.right f h))).tail
    (Step.right (.app f x') (Step.right g h))

/-- Closed witnesses: the argument `I K` reduces to `K`. -/
example : Relation.Join Steps I (.app (.app K I) K) :=
  k_erasure_peak I (Step.i K)

example : Relation.Join Steps (.app (.app I (.app I K)) (.app K (.app I K)))
    (.app (.app (.app S I) K) K) :=
  s_duplication_peak I K (Step.i K)

end Conway.Combinators_en
