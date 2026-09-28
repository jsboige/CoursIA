import MUH.Structure
import MUH.Cyclic

/-! # Décidabilité de l'équivalence de structures finies (Tegmark R16 Annexe A §1)

Tegmark (2007, Annexe A §1 in fine) écrit :

> *« There is a simple halting algorithm for determining whether any two
>    finite mathematical structure definitions are equivalent. »*

L'algorithme est l'**énumération des tableaux de valeurs** : deux structures
sont équivalentes si et seulement si chaque relation de l'une est obtenue par
composition finie des relations de l'autre (et réciproquement). Pour des
structures finies (cardinaux bornés et arités bornées), l'espace des
compositions est fini, donc l'algorithme termine.

Ce module formalise un cas restreint :
  - arité ≤ 2,
  - cardinalité de chaque ensemble ≤ 3,
  - 1 seul ensemble.

`decideEq` reste un stub et ne décide pas cette équivalence. Le présent
module énumère effectivement les tables des opérations binaires sur un
ensemble fini et décide leur égalité stricte, cardinalité comprise. Ce cas
particulier ne couvre ni le renommage des éléments ni la génération mutuelle
par composition. -/

namespace Decidable

/-- L'identité entre deux structures : même nombre d'ensembles, mêmes
    cardinaux, mêmes relations (signature + table). C'est la définition la plus
    stricte — Tegmark §1 demande l'équivalence par génération mutuelle, qui est
    plus générale. Pour le cas restreint (arité ≤ 2, cardinal ≤ 3), on se
    contente de l'égalité point par point sur les tables. -/
def strictEq {n : Nat} {sizes : Fin n → Nat}
    (r₁ r₂ : Rel n sizes) : Prop :=
  r₁ = r₂

/-- **Stub.** Une structure est dite *close par composition binaire* si, pour toute paire
    de relations R(a, b) : S×S → S et R(a, b) : S×S → S, la composée
    R(R(a, c), b) : S×S×S → S est aussi une relation Tegmark (arité 3). Cette
    condition n'est pas vérifiée pour C₂/C₃ directement (la composition donne
    une relation ternaire), mais elle l'est pour les structures à générateurs
    complets.

    Le code livré n'expose que le constructeur `trivial` — c'est un **stub
    décoratif** pour réservation du nom. L'implémentation de la condition
    n'est pas en scope ; voir #16958. -/
inductive ClosedUnderComp : Prop
  | trivial : ClosedUnderComp

/-- Pour un ensemble à 1 seul élément, l'arité et le cardinal sont triviaux :
    il n'y a qu'une seule relation possible (la fonction constante). -/
def trivialStructure : Structure :=
  { nSets := 1
  , sizes := fun _ => 1
  , rels := [{ sig := { arity := 0
                       , args := fun i => i.elim0
                       , out := (0 : Fin 1) }
             , table := fun _ => (0 : Fin 1) }]
  , sizes_pos := fun _ => Nat.one_pos }

/-- **Stub documentaire.** Pour une structure à 1 ensemble de cardinal 2 et une relation
    binaire Booléenne, l'espace des tables possibles est de taille 2⁴ = 16. La
    décidabilité serait triviale par énumération des 16 tables. Cette
    définition ne fait que retourner le compte — l'implémentation effective
    de l'énumération n'est pas livrée ; voir #16958. -/
def boolBinaryTableCount : Nat := 2 ^ (2 * 2)

/-- **Stub.** `decideEq` : deux structures sont équivalentes si leurs tables
    coïncident (égalité point par point). Cette décidabilité serait triviale :
    on parcourrait les arguments et on comparerait.

    Le stub actuel retourne `true` quand les deux structures ont le même
    nombre d'ensembles — une version complète comparerait les tables de
    valeurs une par une. Voir #16958 pour le suivi de l'implémentation. -/
def decideEq (s₁ s₂ : Structure) : Bool :=
  s₁.nSets == s₂.nSets

/-- Énumère les `m × m` valeurs d'une relation binaire sur un ensemble fini.
    Cette tranche compare les tables à signature et cardinalité identiques ;
    elle ne décide pas l'équivalence par composition de Tegmark. -/
def binaryTable (m : Nat) (f : Fin m → Fin m → Fin m) : List (List Nat) :=
  List.ofFn (fun a : Fin m =>
    List.ofFn (fun b : Fin m => (f a b).val))

/-- Compare deux opérations binaires typées, y compris leurs cardinaux.
    C'est une égalité stricte des tables, non une équivalence des structures
    par renommage des éléments ou par génération mutuelle. -/
def sameBinaryOperation (m n : Nat) (f : Fin m → Fin m → Fin m)
    (g : Fin n → Fin n → Fin n) : Bool :=
  (m, binaryTable m f) == (n, binaryTable n g)

example : sameBinaryOperation 2 2 Cyclic.mult2Table Cyclic.mult2Table = true := rfl
example : sameBinaryOperation 3 3 Cyclic.mult3Table Cyclic.mult3Table = true := rfl
example : sameBinaryOperation 2 2 Cyclic.mult2Table (fun _ _ => 0) = false := rfl
example : sameBinaryOperation 2 3 Cyclic.mult2Table Cyclic.mult3Table = false := rfl

end Decidable