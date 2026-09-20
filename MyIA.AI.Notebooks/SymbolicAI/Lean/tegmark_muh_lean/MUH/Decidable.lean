import MUH.Structure

/-! # Décidabilité de l'équivalence de structures finies (Tegmark R16 Annexe A §1)

Tegmark (2007, Annexe A §1 in fine) écrit :

> *« There is a simple halting algorithm for determining whether any two
>    finite mathematical structure definitions are equivalent. »*

Le présent module **ne livre pas** cet algorithme. Il en expose le **squelette
documentaire** dans le cas restreint (arité ≤ 2, cardinal ≤ 3, 1 seul
ensemble) pour ancrer la formalisation sur le texte source. L'implémentation
effective — énumération exhaustive des tables de valeurs, comparaison point à
point, preuve de terminaison — est **hors-scope** de cette introduction et
fait l'objet du suivi **#16958**. Les définitions présentes ici sont donc
des stubs marqués comme tels, **pas** un algorithme haltant.

Ce module formalise un cas restreint :
  - arité ≤ 2,
  - cardinalité de chaque ensemble ≤ 3,
  - 1 seul ensemble.

L'algorithme halt *cible* est `decidable_equiv` (à implémenter) pour les
structures à 1 ensemble, arité 0/1/2, cardinal 2 ou 3. -/

namespace Decidable

/-- L'identité entre deux structures : même nombre d'ensembles, mêmes
    cardinaux, mêmes relations (signature + table). C'est la définition la plus
    stricte — Tegmark §1 demande l'équivalence par génération mutuelle, qui est
    plus générale. Pour le cas restreint (arité ≤ 2, cardinal ≤ 3), on se
    contente de l'égalité point par point sur les tables. -/
def strictEq {n : Nat} {sizes : Fin n → Nat}
    (r₁ r₂ : Rel n sizes) : Prop :=
  r₁ = r₂

/-- **Stub.** Une structure est dite *close par composition binaire* si, pour
    toute paire de relations R(a, b) : S×S → S et R(a, b) : S×S → S, la composée
    R(R(a, c), b) : S×S×S → S est aussi une relation Tegmark (arité 3).

    Le constructeur `trivial` est un placeholder — `ClosedUnderComp` n'est pas
    instancié par une vraie composition dans cette introduction. Une
    formalisation complète reste à faire (#16958). -/
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

/-- **Stub décoratif.** Pour une structure à 1 ensemble de cardinal 2 et une
    relation binaire Booléenne, l'espace des tables possibles est de taille
    `2^4 = 16`. La valeur `boolBinaryTableCount = 16` est citée pour ancrer le
    raisonnement ; elle **n'est pas utilisée** par `decideEq` et ne démontre
    rien par elle-même. Une implémentation effective comparerait
    exhaustivement les 16 tables (#16958). -/
def boolBinaryTableCount : Nat := 2 ^ (2 * 2)

/-- **Stub.** `decideEq` est l'**ébauche** d'un décideur pour l'équivalence de
    structures. L'implémentation livrée compare uniquement `nSets` — une
    version complète comparerait les tables de valeurs une par une (et prouverait
    la décidabilité au sens de Tegmark). Suivi #16958. -/
def decideEq (s₁ s₂ : Structure) : Bool :=
  s₁.nSets == s₂.nSets

end Decidable