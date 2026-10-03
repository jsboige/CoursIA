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

`decideEq` compare les en-têtes (nombre d'ensembles, cardinaux, nombre de
relations) sans les tables. Le présent module énumère effectivement les
tables des opérations binaires sur un ensemble fini et décide leur égalité
stricte, cardinalité comprise — avec le **théorème de correction**
`sameBinaryOperation_eq_iff` : `sameBinaryOperation m m f g = true ↔ f = g`.
Ce cas particulier ne couvre ni le renommage des éléments ni la génération
mutuelle par composition. -/

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

/-- **En-têtes seulement.** `decideEq` compare ce qui se décide sans
`Fin.pi` (hors core) : le nombre d'ensembles, les cardinaux (via
`List.ofFn`) et le nombre de relations — **pas les tables**.

Pour la classe restreinte (1 ensemble, 1 relation binaire), la comparaison
complète des tables est `sameBinaryOperation`, dont la correction est
prouvée par `sameBinaryOperation_eq_iff` ci-dessous. Cette définition
remplace un stub qui retournait `true` dès que le nombre d'ensembles
coïncidait. L'énumération des tables d'arité quelconque reste ouverte :
voir #16958. -/
def decideEq (s₁ s₂ : Structure) : Bool :=
  s₁.nSets == s₂.nSets
  && List.ofFn s₁.sizes == List.ofFn s₂.sizes
  && s₁.rels.length == s₂.rels.length

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

example : decideEq Cyclic.c2 Cyclic.c3 = false := rfl
example : decideEq Cyclic.c3 Cyclic.c3 = true := rfl

/-! ## Correction du décideur (théorème)

`sameBinaryOperation` ne se contente pas de comparer des listes : il
**décide correctement** l'égalité des opérations. La direction facile
(`f = g` → tables égales) est la congruence de `List.ofFn`. La direction
utile (tables égales → `f = g`) extrait chaque entrée `(a, b)` de la
table par `List.getElem?_ofFn`, puis conclut par `Fin.val_inj`. -/

/-- Congruence : des opérations égales ont des tables égales. -/
theorem binaryTable_eq_of_eq (m : Nat) (f g : Fin m → Fin m → Fin m)
    (h : f = g) : binaryTable m f = binaryTable m g := by
  rw [h]

/-- Extraction : des tables égales donnent des opérations égales — chaque
entrée `(a, b)` se relit dans la table par `List.getElem?_ofFn`
(l'égalité de structure `⟨a.val, a.isLt⟩ ≡ a` est définitionnelle). -/
theorem eq_of_binaryTable_eq (m : Nat) (f g : Fin m → Fin m → Fin m)
    (h : binaryTable m f = binaryTable m g) : f = g := by
  apply funext
  intro a
  apply funext
  intro b
  have key : (f a b).val = (g a b).val := by
    have ha : (binaryTable m f)[a.val]? = (binaryTable m g)[a.val]? := by rw [h]
    simp only [binaryTable, List.getElem?_ofFn, dif_pos a.isLt] at ha
    have ha' : List.ofFn (fun y : Fin m => (f a y).val)
        = List.ofFn (fun y : Fin m => (g a y).val) := Option.some.inj ha
    have hb : (List.ofFn (fun y : Fin m => (f a y).val))[b.val]?
        = (List.ofFn (fun y : Fin m => (g a y).val))[b.val]? := by rw [ha']
    simp only [List.getElem?_ofFn, dif_pos b.isLt] at hb
    exact Option.some.inj hb
  exact Fin.val_inj.mp key

/-- Les tables décident l'égalité des opérations :
    `binaryTable m f = binaryTable m g ↔ f = g`. -/
theorem binaryTable_eq_iff (m : Nat) (f g : Fin m → Fin m → Fin m) :
    binaryTable m f = binaryTable m g ↔ f = g :=
  ⟨eq_of_binaryTable_eq m f g, binaryTable_eq_of_eq m f g⟩

/-- **Théorème de correction du décideur** : pour la classe restreinte
(1 ensemble, opération binaire), `sameBinaryOperation m m f g = true` si
et seulement si `f = g`. Le « simple halting algorithm » de Tegmark est
ici un décideur **prouvé correct** sur cette tranche. -/
theorem sameBinaryOperation_eq_iff (m : Nat) (f g : Fin m → Fin m → Fin m) :
    sameBinaryOperation m m f g = true ↔ f = g := by
  constructor
  · intro h
    have h' : ((m, binaryTable m f) : Nat × List (List Nat))
        = ((m, binaryTable m g) : Nat × List (List Nat)) :=
      beq_iff_eq.mp h
    rw [Prod.mk.injEq] at h'
    exact eq_of_binaryTable_eq m f g h'.2
  · intro h
    apply beq_iff_eq.mpr
    rw [Prod.mk.injEq, h]
    exact ⟨rfl, rfl⟩

/-- Le décideur distingue l'addition mod 3 de l'opération constante —
et la correction certifie que ce n'est pas un artefact d'encodage :
`false` signifie réellement « opérations différentes ». -/
example : sameBinaryOperation 3 3 Cyclic.mult3Table (fun _ _ => 0) = false := by
  cases h : sameBinaryOperation 3 3 Cyclic.mult3Table (fun _ _ => 0) with
  | false => rfl
  | true =>
    have heq := (sameBinaryOperation_eq_iff 3 Cyclic.mult3Table (fun _ _ => 0)).mp h
    have h1 : Cyclic.mult3Table (1 : Fin 3) (1 : Fin 3) = (0 : Fin 3) :=
      congrFun (congrFun heq (1 : Fin 3)) (1 : Fin 3)
    exact absurd h1 (by decide)

end Decidable
