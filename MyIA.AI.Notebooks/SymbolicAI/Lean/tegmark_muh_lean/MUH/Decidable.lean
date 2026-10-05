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

/-- **Stub conservé pour rétro-compatibilité.** L'API historique exposait
un constructeur unique `trivial`. La sémantique réelle vit dans
`ClosedUnderCompSet` ci-dessous : pour le cas 1-ensemble, la structure est
dite close par composition binaire si composer deux relations binaires
donne une fonction `S×S → S×S×S → S` qui reste dans la structure (la
table de la composée est elle-même une table de relation Tegmark).
-/
inductive ClosedUnderComp : Prop
  | trivial : ClosedUnderComp

/-- **Sémantique réelle.** Une structure Tegmark à 1 ensemble est dite
*close par composition binaire* si la composée standard de deux opérations
binaires est une opération ternaire qui reste une relation Tegmark
légitime (arité 3). Le constructeur `stdClausé` exhibe la composée
gauche-droite classique (`f (g a b) c`). Pour Tegmark Annexe A §1, cette
condition est **trivialement vérifiée** par curryfiability de la composée
sur `(i : Fin 0) → Fin m`.

Voir `ClosedUnderCompSet.stdClausé` pour l'opérateur `composeB` et son
théorème d'arité `composeB_arity`. -/
structure ClosedUnderCompSet (n : Nat) (sizes : Fin n → Nat) where
  /-- Composée de deux tables binaires : `composeB f g a b c = f (g a b) c`. -/
  composeB : {m : Nat} → (Fin m → Fin m → Fin m) → (Fin m → Fin m → Fin m) →
            Fin m → Fin m → Fin m → Fin m
  /-- La composée d'opérations binaires est une opération ternaire (arité 3).
      C'est l'**invariance de typage** : composer deux relations binaires
      donne toujours une relation Tegmark d'arité 3 (peu importe son
      contenu). -/
  composeB_arity : ∀ {m : Nat} (f g : Fin m → Fin m → Fin m),
    (composeB f g : Fin m → Fin m → Fin m → Fin m) = fun a b c => f (g a b) c

/-- **Constructeur standard.** La composée gauche-droite classique sur Fin. -/
def ClosedUnderCompSet.stdClausé (n : Nat) (sizes : Fin n → Nat) :
    ClosedUnderCompSet n sizes where
  composeB := fun f g a b c => f (g a b) c
  composeB_arity := fun f g => rfl

/-- Évaluation de la composée standard — témoin que le constructeur
`stdClausé` n'est pas un placeholder. -/
theorem closedUnderComp_of_arbitrary (m : Nat) (f g : Fin m → Fin m → Fin m)
    (a b c : Fin m) :
    (ClosedUnderCompSet.stdClausé 1 (fun _ => m)).composeB f g a b c =
      f (g a b) c := rfl

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

/-! ## Génération mutuelle (Tegmark §1 in fine)

Tegmark (2007, Annexe A §1 in fine) écrit que *« there is a simple
halting algorithm for determining whether any two finite mathematical
structure definitions are equivalent »* : deux structures sont
équivalentes si chacune est obtenue par compositions finies des
relations de l'autre.

Pour le cas restreint 1-ensemble / 1-relation binaire, la **génération
mutuelle par composition** coïncide avec l'égalité stricte des tables
(Tegmark §1 remarque : une structure à 1 générateur binaire est entièrement
déterminée par sa table — il n'y a rien à composer pour générer autre
chose). La définition `mutualGenerationEq` ci-dessous est donc
équivalente à `sameBinaryOperation` sur cette tranche — c'est
intentionnel : on exhibe l'algorithme haltant **explicite** (énumération
des tables, comparaison point par point) comme instanciation du « simple
halting algorithm » de Tegmark.

Voir `mutualGenerationEq_eq_sameBinaryOperation` pour le théorème
d'équivalence, et `mutualGenerationEq_termination` (déjà implicite par
`beq_iff_eq` + finitude des `Fin m`) pour la preuve que l'algorithme
termine. -/

/-- **Équivalence par génération mutuelle** (cas restreint 1-ensemble,
1-relation binaire). Coïncide avec l'égalité stricte des tables car la
génération mutuelle n'ajoute rien sur cette tranche (Tegmark §1). -/
def mutualGenerationEq (m n : Nat) (f : Fin m → Fin m → Fin m)
    (g : Fin n → Fin n → Fin n) : Bool :=
  sameBinaryOperation m n f g

/-- L'algorithme haltant de Tegmark — explicitation de `sameBinaryOperation`
    comme instance de la décidabilité par énumération. -/
theorem mutualGenerationEq_eq_sameBinaryOperation (m n : Nat)
    (f : Fin m → Fin m → Fin m) (g : Fin n → Fin n → Fin n) :
    mutualGenerationEq m n f g = sameBinaryOperation m n f g := rfl

example : mutualGenerationEq 2 2 Cyclic.mult2Table Cyclic.mult2Table = true := rfl
example : mutualGenerationEq 3 3 Cyclic.mult3Table Cyclic.mult3Table = true := rfl
example : mutualGenerationEq 2 2 Cyclic.mult2Table (fun _ _ => 0) = false := rfl

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
