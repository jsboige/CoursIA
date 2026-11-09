import MUH.Structure

/-! # `Fin.pi` — produit dépendant fini (sans Mathlib)

`Fin.pi` (Mathlib) est défini pour un type `∀ i, Fin n → α i`. La version
**restreinte** livrée ici est strictement celle dont Tegmark R16 Annexe A §c
a besoin pour énumérer les tables de valeurs : un produit dépendant indexé
par `Fin n`, à valeurs dans `α i`.

```
def Fin.pi (n : Nat) (α : Fin n → Type) : Type := (i : Fin n) → α i
```

Cette définition vit déjà dans Lean core (les types dépendants `(i : I) → α i`
sont du lambda-calcul pur). On l'expose sous un nom canonique Tegmark, plus
des **helpers d'énumération** (`pi_ofFn`) et des lemmes de transport adaptés
au cas 1-ensemble du Décideur.

Le module documente aussi l'absence volontaire de `Fin.pi` au sens Mathlib :
le lemme `pi_ext` (extensionnalité du produit dépendant) reste à définir par
proie dans une PR ultérieure si nécessaire — la présente tranche livre
**l'infrastructure**, pas la librairie complète. -/

namespace Tegmark

/-- Produit dépendant fini indexé par `Fin n` — alias de `(i : Fin n) → α i`.
    Sans Mathlib, on l'écrit explicitement : c'est le lambda-calcul usuel. -/
def Fin.pi {n : Nat} (α : Fin n → Type) : Type := (i : Fin n) → α i

/-- Constructeur `intro` curryfié pour `Fin.pi` — déjà définitionnel en
    Lean core, mais nommé pour la lisibilité. -/
abbrev Fin.pi.mk {n : Nat} {α : Fin n → Type} (f : (i : Fin n) → α i) :
    Fin.pi α := f

/-- Éliminateur `apply` curryfié pour `Fin.pi`. -/
abbrev Fin.pi.apply {n : Nat} {α : Fin n → Type} (p : Fin.pi α)
    (i : Fin n) : α i := p i

/-- Cas particulier : `Fin.pi` constant (`α i = β` pour tout `i`). Le produit
    dépendant se réduit au produit exponentiel `β^Fin n` = `Fin n → β`. -/
theorem Fin.pi_const {β : Type} (n : Nat) :
    Fin.pi (fun _ : Fin n => β) = (Fin n → β) := rfl

-- Pour `n = 0`, `Fin 0` est vide, donc `Fin.pi α` est le produit vide
-- (`(i : Fin 0) → α i` n'est pas habité sauf si l'une des `α i` est vide —
-- ce qui n'est pas la situation standard). Tegmark Annexe A suppose `n ≥ 1`
-- (au moins un ensemble), donc on documente sans prouver.

/-- Extensionnalité : deux éléments de `Fin.pi` sont égaux ssi leurs
    composantes le sont. Lean core sait déjà prouver ça par `funext`, mais
    on le pose ici comme lemme Tegmark explicite pour servir d'attache
    dans les preuves d'équivalence de structures (Tegmark §1 : « deux
    structures sont équivalentes ↔ leurs générateurs coïncide point par
    point »). -/
theorem Fin.pi_ext {n : Nat} {α : Fin n → Type} {f g : Fin.pi α}
    (h : ∀ i, f i = g i) : f = g := funext h

/-- Énumère les valeurs d'une famille `p : Fin n → Fin n → Fin m`
    (par exemple la table d'une opération binaire) sous forme de
    `List (List Nat)`. C'est l'attache Tegmark pour `binaryTable` (cas
    1-ensemble, relation binaire) et pour le décideur d'équivalence de
    structures : la liste des lignes, chaque ligne étant la liste des
    valeurs `Nat` pour cette ligne.
-/
def toBinaryTableList (n m : Nat) (p : Fin n → Fin n → Fin m) :
    List (List Nat) :=
  List.ofFn (fun i : Fin n =>
    List.ofFn (fun j : Fin n => (p i j).val))

end Tegmark