import MUH.Structure

/-! # Énumération effective des tables finies — le « halting algorithm » rendu réel

Tegmark (2007, Annexe A §1 in fine) : *« there is a simple halting algorithm
for determining whether any two finite mathematical structure definitions are
equivalent »*. L'algorithme suppose l'**énumération des tableaux de valeurs**
d'une structure finie. Avant ce module, le lake comparait des tables données
(`sameBinaryOperation`, correction prouvée dans `MUH.Decidable`) mais
n'**énumérait** rien : `boolBinaryTableCount` était un compte documentaire,
pas une liste.

Ce module livre l'énumération effective, pour les deux arités qui portent
le récit de l'Annexe A :

- **arité 2** (les tables binaires, `m ^ (m * m)` éléments) — l'espace où
  vivent les générateurs (C₂, C₃, Sheffer/NAND) ;
- **arité 3** (les tables ternaires, `m ^ (m * m * m)` éléments) — l'arité
  **exacte** de la composée de deux relations binaires
  (`ClosedUnderCompSet.composeB`, règle (3) du §1) : la clôture par
  composition se constate **par appartenance à l'énumération**
  (`Decidable.composeB_mem_allTernaryTables`, dans le module consommateur).

Deux théorèmes font de chaque liste une énumération honnête :
`mem_allBinaryTables` / `mem_allTernaryTables` (**exhaustivité** : toute
table est dans la liste — l'algorithme n'oublie aucun candidat) et
`allBinaryTables_length` / `allTernaryTables_length` (**compte** : la taille
de l'espace, `m ^ (m ^ k)` par arité `k`). Le caractère haltant est porté
par la construction : ce sont des `List` finies.

L'énumération à **arité quelconque** (forme tuple `(i : Fin k) → Fin m`)
reste à livrer pour la clause générale de l'Annexe A ; la présente tranche
couvre les arités 2 et 3 utilisées par le lake.

Construction : une table d'arité `a` sur `Fin m` est une fonction
`Fin a → β` dont chaque valeur parcourt une liste `vals` donnée
(`allFunInto`, récursion sur `a` par `fcons`). Les tables binaires sont
`allFunInto (tables unaires) m` (chaque ligne est elle-même une table
unaire), les ternaires `allFunInto (tables binaires) m`. Les accessoires
`fcons`/`ftail` (cons/tail des vecteurs-fonctions) sont définis localement :
le core Lean 4.33 n'expose pas `Fin.cons`/`Fin.tail`. -/

namespace Enumeration

/-! ## Vecteurs-fonctions : `fcons` et `ftail` (locaux au core) -/

/-- Cons d'un vecteur-fonction : `fcons x t` vaut `x` en indice 0 et
`t` décalé ensuite. -/
def fcons {n : Nat} {β : Type} (x : β) (t : Fin n → β) :
    Fin (n + 1) → β :=
  fun i =>
    match i with
    | ⟨0, _⟩ => x
    | ⟨j + 1, _⟩ => t ⟨j, Nat.lt_of_succ_lt_succ (by omega)⟩

/-- Tail d'un vecteur-fonction : décale les indices de 1. -/
def ftail {n : Nat} {β : Type} (f : Fin (n + 1) → β) : Fin n → β :=
  fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

@[simp] theorem fcons_zero {n : Nat} {β : Type} (x : β) (t : Fin n → β) :
    ∀ (h : 0 < n + 1), fcons x t ⟨0, h⟩ = x :=
  fun _ => rfl

@[simp] theorem fcons_succ {n : Nat} {β : Type} (x : β) (t : Fin n → β)
    (j : Nat) (h : j + 1 < n + 1) :
    fcons x t ⟨j + 1, h⟩ = t ⟨j, Nat.lt_of_succ_lt_succ (by omega)⟩ :=
  rfl

@[simp] theorem ftail_fcons {n : Nat} {β : Type} (x : β) (t : Fin n → β) :
    ftail (fcons x t) = t := by
  funext i
  rfl

/-- Décomposition canonique : toute fonction sur `Fin (n+1)` est le `fcons`
de sa valeur en 0 et de sa queue. -/
theorem fcons_ftail_self {n : Nat} {β : Type} (f : Fin (n + 1) → β) :
    fcons (f ⟨0, Nat.succ_pos n⟩) (ftail f) = f := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨j + 1, _⟩ => rfl

/-! ## Cœur : énumérer les fonctions `Fin a → β` -/

/-- Tous les éléments de `Fin m`, comme liste indexée. -/
def finRange (m : Nat) : List (Fin m) := List.ofFn (fun i => i)

@[simp] theorem finRange_length (m : Nat) : (finRange m).length = m :=
  List.length_ofFn

/-- Tout élément de `Fin m` est dans `finRange m`. -/
theorem mem_finRange {m : Nat} (i : Fin m) : i ∈ finRange m :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

/-- **Énumérateur universel** : toutes les fonctions `Fin a → β` dont les
valeurs parcourent `vals`, construites par récursion sur l'arité `a`
(`fcons` d'une tête dans `vals` sur une queue déjà énumérée). -/
def allFunInto {β : Type} (vals : List β) : (a : Nat) → List (Fin a → β)
  | 0 => [fun i => i.elim0]
  | a + 1 =>
      (allFunInto vals a).flatMap
        (fun tail => vals.map (fun head => fcons head tail))

/-- La longueur d'un `flatMap` à second membre constant. -/
theorem length_flatMap_map {α β γ : Type} (l : List α) (l₂ : List β)
    (f : α → β → γ) :
    (l.flatMap (fun x => l₂.map (f x))).length = l.length * l₂.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_map, ih, Nat.succ_mul]
      omega

/-- **Compte** : l'énumérateur produit exactement `|vals| ^ a` fonctions. -/
theorem allFunInto_length {β : Type} (vals : List β) (a : Nat) :
    (allFunInto vals a).length = vals.length ^ a := by
  induction a with
  | zero => simp [allFunInto]
  | succ n ih =>
      calc (allFunInto vals (n + 1)).length
          = ((allFunInto vals n).flatMap
              (fun tail => vals.map (fun head => fcons head tail))).length := rfl
        _ = (allFunInto vals n).length * vals.length :=
            length_flatMap_map _ _ _
        _ = vals.length ^ n * vals.length := by rw [ih]
        _ = vals.length ^ (n + 1) := Nat.pow_succ vals.length n

/-- **Exhaustivité** : toute fonction `Fin a → β` dont les valeurs sont dans
`vals` appartient à l'énumération. C'est la complétude du « halting
algorithm » : aucun candidat n'est oublié. -/
theorem mem_allFunInto_of_mem {β : Type} (vals : List β) :
    ∀ {a : Nat} (f : Fin a → β), (∀ i, f i ∈ vals) → f ∈ allFunInto vals a
  | 0, f, _ =>
      List.mem_singleton.2 (funext fun i => i.elim0)
  | a + 1, f, hf => by
      have hdecomp : f = fcons (f ⟨0, Nat.succ_pos a⟩) (ftail f) :=
        (fcons_ftail_self f).symm
      rw [hdecomp]
      refine (List.mem_flatMap).2 ⟨ftail f,
        mem_allFunInto_of_mem vals (ftail f) (fun i => hf _),
        List.mem_map_of_mem (hf _)⟩

/-! ## Tables binaires (arité 2) -/

/-- **Toutes** les tables binaires sur `Fin m` : chaque ligne est une table
unaire énumérée, et les lignes sont elles-même énumérées — `m ^ (m * m)`
éléments. -/
def allBinaryTables (m : Nat) : List (Fin m → Fin m → Fin m) :=
  allFunInto (allFunInto (finRange m) m) m

/-- **Exhaustivité binaire** : toute table binaire sur `Fin m` est dans
l'énumération. -/
theorem mem_allBinaryTables {m : Nat} (t : Fin m → Fin m → Fin m) :
    t ∈ allBinaryTables m :=
  mem_allFunInto_of_mem _ t (fun _ =>
    mem_allFunInto_of_mem _ _ (fun _ => mem_finRange _))

/-- **Compte binaire** : `m ^ (m²)` tables. -/
theorem allBinaryTables_length (m : Nat) :
    (allBinaryTables m).length = m ^ (m * m) := by
  simp only [allBinaryTables, allFunInto_length, finRange_length]
  rw [← Nat.pow_mul]

/-- Sur `Fin 2`, l'espace des tables binaires a exactement `2⁴ = 16`
éléments — la valeur que l'ancien `boolBinaryTableCount` documentaire
annonçait sans la calculer. -/
example : (allBinaryTables 2).length = 16 := by decide

/-! ## Tables ternaires (arité 3 = l'arité de la composée) -/

/-- **Toutes** les tables ternaires sur `Fin m` — `m ^ (m³)` éléments.
C'est l'espace où vit la composée de deux relations binaires (règle (3)
de l'Annexe A §1). -/
def allTernaryTables (m : Nat) : List (Fin m → Fin m → Fin m → Fin m) :=
  allFunInto (allBinaryTables m) m

/-- **Exhaustivité ternaire** : toute table ternaire sur `Fin m` est dans
l'énumération. -/
theorem mem_allTernaryTables {m : Nat} (t : Fin m → Fin m → Fin m → Fin m) :
    t ∈ allTernaryTables m :=
  mem_allFunInto_of_mem _ t (fun _ => mem_allBinaryTables _)

/-- **Compte ternaire** : `m ^ (m³)` tables. -/
theorem allTernaryTables_length (m : Nat) :
    (allTernaryTables m).length = m ^ (m * m * m) := by
  simp only [allTernaryTables, allFunInto_length, allBinaryTables_length]
  rw [← Nat.pow_mul]

-- Sur `Fin 2`, l'espace ternaire a exactement `2⁸ = 256` éléments.
set_option maxRecDepth 8000 in
example : (allTernaryTables 2).length = 256 := by decide

end Enumeration
