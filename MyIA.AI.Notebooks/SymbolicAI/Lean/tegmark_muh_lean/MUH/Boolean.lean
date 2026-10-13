import MUH.Structure
import MUH.Encoding

/-! # Algèbre de Boole (Tegmark R16 Annexe A §2a) — 1 générateur (Sheffer / NAND)

Tegmark (2007, Annexe A §2a) exhibe l'algèbre de Boole à 2 éléments comme
exemple de structure finie : un ensemble `S = {0, 1}` et 8 relations
génératrices (F, T, NOT, AND, OR, IMPLIES, XOR, NAND). Il montre ensuite
(equation (A2)) que la **même** structure est définie par un seul générateur
R (Sheffer / NAND), qui satisfait :
```
  F = (X|(X|X))|(X|(X|X)),  T = X|(X|X),  ¬X = X|X,
  X&Y = (X|Y)|(X|Y),        X∨Y = (X|X)|(Y|Y),   X→Y = X|(Y|Y),
  X⊕Y = (X|Y)|((X|X)|(Y|Y)), X≡Y = X|Y .
```

Ce module :
  - définit l'algèbre de Boole comme `Structure` (1 ensemble à 2 éléments,
    4 relations Booléennes — F, T, NOT, AND — Tegmark eq. (A1)),
  - définit la version « Sheffer » à 1 générateur NAND.

**Scope réel** : ce module **ne prouve pas** l'équivalence Sheffer ↔ 4
  générateurs ; il exhibe les deux encodages comme `Structure` distinctes. La
  preuve d'équivalence (même univers de relations accessibles par composition)
  est hors-scope de cette PR — voir #16958 pour le suivi. -/

namespace Boolean

/-- S = {0, 1} : le seul ensemble de l'algèbre de Boole à 2 éléments. -/
def boolSizes : Fin 1 → Nat := fun _ => 2

-- Ensemble des cardinaux `sizes_pos` : 1 seul ensemble de cardinal 2 > 0.
-- `0 < 2` est décidé par omega (pas de dépendance sur l'index).
example : (i : Fin 1) → 0 < boolSizes i := fun _ => by simp [boolSizes]

/-- La relation NAND : X|Y = ¬(X ∧ Y). Table de vérité :
    `NAND(0, 0) = 1, NAND(0, 1) = 1, NAND(1, 0) = 1, NAND(1, 1) = 0`.
    Sortie en `Fin 2` (0 = false, 1 = true), comme requis par `Rel.table`. -/
def nandTable : Fin 2 → Fin 2 → Fin 2 := fun
  | ⟨0, _⟩, ⟨0, _⟩ => ⟨1, by decide⟩   -- NAND(0,0) = 1
  | ⟨0, _⟩, ⟨1, _⟩ => ⟨1, by decide⟩   -- NAND(0,1) = 1
  | ⟨1, _⟩, ⟨0, _⟩ => ⟨1, by decide⟩   -- NAND(1,0) = 1
  | ⟨1, _⟩, ⟨1, _⟩ => ⟨0, by decide⟩   -- NAND(1,1) = 0

/-- La structure « Sheffer » : 1 ensemble {0,1}, 1 seule relation NAND
    (binaire). Tegmark equation (A2). -/
def sheffer : Structure :=
  { nSets := 1
  , sizes := boolSizes
  , rels := [{ sig := { arity := 2
                       , args := fun _ => (0 : Fin 1)
                       , out := (0 : Fin 1) }
             , table := fun args => nandTable (args 0) (args 1) }]
  , sizes_pos := fun _ => by simp [boolSizes] }

/-- La relation NOT (unaire) : NOT(0) = 1, NOT(1) = 0. Tegmark eq. (A2) :
    `¬X = X|X`. Sortie en `Fin 2`. -/
def notTable : Fin 2 → Fin 2
  | ⟨0, _⟩ => ⟨1, by decide⟩   -- NOT(0) = 1
  | ⟨1, _⟩ => ⟨0, by decide⟩   -- NOT(1) = 0

/-- La relation AND (binaire) : X&Y = (X|Y)|(X|Y) (Tegmark eq. (A2)).
    Sortie en `Fin 2`. -/
def andTable : Fin 2 → Fin 2 → Fin 2 := fun
  | ⟨0, _⟩, ⟨0, _⟩ => ⟨0, by decide⟩   -- 0&0 = 0
  | ⟨0, _⟩, ⟨1, _⟩ => ⟨0, by decide⟩   -- 0&1 = 0
  | ⟨1, _⟩, ⟨0, _⟩ => ⟨0, by decide⟩   -- 1&0 = 0
  | ⟨1, _⟩, ⟨1, _⟩ => ⟨1, by decide⟩   -- 1&1 = 1

/-- L'algèbre de Boole complète (4 générateurs : F, T, NOT, AND). Tegmark
    eq. (A1) — on omet IMPLIES, XOR, NAND qui s'obtiennent par composition
    de F/T/NOT/AND/NAND. -/
def fullBoolean : Structure :=
  { nSets := 1
  , sizes := boolSizes
  , rels := [
      -- F : constant False (arity 0) — tuple vide, table constante
      { sig := { arity := 0
               , args := fun i => i.elim0
               , out := (0 : Fin 1) }
      , table := fun _ => (0 : Fin 2) },
      -- T : constant True (arity 0) — tuple vide, table constante
      { sig := { arity := 0
               , args := fun i => i.elim0
               , out := (0 : Fin 1) }
      , table := fun _ => (1 : Fin 2) },
      -- NOT : arity 1, l'unique argument est `args 0 : Fin (boolSizes 0) = Fin 2`.
      { sig := { arity := 1
               , args := fun _ => (0 : Fin 1)
               , out := (0 : Fin 1) }
      , table := fun args => notTable (args 0) },
      -- AND : arity 2 (binaire), args de type `Fin 2`, sortie `Fin 2`.
      { sig := { arity := 2
               , args := fun _ => (0 : Fin 1)
               , out := (0 : Fin 1) }
      , table := fun args => andTable (args 0) (args 1) }
    ]
  , sizes_pos := fun _ => by simp [boolSizes] }

/-- Vérifie que `NAND(0, 0) = 1` — premier cas de la table de Sheffer. -/
example : nandTable (0 : Fin 2) (0 : Fin 2) = (1 : Fin 2) := rfl

/-- Vérifie que `NAND(1, 1) = 0` — dernier cas de la table de Sheffer. -/
example : nandTable (1 : Fin 2) (1 : Fin 2) = (0 : Fin 2) := rfl

/-- Vérifie que `NOT(0) = 1` — Tegmark eq. (A2) `¬X = X|X`, et `0|0 = 1`. -/
example : notTable (0 : Fin 2) = (1 : Fin 2) := rfl

/-- Rel unaire canonique (miroir du NOT de `fullBoolean`), servant de valeur
    par défaut pour extraire et évaluer la table du 3e générateur. -/
def defaultUnary : Rel 1 boolSizes :=
  { sig := { arity := 1, args := fun _ => (0 : Fin 1), out := (0 : Fin 1) }
    table := fun args => notTable (args 0) }

/-- Contre-exemple d'Hermes levé (concern #1, #16958) : au typing tuple,
    la relation NOT de `fullBoolean` n'est plus la constante 1 — `NOT(1) = 0`
    et `NOT(0) = 1`, évalués sur la structure elle-même. Au typing curryfié
    d'avant le fix, l'argument réel était ignoré (NOT(x) = 1 partout). -/
example : (fullBoolean.rels[2]?.getD defaultUnary).table
    (fun _ => (1 : Fin 2)) = (0 : Fin 2) := rfl

example : (fullBoolean.rels[2]?.getD defaultUnary).table
    (fun _ => (0 : Fin 2)) = (1 : Fin 2) := rfl

/-! ## Les identités de Sheffer (Tegmark R16 Annexe A, eq. (A2))

Tegmark affirme que le seul générateur NAND (Sheffer) redéfinit toute
l'algèbre de Boole : chaque connectique s'écrit par composition de `|`.
Les théorèmes ci-dessous **prouvent** les six identités dont l'énoncé
est vrai sur la table à 2 éléments — F, T, ¬, &, ∨, → — par épuisement
des cas (`forall_fin2`, `forall_fin2_fin2`).

Note d'honnêteté : les deux dernières identités citées dans l'en-tête
de ce module (`X⊕Y = (X|Y)|((X|X)|(Y|Y))` et `X≡Y = X|Y`) **ne sont pas
des identités** de la table NAND à 2 éléments — p.ex. `X|Y` en (1,1)
vaut 0 alors que X≡Y y vaut 1. Elles ne sont pas prouvées ici ; la
formulation exacte de l'éq. (A2) du papier demande vérification avant
toute formalisation. -/

/-- La relation OR (binaire) : X∨Y = (X|X)|(Y|Y) (Tegmark eq. (A2)).
    Table : 0∨0=0, 0∨1=1, 1∨0=1, 1∨1=1. -/
def orTable : Fin 2 → Fin 2 → Fin 2 := fun
  | ⟨0, _⟩, ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨0, _⟩, ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩, ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩, ⟨1, _⟩ => ⟨1, by decide⟩

/-- La relation IMPLIES (binaire) : X→Y = X|(Y|Y) (Tegmark eq. (A2)).
    Table : 0→0=1, 0→1=1, 1→0=0, 1→1=1. -/
def impliesTable : Fin 2 → Fin 2 → Fin 2 := fun
  | ⟨0, _⟩, ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨0, _⟩, ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩, ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩, ⟨1, _⟩ => ⟨1, by decide⟩

/-- **Tegmark (A2), constante T** : `T = X|(X|X)` — pour tout X, le
    NAND de X et de ¬X vaut toujours 1. -/
theorem tegmark_T (x : Fin 2) :
    nandTable x (nandTable x x) = (1 : Fin 2) :=
  forall_fin2
    (P := fun a => nandTable a (nandTable a a) = (1 : Fin 2)) rfl rfl x

/-- **Tegmark (A2), constante F** : `F = (X|(X|X))|(X|(X|X))` — le NAND
    de T avec lui-même vaut toujours 0. -/
theorem tegmark_F (x : Fin 2) :
    nandTable (nandTable x (nandTable x x))
              (nandTable x (nandTable x x)) = (0 : Fin 2) :=
  forall_fin2
    (P := fun a => nandTable (nandTable a (nandTable a a))
              (nandTable a (nandTable a a)) = (0 : Fin 2)) rfl rfl x

/-- **Tegmark (A2), négation** : `¬X = X|X` — NOT s'obtient par NAND
    de X avec lui-même. -/
theorem tegmark_not (x : Fin 2) :
    notTable x = nandTable x x :=
  forall_fin2 (P := fun a => notTable a = nandTable a a) rfl rfl x

/-- **Tegmark (A2), conjonction** : `X&Y = (X|Y)|(X|Y)` — AND est le
    NAND du NAND. -/
theorem tegmark_and (x y : Fin 2) :
    andTable x y = nandTable (nandTable x y) (nandTable x y) :=
  forall_fin2_fin2
    (P := fun a b => andTable a b = nandTable (nandTable a b) (nandTable a b))
    rfl rfl rfl rfl x y

/-- **Tegmark (A2), disjonction** : `X∨Y = (X|X)|(Y|Y)` — OR par loi de
    De Morgan via NAND. -/
theorem tegmark_or (x y : Fin 2) :
    orTable x y = nandTable (nandTable x x) (nandTable y y) :=
  forall_fin2_fin2
    (P := fun a b => orTable a b = nandTable (nandTable a a) (nandTable b b))
    rfl rfl rfl rfl x y

/-- **Tegmark (A2), implication** : `X→Y = X|(Y|Y)`. -/
theorem tegmark_implies (x y : Fin 2) :
    impliesTable x y = nandTable x (nandTable y y) :=
  forall_fin2_fin2
    (P := fun a b => impliesTable a b = nandTable a (nandTable b b))
    rfl rfl rfl rfl x y

end Boolean