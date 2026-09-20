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
  - définit la version « Sheffer » à 1 générateur NAND,
  - **ne prouve pas** l'équivalence Sheffer ↔ 4 générateurs. Cette équivalence
    est référencée dans le texte Tegmark (eq. (A2)) mais sa formalisation
    constructive en Lean 4 (composition mutuelle, clôture par composition) est
    **hors-scope** de cette introduction. Suivi #16958. -/

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

end Boolean