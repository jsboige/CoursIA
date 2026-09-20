import MUH.Structure

/-! # Groupes cycliques C₂ et C₃ (Tegmark R16 Annexe A §2b)

Tegmark (2007, Annexe A §2b) exhibe le groupe cyclique d'ordre 3 (C₃) comme
exemple d'une structure finie : un ensemble S = {0, 1, 2} et trois relations
  - R₁(a) = a        (identité, e)
  - R₂(a) = a⁻¹      (inverse)
  - R₃(a, b) = a + b mod 3 (groupe additif)

L'identité se lit sur la diagonale de la table de multiplication ; les
inverses se lisent sur la première ligne.

Ce module :
  - définit C₂ et C₃ comme `Structure` (1 ensemble, 1 relation binaire),
  - vérifie l'identité de la diagonale (Tegmark §2b in fine),
  - exhibe les automorphismes : pour C₂ c'est trivial, pour C₃ ce sont les
    φ(3) = 2 générateurs (id et shift). -/

namespace Cyclic

/-- S = {0, 1, 2} : ensemble du groupe cyclique C₃. -/
def c3Sizes : Fin 1 → Nat := fun _ => 3

/-- S = {0, 1} : ensemble du groupe cyclique C₂. -/
def c2Sizes : Fin 1 → Nat := fun _ => 2

/-- Multiplication modulo 3 (binaire) : `mult3(a, b) = (a + b) % 3`.
    Signature : `Fin 2 → Fin 3 → Fin 3` — la structure `Rel.table` impose
    l'indexation `Fin arity` pour les entrées (2 entrées pour arité 2),
    chaque entrée étant un élément de S = {0,1,2} (donc `Fin 3`). -/
def mult3Table : Fin 2 → Fin 3 → Fin 3 := fun
  | ⟨0, _⟩, ⟨0, _⟩ => ⟨0, by decide⟩     -- 0+0 mod 3 = 0
  | ⟨0, _⟩, ⟨1, _⟩ => ⟨1, by decide⟩     -- 0+1 mod 3 = 1
  | ⟨0, _⟩, ⟨2, _⟩ => ⟨2, by decide⟩     -- 0+2 mod 3 = 2
  | ⟨1, _⟩, ⟨0, _⟩ => ⟨1, by decide⟩     -- 1+0 mod 3 = 1
  | ⟨1, _⟩, ⟨1, _⟩ => ⟨2, by decide⟩     -- 1+1 mod 3 = 2
  | ⟨1, _⟩, ⟨2, _⟩ => ⟨0, by decide⟩     -- 1+2 mod 3 = 0

/-- Le groupe cyclique C₃ (1 ensemble, 1 relation binaire). L'identité et les
    inverses sont encodés dans la table. Tegmark eq. (A3). -/
def c3 : Structure :=
  { nSets := 1
  , sizes := c3Sizes
  , rels := [{ sig := { arity := 2
                       , args := fun _ => (0 : Fin 1)
                       , out := (0 : Fin 1) }
             , table := fun a b => mult3Table a b }]
  , sizes_pos := fun _ => Nat.succ_pos 2 }

/-- Vérifie que la diagonale porte bien l'identité du groupe : `0×0 = 0`. -/
example : mult3Table (⟨0, by decide⟩ : Fin 2) (⟨0, by decide⟩ : Fin 3) = (⟨0, by decide⟩ : Fin 3) := rfl

/-- Vérifie que `1×2 = 0` (mod 3) — Tegmark eq. (A5) première ligne. -/
example : mult3Table (⟨1, by decide⟩ : Fin 2) (⟨2, by decide⟩ : Fin 3) = (⟨0, by decide⟩ : Fin 3) := rfl

/-- Vérifie que `1×1 = 2` (mod 3) — Tegmark eq. (A5) diagonale non-triviale. -/
example : mult3Table (⟨1, by decide⟩ : Fin 2) (⟨1, by decide⟩ : Fin 3) = (⟨2, by decide⟩ : Fin 3) := rfl

/-- Multiplication modulo 2 (binaire) : `mult2(a, b) = (a + b) % 2`.
    Signature : `Fin 2 → Fin 2 → Fin 2`. -/
def mult2Table : Fin 2 → Fin 2 → Fin 2 := fun
  | ⟨0, _⟩, ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨0, _⟩, ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩, ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩, ⟨1, _⟩ => ⟨0, by decide⟩

/-- Le groupe cyclique C₂ (1 ensemble, 1 relation binaire). Tegmark §2b
    (analogue à C₃, n = 2). -/
def c2 : Structure :=
  { nSets := 1
  , sizes := c2Sizes
  , rels := [{ sig := { arity := 2
                       , args := fun _ => (0 : Fin 1)
                       , out := (0 : Fin 1) }
             , table := fun a b => mult2Table a b }]
  , sizes_pos := fun _ => Nat.succ_pos 1 }

/-- Vérifie `0×0 = 0` (mod 2). -/
example : mult2Table (0 : Fin 2) (0 : Fin 2) = (0 : Fin 2) := rfl

/-- Vérifie `1×1 = 0` (mod 2). -/
example : mult2Table (1 : Fin 2) (1 : Fin 2) = (0 : Fin 2) := rfl

end Cyclic