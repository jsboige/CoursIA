import MUH.Aut
import MUH.Cyclic

/-! # Automorphismes concrets : C₂ et C₃ (Tegmark R16 Annexe A §2b)

Tegmark (2007, Annexe A §2b) lit les automorphismes d'une structure finie
sur sa table de multiplication. Ce module calcule **explicitement** le
groupe d'automorphismes des deux groupes cycliques de `MUH.Cyclic` :

  - **C₃ = (Z/3, +)** : `Aut(C₃) = {id, x ↦ 2x}` — deux éléments. Le
    « shift » `x ↦ x+1` n'est **pas** un automorphisme : il ne préserve
    pas la table (`φ(0+0) = 1` mais `φ(0)+φ(0) = 2`).
  - **C₂ = (Z/2, +)** : `Aut(C₂) = {id}` — un seul élément. L'échange
    `x ↦ x+1` échoue pareillement (`φ(1+1) = φ(0) = 1` mais
    `φ(1)+φ(1) = 0+0 = 0`).

Les théorèmes d'**exhaustivité** (`c3_auto`, `c2_auto`) prouvent qu'il
n'y en a pas d'autres : tout automorphisme de C₃ est l'identité ou le
doublement, tout automorphisme de C₂ est l'identité. La démonstration
lit la table exactement comme Tegmark la décrit : la diagonale fixe
l'image de 0 (`0+0 = 0`), la ligne `1+2 = 0` propage la contrainte, et
l'injectivité exclut les valeurs déjà prises.

L'analyse par cas vit dans des **cœurs combinatoires** (`c3_auto_core`,
`c2_auto_core`) énoncés sur des fonctions `Fin 3 → Fin 3` / `Fin 2 → Fin 2`
pures : les littéraux y sont bien typés. Les théorèmes finaux appliquent
ces cœurs à `φ.φ 0` — la coercition `Fin (c3On.sizes 0) ≡ Fin 3` est
définitionnelle. Les structures `c3On`/`c2On` sont les ponts
`Cyclic → Aut.StructureOn` : mêmes cardinaux, même relation binaire
(même table) que `Cyclic.c3` / `Cyclic.c2`, sous la forme paramétrique
attendue par `MUH.Aut`. -/

namespace Examples

open Cyclic Aut

/-! ## Ponts `Cyclic → Aut.StructureOn` -/

/-- La relation binaire « addition mod 3 » sous la forme `Rel` attendue
    par `StructureOn` (miroir de l'unique relation de `Cyclic.c3`,
    même table `mult3Table`). -/
def c3Rel : Rel 1 c3Sizes where
  sig := { arity := 2, args := fun _ => (0 : Fin 1), out := (0 : Fin 1) }
  table := fun args => mult3Table (args 0) (args 1)

/-- C₃ vu comme `Aut.StructureOn` : 1 ensemble à 3 éléments, la seule
    relation binaire d'addition. -/
def c3On : Aut.StructureOn 1 where
  sizes := c3Sizes
  sizes_pos := fun _ => Nat.succ_pos 2
  rels := [c3Rel]

/-- La relation binaire « addition mod 2 » sous la forme `Rel` (miroir
    de l'unique relation de `Cyclic.c2`, même table `mult2Table`). -/
def c2Rel : Rel 1 c2Sizes where
  sig := { arity := 2, args := fun _ => (0 : Fin 1), out := (0 : Fin 1) }
  table := fun args => mult2Table (args 0) (args 1)

/-- C₂ vu comme `Aut.StructureOn` : 1 ensemble à 2 éléments, la seule
    relation binaire. -/
def c2On : Aut.StructureOn 1 where
  sizes := c2Sizes
  sizes_pos := fun _ => Nat.succ_pos 1
  rels := [c2Rel]

/-- Appartenance de la relation unique de C₃ à sa structure. -/
theorem c3Rel_mem : c3Rel ∈ c3On.rels := List.Mem.head _

/-- Appartenance de la relation unique de C₂ à sa structure. -/
theorem c2Rel_mem : c2Rel ∈ c2On.rels := List.Mem.head _

/-! ## L'automorphisme non trivial de C₃ : x ↦ 2x -/

/-- La permutation `x ↦ 2x (mod 3)` — le seul candidat non trivial
    d'automorphisme de C₃ (l'image d'un générateur par un générateur). -/
def c3Double : Fin 3 → Fin 3 := fun x => ⟨(2 * x.val) % 3, by omega⟩

/-- `x ↦ 2x` préserve la table d'addition de C₃ : `2(a+b) = 2a + 2b`
    (mod 3), case par case sur la table 3×3. -/
theorem c3Double_table (a b : Fin 3) :
    c3Double (mult3Table a b) = mult3Table (c3Double a) (c3Double b) := by
  cases a with
  | mk va ha =>
    cases b with
    | mk vb hb =>
      match va, vb with
      | 0, 0 => simp [c3Double, mult3Table]
      | 0, 1 => simp [c3Double, mult3Table]
      | 0, 2 => simp [c3Double, mult3Table]
      | 1, 0 => simp [c3Double, mult3Table]
      | 1, 1 => simp [c3Double, mult3Table]
      | 1, 2 => simp [c3Double, mult3Table]
      | 2, 0 => simp [c3Double, mult3Table]
      | 2, 1 => simp [c3Double, mult3Table]
      | 2, 2 => simp [c3Double, mult3Table]
      | n + 3, _ => exact absurd ha (by omega)
      | _, n + 3 => exact absurd hb (by omega)

/-- La même préservation, en forme « args » : c'est sous cette forme
    que le but `rel_pres` se consomme (la table appliquée à un tuple). -/
theorem c3Double_args (args : (i : Fin 2) → Fin 3) :
    c3Double (mult3Table (args 0) (args 1)) =
      mult3Table (c3Double (args 0)) (c3Double (args 1)) :=
  c3Double_table (args 0) (args 1)

/-- `x ↦ 2x` est injective sur `Fin 3` (énumération des 9 couples). -/
theorem c3Double_inj : Function.Injective c3Double := by
  intro x y h
  cases x with
  | mk vx hx =>
    cases y with
    | mk vy hy =>
      simp only [Fin.mk.injEq, c3Double] at h
      simp only [Fin.mk.injEq]
      match vx, vy with
      | 0, 0 => rfl
      | 0, 1 => omega
      | 0, 2 => omega
      | 1, 0 => omega
      | 1, 1 => rfl
      | 1, 2 => omega
      | 2, 0 => omega
      | 2, 1 => omega
      | 2, 2 => rfl
      | n + 3, _ => omega
      | _, n + 3 => omega

/-- **x ↦ 2x est un automorphisme de C₃.** -/
def c3DoubleAuto : Aut.IsAutomorphism c3On where
  φ := fun _ => c3Double
  φ_inj := fun _ => c3Double_inj
  rel_pres := by
    intro r hmem args
    have h' : r = c3Rel := List.mem_singleton.mp hmem
    subst h'
    exact c3Double_args args

/-- Le doublement est involutif : `2·2x = 4x ≡ x (mod 3)` — il est son
    propre inverse dans Aut(C₃). -/
theorem c3Double_c3Double (x : Fin 3) : c3Double (c3Double x) = x := by
  cases x with
  | mk v h =>
    match v with
    | 0 => simp [c3Double]
    | 1 => simp [c3Double]
    | 2 => simp [c3Double]
    | n + 3 => exact absurd h (by omega)

/-- `x ↦ 2x` comme **élément du groupe** `Aut(C₃)` : son inverse porté
    est lui-même (involutif). -/
def c3DoubleAut : Aut c3On where
  toAuto := c3DoubleAuto
  inv := c3DoubleAuto
  rinv := by
    apply isAuto_eq
    funext i x
    exact c3Double_c3Double x
  linv := by
    apply isAuto_eq
    funext i x
    exact c3Double_c3Double x

/-- Le doublement n'est pas l'identité : `2·1 = 2 ≠ 1`. -/
example : c3Double (1 : Fin 3) = (2 : Fin 3) := rfl

/-! ## Exhaustivité : Aut(C₃) = {id, x ↦ 2x} -/

/-- Le tuple `(a, b) : Fin 2 → Fin 3` comme argument de la relation
    binaire de C₃. -/
def pair3 (a b : Fin 3) : (i : Fin 2) → Fin 3 :=
  fun i =>
    match i with
    | ⟨0, _⟩ => a
    | ⟨1, _⟩ => b
    | ⟨n + 2, h⟩ => absurd h (by omega)

/-- Le tuple `(a, b) : Fin 2 → Fin 2` comme argument de la relation
    binaire de C₂. -/
def pair2 (a b : Fin 2) : (i : Fin 2) → Fin 2 :=
  fun i =>
    match i with
    | ⟨0, _⟩ => a
    | ⟨1, _⟩ => b
    | ⟨n + 2, h⟩ => absurd h (by omega)

/-- **Cœur combinatoire de l'exhaustivité C₃**, énoncé sur une fonction
    `Fin 3 → Fin 3` pure : une permutation injective qui préserve la
    table d'addition est l'identité ou le doublement.

    Schéma : l'image de 0 est fixée par la diagonale (`0+0 = 0`), puis
    `1+2 = 0` et l'injectivité laissent à l'image de 1 exactement deux
    choix, qui déterminent toute la permutation. -/
theorem c3_auto_core {g : Fin 3 → Fin 3}
    (hinj : Function.Injective g)
    (htab : ∀ a b : Fin 3, g (mult3Table a b) = mult3Table (g a) (g b)) :
    (∀ x, g x = x) ∨ (∀ x, g x = c3Double x) := by
  -- L'image de 0 : la diagonale 0+0 = 0 force g 0 = 0.
  have e00 : g (0 : Fin 3) = mult3Table (g (0 : Fin 3)) (g (0 : Fin 3)) :=
    htab 0 0
  have h0 : g (0 : Fin 3) = (0 : Fin 3) := by
    cases hx : g (0 : Fin 3) with
    | mk v hv =>
      rw [hx] at e00
      match v with
      | 0 => rfl
      | 1 => exact absurd e00 (by simp [mult3Table])
      | 2 => exact absurd e00 (by simp [mult3Table])
      | n + 3 => exact absurd hv (by omega)
  -- L'image de 1 ne peut être 0 (déjà prise, et g injective).
  have h1ne0 : g (1 : Fin 3) ≠ (0 : Fin 3) := by
    intro h1
    have h01 : g (0 : Fin 3) = g (1 : Fin 3) := by rw [h0, h1]
    exact absurd (hinj h01) (by decide)
  -- Deux cas : g 1 = 1 (identité) ou g 1 = 2 (doublement).
  have e12 : g (0 : Fin 3) =
      mult3Table (g (1 : Fin 3)) (g (2 : Fin 3)) :=
    htab 1 2
  cases hy : g (1 : Fin 3) with
  | mk v hv =>
    match v with
    | 0 => exact absurd hy h1ne0
    | 1 =>
      -- g 1 = 1 : la ligne 1+2 = 0 force g 2 = 2, donc g = id.
      have h2 : g (2 : Fin 3) = (2 : Fin 3) := by
        rw [h0, hy] at e12
        cases hz : g (2 : Fin 3) with
        | mk w hw =>
          rw [hz] at e12
          match w with
          | 0 => exact absurd e12 (by simp [mult3Table])
          | 1 => exact absurd e12 (by simp [mult3Table])
          | 2 => rfl
          | n + 3 => exact absurd hw (by omega)
      left
      exact forall_fin3 (P := fun y => g y = y) h0 hy h2
    | 2 =>
      -- g 1 = 2 : la ligne 1+2 = 0 force g 2 = 1, donc g = doublement.
      have h2 : g (2 : Fin 3) = (1 : Fin 3) := by
        rw [h0, hy] at e12
        cases hz : g (2 : Fin 3) with
        | mk w hw =>
          rw [hz] at e12
          match w with
          | 0 => exact absurd e12 (by simp [mult3Table])
          | 1 => rfl
          | 2 => exact absurd e12 (by simp [mult3Table])
          | n + 3 => exact absurd hw (by omega)
      right
      exact forall_fin3 (P := fun y => g y = c3Double y) h0 hy h2
    | n + 3 => exact absurd hv (by omega)

/-- **Exhaustivité pour C₃** : tout automorphisme de C₃ est l'identité
    ou le doublement `x ↦ 2x`. Autrement dit `Aut(C₃)` a exactement deux
    éléments (distincts, voir `c3Double 1 = 2` ci-dessus). -/
theorem c3_auto (φ : Aut.IsAutomorphism c3On) :
    φ = Aut.autId c3On ∨ φ = c3DoubleAuto := by
  have hcore : (∀ x : Fin 3, φ.φ (0 : Fin 1) x = x) ∨
      (∀ x : Fin 3, φ.φ (0 : Fin 1) x = c3Double x) :=
    c3_auto_core (φ.φ_inj (0 : Fin 1))
      (fun a b => φ.rel_pres c3Rel c3Rel_mem (pair3 a b))
  rcases hcore with hfun | hfun
  · left
    apply isAuto_eq
    funext i x
    cases i with
    | mk vi hi =>
      match vi with
      | 0 => exact hfun x
      | n + 1 => exact absurd hi (by omega)
  · right
    apply isAuto_eq
    funext i x
    cases i with
    | mk vi hi =>
      match vi with
      | 0 => exact hfun x
      | n + 1 => exact absurd hi (by omega)

/-! ## C₂ : le groupe d'automorphismes est trivial -/

/-- **Cœur combinatoire de l'exhaustivité C₂** : une permutation
    injective de `Fin 2` qui préserve la table d'addition est
    l'identité.

    L'échange `x ↦ x+1` échoue : `φ(1+1) = φ(0) = 1` mais
    `φ(1)+φ(1) = 0+0 = 0` — c'est l'**injectivité** qui tue le cas
    `g 1 = 0` (la table seule l'autorise : l'application constante 0
    préserve la table mais n'est pas injective). -/
theorem c2_auto_core {g : Fin 2 → Fin 2}
    (hinj : Function.Injective g)
    (htab : ∀ a b : Fin 2, g (mult2Table a b) = mult2Table (g a) (g b)) :
    ∀ x, g x = x := by
  -- L'image de 0 : la diagonale force g 0 = 0.
  have e00 : g (0 : Fin 2) = mult2Table (g (0 : Fin 2)) (g (0 : Fin 2)) :=
    htab 0 0
  have h0 : g (0 : Fin 2) = (0 : Fin 2) := by
    cases hx : g (0 : Fin 2) with
    | mk v hv =>
      rw [hx] at e00
      match v with
      | 0 => rfl
      | 1 => exact absurd e00 (by simp [mult2Table])
      | n + 2 => exact absurd hv (by omega)
  -- g 1 ≠ 0 par injectivité, donc g 1 = 1 : l'identité.
  have h1 : g (1 : Fin 2) = (1 : Fin 2) := by
    cases hy : g (1 : Fin 2) with
    | mk v hv =>
      match v with
      | 0 =>
        have h01 : g (0 : Fin 2) = g (1 : Fin 2) := by rw [h0, hy]; rfl
        exact absurd (hinj h01) (by decide)
      | 1 => rfl
      | n + 2 => exact absurd hv (by omega)
  exact forall_fin2 (P := fun y => g y = y) h0 h1

/-- **Exhaustivité pour C₂** : tout automorphisme de C₂ est l'identité —
    le groupe d'automorphismes est trivial. -/
theorem c2_auto (φ : Aut.IsAutomorphism c2On) :
    φ = Aut.autId c2On := by
  have hfun : ∀ x : Fin 2, φ.φ (0 : Fin 1) x = x :=
    c2_auto_core (φ.φ_inj (0 : Fin 1))
      (fun a b => φ.rel_pres c2Rel c2Rel_mem (pair2 a b))
  apply isAuto_eq
  funext i x
  cases i with
  | mk vi hi =>
    match vi with
    | 0 => exact hfun x
    | n + 1 => exact absurd hi (by omega)

end Examples
