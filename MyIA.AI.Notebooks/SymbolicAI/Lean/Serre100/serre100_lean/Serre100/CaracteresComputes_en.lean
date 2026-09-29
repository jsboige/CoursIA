import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Character tables computed by the kernel: Schur orthogonality verified

Kernel pendant of the notebook `05-table-de-caracteres.ipynb` (series
*Serre 100*, EPIC #16334 — "kernel pendants" graduation path). The
notebook *measures* in Python the character tables of S₃ and S₄
(Murnaghan–Nakayama rule) and checks the two Schur orthogonality
families; this module has the Lean kernel verify the same tables, and
proves the notebook's independent witnesses directly on `Equiv.Perm`.

Plan, mirroring the notebook (§1 and §2):

1. **Definitions** (`tableS3`, `taillesClassesS3`, `tableS4`,
   `taillesClassesS4`, `indiceClasseS3`, `indiceClasseS4`) — the tables
   are the notebook's data, row by row; the column index of a
   permutation is read off its fixed points and `σ²`.
2. **Witnesses on `Equiv.Perm`**: the sign row of each table IS the sign
   of every permutation (an equality in `ℤˣ`), and the standard
   character is fixed points − 1 — the notebook's "exact coincidences",
   proved on the whole group rather than observed on classes.
3. **Orthogonality**: rows (`∑ |C| χᵢ χⱼ = |G| δ`) and columns
   (`∑ χᵢ(C) χᵢ(C') = (|G|/|C|) δ`) for S₃ and S₄, by the kernel.
4. **Degrees**: the general lemma `sommeCarresDegres` derives
   `∑ d² = |G|` from column orthogonality, then instantiates on both
   tables; the degrees of 2T (§3 of the notebook, seven irreducibles)
   verify `∑ d² = 24`.

Out of scope (documented): the table of 2T lives over ℚ(√−3) — its
non-rational values require a coefficient ring (`AdjoinRoot`,
cyclotomic field) and await a dedicated pendant; the
Murnaghan–Nakayama recursion itself stays on the Python side of the
notebook.
-/

set_option autoImplicit false

namespace Serre100_en

/-! ## Definitions — the notebook's tables, as data

Rows = partitions (characters), columns = conjugacy classes.
S₃: rows `(3)`, `(2,1)`, `(1³)` over the classes `1³` (size 1), `2·1`
(size 3), `3` (size 2). S₄: rows `(4)`, `(3,1)`, `(2,2)`, `(2,1,1)`,
`(1⁴)` over the classes of sizes 1, 6, 3, 8, 6.
-/

/-- Character table of S₃ (notebook, "table of S₃" cell): rows
`(3)`, `(2,1)`, `(1³)`; columns `1³`, `2·1`, `3`. -/
def tableS3 : Fin 3 → Fin 3 → ℤ :=
  ![![1, 1, 1], ![2, 0, -1], ![1, -1, 1]]

/-- Sizes of the conjugacy classes of S₃: 1, 3, 2. -/
def taillesClassesS3 : Fin 3 → ℤ := ![1, 3, 2]

/-- Character table of S₄ (notebook, "table of S₄" cell): rows
`(4)`, `(3,1)`, `(2,2)`, `(2,1,1)`, `(1⁴)`; columns `1⁴`, `2·1²`,
`2²`, `3·1`, `4`. -/
def tableS4 : Fin 5 → Fin 5 → ℤ :=
  ![![1, 1, 1, 1, 1],
    ![3, 1, -1, 0, -1],
    ![2, 0, 2, -1, 0],
    ![3, -1, -1, 0, 1],
    ![1, -1, 1, 1, -1]]

/-- Sizes of the conjugacy classes of S₄: 1, 6, 3, 8, 6. -/
def taillesClassesS4 : Fin 5 → ℤ := ![1, 6, 3, 8, 6]

/-- Number of fixed points of a permutation of `Fin n`: the fixed
points are the `x` such that `σ x = x` (notebook, `points_fixes`). -/
def pointsFixes {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun x => σ x = x)).card

/-- Column index of `σ` in the S₃ table, read off its fixed points:
3 fixed points (identity), 1 (transposition), 0 (3-cycle). -/
def indiceClasseS3 (σ : Equiv.Perm (Fin 3)) : Fin 3 :=
  if pointsFixes σ = 3 then 0
  else if pointsFixes σ = 1 then 1
  else 2

/-- Column index of `σ` in the S₄ table, read off its fixed points and
`σ²`: 4 fixed points (`1⁴`), 2 (`2·1²`), 1 (`3·1`); without a fixed
point, `σ² = 1` tells the `2²` type from the `4` type. -/
def indiceClasseS4 (σ : Equiv.Perm (Fin 4)) : Fin 5 :=
  if pointsFixes σ = 4 then 0
  else if pointsFixes σ = 2 then 1
  else if pointsFixes σ = 1 then 3
  else if σ * σ = 1 then 2
  else 4

/-! ## The notebook's witnesses, proved on `Equiv.Perm`

The notebook checks its tables against independent witnesses (cells
"expected standard (pf − 1)" and "expected sign (−1)^(n−cyc)"); the
kernel proves them here for **every permutation**, the table being read
through `indiceClasse`. The sign equality lives in `ℤˣ` — the target
group of `Equiv.Perm.sign` — without a coercion to `ℤ`.
-/

/-- Sign row of S₃, as values in `ℤˣ` (the `(1³)` row of the table,
reread in the target group of the sign). -/
def tableSigneS3 : Fin 3 → ℤˣ := ![1, -1, 1]

/-- Sign row of S₄, as values in `ℤˣ` (the `(1⁴)` row of the table). -/
def tableSigneS4 : Fin 5 → ℤˣ := ![1, -1, 1, 1, -1]

/-- Sign witness of S₃: the `(1³)` row of the table is the sign of
every permutation (6 elements covered by the kernel). -/
theorem temoinSigneS3 : ∀ σ : Equiv.Perm (Fin 3),
    Equiv.Perm.sign σ = tableSigneS3 (indiceClasseS3 σ) := by decide

/-- Standard witness of S₃: the character of the standard
representation (row `(2,1)`) is fixed points − 1 on every permutation. -/
theorem temoinStandardS3 : ∀ σ : Equiv.Perm (Fin 3),
    (pointsFixes σ : ℤ) - 1 = tableS3 1 (indiceClasseS3 σ) := by decide

/-- Sign witness of S₄: the `(1⁴)` row of the table is the sign of
every permutation (24 elements covered by the kernel). -/
theorem temoinSigneS4 : ∀ σ : Equiv.Perm (Fin 4),
    Equiv.Perm.sign σ = tableSigneS4 (indiceClasseS4 σ) := by decide

/-- Standard witness of S₄: the `(3,1)` row is fixed points − 1. -/
theorem temoinStandardS4 : ∀ σ : Equiv.Perm (Fin 4),
    (pointsFixes σ : ℤ) - 1 = tableS4 1 (indiceClasseS4 σ) := by decide

/-- Twist witness of S₄: the `(2,1,1)` row is the standard character
times the sign row — exercise 3 of the notebook, ahead of schedule (both
factors are reread in the same table; the second is the `(1⁴)` row,
equal to the sign by `temoinSigneS4`). -/
theorem temoinStandardSigneS4 : ∀ σ : Equiv.Perm (Fin 4),
    tableS4 3 (indiceClasseS4 σ)
      = ((pointsFixes σ : ℤ) - 1) * tableS4 4 (indiceClasseS4 σ) := by decide

/-! ## Schur orthogonality — both families, by the kernel

Rows (notebook, cell 8): `∑_C |C| χᵢ(C) χⱼ(C) = |G| δᵢⱼ` — the table is
an orthonormal family for the form weighted by the class sizes.
Columns: `∑ᵢ χᵢ(C) χᵢ(C') = (|G|/|C|) δ_CC'`.
-/

/-- Row orthogonality for S₃ (6 pairs covered, weights = class sizes). -/
theorem orthogonaliteLignesS3 : ∀ i j : Fin 3,
    ∑ k, taillesClassesS3 k * tableS3 i k * tableS3 j k
      = if i = j then 6 else 0 := by decide

/-- Column orthogonality for S₃ (9 pairs covered). -/
theorem orthogonaliteColonnesS3 : ∀ j k : Fin 3,
    ∑ i, tableS3 i j * tableS3 i k
      = if j = k then 6 / taillesClassesS3 k else 0 := by decide

/-- Row orthogonality for S₄ (the 15 pairs of the upper triangle and
the diagonal, extended to all ordered pairs). -/
theorem orthogonaliteLignesS4 : ∀ i j : Fin 5,
    ∑ k, taillesClassesS4 k * tableS4 i k * tableS4 j k
      = if i = j then 24 else 0 := by decide

/-- Column orthogonality for S₄ (25 pairs covered). -/
theorem orthogonaliteColonnesS4 : ∀ j k : Fin 5,
    ∑ i, tableS4 i j * tableS4 i k
      = if j = k then 24 / taillesClassesS4 k else 0 := by decide

/-! ## Degrees — a consequence of column orthogonality

The notebook reads `∑ d² = |G|` as a sanity check; it is in fact column
orthogonality evaluated at the neutral class (centralizer 1). The
general lemma below derives it once for any table, then instantiates.
-/

/-- From column orthogonality, the sum of squared degrees (first
column = neutral class, size 1) equals the order of the group. -/
theorem sommeCarresDegres {n : ℕ} [NeZero n] (T : Fin n → Fin n → ℤ) (G : ℤ) (c : Fin n → ℤ)
    (hcol : ∀ j k : Fin n, ∑ i, T i j * T i k = if j = k then G / c k else 0)
    (hc1 : c 0 = 1) : ∑ i, T i 0 * T i 0 = G := by
  simpa [hc1] using hcol 0 0

/-- Degrees of S₃: `1 + 4 + 1 = 6 = |S₃|` — the notebook's size check,
derived from orthogonality. -/
example : ∑ i, tableS3 i 0 * tableS3 i 0 = 6 :=
  sommeCarresDegres tableS3 6 taillesClassesS3 orthogonaliteColonnesS3 rfl

/-- Degrees of S₄: `1 + 9 + 4 + 9 + 1 = 24 = |S₄|` — the
`sum d^2 = 24` of cell 8 of the notebook, derived rather than
observed. -/
example : ∑ i, tableS4 i 0 * tableS4 i 0 = 24 :=
  sommeCarresDegres tableS4 24 taillesClassesS4 orthogonaliteColonnesS4 rfl

/-- The transposition column: sum of squares `4 = 24/6 = |G|/|C|` —
the last numeric check of cell 8 of the notebook. -/
theorem carresTranspositionsS4 :
    ∑ i, tableS4 i 1 * tableS4 i 1 = 4 := by
  simpa [taillesClassesS4] using orthogonaliteColonnesS4 1 1

/-! ## The degrees of 2T — seven irreducibles, without the table

The notebook (§3, cell "the full 7×7 table of 2T over ℚ(√−3)") obtains
the degrees of 2T (the binary tetrahedral group, 24 elements): three
linear characters (factors through C₃), three twists of the natural
character, and one 3-dim SO(3) — i.e. `1, 1, 1, 2, 2, 2, 3`. The table
itself lives over ℚ(√−3) and awaits a dedicated pendant (see the
module header); the sum of squares is already an integer statement. -/

/-- Degrees of the seven irreducible representations of 2T (notebook
§3). -/
def degres2T : Fin 7 → ℤ := ![1, 1, 1, 2, 2, 2, 3]

/-- `1 + 1 + 1 + 4 + 4 + 4 + 9 = 24 = |2T|`: the notebook's size
check, by the kernel. -/
example : ∑ i, degres2T i ^ 2 = 24 := by decide

end Serre100_en
