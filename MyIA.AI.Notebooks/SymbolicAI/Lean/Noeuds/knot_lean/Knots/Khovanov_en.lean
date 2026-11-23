/-
  Knots.Khovanov_en — Khovanov homology of the trefoil (bench #8182)
  ====================================================================

  This file builds the **Khovanov complex** of a knot diagram given as a
  PD code, following Bar-Natan, *On Khovanov's categorification of the
  Jones polynomial* (arXiv:math/0201043, §2-§3), and evaluates it on the
  lake's trefoil (`Knots.Basic_en.trefoilDiagram`). It builds on the
  Kauffman bracket of `Knots.Jones_en`: states, the two A/B smoothings,
  loop enumeration and crossing signs are already defined and proved
  there.

  ## Conventions (Bar-Natan's, aligned with A14 of Jones)

  - The module `V` has basis `v₊` (degree +1) and `v₋` (degree −1); here
    `v₊ = true`, `v₋ = false`.
  - Bar-Natan's **0-smoothing** is the **A** smoothing (`true` in Jones),
    the **1-smoothing** is the **B** smoothing (`false`). The height `r`
    of a state is its number of 1-smoothings, hence the number of
    `false`.
  - At the vertex `ε` of height `r`, whose smoothing has `k` loops, one
    attaches `V^ε := V^{⊗k}{r}` (quantum shift `{r}`; `qdim V^ε = q^r
    (q + q⁻¹)^k`). Tensor factors are ordered by **increasing minimal
    edge** of the loop (§3 of Bar-Natan): `sortedComponents`.
  - Cube edges flip a **0 → 1** (A → B); the sign is
    `(−1)^{number of 1s before the flipped crossing}`. The edge map is
    `m` when two loops merge, `Δ` when one loop splits, the identity on
    the other factors:
    `m(v₊⊗v₊) = v₊`, `m(v₊⊗v₋) = m(v₋⊗v₊) = v₋`, `m(v₋⊗v₋) = 0`,
    `Δ(v₊) = v₊⊗v₋ + v₋⊗v₊`, `Δ(v₋) = v₋⊗v₋`.
  - The final complex is `C(L) = L[−n₋]{n₊ − 2n₋}`; `n₊` and `n₋` are the
    numbers of positive and negative crossings in the sense of
    `Knots.Jones_en.crossingSign`. These integers are the only use of
    planarity; the lake's trefoil has `n₊ = 3`, `n₋ = 0`.

  ## What the file decides (kernel, `decide`)

  On `trefoilDiagram`:

  - chain group dimensions: **4, 6, 12, 8** (30 generators);
  - **`d ∘ d = 0`** at both composable stages;
  - differential ranks: **2, 4, 7**;
  - homology dimensions per stage: **2, 0, 1, 1**;
  - graded homology table (over ℚ): `H^{0,1}`, `H^{0,3}`, `H^{2,5}`,
    `H^{3,9}` of dimension 1, everything else zero, i.e. `q + q³ + q⁵t² + q⁹t³`
    — the table published by Bar-Natan §4.1 for his demonstration trefoil;
  - graded Euler characteristic at `q = −1`: **χ|_{q=−1} = −2**.

  ## Scope: ranks over ℚ, torsion invisible

  `matRank` eliminates over `ℤ` and returns the rank **over ℚ**: that is what
  the dimensions need, but the table obtained is that of `H^r(L; ℚ)`. Integer
  torsion (for instance the ℤ₂ part the trefoil carries in the Knot Atlas
  table) appears nowhere here and is not claimed. The theorems below therefore
  state graded dimensions of `H^r(L; ℚ)`, never the full invariant over `ℤ`.

  ## Divergences recorded against the pre-registration (#12208)

  - The pre-registration announced "27 generators, C¹ of dimension 3";
    the computation gives **30 generators**, dimensions 4/6/12/8 per
    stage (the "3" conflated the rank of the degree-0 graded piece with
    the module dimension).
  - The pre-registration announced "same PD code as Bar-Natan";
    `trefoilDiagram` is in fact `[⟨1,4,2,5⟩, ⟨3,6,4,1⟩, ⟨5,2,6,3⟩]`,
    whereas Bar-Natan's demonstration code is literally
    `X[1,5,2,4], X[5,3,6,2], X[3,1,4,6]` — the two codes are related by
    swapping `e2 ↔ e4` crossing by crossing (the mirror in the sense of
    `mirrorCrossing`). The bench is built on the lake's diagram, and its
    graded homology coincides with the published table: the code
    divergence is not one for the invariant.
  - The sealed discriminator concerned χ|_{q=−1} (the KNOTS-02 notebook
    printed −8); the bench decides **−2**, compatible with Bar-Natan's
    table (`q + q³ + q⁵ − q⁹` at `t = −1` is −2).

  Reference: D. Bar-Natan, arXiv:math/0201043 (copy archived in the shared
  bibliography store, outside the repository). Issue #8182; sealed
  pre-registration #12208.
-/

import Knots.Jones_en

/-- Indexed access with a default value. The core of this Lean version does
not provide `List.get!`; this shim restores it on top of `List.getD`, which is
present, so the definitions stay reducible by `decide`. Declared `private`:
the `Khovanov` companion carries a twin, and a module importing both would
otherwise see two declarations of the same name. -/
private def List.get! {α : Type} [Inhabited α] (l : List α) (i : Nat) : α := l.getD i default

namespace Knots_en

/-! ## The module `V` and its maps (1+1-dimensional TQFT, §3.2)

`true` represents `v₊` (degree +1), `false` represents `v₋` (degree −1). -/

/-- `m : V ⊗ V → V`, the Frobenius multiplication: `v₊⊗v₊ ↦ v₊`,
`v₊⊗v₋ ↦ v₋`, `v₋⊗v₊ ↦ v₋`, `v₋⊗v₋ ↦ 0`. -/
def khMulGen (a b : Bool) : List (ℤ × Bool) :=
  if a && b then [(1, true)]
  else if a || b then [(1, false)]
  else []

/-- `Δ : V → V ⊗ V`, the comultiplication: `v₊ ↦ v₊⊗v₋ + v₋⊗v₊`,
`v₋ ↦ v₋⊗v₋`. -/
def khComulGen (a : Bool) : List (ℤ × (Bool × Bool)) :=
  if a then [(1, (true, false)), (1, (false, true))]
  else [(1, (false, false))]

/-- Sign of the edge flipping crossing `i` of state `v`:
`(−1)^{number of 1-smoothings before i}`. -/
def khEdgeSign (v : List Bool) (i : Nat) : ℤ :=
  if (v.take i).count false % 2 == 0 then 1 else -1

/-! ## Canonical loop order

Bar-Natan labels each loop by its minimal edge and orders tensor factors
increasingly. `connectedComponents` from `Knots.Jones_en` returns a
partition whose order is not canonical; each component is sorted, then the
list by minimal edge. -/

/-- Sorted insertion of a natural number. -/
def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertNat x ys

/-- Insertion sort of a list of natural numbers. -/
def sortNats : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (sortNats xs)

/-- Sorted insertion of a component (comparison by minimal edge). -/
def insertComp (c : List Nat) : List (List Nat) → List (List Nat)
  | [] => [c]
  | d :: ds => if c.head! ≤ d.head! then c :: d :: ds else d :: insertComp c ds

/-- Sorting of components by minimal edge. -/
def sortComps : List (List Nat) → List (List Nat)
  | [] => []
  | c :: cs => insertComp c (sortComps cs)

/-- Connected components of state `v`, each sorted, the list ordered by
minimal edge: the canonical order of tensor factors. -/
def sortedComponents (d : KnotDiagram) (v : List Bool) : List (List Nat) :=
  sortComps ((connectedComponents (stateConnections d v)).map sortNats)

/-! ## The edge map

For an edge flipping crossing `i` of state `v` (from `v[i] = true` to
`false`), the loops before and after are computed, the old loops feeding
each new loop are read off, and `m` is applied (a merge: two old loops
into one new) or `Δ` (a split: one old loop into two new), the identity
elsewhere. -/

/-- For each new loop, the indices of the old loops feeding it (they share
an edge). -/
def khFeeders (old newC : List (List Nat)) : List (List Nat) :=
  newC.map (fun nc =>
    (List.range old.length).filter (fun oi => (old.get! oi).any (fun e => nc.contains e)))

/-- Terms `(coeff, new marks)` of the edge flipping crossing `i` of state
`v`, the marks `m` listing the chosen basis on each loop in canonical
order. -/
def khEdgeTerms (d : KnotDiagram) (v : List Bool) (m : List Bool) (i : Nat) :
    List (ℤ × List Bool) :=
  let v' := v.set i false
  let old := sortedComponents d v
  let newC := sortedComponents d v'
  let feed := khFeeders old newC
  if newC.length + 1 = old.length then
    -- merge: one new loop has two feeders
    match (List.range newC.length).find? (fun j => 2 ≤ (feed.get! j).length) with
    | none => []
    | some j =>
      let fs := feed.get! j
      let i1 := fs.get! 0
      let i2 := fs.get! 1
      (khMulGen (m.get! i1) (m.get! i2)).map (fun (c, b) =>
        (c, (List.range newC.length).map (fun jj =>
          if jj = j then b else m.get! (feed.get! jj).head!)))
  else if newC.length = old.length + 1 then
    -- split: one old loop feeds two new ones
    let js := (List.range newC.length).filter (fun j => (feed.get! j).length = 1)
    match js.find? (fun j => 2 ≤ (js.filter (fun j2 => feed.get! j2 = feed.get! j)).length) with
    | none => []
    | some j =>
      let oStar := (feed.get! j).head!
      let pair := js.filter (fun j2 => feed.get! j2 = [oStar])
      let j1 := pair.get! 0
      let j2 := pair.get! 1
      (khComulGen (m.get! oStar)).map (fun (c, f) =>
        (c, (List.range newC.length).map (fun jj =>
          if jj = j1 then f.1 else if jj = j2 then f.2
          else m.get! (feed.get! jj).head!)))
  else []

/-! ## Chain groups and differential -/

/-- Generators of the complex over a state: a choice of basis element per
loop, in canonical order. -/
def khGen (d : KnotDiagram) (v : List Bool) : List (List Bool × List Bool) :=
  (allBoolVectors (stateLoops d v)).map (fun m => (v, m))

/-- Generators of the chain group `C^r`: all states of height `r` (number
of 1-smoothings, hence of `false`) with all their bases. -/
def khChainGens (d : KnotDiagram) (r : Nat) : List (List Bool × List Bool) :=
  ((allBoolVectors d.crossings.length).filter (fun v => v.count false = r)).flatMap (khGen d)

/-- Entry of a differential matrix: the coefficient linking the source
generator to the target generator. -/
def khDiffEntry (d : KnotDiagram) (tgt src : List Bool × List Bool) : ℤ :=
  let v := src.1
  let m := src.2
  let v' := tgt.1
  let m' := tgt.2
  ((List.range v.length).filter (fun i => v.get! i == true && v.set i false == v')).foldl
    (fun acc i =>
      acc + khEdgeSign v i *
        ((khEdgeTerms d v m i).foldl (fun a t => if t.2 = m' then a + t.1 else a) 0)) 0

/-- Matrix of the differential `d^r : C^r → C^{r+1}` (rows = targets,
columns = sources). -/
def khDiff (d : KnotDiagram) (r : Nat) : List (List ℤ) :=
  (khChainGens d (r + 1)).map (fun t => (khChainGens d r).map (fun s => khDiffEntry d t s))

/-- Matrix product over `ℤ` (lists of rows). -/
def matMul (A B : List (List ℤ)) : List (List ℤ) :=
  let w := (B.headD []).length
  A.map (fun row => (List.range w).map (fun j =>
    (List.range B.length).foldl (fun acc t => acc + row.get! t * (B.get! t).get! j) 0))

/-- Cancellation of column `c` of row `r` by the pivot row `p`, by integer
row operations: `r' = p[c]·r − r[c]·p`. -/
def rowCancel (p r : List ℤ) (c : Nat) : List ℤ :=
  (List.range p.length).map (fun j => p.get! c * r.get! j - r.get! c * p.get! j)

/-- Rank by integer elimination (pivot found column by column, remaining
rows cancelled). The `ℚ`-rank of an integer matrix is unchanged by these
operations; the fuel decreases at each pivot. -/
def matRankAux : Nat → List (List ℤ) → Nat
  | 0, _ => 0
  | fuel + 1, rows =>
    match rows.find? (fun r => r.any (fun x => x ≠ 0)) with
    | none => 0
    | some p =>
      let c := ((List.range p.length).find? (fun j => p.get! j ≠ 0)).getD 0
      let rest := (rows.erase p).map (fun r => rowCancel p r c)
      1 + matRankAux fuel rest

/-- Rank of an integer matrix over `ℚ`. -/
def matRank (M : List (List ℤ)) : Nat :=
  matRankAux (M.length * ((M.headD []).length) + 1) M

/-- Homology dimension at stage `r`: `dim C^r − rank d^{r−1} − rank d^r`. -/
def homDim (d : KnotDiagram) (r : Nat) : Nat :=
  (khChainGens d r).length
    - (if r = 0 then 0 else matRank (khDiff d (r - 1)))
    - matRank (khDiff d r)

/-! ## Quantum grading and Euler characteristic -/

/-- Number of positive crossings (in the sense of `crossingSign`). -/
def nPlus (d : KnotDiagram) : Nat :=
  (d.crossings.filter (fun c => crossingSign d.numEdges c = 1)).length

/-- Number of negative crossings. -/
def nMinus (d : KnotDiagram) : Nat :=
  (d.crossings.filter (fun c => crossingSign d.numEdges c = -1)).length

/-- Quantum degree of a generator: `(#v₊ − #v₋) + r + (n₊ − 2n₋)`, where
`r` is the state's height (the vertex's `{r}` shift). The differential
preserves it. -/
def qDeg (d : KnotDiagram) (g : List Bool × List Bool) : ℤ :=
  ((g.2.count true : ℤ) - (g.2.count false : ℤ)) + (g.1.count false : ℤ)
    + (nPlus d : ℤ) - 2 * (nMinus d : ℤ)

/-- The differential preserves the quantum degree: every non-zero entry of
`d^{r,j}` links two generators with the same `qDeg`. This is the premise of
`homGradedDim` — without it, the block matrices do not describe the graded
differential. -/
def khDiffPreservesQDeg (d : KnotDiagram) (r : Nat) : Bool :=
  (khChainGens d (r + 1)).all (fun t =>
    (khChainGens d r).all (fun s =>
      khDiffEntry d t s == 0 || qDeg d t == qDeg d s))

/-- Sorted insertion of an integer. -/
def insertInt (x : ℤ) : List ℤ → List ℤ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertInt x ys

/-- Insertion sort of a list of integers. -/
def sortInts : List ℤ → List ℤ
  | [] => []
  | x :: xs => insertInt x (sortInts xs)

/-- Graded dimensions of `C^r`: list `(j, dim)` sorted by degree. -/
def gradedDim (d : KnotDiagram) (r : Nat) : List (ℤ × Nat) :=
  let gs := khChainGens d r
  (sortInts ((gs.map (qDeg d)).eraseDups)).map (fun j =>
    (j, gs.countP (fun g => qDeg d g = j)))

/-- Graded Euler characteristic evaluated at `q = −1`:
`Σ_{r,g} (−1)^{r + deg(g)}`. -/
def chiAtMinusOne (d : KnotDiagram) : ℤ :=
  (List.range (d.crossings.length + 1)).foldl (fun acc r =>
    acc + (khChainGens d r).foldl (fun a g =>
      a + (if ((r : ℤ) + qDeg d g) % 2 = 0 then 1 else -1)) 0) 0

/-- Generators of `C^{r}` at quantum degree `j`. -/
def khChainGensAt (d : KnotDiagram) (r : Nat) (j : ℤ) : List (List Bool × List Bool) :=
  (khChainGens d r).filter (fun g => qDeg d g = j)

/-- Graded homology dimension: `dim C^{r,j} − rank d^{r−1}|_j − rank
d^r|_j` (the differential preserves `qDeg`, so the degree-`j` block is a
subcomplex). -/
def homGradedDim (d : KnotDiagram) (r : Nat) (j : ℤ) : Nat :=
  let srcs := khChainGensAt d r j
  let bIn := if r = 0 then 0 else
    matRank ((srcs).map (fun t => (khChainGensAt d (r - 1) j).map (fun s => khDiffEntry d t s)))
  let bOut :=
    matRank (((khChainGensAt d (r + 1) j)).map (fun t => srcs.map (fun s => khDiffEntry d t s)))
  srcs.length - bIn - bOut

/-! ## Evaluations on the trefoil (decided by the kernel)

Pinned values: these are the numbers the kernel computation must return
and that the PR cites. Any convention regression breaks them. -/

/-- The lake's trefoil has three positive crossings. -/
theorem nPlus_trefoil : nPlus trefoilDiagram = 3 := by decide

/-- … and no negative crossing. -/
theorem nMinus_trefoil : nMinus trefoilDiagram = 0 := by decide

/-- Loops of the all-A state (0-smoothings): 2. -/
theorem loops_allA_trefoil : stateLoops trefoilDiagram [true, true, true] = 2 := by decide

/-- Loops of the all-B state (1-smoothings): 3. -/
theorem loops_allB_trefoil : stateLoops trefoilDiagram [false, false, false] = 3 := by decide

/-- Loops of the three one-1-smoothing states: 1 everywhere. -/
theorem loops_r1_trefoil :
    stateLoops trefoilDiagram [true, true, false] = 1 ∧
    stateLoops trefoilDiagram [true, false, true] = 1 ∧
    stateLoops trefoilDiagram [false, true, true] = 1 := by decide

/-- Loops of the three two-1-smoothing states: 2 everywhere. -/
theorem loops_r2_trefoil :
    stateLoops trefoilDiagram [true, false, false] = 2 ∧
    stateLoops trefoilDiagram [false, true, false] = 2 ∧
    stateLoops trefoilDiagram [false, false, true] = 2 := by decide

/-- Chain group dimensions: 4, 6, 12, 8. -/
theorem dim_chain_trefoil :
    (khChainGens trefoilDiagram 0).length = 4 ∧
    (khChainGens trefoilDiagram 1).length = 6 ∧
    (khChainGens trefoilDiagram 2).length = 12 ∧
    (khChainGens trefoilDiagram 3).length = 8 := by decide

/-- `d¹ ∘ d⁰ = 0`. -/
theorem khovanov_d0_square_zero :
    (matMul (khDiff trefoilDiagram 1) (khDiff trefoilDiagram 0)).all
      (fun row => row.all (fun x => x == 0)) = true := by decide

/-- `d² ∘ d¹ = 0`. -/
theorem khovanov_d1_square_zero :
    (matMul (khDiff trefoilDiagram 2) (khDiff trefoilDiagram 1)).all
      (fun row => row.all (fun x => x == 0)) = true := by decide

/-- Differential ranks: 2, 4, 7. -/
theorem ranks_trefoil :
    matRank (khDiff trefoilDiagram 0) = 2 ∧
    matRank (khDiff trefoilDiagram 1) = 4 ∧
    matRank (khDiff trefoilDiagram 2) = 7 := by decide

/-- Homology dimensions per stage: 2, 0, 1, 1 (total 4). -/
theorem homDim_trefoil :
    homDim trefoilDiagram 0 = 2 ∧
    homDim trefoilDiagram 1 = 0 ∧
    homDim trefoilDiagram 2 = 1 ∧
    homDim trefoilDiagram 3 = 1 := by decide

/-- Graded dimensions of the chain groups. -/
theorem gradedDim_trefoil :
    gradedDim trefoilDiagram 0 = [(1, 1), (3, 2), (5, 1)] ∧
    gradedDim trefoilDiagram 1 = [(3, 3), (5, 3)] ∧
    gradedDim trefoilDiagram 2 = [(3, 3), (5, 6), (7, 3)] ∧
    gradedDim trefoilDiagram 3 = [(3, 1), (5, 3), (7, 3), (9, 1)] := by decide

/-- The differential preserves `qDeg` at the trefoil's three composable
stages: the degree-`j` block really is a subcomplex, which is what
`homGradedDim` needs for its graded table to be that of homology rather than
an assembly of ranks. -/
theorem qDeg_step_trefoil :
    khDiffPreservesQDeg trefoilDiagram 0 = true ∧
    khDiffPreservesQDeg trefoilDiagram 1 = true ∧
    khDiffPreservesQDeg trefoilDiagram 2 = true := by decide

/-- The graded homology table (over ℚ): `q + q³ + q⁵t² + q⁹t³`, identical to
the table published by Bar-Natan §4.1 for his demonstration trefoil. -/
theorem homGradedDim_trefoil :
    homGradedDim trefoilDiagram 0 1 = 1 ∧
    homGradedDim trefoilDiagram 0 3 = 1 ∧
    homGradedDim trefoilDiagram 1 3 = 0 ∧
    homGradedDim trefoilDiagram 1 5 = 0 ∧
    homGradedDim trefoilDiagram 2 5 = 1 ∧
    homGradedDim trefoilDiagram 3 9 = 1 := by decide

/-- Graded Euler characteristic at `q = −1`: −2 (the pre-registration's
discriminator; the KNOTS-02 notebook printed −8). -/
theorem chi_trefoil : chiAtMinusOne trefoilDiagram = -2 := by decide

/-! ## Evaluations on the figure-eight knot (decided by the kernel)

Case 22 of bench #8182, sealed by a five-field pre-registration BEFORE the
run (comment of 2026-10-22 on the issue): every value below was predicted
by the Python mirror validated on the trefoil, then decided by the kernel —
none was adjusted after the fact. The figure-eight has `n₊ = n₋ = 2`
(per-crossing signs [−1, −1, +1, +1]): the two diagonals
`j − 2r ∈ {−5, −3}` expected of an alternating knot with `s = 0` are read
directly off the graded table. Amphichirality `V(4₁)(t) = V(4₁)(t⁻¹)` shows
up as `χ|_{q=−1} = −2`, i.e. `Ĵ(4₁)|_{t=−1} = q⁻⁵ + q⁵`. -/

/-- The lake's figure-eight has two positive crossings. -/
theorem nPlus_figureEight : nPlus figureEightPlanarDiagram = 2 := by decide

/-- … and two negative crossings (writhe 0, already decided in `Jones`). -/
theorem nMinus_figureEight : nMinus figureEightPlanarDiagram = 2 := by decide

/-- Loops of the all-A state: 3. -/
theorem loops_allA_figureEight :
    stateLoops figureEightPlanarDiagram [true, true, true, true] = 3 := by decide

/-- Loops of the all-B state: 3. -/
theorem loops_allB_figureEight :
    stateLoops figureEightPlanarDiagram [false, false, false, false] = 3 := by decide

/-- Chain group dimensions: 8, 16, 18, 16, 8 (66 generators). -/
theorem dim_chain_figureEight :
    (khChainGens figureEightPlanarDiagram 0).length = 8 ∧
    (khChainGens figureEightPlanarDiagram 1).length = 16 ∧
    (khChainGens figureEightPlanarDiagram 2).length = 18 ∧
    (khChainGens figureEightPlanarDiagram 3).length = 16 ∧
    (khChainGens figureEightPlanarDiagram 4).length = 8 := by decide

/-- `d¹ ∘ d⁰ = 0`. -/
theorem khovanov_f8_d0_square_zero :
    (matMul (khDiff figureEightPlanarDiagram 1) (khDiff figureEightPlanarDiagram 0)).all
      (fun row => row.all (fun x => x == 0)) = true := by decide

/-- `d² ∘ d¹ = 0`. -/
theorem khovanov_f8_d1_square_zero :
    (matMul (khDiff figureEightPlanarDiagram 2) (khDiff figureEightPlanarDiagram 1)).all
      (fun row => row.all (fun x => x == 0)) = true := by decide

/-- `d³ ∘ d² = 0`. -/
theorem khovanov_f8_d2_square_zero :
    (matMul (khDiff figureEightPlanarDiagram 3) (khDiff figureEightPlanarDiagram 2)).all
      (fun row => row.all (fun x => x == 0)) = true := by decide

/-- Differential ranks: 7, 8, 8, 7. -/
theorem ranks_figureEight :
    matRank (khDiff figureEightPlanarDiagram 0) = 7 ∧
    matRank (khDiff figureEightPlanarDiagram 1) = 8 ∧
    matRank (khDiff figureEightPlanarDiagram 2) = 8 ∧
    matRank (khDiff figureEightPlanarDiagram 3) = 7 := by decide

/-- Homology dimensions per stage: 1, 1, 2, 1, 1 (total 6). -/
theorem homDim_figureEight :
    homDim figureEightPlanarDiagram 0 = 1 ∧
    homDim figureEightPlanarDiagram 1 = 1 ∧
    homDim figureEightPlanarDiagram 2 = 2 ∧
    homDim figureEightPlanarDiagram 3 = 1 ∧
    homDim figureEightPlanarDiagram 4 = 1 := by decide

/-- The differential preserves `qDeg` at the figure-eight's four stages. -/
theorem qDeg_step_figureEight :
    khDiffPreservesQDeg figureEightPlanarDiagram 0 = true ∧
    khDiffPreservesQDeg figureEightPlanarDiagram 1 = true ∧
    khDiffPreservesQDeg figureEightPlanarDiagram 2 = true ∧
    khDiffPreservesQDeg figureEightPlanarDiagram 3 = true := by decide

/-- The graded homology table: six dimension-1 points on the two diagonals
`j − 2r ∈ {−5, −3}`, and two off-diagonal control zeros (`H^{1,1}`,
`H^{2,3}`) — the support predicted by the thin conjecture. -/
theorem homGradedDim_figureEight :
    homGradedDim figureEightPlanarDiagram 0 (-5) = 1 ∧
    homGradedDim figureEightPlanarDiagram 1 (-1) = 1 ∧
    homGradedDim figureEightPlanarDiagram 2 (-1) = 1 ∧
    homGradedDim figureEightPlanarDiagram 2 1 = 1 ∧
    homGradedDim figureEightPlanarDiagram 3 1 = 1 ∧
    homGradedDim figureEightPlanarDiagram 4 5 = 1 ∧
    homGradedDim figureEightPlanarDiagram 1 1 = 0 ∧
    homGradedDim figureEightPlanarDiagram 2 3 = 0 := by decide

/-- Graded Euler characteristic at `q = −1`: −2, i.e.
`Ĵ(4₁)|_{t=−1} = q⁻⁵ + q⁵` — consistent with amphichirality. -/
theorem chi_figureEight : chiAtMinusOne figureEightPlanarDiagram = -2 := by decide

end Knots_en