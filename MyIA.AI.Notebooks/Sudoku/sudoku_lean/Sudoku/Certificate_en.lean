import Mathlib
import Sudoku.Basic_en
import Sudoku.ExactCover_en

/-!
# Sudoku.Certificate — concrete DLX certificates verified by the native lake

Issue #22375. The DLX solver of the series (`dlx_certificates.py`, faithful
extraction of the engine from `Sudoku-02-DancingLinks-Python.ipynb`) produces
**placement certificates**: the list of the 81 `(cell, value)` pairs chosen
by Algorithm X. This module provides the **lake-side** verification organ:

1. `Certificate.RawCertificate` — the transportable certificate format
   (version, puzzle, clues, placements), emitted by
   `dlx_certificates.certificate_to_lean`;
2. `Certificate.sudokuScopeList` — the 27 concrete scopes of the 9×9 Sudoku
   (9 rows, 9 columns, 9 blocks) as a **computable list**
   `List (Finset (Fin 81))`, and `Certificate.sudokuScopes` — the associated
   `Finset` (`Scopes (Fin 81)`, consumed by `ExactCover`);
3. `Certificate.checkCertificate` — a **computable staged checker** (in
   order: raw duplicate, cell conflict, completeness, exact cover per
   scope, clue respect), evaluable by `decide` on a concrete certificate.
   The enumeration of cells and values goes through `List.finRange`
   (computable), **not** through `Finset.toList` (noncomputable in this
   Mathlib — the checker must stay evaluable);
4. the **soundness bridge**: `checkOk_isExactCover` — checker acceptance
   entails `ExactCover.IsExactCover` on the concrete scopes, then
   `checkOk_givesSolution` extracts an actual `Solution` via the existing
   theorem `exact_cover_imp_solution` (reuse, not re-implementation of the
   abstract equivalence — cf #4055).

## Conventions (identical to `dlx_certificates.py`)

- `cell : Fin 81`, encoding `r * 9 + c` (r, c in `[0, 8]`);
- `value : Fin 9`, encoding `v - 1` (Sudoku value 1-9 → `[0, 8]`).

## Rejection stages and parity with the Python validator

The Python validator (`validate_certificate`) examines six stages; the
first one (`domain`) is **vacuously true** here: a pair of type
`Fin 81 × Fin 9` cannot leave the domain. The five remaining stages are
examined by `checkCertificate` in the same order, and a rejection reports
the offending stage.

## Residual trust

The Python → Lean literal transcription (puzzle string, placement list) is
not proved; **everything else** — duplicates, per-cell uniqueness,
completeness, exact cover per scope, clue respect — is re-verified by this
checker, independently of the producer.
-/

namespace Sudoku_en

/-! ## Geometry of the 9×9 board -/

/-- The cell `(r, c)` as linear index `r * 9 + c`. -/
def cellOf (r c : Fin 9) : Fin 81 :=
  ⟨r.val * 9 + c.val, by have := r.isLt; have := c.isLt; omega⟩

/-- The 3×3 block of a cell: `(r / 3) * 3 + c / 3`, in `[0, 8]`. -/
def blockOf (i : Fin 81) : Fin 9 :=
  ⟨i.val / 9 / 3 * 3 + i.val % 9 / 3, by have := i.isLt; omega⟩

/-- `cellOf` is injective at the level of natural indices: from
    `cellOf r c = cellOf r' c'` we get `r.val = r'.val` and `c.val = c'.val`
    (the encoding `r * 9 + c` with `r, c < 9` is a bijection). -/
theorem cellOf_val_inj {r r' c c' : Fin 9}
    (h : cellOf r c = cellOf r' c') : r.val = r'.val ∧ c.val = c'.val := by
  have h9r : r.val < 9 := r.isLt
  have h9r' : r'.val < 9 := r'.isLt
  have h9c : c.val < 9 := c.isLt
  have h9c' : c'.val < 9 := c'.isLt
  have he : r.val * 9 + c.val = r'.val * 9 + c'.val :=
    congrArg (fun i : Fin 81 => i.val) h
  omega

/-- The 9 cells of row `r`. -/
def Certificate.rowCells (r : Fin 9) : Finset (Fin 81) :=
  (Finset.univ : Finset (Fin 9)).image (cellOf r)

/-- The 9 cells of column `c`. -/
def Certificate.colCells (c : Fin 9) : Finset (Fin 81) :=
  (Finset.univ : Finset (Fin 9)).image fun r => cellOf r c

/-- The cell of index `p` in block `b`: rows `3 * (b / 3) + p / 3` cross
    columns `3 * (b % 3) + p % 3` — the 9 pairs of the block, enumerated
    by `p : Fin 9`. -/
def Certificate.blocCell (b : Fin 9) (p : Fin 9) : Fin 81 :=
  cellOf ⟨3 * (b.val / 3) + p.val / 3, by have := b.isLt; have := p.isLt; omega⟩
    ⟨3 * (b.val % 3) + p.val % 3, by have := b.isLt; have := p.isLt; omega⟩

/-- The 9 cells of block `b`. -/
def Certificate.blocCells (b : Fin 9) : Finset (Fin 81) :=
  (Finset.univ : Finset (Fin 9)).image (Certificate.blocCell b)

/-- The 27 concrete scopes of the 9×9 Sudoku: 9 rows, 9 columns, 9 blocks —
    as a **computable list** (the enumeration goes through `List.finRange`,
    computable; `Finset.toList` is noncomputable in this Mathlib). -/
def Certificate.sudokuScopeList : List (Finset (Fin 81)) :=
  (List.finRange 9).map Certificate.rowCells ++
  (List.finRange 9).map Certificate.colCells ++
  (List.finRange 9).map Certificate.blocCells

/-- The `Finset` of the 27 scopes, consumed by `ExactCover` (`Scopes (Fin 81)`). -/
def Certificate.sudokuScopes : Scopes (Fin 81) :=
  Certificate.sudokuScopeList.toFinset

/-- The list indeed carries the 27 scopes (9 rows + 9 columns + 9 blocks). -/
example : Certificate.sudokuScopeList.length = 27 := by
  simp [Certificate.sudokuScopeList]

/-- Every concrete scope is "full house": 9 cells for 9 values. This is the
    hypothesis under which `Sudoku.ExactCover.sudoku_iff_exact_cover` holds
    for the 9×9. -/
theorem Certificate.sudokuScopeList_full_house :
    ∀ s ∈ Certificate.sudokuScopeList, s.card = 9 := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨r, -, hrfl⟩ := List.mem_map.mp hs
      rw [← hrfl]
      simp only [Certificate.rowCells]
      rw [Finset.card_image_of_injective _
        (fun a b hab => Fin.ext (cellOf_val_inj hab).2)]
      simp
    · obtain ⟨c, -, hcfl⟩ := List.mem_map.mp hs
      rw [← hcfl]
      simp only [Certificate.colCells]
      rw [Finset.card_image_of_injective _
        (fun a b hab => Fin.ext (cellOf_val_inj hab).1)]
      simp
  · obtain ⟨b, -, hbfl⟩ := List.mem_map.mp hs
    rw [← hbfl]
    simp only [Certificate.blocCells]
    rw [Finset.card_image_of_injective _ ?_]
    · simp
    · intro p p' hp
      obtain ⟨hr, hc⟩ := cellOf_val_inj hp
      have hp' := p.isLt
      have hp9 := p'.isLt
      have hb := b.isLt
      have hc' : 3 * (b.val % 3) + p.val % 3 = 3 * (b.val % 3) + p'.val % 3 := hc
      have hr' : 3 * (b.val / 3) + p.val / 3 = 3 * (b.val / 3) + p'.val / 3 := hr
      exact Fin.ext (by omega)

/-! ## Certificate format -/

/-- A transportable DLX certificate, as emitted by
    `dlx_certificates.certificate_to_lean`.

    The `version` and `puzzle` fields are transport metadata: the checker
    verifies the geometric constraints from `placements` and the agreement
    with `clues`, independently of the `puzzle` string. -/
structure Certificate.RawCertificate (C V : Type*) where
  /-- Format version (transport; the checker does not depend on its value). -/
  version : ℕ
  /-- 81-character puzzle string (transport, informational). -/
  puzzle : String
  /-- Puzzle clues: `(cell, value)` list. -/
  clues : List (C × V)
  /-- The DLX selection: `(cell, value)` list claimed complete. -/
  placements : List (C × V)

/-! ## Computable primitives (self-contained, by induction) -/

/-- The value the placement list assigns to cell `c`, if it appears there
    (first occurrence). Defined by induction: its equations are
    definitional, with no API dependency. -/
def Certificate.placementValue : List (Fin 81 × Fin 9) → Fin 81 → Option (Fin 9)
  | [], _ => none
  | (c', v') :: t, c => if c' = c then some v' else Certificate.placementValue t c

/-- True if the raw list contains the same exact pair twice. This is the
    trap the "raw duplicate" stage closes: converting to a set would erase
    the repetition. -/
def Certificate.hasRawDuplicate : List (Fin 81 × Fin 9) → Bool
  | [] => false
  | p :: t => t.contains p || Certificate.hasRawDuplicate t

/-- True if two distinct placements carry two values on the same cell. -/
def Certificate.hasCellConflict : List (Fin 81 × Fin 9) → Bool
  | [] => false
  | (c, _) :: t =>
      t.any (fun p => p.1 = c) || Certificate.hasCellConflict t

/-! ## Induction lemmas -/

/-- Without cell conflict, the value found by `placementValue` is exactly
    that of the placement: search by cell and membership in the list
    coincide. -/
theorem Certificate.placementValue_iff {pl : List (Fin 81 × Fin 9)}
    (h : Certificate.hasCellConflict pl = false) (c : Fin 81) (v : Fin 9) :
    Certificate.placementValue pl c = some v ↔ (c, v) ∈ pl := by
  induction pl with
  | nil => simp [Certificate.placementValue]
  | cons p t ih =>
    have hct : Certificate.hasCellConflict t = false := by
      simp [Certificate.hasCellConflict] at h; exact h.2
    by_cases hpc : p.1 = c
    · subst hpc
      simp only [Certificate.placementValue]
      constructor
      · intro heq
        have hv : p.2 = v := Option.some.inj (by simpa using heq)
        subst hv
        exact List.mem_cons_self
      · intro hmem
        rcases List.mem_cons.mp hmem with hhead | htail
        · have hv : v = p.2 := congrArg Prod.snd hhead
          rw [hv]
          simp
        · exact absurd htail (by
            have hany : t.any (fun q : Fin 81 × Fin 9 => decide (q.1 = p.1)) = true :=
              List.any_eq_true.mpr ⟨(p.1, v), htail, decide_eq_true rfl⟩
            have hconf : Certificate.hasCellConflict (p :: t) = true := by
              simp [Certificate.hasCellConflict, hany]
            rw [hconf] at h; exact Bool.noConfusion h)
    · simp only [Certificate.placementValue, if_neg hpc]
      rw [ih hct]
      constructor
      · intro hmem
        exact List.Mem.tail _ hmem
      · intro hmem
        rcases List.mem_cons.mp hmem with hhead | htail
        · exact absurd (show p.1 = c from (congrArg Prod.fst hhead).symm) hpc
        · exact htail

/-- Without cell conflict, a cell carries at most one value: two placements
    on the same cell coincide. -/
theorem Certificate.pair_unique {pl : List (Fin 81 × Fin 9)}
    (h : Certificate.hasCellConflict pl = false) {c : Fin 81} {v v' : Fin 9}
    (h1 : (c, v) ∈ pl) (h2 : (c, v') ∈ pl) : v = v' := by
  induction pl with
  | nil => simp at h1
  | cons p t ih =>
    have hct : Certificate.hasCellConflict t = false := by
      simp [Certificate.hasCellConflict] at h; exact h.2
    by_cases hpc : p.1 = c
    · subst hpc
      rcases List.mem_cons.mp h1 with h1' | h1'
      · rcases List.mem_cons.mp h2 with h2' | h2'
        · exact (congrArg Prod.snd h1').trans (congrArg Prod.snd h2').symm
        · exact absurd h2' (by
            have hany : t.any (fun q : Fin 81 × Fin 9 => decide (q.1 = p.1)) = true :=
              List.any_eq_true.mpr ⟨(p.1, v'), h2', decide_eq_true rfl⟩
            have hconf : Certificate.hasCellConflict (p :: t) = true := by
              simp [Certificate.hasCellConflict, hany]
            rw [hconf] at h; exact Bool.noConfusion h)
      · rcases List.mem_cons.mp h2 with h2' | h2'
        · exact absurd h1' (by
            have hany : t.any (fun q : Fin 81 × Fin 9 => decide (q.1 = p.1)) = true :=
              List.any_eq_true.mpr ⟨(p.1, v), h1', decide_eq_true rfl⟩
            have hconf : Certificate.hasCellConflict (p :: t) = true := by
              simp [Certificate.hasCellConflict, hany]
            rw [hconf] at h; exact Bool.noConfusion h)
        · exact ih hct h1' h2'
    · rcases List.mem_cons.mp h1 with h1' | h1'
      · exact absurd (show p.1 = c from (congrArg Prod.fst h1').symm) hpc
      · rcases List.mem_cons.mp h2 with h2' | h2'
        · exact absurd (show p.1 = c from (congrArg Prod.fst h2').symm) hpc
        · exact ih hct h1' h2'

/-! ## The computable checker -/

/-- Checker verdict: accepted, or rejected by the offending stage (parity
    with `dlx_certificates.RejectionStage`, the `domain` stage being
    vacuously true for pairs typed as `Fin 81 × Fin 9`). -/
inductive Certificate.CheckOutcome where
  | ok
  | rawDuplicate
  | cellConflict
  | completeness
  | exactCover
  | clues

/-- Staged checker, computable and evaluable by `decide` on a concrete
    certificate. The enumeration of cells (`finRange 81`), values
    (`finRange 9`) and scopes (`scopeList`) is a list enumeration,
    computable end to end.

    Examination order (the first failure is reported):

    1. `rawDuplicate` — the raw list contains a repeated exact pair
       (checked BEFORE any conversion to a set, which would erase the
       duplicate);
    2. `cellConflict` — two values on the same cell;
    3. `completeness` — every cell of the board carries a value;
    4. `exactCover` — for every declared scope and every value, exactly one
       cell of the scope carries that value;
    5. `clues` — every puzzle clue is respected. -/
def Certificate.checkCertificate (cert : Certificate.RawCertificate (Fin 81) (Fin 9))
    (scopeList : List (Finset (Fin 81))) : Certificate.CheckOutcome :=
  if !Certificate.hasRawDuplicate cert.placements then
    if !Certificate.hasCellConflict cert.placements then
      if (List.finRange 81).all
          fun c => (Certificate.placementValue cert.placements c).isSome then
        if scopeList.all fun s =>
            (List.finRange 9).all fun v =>
              decide ((s.filter fun c =>
                Certificate.placementValue cert.placements c = some v).card = 1) then
          if cert.clues.all fun p =>
              decide (Certificate.placementValue cert.placements p.1 = some p.2) then
            Certificate.CheckOutcome.ok
          else Certificate.CheckOutcome.clues
        else Certificate.CheckOutcome.exactCover
      else Certificate.CheckOutcome.completeness
    else Certificate.CheckOutcome.cellConflict
  else Certificate.CheckOutcome.rawDuplicate

/-! ## Soundness: acceptance entails exact cover -/

/-- Unfolding of the "ok" verdict into its five positive conditions (`∀`
    form: every `List.all` enumeration is replaced by its pointwise
    statement, via `List.all_eq_true` and `List.mem_finRange`). -/
theorem Certificate.checkOk_iff (cert : Certificate.RawCertificate (Fin 81) (Fin 9))
    (scopeList : List (Finset (Fin 81))) :
    Certificate.checkCertificate cert scopeList = Certificate.CheckOutcome.ok ↔
      Certificate.hasRawDuplicate cert.placements = false ∧
      Certificate.hasCellConflict cert.placements = false ∧
      (∀ c : Fin 81, (Certificate.placementValue cert.placements c).isSome = true) ∧
      (∀ s ∈ scopeList, ∀ v : Fin 9,
          (s.filter fun c =>
            Certificate.placementValue cert.placements c = some v).card = 1) ∧
      (∀ p ∈ cert.clues,
          Certificate.placementValue cert.placements p.1 = some p.2) := by
  unfold Certificate.checkCertificate
  split_ifs <;> simp_all [List.mem_finRange, decide_eq_true_eq] <;> assumption

/-- **Soundness bridge.** A certificate accepted by the checker is an exact
    cover in the sense of `Sudoku.ExactCover.IsExactCover` on the concrete
    scopes: every cell carries exactly one value, and every (scope, value)
    pair is carried by exactly one cell of the scope. -/
theorem Certificate.checkOk_isExactCover (cert : Certificate.RawCertificate (Fin 81) (Fin 9))
    (scopeList : List (Finset (Fin 81)))
    (hok : Certificate.checkCertificate cert scopeList = Certificate.CheckOutcome.ok) :
    ExactCover.IsExactCover cert.placements.toFinset scopeList.toFinset := by
  obtain ⟨-, hnc, hall_cells, hcover, -⟩ :=
    (Certificate.checkOk_iff cert scopeList).mp hok
  constructor
  · -- Every cell: exactly one value.
    intro c
    cases ho : Certificate.placementValue cert.placements c with
    | none =>
      have hc := hall_cells c
      rw [ho] at hc
      simp at hc
    | some v =>
      refine ⟨v, List.mem_toFinset.mpr
        ((Certificate.placementValue_iff hnc c v).mp ho), ?_⟩
      intro v' hv'
      exact Certificate.pair_unique hnc
        (List.mem_toFinset.mp hv')
        ((Certificate.placementValue_iff hnc c v).mp ho)
  · -- Every (scope, value): exactly one cell of the scope.
    intro s hs v
    have hvcard : (s.filter fun c =>
        Certificate.placementValue cert.placements c = some v).card = 1 :=
      hcover s (List.mem_toFinset.mp hs) v
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hvcard
    have hamem : a ∈ s ∧ Certificate.placementValue cert.placements a = some v := by
      have h1 : a ∈ s.filter (fun c => Certificate.placementValue cert.placements c = some v) := by
        rw [ha]; simp
      simpa [Finset.mem_filter] using h1
    refine ⟨a, ⟨hamem.1, List.mem_toFinset.mpr
      ((Certificate.placementValue_iff hnc a v).mp hamem.2)⟩, ?_⟩
    rintro c' ⟨hc's, hc'v⟩
    have hc'pv : Certificate.placementValue cert.placements c' = some v :=
      (Certificate.placementValue_iff hnc c' v).mpr (List.mem_toFinset.mp hc'v)
    have h2 : c' ∈ s.filter (fun c => Certificate.placementValue cert.placements c = some v) :=
      Finset.mem_filter.mpr ⟨hc's, hc'pv⟩
    rw [ha] at h2
    simpa [Finset.mem_singleton] using h2

/-- Acceptance entails the respect of every puzzle clue. -/
theorem Certificate.checkOk_cluesRespected
    (cert : Certificate.RawCertificate (Fin 81) (Fin 9))
    (scopeList : List (Finset (Fin 81)))
    (hok : Certificate.checkCertificate cert scopeList = Certificate.CheckOutcome.ok)
    (c : Fin 81) (v : Fin 9) (hclue : (c, v) ∈ cert.clues) :
    Certificate.placementValue cert.placements c = some v := by
  obtain ⟨-, -, -, -, hclues⟩ := (Certificate.checkOk_iff cert scopeList).mp hok
  exact hclues (c, v) hclue

/-- **Loop closed with the existing theorem.** An accepted certificate
    yields an actual 9×9 Sudoku solution: the assignment reconstructed by
    `Sudoku.ExactCover.exact_cover_imp_solution` (theorem of
    `ExactCover.lean`, reused as is — cf #4055). -/
theorem Certificate.checkOk_givesSolution
    (cert : Certificate.RawCertificate (Fin 81) (Fin 9))
    (hok : Certificate.checkCertificate cert Certificate.sudokuScopeList =
      Certificate.CheckOutcome.ok) :
    ∃ σ, IsSolution Certificate.sudokuScopes σ ∧
      toSelection σ = cert.placements.toFinset :=
  exact_cover_imp_solution Certificate.sudokuScopes _
    (Certificate.checkOk_isExactCover cert Certificate.sudokuScopeList hok)

end Sudoku_en
