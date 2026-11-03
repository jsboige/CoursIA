import Mathlib
import Sudoku.Basic
import Sudoku.ExactCover

/-!
# Sudoku.Certificate — certificats DLX concrets vérifiés par le lake natif

Issue #22375. Le solveur DLX de la série (`dlx_certificates.py`, extraction
fidèle du moteur de `Sudoku-02-DancingLinks-Python.ipynb`) produit des
**certificats de placements** : la liste des 81 couples `(cellule, valeur)`
choisis par l'algorithme X. Ce module fournit l'organe de vérification **du
lake** :

1. `Certificate.RawCertificate` — le format de certificat transportable
   (version, puzzle, indices, placements), émis par
   `dlx_certificates.certificate_to_lean` ;
2. `Certificate.sudokuScopeList` — les 27 portées concrètes du Sudoku 9×9
   (9 lignes, 9 colonnes, 9 blocs) comme **liste calculable**
   `List (Finset (Fin 81))`, et `Certificate.sudokuScopes` — leur
   `Finset` associé (`Scopes (Fin 81)`, consommé par `ExactCover`) ;
3. `Certificate.checkCertificate` — un **checker calculable par étages**
   (dans l'ordre : doublon brut, conflit de cellule, complétude, couverture
   exacte par portée, respect des indices), évaluable par `decide` sur un
   certificat concret. L'énumération des cellules et des valeurs passe par
   `List.finRange` (calculable), **pas** par `Finset.toList` (noncalculable
   dans ce Mathlib — le checker doit rester évaluable) ;
4. le **pont de soundness** : `checkOk_isExactCover` — l'acceptation du
   checker entraîne `ExactCover.IsExactCover` sur les portées concrètes,
   puis `checkOk_givesSolution` extrait une vraie `Solution` via le
   théorème existant `exact_cover_imp_solution` (réutilisation, pas
   ré-implémentation de l'équivalence abstraite — cf #4055).

## Conventions (identiques à `dlx_certificates.py`)

- `cellule : Fin 81`, encodage `r * 9 + c` (r, c dans `[0, 8]`) ;
- `valeur : Fin 9`, encodage `v - 1` (valeur Sudoku 1-9 → `[0, 8]`).

## Étages de rejet et parité avec le validateur Python

Le validateur Python (`validate_certificate`) examine six étages ; le
premier (`domain`) est **vacuement vrai** ici : un couple de type
`Fin 81 × Fin 9` ne peut pas sortir du domaine. Les cinq étages restants
sont examinés par `checkCertificate` dans le même ordre, et le rejet
rapporte l'étage fautif.

## Confiance résiduelle

La transcription Python → littéral Lean (chaîne du puzzle, liste des
placements) n'est pas prouvée ; **tout le reste** — doublons, unicité par
cellule, complétude, couverture exacte par portée, respect des indices —
est re-vérifié par ce checker, indépendamment du producteur.
-/

namespace Sudoku

/-! ## Géométrie du plateau 9×9 -/

/-- La cellule `(r, c)` en index linéaire `r * 9 + c`. -/
def cellOf (r c : Fin 9) : Fin 81 :=
  ⟨r.val * 9 + c.val, by have := r.isLt; have := c.isLt; omega⟩

/-- Le bloc 3×3 d'une cellule : `(r / 3) * 3 + c / 3`, en `[0, 8]`. -/
def blockOf (i : Fin 81) : Fin 9 :=
  ⟨i.val / 9 / 3 * 3 + i.val % 9 / 3, by have := i.isLt; omega⟩

/-- `cellOf` est injectif, au niveau des indices naturels : de
    `cellOf r c = cellOf r' c'` on tire `r.val = r'.val` et `c.val = c'.val`
    (l'encodage `r * 9 + c` avec `r, c < 9` est une bijection). -/
theorem cellOf_val_inj {r r' c c' : Fin 9}
    (h : cellOf r c = cellOf r' c') : r.val = r'.val ∧ c.val = c'.val := by
  have h9r : r.val < 9 := r.isLt
  have h9r' : r'.val < 9 := r'.isLt
  have h9c : c.val < 9 := c.isLt
  have h9c' : c'.val < 9 := c'.isLt
  have he : r.val * 9 + c.val = r'.val * 9 + c'.val :=
    congrArg (fun i : Fin 81 => i.val) h
  omega

/-- Les 9 cellules de la ligne `r`. -/
def Certificate.rowCells (r : Fin 9) : Finset (Fin 81) :=
  (Finset.univ : Finset (Fin 9)).image (cellOf r)

/-- Les 9 cellules de la colonne `c`. -/
def Certificate.colCells (c : Fin 9) : Finset (Fin 81) :=
  (Finset.univ : Finset (Fin 9)).image fun r => cellOf r c

/-- La cellule d'indice `p` du bloc `b` : les lignes `3 * (b / 3) + p / 3`
    croisent les colonnes `3 * (b % 3) + p % 3` — les 9 couples du bloc,
    énumérés par `p : Fin 9`. -/
def Certificate.blocCell (b : Fin 9) (p : Fin 9) : Fin 81 :=
  cellOf ⟨3 * (b.val / 3) + p.val / 3, by have := b.isLt; have := p.isLt; omega⟩
    ⟨3 * (b.val % 3) + p.val % 3, by have := b.isLt; have := p.isLt; omega⟩

/-- Les 9 cellules du bloc `b`. -/
def Certificate.blocCells (b : Fin 9) : Finset (Fin 81) :=
  (Finset.univ : Finset (Fin 9)).image (Certificate.blocCell b)

/-- Les 27 portées concrètes du Sudoku 9×9 : 9 lignes, 9 colonnes, 9 blocs —
    comme **liste calculable** (l'énumération passe par `List.finRange`,
    calculable ; `Finset.toList` est noncalculable dans ce Mathlib). -/
def Certificate.sudokuScopeList : List (Finset (Fin 81)) :=
  (List.finRange 9).map Certificate.rowCells ++
  (List.finRange 9).map Certificate.colCells ++
  (List.finRange 9).map Certificate.blocCells

/-- Le `Finset` des 27 portées, consommé par `ExactCover` (`Scopes (Fin 81)`). -/
def Certificate.sudokuScopes : Scopes (Fin 81) :=
  Certificate.sudokuScopeList.toFinset

/-- La liste porte bien les 27 portées (9 lignes + 9 colonnes + 9 blocs). -/
example : Certificate.sudokuScopeList.length = 27 := by
  simp [Certificate.sudokuScopeList]

/-- Chaque portée concrète est « pleine maison » : 9 cellules pour 9 valeurs.
    C'est l'hypothèse sous laquelle `Sudoku.ExactCover.sudoku_iff_exact_cover`
    vaut pour le 9×9. -/
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

/-! ## Format de certificat -/

/-- Un certificat DLX transportable, tel qu'émis par
    `dlx_certificates.certificate_to_lean`.

    Les champs `version` et `puzzle` sont des métadonnées de transport : le
    checker vérifie les contraintes géométriques depuis `placements` et la
    concordance avec `clues`, indépendamment de la chaîne `puzzle`. -/
structure Certificate.RawCertificate (C V : Type*) where
  /-- Version du format (transport ; le checker ne dépend pas de sa valeur). -/
  version : ℕ
  /-- Chaîne 81 caractères du puzzle (transport, informationnelle). -/
  puzzle : String
  /-- Indices du puzzle : liste `(cellule, valeur)`. -/
  clues : List (C × V)
  /-- La sélection DLX : liste `(cellule, valeur)` prétendue complète. -/
  placements : List (C × V)

/-! ## Primitives calculables (auto-contenues, par induction) -/

/-- La valeur que la liste de placements assigne à la cellule `c`, si elle
    y figure (première occurrence). Défini par induction : ses équations
    sont définitionnelles, sans dépendance d'API. -/
def Certificate.placementValue : List (Fin 81 × Fin 9) → Fin 81 → Option (Fin 9)
  | [], _ => none
  | (c', v') :: t, c => if c' = c then some v' else Certificate.placementValue t c

/-- Vrai si la liste brute contient deux fois la même paire exacte. C'est le
    piège que l'étage « doublon brut » ferme : la conversion en ensemble
    effacerait la répétition. -/
def Certificate.hasRawDuplicate : List (Fin 81 × Fin 9) → Bool
  | [] => false
  | p :: t => t.contains p || Certificate.hasRawDuplicate t

/-- Vrai si deux placements distincts portent deux valeurs sur une même
    cellule. -/
def Certificate.hasCellConflict : List (Fin 81 × Fin 9) → Bool
  | [] => false
  | (c, _) :: t =>
      t.any (fun p => p.1 = c) || Certificate.hasCellConflict t

/-! ## Lemmes d'induction -/

/-- Sans conflit de cellule, la valeur trouvée par `placementValue` est
    exactement celle du placement : la recherche par cellule et l'appartenance
    à la liste coïncident. -/
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

/-- Sans conflit de cellule, une cellule porte au plus une valeur : deux
    placements sur la même cellule coïncident. -/
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

/-! ## Le checker calculable -/

/-- Verdict du checker : accepté, ou rejeté par l'étage fautif (parité avec
    `dlx_certificates.RejectionStage`, l'étage `domain` étant vacuement vrai
    pour des couples typés `Fin 81 × Fin 9`). -/
inductive Certificate.CheckOutcome where
  | ok
  | rawDuplicate
  | cellConflict
  | completeness
  | exactCover
  | clues

/-- Checker par étages, calculable et évaluable par `decide` sur un
    certificat concret. L'énumération des cellules (`finRange 81`), des
    valeurs (`finRange 9`) et des portées (`scopeList`) est une énumération
    de listes, calculable de bout en bout.

    Ordre d'examen (le premier échec est rapporté) :

    1. `rawDuplicate` — la liste brute contient une paire exacte répétée
       (contrôlé AVANT toute conversion en ensemble, qui effacerait le
       doublon) ;
    2. `cellConflict` — deux valeurs sur une même cellule ;
    3. `completeness` — toute cellule du plateau porte une valeur ;
    4. `exactCover` — pour chaque portée déclarée et chaque valeur, exactement
       une cellule de la portée porte cette valeur ;
    5. `clues` — chaque indice du puzzle est respecté. -/
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

/-! ## Soundness : l'acceptation entraîne la couverture exacte -/

/-- Dépliage du verdict « ok » en ses cinq conditions positives (forme `∀` :
    chaque énumération `List.all` y est remplacée par son énoncé point par
    point, via `List.all_eq_true` et `List.mem_finRange`). -/
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

/-- **Pont de soundness.** Un certificat accepté par le checker est une
    couverture exacte au sens de `Sudoku.ExactCover.IsExactCover` sur les
    portées concrètes : chaque cellule porte exactement une valeur, et chaque
    paire (portée, valeur) est portée par exactement une cellule de la
    portée. -/
theorem Certificate.checkOk_isExactCover (cert : Certificate.RawCertificate (Fin 81) (Fin 9))
    (scopeList : List (Finset (Fin 81)))
    (hok : Certificate.checkCertificate cert scopeList = Certificate.CheckOutcome.ok) :
    ExactCover.IsExactCover cert.placements.toFinset scopeList.toFinset := by
  obtain ⟨-, hnc, hall_cells, hcover, -⟩ :=
    (Certificate.checkOk_iff cert scopeList).mp hok
  constructor
  · -- Chaque cellule : exactement une valeur.
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
  · -- Chaque (portée, valeur) : exactement une cellule de la portée.
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

/-- L'acceptation entraîne le respect de chaque indice du puzzle. -/
theorem Certificate.checkOk_cluesRespected
    (cert : Certificate.RawCertificate (Fin 81) (Fin 9))
    (scopeList : List (Finset (Fin 81)))
    (hok : Certificate.checkCertificate cert scopeList = Certificate.CheckOutcome.ok)
    (c : Fin 81) (v : Fin 9) (hclue : (c, v) ∈ cert.clues) :
    Certificate.placementValue cert.placements c = some v := by
  obtain ⟨-, -, -, -, hclues⟩ := (Certificate.checkOk_iff cert scopeList).mp hok
  exact hclues (c, v) hclue

/-- **Boucle bouclée avec le théorème existant.** Un certificat accepté
    produit une vraie solution Sudoku du 9×9 : l'affectation reconstruite
    par `Sudoku.ExactCover.exact_cover_imp_solution` (théorème de
    `ExactCover.lean`, réutilisé tel quel — cf #4055). -/
theorem Certificate.checkOk_givesSolution
    (cert : Certificate.RawCertificate (Fin 81) (Fin 9))
    (hok : Certificate.checkCertificate cert Certificate.sudokuScopeList =
      Certificate.CheckOutcome.ok) :
    ∃ σ, IsSolution Certificate.sudokuScopes σ ∧
      toSelection σ = cert.placements.toFinset :=
  exact_cover_imp_solution Certificate.sudokuScopes _
    (Certificate.checkOk_isExactCover cert Certificate.sudokuScopeList hok)

end Sudoku
