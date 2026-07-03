import Mathlib
import Sudoku.Basic

-- La variable de section `[Fintype V] [DecidableEq V]` est requise par les
-- lemmes du jalon « pleine maison » (`toSelection_scopeVal_unique`,
-- `solution_imp_exact_cover` via `full_house_present` qui cite `Fintype.card V`)
-- mais pas par les lemmes structurels (`toSelection`, `mem_toSelection_iff`,
-- `toSelection_cell_unique`) qui ne mobilisent que la structure d'image sur `ι`.
set_option linter.unusedSectionVars false

/-!
# Sudoku.ExactCover — réduction Sudoku ⇔ couverture exacte (Knuth)

Issue #4055 (jalon restant après `Propagation.lean`). La **couverture exacte**
(exact cover, Knuth 2000, « Dancing Links ») est l'encodage canonique d'un
Sudoku en un problème universel : on exprime chaque contrainte du Sudoku comme
un « élément » à couvrir, chaque placement possible `(cellule, valeur)` comme
une option couvrant un petit sous-ensemble d'éléments, et une solution Sudoku
comme une **couverture exacte** — une sélection d'options où chaque élément est
couvert **exactement une fois**.

## L'encodage (Knuth, 4 familles de contraintes)

Pour un Sudoku concret (9×9), l'univers des contraintes compte `4 × 81 = 324`
éléments répartis en 4 familles :

1. **Cellule** — `cell c` : « la cellule `c` reçoit exactement une valeur »
   (81 contraintes) ;
2. **Ligne** — `scopeVal ℓ v` : « la ligne `ℓ` contient la valeur `v` » ;
3. **Colonne** — idem ;
4. **Bloc** — idem.

Dans notre cadre abstrait (`Sudoku.Basic`), les familles 2–4 fusionnent en une
seule : `scopeVal s v` pour une portée `s ∈ scopes`. L'univers des contraintes
se réduit à deux familles : `cell c` et `scopeVal s v`.

Une option `(c, v) : ι × V` couvre `{cell c} ∪ {scopeVal s v | s ∈ scopes, c ∈ s}`.
La sélection associée à une affectation `σ` est `toSelection σ = {(c, σ c) | c}`.

## Résultat

Le théorème capstone `sudoku_iff_exact_cover` (sous l'hypothèse « pleine
maison » `∀ s ∈ scopes, s.card = card V`, satisfaite par le Sudoku 9×9 où chaque
portée a 9 cellules pour 9 valeurs) établit l'**équivalence complète** entre
résoudre le Sudoku et résoudre un problème de couverture exacte :

  `(∃ σ, IsSolution scopes σ) ↔ (∃ sel, IsExactCover sel scopes)`.

**Sens direct** `solution_imp_exact_cover` — une solution est une couverture
exacte :

- Chaque **cellule** est couverte exactement une fois — par construction de
  `toSelection` (une option `(c, σ c)` par cellule), via `mem_toSelection_iff`.
- Chaque **(portée, valeur)** est couverte **au plus** une fois — c'est
  exactement `AllDistinctOn` (la définition de `IsSolution`) ;
- et **au moins** une fois — par le lemme de la pleine maison
  `full_house_present` (`Sudoku.Basic`), qui dit que dans une portée pleine,
  toute valeur apparaît.

**Sens retour** `exact_cover_imp_solution` — une couverture exacte redonne une
solution : l'affectation reconstruite `fromSelection` (la valeur unique de
chaque cellule) est toutes-distinctes sur chaque portée, car deux cellules d'une
même portée portant la même valeur violeraient l'unicité `∃!` de la paire
(portée, valeur) ; et sa sélection redonne exactement `sel`
(`toSelection_fromSelection`).

**Cadrage honnête (G.3/G.9).** L'équivalence est prouvée intégralement (0
`sorry`). Les axiomes sont le trio standard du noyau Lean 4 (`propext`,
`Classical.choice`, `Quot.sound`) — `Classical.choice` intervient pour la
construction non constructive `fromSelection` (extraire un témoin par cellule
depuis l'`∃!` de couverture), comme toute preuve Mathlib-dépendante ; aucun
axiome ad hoc. Le résultat de calcul massif « 17 indices minimum » reste hors
scope (non formalisable).
-/

namespace Sudoku

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- Une sélection de placements (cellule, valeur) — l'analogue d'une sous-famille
    d'options dans l'encodage de Knuth. -/
abbrev ExactCover.Sel (ι V : Type*) := Finset (ι × V)

/-- `sel` est une **couverture exacte** de la structure `scopes` si chaque
    cellule est couverte exactement une fois (une seule valeur par cellule) ET
    chaque paire (portée, valeur) — pour toute portée déclarée — est couverte
    exactement une fois (une seule cellule de la portée porte la valeur). -/
def ExactCover.IsExactCover (sel : Sel ι V) (scopes : Scopes ι) : Prop :=
  (∀ c : ι, ∃! v : V, (c, v) ∈ sel) ∧
  (∀ s ∈ scopes, ∀ v : V, ∃! c : ι, c ∈ s ∧ (c, v) ∈ sel)

/-- La sélection associée à une affectation `σ` : un placement `(c, σ c)` par
    cellule. Par construction, chaque cellule y apparaît exactement une fois. -/
def toSelection (σ : Solution ι V) : ExactCover.Sel ι V :=
  Finset.univ.image (fun c : ι => (c, σ c))

/-- **Caractérisation de l'appartenance.** `(c, v)` est dans la sélection
    associée à `σ` si et seulement si `v = σ c`. C'est le lemme-clé qui ramène
    toute question sur la sélection à une question sur `σ` elle-même. -/
theorem mem_toSelection_iff (σ : Solution ι V) (c : ι) (v : V) :
    (c, v) ∈ toSelection σ ↔ σ c = v := by
  constructor
  · intro h
    rw [toSelection, Finset.mem_image] at h
    obtain ⟨x, -, hx⟩ := h
    injection hx with h1 h2
    subst h1
    exact h2
  · intro h
    rw [toSelection, Finset.mem_image]
    refine ⟨c, Finset.mem_univ _, ?_⟩
    rw [h]

/-! ## Sens direct : une solution est une couverture exacte -/

/-- **Cellule couverte exactement une fois.** Dans `toSelection σ`, chaque
    cellule `c` reçoit une unique valeur (`σ c`) — l'exhaustivité cellulaire de
    l'encodage, par construction. -/
theorem toSelection_cell_unique (σ : Solution ι V) (c : ι) :
    ∃! v : V, (c, v) ∈ toSelection σ := by
  refine ⟨σ c, (mem_toSelection_iff σ c (σ c)).mpr rfl, ?_⟩
  rintro v hv
  exact ((mem_toSelection_iff σ c v).mp hv).symm

/-- **Paire (portée, valeur) couverte exactement une fois (solution + pleine
    maison).** Si `σ` est toutes-distinctes sur `s` et que `s` est pleine
    (`s.card = card V`), alors pour toute valeur `v` il existe une **unique**
    cellule `c ∈ s` portant `v` : existence par le lemme de la pleine maison
    (`full_house_present`), unicité par `AllDistinctOn` (injectivité). -/
theorem toSelection_scopeVal_unique (σ : Solution ι V) (s : Finset ι) (v : V)
    (hcard : s.card = Fintype.card V) (hAD : AllDistinctOn σ s) :
    ∃! c : ι, c ∈ s ∧ (c, v) ∈ toSelection σ := by
  obtain ⟨c, hcs, hσcv⟩ := full_house_present σ s v hcard hAD
  refine ⟨c, ⟨hcs, (mem_toSelection_iff σ c v).mpr hσcv⟩, ?_⟩
  rintro c' ⟨hc's, hcv'⟩
  rw [mem_toSelection_iff] at hcv'
  exact hAD hc's hcs (hcv'.trans hσcv.symm)

/-- **Sens direct de l'équivalence.** Une solution d'une structure « pleine
    maison » (toute portée a autant de cellules que de valeurs — le cas du
    Sudoku 9×9) est une couverture exacte au sens de Knuth. -/
theorem solution_imp_exact_cover (scopes : Scopes ι) (σ : Solution ι V)
    (hσ : IsSolution scopes σ)
    (hfull : ∀ s ∈ scopes, s.card = Fintype.card V) :
    ExactCover.IsExactCover (toSelection σ) scopes :=
  ⟨fun c => toSelection_cell_unique σ c,
   fun s hs v => toSelection_scopeVal_unique σ s v (hfull s hs) (hσ s hs)⟩

/-! ## Sens retour : une couverture exacte est une solution -/

/-- **Construction inverse.** À partir d'une sélection où chaque cellule est
    couverte exactement une fois, on récupère l'affectation : la valeur unique
    portée par chaque cellule. Non constructive (extraction d'un témoin par
    cellule depuis l'`∃!` de couverture) — repose sur l'axiome `Classical.choice`. -/
noncomputable def fromSelection (sel : ExactCover.Sel ι V)
    (hcell : ∀ c : ι, ∃! v : V, (c, v) ∈ sel) : Solution ι V :=
  fun c => Classical.choose (ExistsUnique.exists (hcell c))

/-- La cellule `c` porte bien sa valeur reconstruite dans `sel`. -/
theorem fromSelection_mem (sel : ExactCover.Sel ι V)
    (hcell : ∀ c : ι, ∃! v : V, (c, v) ∈ sel) (c : ι) :
    (c, fromSelection sel hcell c) ∈ sel :=
  Classical.choose_spec (ExistsUnique.exists (hcell c))

/-- **Caractérisation duale de `mem_toSelection_iff`.** `(c, v)` est dans `sel`
    si et seulement si la valeur reconstruite de `c` vaut `v` — par unicité de
    la valeur couvrant `c`. -/
theorem mem_fromSelection_iff (sel : ExactCover.Sel ι V)
    (hcell : ∀ c : ι, ∃! v : V, (c, v) ∈ sel) (c : ι) (v : V) :
    (c, v) ∈ sel ↔ fromSelection sel hcell c = v := by
  refine ⟨fun hcv => ?_, fun h => ?_⟩
  · obtain ⟨w, hw, huniq⟩ := hcell c
    have h1 : fromSelection sel hcell c = w := huniq _ (fromSelection_mem sel hcell c)
    have h2 : v = w := huniq v hcv
    rw [h1, h2]
  · rw [← h]; exact fromSelection_mem sel hcell c

/-- **La sélection reconstruite est la sélection originale.** `toSelection`
    appliquée à l'affectation reconstruite depuis `sel` redonne exactement
    `sel` : les deux caractérisations d'appartenance coïncident. -/
theorem toSelection_fromSelection (sel : ExactCover.Sel ι V)
    (hcell : ∀ c : ι, ∃! v : V, (c, v) ∈ sel) :
    toSelection (fromSelection sel hcell) = sel := by
  ext ⟨c, v⟩
  rw [mem_toSelection_iff, mem_fromSelection_iff]

/-- **Sens retour de l'équivalence.** Une couverture exacte redonne une
    solution : l'affectation reconstruite est toutes-distinctes sur chaque
    portée (car deux cellules d'une même portée portant la même valeur
    violeraient l'unicité `∃!` de la paire (portée, valeur)), et sa sélection
    est la sélection originale. -/
theorem exact_cover_imp_solution (scopes : Scopes ι) (sel : ExactCover.Sel ι V)
    (hec : ExactCover.IsExactCover sel scopes) :
    ∃ σ, IsSolution scopes σ ∧ toSelection σ = sel :=
  ⟨fromSelection sel hec.1,
   (fun s hs c c' hcs hc's hcc' => by
      have hcv : (c, fromSelection sel hec.1 c) ∈ sel := fromSelection_mem sel hec.1 c
      have hc'v : (c', fromSelection sel hec.1 c) ∈ sel := by
        rw [hcc']; exact fromSelection_mem sel hec.1 c'
      obtain ⟨c0, ⟨hc0s, hc0v⟩, hc0uniq⟩ := hec.2 s hs (fromSelection sel hec.1 c)
      rw [hc0uniq c ⟨hcs, hcv⟩, hc0uniq c' ⟨hc's, hc'v⟩]),
   toSelection_fromSelection sel hec.1⟩

/-- **Équivalence Sudoku ⇔ couverture exacte (Knuth).** Sous l'hypothèse « pleine
    maison » (le cas du Sudoku 9×9), une structure admet une solution si et
    seulement si elle admet une couverture exacte. C'est le théorème
    d'équivalence complet — le sens direct (`solution_imp_exact_cover`) plus le
    sens retour (`exact_cover_imp_solution`). -/
theorem sudoku_iff_exact_cover (scopes : Scopes ι)
    (hfull : ∀ s ∈ scopes, s.card = Fintype.card V) :
    (∃ σ : Solution ι V, IsSolution scopes σ) ↔
      (∃ sel : ExactCover.Sel ι V, ExactCover.IsExactCover sel scopes) := by
  refine ⟨fun ⟨σ, hσ⟩ => ⟨toSelection σ, solution_imp_exact_cover scopes σ hσ hfull⟩,
          fun ⟨sel, hec⟩ => ?_⟩
  obtain ⟨σ, hσ, _⟩ := exact_cover_imp_solution scopes sel hec
  exact ⟨σ, hσ⟩

end Sudoku
