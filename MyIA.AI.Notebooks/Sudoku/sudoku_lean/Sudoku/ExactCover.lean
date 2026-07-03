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

Le théorème principal `solution_imp_exact_cover` (sous l'hypothèse « pleine
maison » `∀ s ∈ scopes, s.card = card V`, satisfaite par le Sudoku 9×9 où chaque
portée a 9 cellules pour 9 valeurs) établit le **sens direct** de l'équivalence :

  `IsSolution scopes σ → IsExactCover (toSelection σ) scopes`.

- Chaque **cellule** est couverte exactement une fois — par construction de
  `toSelection` (une option `(c, σ c)` par cellule), via `mem_toSelection_iff`.
- Chaque **(portée, valeur)** est couverte **au plus** une fois — c'est
  exactement `AllDistinctOn` (la définition de `IsSolution`) ;
- et **au moins** une fois — par le lemme de la pleine maison
  `full_house_present` (`Sudoku.Basic`), qui dit que dans une portée pleine,
  toute valeur apparaît.

**Cadrage honnête (G.3/G.9).** Le sens direct est prouvé intégralement (0
`sorry`). Le sens retour (couverture exacte ⇒ solution) et l'équivalence
complète `sudoku_iff_exact_cover` sont le jalon suivant — délibérément **non
`sorry`-backed**, pour garder la bibliothèque entièrement `sorry`-free (comme
`Propagation.lean` gardait ce même jalon ouvert). Le résultat de calcul massif
« 17 indices minimum » reste hors scope (non formalisable).
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

end Sudoku
