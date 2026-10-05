/-
  StableMarriage.Properties -- tranche 1 (issue #19276)
  Les 5 theoremes du source (Properties.lean, 134 lignes) :
    1. galeShapley_consistent
    2. galeShapley_terminates
    3. galeShapley_individuallyRational
    4. galeShapley_noBlockingPairs (preuve principale, ~60 lignes)
    5. galeShapley_stable
  A composer depuis les lemmes en phase 3 du port.
  Resolution du sorry L73 de GaleShapley.lean amont.

  En tranche 1, on declare les enonces (avec `sorry` documente) ; les
  preuves viendront en phase 3.
-/
namespace StableMarriage

/-- Le matching final est `consistent` : pour toute paire appariee, les
    deux fonctions `menMatches` et `womenMatches` sont d'accord. -/
def consistent {n : Nat} (matching : IntermediateMatching n) : Prop :=
  ∀ m w, matching.menMatches m = some w ↔ matching.womenMatches w = some m

/-- 1. Sortie consistente. Source : `galeShapley_consistent` (Properties.lean).
    Phase 3. -/
theorem galeShapley_consistent {n : Nat} (menPref : Fin n → Fin n → Nat) :
    consistent (galeShapley menPref) := by
  sorry

/-- 2. L'algorithme termine. Source : `galeShapley_terminates`. Phase 3. -/
theorem galeShapley_terminates {n : Nat} (menPref : Fin n → Fin n → Nat) :
    ∃ k, (GSState.runSteps menPref (GSState.initial n) k).terminated := by
  sorry

/-- 3. Pas de partenaire inacceptable. Source : `galeShapley_individuallyRational`.
    Phase 3. -/
theorem galeShapley_individuallyRational {n : Nat}
    (menPref : Fin n → Fin n → Nat)
    (h : ∀ m w, menPref m w < n) :
    ∀ m w, (galeShapley menPref).menMatches m = some w → menPref m w < n := by
  sorry

/-- 4. Pas de paire bloquante (preuve principale). Source :
    `galeShapley_noBlockingPairs` (~60 lignes). Phase 3. -/
theorem galeShapley_noBlockingPairs {n : Nat}
    (menPref womenPref : Fin n → Fin n → Nat) :
    ∀ m w, ¬ IsBlockingPair menPref womenPref
                              (galeShapley menPref).menMatches
                              (galeShapley menPref).womenMatches m w := by
  sorry

/-- 5. Le matching final est stable. Source : `galeShapley_stable`. Compose
    les 4 precedents. Phase 3. Resolution du sorry L73 amont. -/
theorem galeShapley_stable {n : Nat}
    (menPref womenPref : Fin n → Fin n → Nat) :
    ∀ m w, ¬ IsBlockingPair menPref womenPref
                              (galeShapley menPref).menMatches
                              (galeShapley menPref).womenMatches m w := by
  sorry

end StableMarriage
