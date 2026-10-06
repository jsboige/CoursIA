/-
  StableMarriage.Properties -- tranche 1 + tranche 7 (issue #19276)
  Les 5 theoremes du source (Properties.lean, 134 lignes) :
    1. galeShapley_consistent   (phase 3a, tranche 7 : preuve reelle)
    2. galeShapley_terminates
    3. galeShapley_individuallyRational
    4. galeShapley_noBlockingPairs (preuve principale, ~60 lignes)
    5. galeShapley_stable
  A composer depuis les lemmes en phase 3 du port.
  Resolution du sorry L73 de GaleShapley.lean amont.

  En tranche 1, on declare les enonces (avec `sorry` documente) ; les
  preuves viendront en phase 3. Tranche 7 (phase 3a) prouve
  `galeShapley_consistent` reellement, sous la limitation structurelle
  du modele simplifie (runSteps retourne l'etat inchange -- cf.
  commentaire de `galeShapley_eq_initial`).

  Strategie tranche 7 : on decompose en 2 lemmes :
  - `galeShapley_eq_initial` : le matching final EST l'etat initial
    (runSteps est un no-op en tranche 1 -- GaleShapley.lean L106-107).
  - `galeShapley_consistent` : on applique la premiere pour deduire
    que les hommes et femmes sont tous libres (none = none), donc le
    biconditional `(none = some w) ↔ (none = some m)` est trivialement
    `False ↔ False = True`.

  Les autres theoremes (`galeShapley_terminates`,
  `galeShapley_individuallyRational`, `galeShapley_noBlockingPairs`,
  `galeShapley_stable`) restent en `sorry` documente jusqu'a
  l'implementation d'un `runSteps` non-trivial (Phase 3.5 ou Phase 4).
-/
import StableMarriage.Basic
import StableMarriage.GaleShapley

namespace StableMarriage

/-- Le matching final est `consistent` : pour toute paire appariee, les
    deux fonctions `menMatches` et `womenMatches` sont d'accord. -/
def consistent {n : Nat} (matching : IntermediateMatching n) : Prop :=
  ∀ m w, matching.menMatches m = some w ↔ matching.womenMatches w = some m

/-- Tranche 7 (phase 3a) : lemme intermediaire. Le matching final est
    l'etat initial -- consequence directe de la semantique squelettique
    de `GSState.runSteps` (GaleShapley.lean L106-107 : `runSteps _ s _ = s`).

    Strategie : `unfold` des deux definitions, puis `rfl` sur
    l'egalite reductionnelle. La preuve est REELLE (pas de `sorry`),
    et documente la limitation structurelle du modele simplifie.

    Source : `galeShapley_eq_initial`. Phase 3a (tranche 7). -/
theorem galeShapley_eq_initial {n : Nat} (menPref : Fin n → Fin n → Nat) :
    galeShapley menPref = (GSState.initial (n := n)).matching := by
  unfold galeShapley GSState.runSteps
  rfl

/-- 1. Sortie consistente. Source : `galeShapley_consistent` (Properties.lean).
    Phase 3a (tranche 7) : preuve reelle sur le modele simplifie.

    Strategie :
    - On substitue `galeShapley menPref` par `(GSState.initial n).matching`
      grace au lemme `galeShapley_eq_initial`.
    - On unfold the deux projections `menMatches` et `womenMatches` du
      constructeur record : elles valent toutes deux `fun _ => none`.
    - L'application a `m` ou `w` donne `none`, donc les deux cotes du
      biconditional sont `none = some _`, qui sont `False` (par
      `Option.noConfusion` : aucune confusion possible entre `none` et
      `some _`).
    - `False ↔ False` est trivialement `True`, mais comme les deux
      directions dependent d'une hypothese impossible, on passe par
      `Iff.intro` avec elimination directe de l'hypothese.

    **Reduction sorry tranche 7** : 1 `sorry` elimine (le theoreme 1
    est desormais *entierement prouve*). C'est la **7e preuve reelle**
    du port (apres les 6 preservations d'invariants des tranches 2-6).

    Strategie anti-regression (CLAUDE.md section D) : aucun `sorry`
    cache. Le commentaire explique pourquoi la limitation du modele
    (runSteps = no-op) rend la preuve triviale. -/
theorem galeShapley_consistent {n : Nat} (menPref : Fin n → Fin n → Nat) :
    consistent (galeShapley menPref) := by
  intro m w
  -- Substituons le matching final par l'etat initial.
  rw [galeShapley_eq_initial]
  -- Forcer la reduction des projections du constructeur record :
  --   (IntermediateMatching.mk (fun _ => none) (fun _ => none)).menMatches m
  --   --> (fun _ => none) m --> none
  -- Le biconditional devient alors `(none = some w) ↔ (none = some m)`,
  -- qui est `False ↔ False = True`.
  simp only [GSState.initial, IntermediateMatching.mk.injEq]
  apply Iff.intro
  · -- direction avant : `(none = some w) → (none = some m)`
    -- `none = some w` est impossible (noConfusion sur Option) :
    -- `cases h_eq` derive directement `False`, et `False → a` est trivial.
    intro h_eq
    cases h_eq
  · -- direction arriere : `(none = some m) → (none = some w)`
    intro h_eq
    cases h_eq

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
