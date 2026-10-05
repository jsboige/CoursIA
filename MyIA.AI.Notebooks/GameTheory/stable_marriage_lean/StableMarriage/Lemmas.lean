/-
  StableMarriage.Lemmas -- tranche 1 (issue #19276)
  Les 46 lemmes du source mmaaz-git/stable-marriage-lean (Lemmas.lean,
  1010 lignes) seront portes en phase 2-3. Les invariants preserves sont :
    - menAcceptableState
    - womenAcceptableState
    - menProposedDownwardState
    - menMatchedProposedState
    - womenUnmatchedRejectState
    - womenBestState
  Et la terminaison (proposedCount_step_of_free, etc.).

  En tranche 1, on declare les types de lemmes (avec `sorry` documente)
  pour que la structure soit en place ; les preuves sont prevues en
  phase 2 (preservation) et phase 3 (terminaison + stabilite).
-/
namespace StableMarriage

/-- Invariant 1 : tout homme apparie l'est a une femme de sa liste de
    preferences (acceptable). Preservation par `step` (phase 2). -/
def menAcceptableState {n : Nat} (menPref : Fin n → Fin n → Nat)
    (s : GSState n) : Prop :=
  ∀ m w, s.matching.menMatches m = some w → menPref m w < n

/-- Invariant 2 : symetrique pour les femmes. -/
def womenAcceptableState {n : Nat} (womenPref : Fin n → Fin n → Nat)
    (s : GSState n) : Prop :=
  ∀ w m, s.matching.womenMatches w = some m → womenPref w m < n

/-- Invariant 3 : un homme propose dans l'ordre de ses preferences
    (downward closure : s'il a propose a `w2` et prefere `w1` a `w2`, alors
    il a propose a `w1` aussi). -/
def menProposedDownwardState {n : Nat} (menPref : Fin n → Fin n → Nat)
    (s : GSState n) : Prop :=
  ∀ m w1 w2, s.proposed m w2 → menPref m w1 < menPref m w2 → s.proposed m w1

/-- Invariant 4 : un homme apparie a propose a sa partenaire. -/
def menMatchedProposedState {n : Nat} (s : GSState n) : Prop :=
  ∀ m w, s.matching.menMatches m = some w → s.proposed m w

/-- Invariant 5 : une femme libre a ete proposee au moins une fois et a
    rejete. -/
def womenUnmatchedRejectState {n : Nat} (s : GSState n) : Prop :=
  ∀ w, s.isFreeW w → ∃ m, s.proposed m w

/-- Invariant 6 : une femme appariee detient sa meilleure proposition
    courante (sera preservee par `step` en phase 2). -/
def womenBestState {n : Nat} (womenPref : Fin n → Fin n → Nat)
    (s : GSState n) : Prop :=
  ∀ w m m', s.matching.womenMatches w = some m →
    s.proposed m' w → womenPref w m ≤ womenPref w m'

/-- Conservation : `menAcceptableState` est preserve par `step`.
    Source : `step_menAcceptable` (L170-233, 64 lignes). Phase 2. -/
theorem step_menAcceptable {n : Nat} (menPref : Fin n → Fin n → Nat)
    {s : GSState n} (h : menAcceptableState menPref s) (m' : Fin n) :
    menAcceptableState menPref (GSState.step menPref s m') := by
  sorry

/-- Conservation : `proposedCount` augmente apres un `step` sur un homme
    libre. Source : `proposedCount_step_of_free` (L900). Phase 2. -/
theorem proposedCount_step_of_free {n : Nat} (menPref : Fin n → Fin n → Nat)
    (s : GSState n) (m : Fin n) (h : s.isFree m) :
    (GSState.step menPref s m).proposedCount > s.proposedCount := by
  sorry

end StableMarriage
