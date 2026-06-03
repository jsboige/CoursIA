import StableMarriageLean.Lemmas

namespace StableMarriageLean

noncomputable section
open Classical

-- The output matching is consistent.
theorem galeShapley_consistent (P : Problem) :
    consistent P (galeShapley P) := by
  simpa [galeShapley] using
    (runSteps_consistent P (proposalBound P))

-- The algorithm terminates after the proposal bound.
theorem galeShapley_terminates (P : Problem) :
    terminated P
      (GSState.runSteps P (proposalBound P)) := by
  classical
  by_contra hnot
  have hfree : ∃ m, isFree P (GSState.runSteps P (proposalBound P)) m := by
    simpa [terminated] using hnot
  have hlt :
      proposedCount P (GSState.runSteps P (proposalBound P)) < proposalBound P :=
    proposedCount_lt_bound_of_free P _ hfree
  have hcount :
      proposedCount P (GSState.runSteps P (proposalBound P)) =
        proposalBound P := by
    exact proposedCount_runSteps_eq_of_not_terminated P _ hnot
  have hlt' : proposalBound P < proposalBound P := by
    have hlt' := hlt
    simp [hcount] at hlt'
  exact (lt_irrefl _ hlt')

-- The output matching is individually rational.
theorem galeShapley_individuallyRational (P : Problem) :
    individuallyRational P (galeShapley P) := by
  classical
  have hmen : menAcceptableState P (GSState.runSteps P (proposalBound P)) :=
    runSteps_menAcceptable P (proposalBound P)
  have hwomen : womenAcceptableState P (GSState.runSteps P (proposalBound P)) :=
    runSteps_womenAcceptable P (proposalBound P)
  refine ⟨?_, ?_⟩
  · intro m w hmatch
    simpa [galeShapley] using hmen m w hmatch
  · intro w m hmatch
    simpa [galeShapley] using hwomen w m hmatch

-- The output matching has no blocking pairs.
theorem galeShapley_noBlockingPairs (P : Problem) :
    ∀ m w, ¬ blockingPair P (galeShapley P) m w := by
  classical
  intro m w hblock
  rcases hblock with ⟨hacc, hmenpref, hwompref⟩
  -- Unfold the final state to reuse invariants about proposals and best matches.
  let σ := GSState.runSteps P (proposalBound P)
  have hterm : terminated P σ := by
    simpa [σ] using galeShapley_terminates P
  have hdown : menProposedDownwardState P σ :=
    runSteps_menProposedDownward P (proposalBound P)
  have hmatchProp : menMatchedProposedState P σ :=
    runSteps_menMatchedProposed P (proposalBound P)
  have hbest : womenBestState P σ :=
    runSteps_womenBest P (proposalBound P)
  have hrej : womenUnmatchedRejectState P σ :=
    runSteps_womenUnmatchedReject P (proposalBound P)
  have hwomenAcc : womenAcceptableState P σ :=
    runSteps_womenAcceptable P (proposalBound P)
  have hmenAcc : menAcceptableState P σ :=
    runSteps_menAcceptable P (proposalBound P)
  have hmenpref' :
      prefersOpt P.menPrefs m (some w) (σ.matching.menMatches m) := by
    simpa [galeShapley, σ] using hmenpref
  have hwompref' :
      prefersOpt P.womenPrefs w (some m) (σ.matching.womenMatches w) := by
    simpa [galeShapley, σ] using hwompref
  -- Show m must have proposed to w (downward-closure or termination).
  have hprop : σ.proposed m w := by
    cases hmatch : σ.matching.menMatches m with
    | some wmatch =>
        have haccMatch : P.menPrefs.acceptable m wmatch := hmenAcc _ _ hmatch
        have haccw : P.menPrefs.acceptable m w := hacc.1
        have hpref : P.menPrefs.prefers m w wmatch := by
          have hiff :=
            prefersOpt_some_some_iff (p := P.menPrefs) (a := m)
              (o1 := w) (o2 := wmatch) haccw haccMatch
          exact hiff.mp (by simpa [hmatch] using hmenpref')
        have hpropMatch : σ.proposed m wmatch := hmatchProp _ _ hmatch
        exact hdown _ _ _ hpropMatch hpref
    | none =>
        by_contra hnot
        have haccw : P.menPrefs.acceptable m w := hacc.1
        have hwmem : w ∈ candidateWomen P σ m := by
          simp [candidateWomen, haccw, hnot]
        have hfree : isFree P σ m := by
          exact ⟨hmatch, ⟨w, hwmem⟩⟩
        exact (hterm ⟨m, hfree⟩).elim
  -- Split on whether w is unmatched or matched in the final state.
  cases hwmatch : σ.matching.womenMatches w with
  | none =>
      have hnotacc : ¬ P.womenPrefs.acceptable w m :=
        hrej _ _ hwmatch hprop
      have : ¬ prefersOpt P.womenPrefs w (some m) none := by
        simp [prefersOpt, hnotacc]
      exact (this (by simpa [hwmatch] using hwompref')).elim
  | some mW =>
      by_cases hEq : m = mW
      · subst hEq
        have haccW : P.womenPrefs.acceptable w m := hwomenAcc _ _ hwmatch
        have hiff :=
          prefersOpt_some_some_iff (p := P.womenPrefs) (a := w)
            (o1 := m) (o2 := m) haccW haccW
        have hpref : P.womenPrefs.prefers w m m := by
          exact hiff.mp (by simpa [hwmatch] using hwompref')
        exact (P.womenPrefs.prefers_irrefl w m) hpref
      ·
        have hbest' : prefersOpt P.womenPrefs w (some mW) (some m) :=
          hbest _ _ _ hwmatch hprop hEq
        have hcontra :=
          prefersOpt_asymm (p := P.womenPrefs) (a := w) (o1 := mW) (o2 := m) hbest'
        exact (hcontra (by simpa [hwmatch] using hwompref')).elim



-- The output matching is stable.
theorem galeShapley_stable (P : Problem) : stable P (galeShapley P) := by
  classical
  refine ⟨galeShapley_consistent P, ?_, ?_⟩
  · exact galeShapley_individuallyRational P
  · intro m w
    exact galeShapley_noBlockingPairs P m w

end

end StableMarriageLean
