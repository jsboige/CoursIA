/-
  Tour of DominikPeters/SocialChoiceLean Results
  ===============================================

  This file provides a curated tour of the main results formalized in
  DominikPeters/SocialChoiceLean, imported as a Lake dependency.

  Repository: https://github.com/DominikPeters/SocialChoiceLean
  Authors: Dominik Peters (University of Glasgow)
  License: MIT

  Key contributions:
  1. Gibbard-Satterthwaite theorem (strategyproofness => dictatorship)
  2. 4 Condorcet impossibilities
  3. Duggan-Schwartz theorem (multi-winner strategyproofness)
  4. Holliday's impossibility (Split Cycle resolvability)
  5. 15+ voting rules with verified axiom satisfaction
-/

-- Core framework
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Rules

-- Axioms
import SocialChoice.Axioms.Core
import SocialChoice.Axioms.Pareto
import SocialChoice.Axioms.Dictatorship
import SocialChoice.Axioms.Strategyproofness
import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Monotonicity
import SocialChoice.Axioms.Neutrality
import SocialChoice.Axioms.Anonymity
import SocialChoice.Axioms.Clones

-- Impossibility theorems
import SocialChoice.Impossibilities.GibbardSatterthwaite.Main

-- Voting rules
import SocialChoice.Rules.SplitCycle.Defs
import SocialChoice.Rules.Schulze.Defs
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.Copeland.Defs
import SocialChoice.Rules.Minimax.Defs
import SocialChoice.Rules.TopCycle.Defs
import SocialChoice.Rules.UncoveredSet.Defs

namespace PetersTour

open SocialChoice

/-! ## 1. Framework Overview

DominikPeters uses a polymorphic `VotingRule` type:
```
abbrev VotingRule := ∀ {V A : Type} [Fintype V] [Fintype A], Profile V A → Finset A
```

A `Profile V A` maps each voter `v : V` to a `LinearOrder A` (strict linear order).
This differs from our `PrefOrder`-based framework (which uses reflexive+total+transitive
relations via `R x y : Prop`).

Key differences with our port (asouther4/chasenorman):
- Peters: `LinearOrder A` (Lean 4 Mathlib class, decidable)
- Ours: `PrefOrder α` (custom structure, `R x y : Prop`)
- Peters: `VotingRule` polymorphic over all V, A
- Ours: `SCC ι σ` fixed types, `PrefOrder`-based

-/


/-! ## 2. Gibbard-Satterthwaite Theorem

**Theorem** (Gibbard 1973, Satterthwaite 1975):
Every resolute voting rule with >= 3 candidates that satisfies
Unanimity and Strategyproofness must be dictatorial.

This is formalized in `SocialChoice.Impossibilities.GibbardSatterthwaite.Main`:
```
theorem gibbard_satterthwaite
    {V A : Type} [Fintype V] [Nonempty V] [Fintype A] [Nonempty A]
    (hcardA : 3 ≤ Fintype.card A)
    (f : VotingRule)
    (hf_res : Resolute f)
    (hf_unan : Unanimity f)
    (hf_sp : ResoluteStrategyproofness f hf_res) :
    ∃ d : V, ∀ P : Profile V A, f P = {topChoice P d}
```

Proof structure:
- Strong induction on the number of voters
- Base case (1 voter): trivially dictatorial
- Inductive step: clone a voter, apply IH to reduced electorate,
  then analyze whether the dictator is the cloned voter (Case 2)
  or another voter (Case 1)
-/


/-! ## 3. Condorcet Impossibilities

DominikPeters formalizes 4 Condorcet-related impossibility results:

1. **Condorcet + Participation => impossible** (Moulin 1988)
   `SocialChoice.Impossibilities.CondorcetParticipation`

2. **Condorcet + Reinforcement => impossible** (Young 1975)
   `SocialChoice.Impossibilities.CondorcetReinforcement`

3. **Condorcet + Strategyproofness => impossible** (Gibbard-Satterthwaite variant)
   `SocialChoice.Impossibilities.CondorcetStrategyproofness`

4. **Anonymous + Neutral + Resolute => impossible** (for even number of voters)
   `SocialChoice.Impossibilities.AnonymousNeutralResolute`
-/


/-! ## 4. Duggan-Schwartz Theorem

The Duggan-Schwartz theorem extends Gibbard-Satterthwaite to multi-winner rules:
if a voting rule satisfies OptimistStrategyproof AND PessimistStrategyproof
and is non-trivial and onto, then it has a "nominating set" that acts as a
dictating coalition.

Formalized in `SocialChoice.Impossibilities.DugganSchwartz.Main`.
-/


/-! ## 5. Voting Rules and Their Properties

DominikPeters verifies axiom satisfaction for 15+ voting rules:

### Condorcet-Consistent Rules
- **Split Cycle** (Holliday & Pacuit 2023): Acyclic method using margin comparison
  `SocialChoice.Rules.SplitCycle`
  Verified: Condorcet, Monotonicity, Pareto, Neutrality, Smith, Clones

- **Schulze** (Schulze 2011): Path-based comparison
  `SocialChoice.Rules.Schulze`
  Verified: Condorcet, Monotonicity, Neutrality, Smith, Clones, Transitivity

- **Copeland**: Win/loss scoring
  `SocialChoice.Rules.Copeland`
  Verified: Condorcet, Monotonicity, Neutrality, Pareto, Smith

- **Top Cycle** (Smith set): Maximal element of the majority relation
  `SocialChoice.Rules.TopCycle`
  Verified: Condorcet, Monotonicity, Smith, MutualMajority

- **Uncovered Set**: Based on covering relation
  `SocialChoice.Rules.UncoveredSet`
  Verified: Condorcet, Monotonicity, Neutrality, Smith, Clones

- **Black**: Condorcet winner if exists, else Borda
  `SocialChoice.Rules.Black`
  Verified: Condorcet, Monotonicity, Neutrality, Pareto

### Elimination Rules
- **Instant Runoff Voting (IRV)**: Sequential elimination
  `SocialChoice.Rules.ScoringElimination.InstantRunoffVoting`
  Verified: CondorcetLoser, Majority, MutualMajority, Clones

- **Baldwin**: Borda-based elimination
  `SocialChoice.Rules.ScoringElimination.Baldwin`
  Verified: Condorcet, CondorcetLoser, Smith

- **Coombs**: Last-place elimination
  `SocialChoice.Rules.ScoringElimination.Coombs`
  Verified: Condorcet, CondorcetLoser, Majority

### Scoring Rules
- **Borda count**: `SocialChoice.Rules.ScoringRules.Borda`
  Verified: Monotonicity, Neutrality, Pareto, Participation

- **Plurality**: `SocialChoice.Rules.ScoringRules.Plurality`
  Verified: Monotonicity, Majority

- **Veto/Anti-plurality**: `SocialChoice.Rules.ScoringRules.Veto`
  Verified: Monotonicity, Majority
-/


/-! ## 6. Key Definitions Reference

```
-- Profile: maps voters to strict linear orders
structure Profile (V A : Type) [Fintype V] [Fintype A] where
  pref : V → LinearOrder A

-- Margin: difference in pairwise support
noncomputable def margin {V A} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) : Int

-- Condorcet winner: beats every other by strict majority
def CondorcetWinner {V A} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Prop

-- Split Cycle defeat: positive margin, no stronger cycle
noncomputable def splitCycleDefeats {V A} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) : Prop :=
  margin_pos P x y ∧
    ¬ ∃ c : List A, x ∈ c ∧ y ∈ c ∧
      cycle (fun a b => margin P x y ≤ margin P a b) c
```
-/


/-! ## 7. Axiom Summary Table

The `@[scAxiom]` and `@[scRule]` attributes mark definitions for the
axiom verification framework. Each rule file proves axiom satisfaction
using `PreservedUnderRefinement` lemmas for compositional reasoning.

| Axiom | Definition |
|-------|------------|
| Resolute | Single winner for every profile |
| NonTrivial | Some candidate can lose |
| Onto | Every candidate can win |
| Unanimity | If all rank c first, c wins |
| ParetoEfficiency | Unanimously dominated candidates lose |
| CondorcetConsistency | Condorcet winner uniquely wins |
| CondorcetLoserCriterion | Condorcet losers never win |
| Monotonicity | Raising c preserves c winning |
| Neutrality | Permuting candidates permutes winners |
| Anonymity | Permuting voters doesn't change outcome |
| Strategyproofness | No voter can gain by misreporting |
| Clones | Cloning a candidate preserves outcome |
| Smith | Smith set candidates only win |
| Reinforcement | Union of disjoint electorates => intersection |
| Participation | Adding voters with c on top preserves c winning |
| Reversal | Reversing all ballots reverses losers |
| Resolvability | Non-singleton output can be resolved |
-/

end PetersTour
