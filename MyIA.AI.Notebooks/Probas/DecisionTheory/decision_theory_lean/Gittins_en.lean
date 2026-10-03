import Gittins.Basic
import Gittins.Discount
import Gittins.GittinsTheorem

/-!
# Gittins Index — Formal Verification

This library formalizes key concepts of the Gittins Index theorem
for multi-armed bandits with geometric discounting.

## Contents
- `Gittins.Basic`: Bandit arm types, policy, value function
- `Gittins.Discount`: Geometric discount identities (proved)
- `Gittins.GittinsTheorem`: Gittins Index definition and optimality (sorry)

## Status
- Proved lemmas: geometric convergence, present value, discount monotonicity
- Sorry statements: Gittins optimality theorem, index computation

## References
- J.C. Gittins, "Bandit Processes and Dynamic Allocation Indices" (1979)
- J.C. Gittins and D.M. Jones, "A dynamic allocation index for the
  discounted multiarmed bandit problem" (1974)

i18n convention (EPIC #4980, user decision 2026-07-04): this root
aggregator file is the English mirror of `Gittins.lean` (FR-first canonical).
Sibling pair model ratified 2026-07-04 per
`.claude/rules/code-style.md` §Lean i18n (FR-first canonical with optional
EN sibling for publication audience). This is a pure landing doc module
(imports + module docstring, no declarations) so no namespace suffix is
needed (mirrors the FR root structure exactly). Submodule EN siblings live
under `Gittins/*_en.lean`.
-/
