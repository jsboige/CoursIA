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
-/
