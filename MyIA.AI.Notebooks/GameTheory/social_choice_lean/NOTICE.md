# Attribution Notice - Social Choice Theory (Lean 4)

This library formalizes key results in social choice theory in Lean 4.
It is derived from multiple open-source projects and academic work.

## Original Sources

### asouther4/lean-social-choice (Lean 3)
- **URL**: https://github.com/asouther4/lean-social-choice
- **License**: MIT
- **Usage**: Original Lean 3 formalization of Arrow's theorem and Sen's paradox.
  Ported to Lean 4 with significant modifications including the Geanakoplos (2005)
  proof approach for Arrow's theorem and bidirectional formulation for Sen's theorem.

### chasenorman/lean-social-choice (Lean 3 fork)
- **URL**: https://github.com/chasenorman/lean-social-choice
- **License**: MIT
- **Usage**: Fork with additional definitions and lemma structures used as reference
  during the Lean 4 port.

### DominikPeters/lean-social-choice (Lean 3 fork)
- **URL**: https://github.com/DominikPeters/lean-social-choice
- **License**: MIT
- **Usage**: Fork with alternative proof structures consulted during development.

## Academic References

- **Arrow, K.J.** (1951). *Social Choice and Individual Values*. Wiley.
- **Sen, A.** (1970). *Collective Choice and Social Welfare*. Holden-Day.
- **Geanakoplos, J.** (2005). "Three Brief Proofs of Arrow's Impossibility Theorem."
  *Economic Theory*, 26(1), 211-215.

## Mathematical Library

This project depends on **Mathlib**, the Lean 4 mathematical library:
- **URL**: https://github.com/leanprover-community/mathlib4
- **License**: Apache 2.0

## Lean Toolchain

- **Lean**: v4.28.0-rc1+
- **Lake**: v5.0.0+
