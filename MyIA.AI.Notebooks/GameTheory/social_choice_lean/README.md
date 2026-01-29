# Social Choice Theory in Lean 4

Complete port of [asouther4/lean-social-choice](https://github.com/asouther4/lean-social-choice) from Lean 3 to Lean 4.

## Contents

This library formalizes key results in social choice theory:

### Arrow's Impossibility Theorem

**Main theorem**: Any social welfare function over at least 3 alternatives that satisfies:
1. **Weak Pareto**: If everyone strictly prefers x to y, society does too
2. **Independence of Irrelevant Alternatives (IIA)**: Social ranking of x vs y depends only on individual rankings of x vs y

...must be a **dictatorship** (one individual determines all social rankings).

### Sen's Liberal Paradox

**Main theorem**: No social decision procedure can simultaneously satisfy:
1. **Weak Pareto criterion**
2. **Minimal liberalism**: Some individuals are decisive over some pairs

## Structure

```
SocialChoice/
├── Basic.lean       # Core definitions (P, I, QuasiOrder, PrefOrder, choice sets)
├── Arrow.lean       # Arrow's Impossibility Theorem
└── Sen.lean         # Sen's Liberal Paradox
```

## Building

```bash
# First time: fetch Mathlib cache
lake exe cache get

# Build the library
lake build
```

## Key Definitions

| Definition | Description |
|------------|-------------|
| `P R x y` | Strict preference: x is strictly preferred to y |
| `I R x y` | Indifference: x and y are equally ranked |
| `PrefOrder` | Complete, transitive, reflexive preference relation |
| `Profile` | Assignment of preferences to individuals |
| `SWF` | Social welfare function: profiles → social preference |
| `weak_pareto` | Unanimity condition |
| `ind_of_irr_alts` | Independence of irrelevant alternatives |
| `is_dictatorship` | One individual determines all rankings |

## Proof Structure (Arrow)

1. **Extremal Lemma**: If all place b at top or bottom, society does too
2. **Pivot Existence**: Every alternative has a pivotal individual
3. **Third Step**: Pivots become dictators over non-b pairs
4. **Fourth Step**: Partial dictatorship extends to full dictatorship

## References

- Arrow, K. J. (1951). Social Choice and Individual Values
- Sen, A. K. (1970). Collective Choice and Social Welfare
- Geanakoplos, J. (2005). Three Brief Proofs of Arrow's Impossibility Theorem

## Original Repository

Ported from: https://github.com/asouther4/lean-social-choice (Lean 3, 272 commits)

## License

See the main repository license.
