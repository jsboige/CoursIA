# hecke_lean — Classical Hecke operators

Standalone Lean 4 lake dedicated to the **classical Hecke operators** on
the upper half-plane: explicit construction of the representatives
`γ_{p,j} = !![1, j; 0, p]` and `!![p, 0; 0, 1]`, the operators `U_p` and
`T_p` via the slash action, full linearity (addition, negation,
subtraction, scalars), and the **Fourier coefficient formula**

$$
(T_p f)_n \;=\; a(np) + \begin{cases} p^{k-1}\, a(n/p) & \text{if } p \mid n, \\ 0 & \text{otherwise}, \end{cases}
$$

formalized by `coeffHeckeT` with its two reading lemmas
`coeffHeckeT_of_dvd` / `coeffHeckeT_of_not_dvd`, plus computable examples
(weight 12, `p ∈ {2, 3}`).

## Origin

Sub-grain of #14771 (mapping of the `anthropics/fermats-last-theorem`
repository for CoursIA), delivered under #14784. The module is a
pedagogical port of the upstream file
`Definitions/Def_ModularForm_HeckeOperator.lean` (commit `aa2d8b34692b`):
statements and proofs carried over unchanged, FR docstrings + EN sibling
(`ModularForm_en`), computable examples added — see `NOTICE.md` for the
Apache-2.0 attribution.

## Building

```bash
lake update && lake exe cache get && lake build
```

Target: Lean `v4.33.0`, Mathlib pin `db584cd6d46c` (anchor #14773).
No `sorry`, no `native_decide`; axioms of the flagship declarations:
`[propext, Classical.choice, Quot.sound]`.

## Structure

| File | Content |
|------|---------|
| `Hecke/HeckeOperator.lean` | Main module (FR docstrings) |
| `Hecke/HeckeOperator_en.lean` | English sibling, namespace `ModularForm_en` |
| `Hecke.lean` / `Hecke_en.lean` | Root aggregators |

## Follow-ups

The Petersson product and cusp forms form a downstream grain (see #14784).
The other FLT sub-grains (adic completions #14783, ramification groups
#14786…) live in `galois_lean` after the #14773 migration — this lake is
autonomous and does not depend on it.
