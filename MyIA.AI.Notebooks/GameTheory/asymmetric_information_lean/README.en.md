# `asymmetric_information_lean` — Lean 4 Lake

Formalization of the **founding models** of informational asymmetry in
game theory, in the continuation of the **GT-17** (Game Theory) of the
`CoursIA` notebook family.

## Scope

| Model | Module | Reference |
|---|---|---|
| Lemons (used car market) | `AsymmetricInformation.Lemons` | Akerlof (1970) *QJE* 83(3):488-500 |
| Signaling (education signal) | `AsymmetricInformation.Signaling` | Spence (1973) *QJE* 87(3):355-374 |
| Screening (adverse selection, insurer competition) | `AsymmetricInformation.Screening` | Rothschild-Stiglitz (1976) *QJE* 90(4):629-649 |
| Anticipatory / cross-subsidy | `AsymmetricInformation.MiyazakiWilson` | Wilson 1977 *JET* 16:167-207, Miyazaki 1977 *Bell J.* 8(2):394-418, Spence 1978 |
| Non-trivial Bayesian bridge | `AsymmetricInformation.BayesianLink` | `lean_game_defs_ext.Bayesian` (upstream) |

**First delivery**: bounded scope, conforming to the canonical audit
c.475 (framing corrected by po-2025 before delivery, see Epic **#12844**).

## Explicit bounds

- **No** general existence/uniqueness theorem for the anticipatory
  equilibrium (Wilson-MWS) — each lemma lists its FINITE hypotheses.
- **No** auxiliary clause in κ (Lemons) — fixed-point on participation
  regions only.
- **No** cross-subsidy in RS (1976) — cross-subsidy belongs to the
  MWS anticipatory framework (1977-1978).
- **No** Mathlib `os`: all proofs rely on Lean 4 core +
  `lean_game_defs_ext.Bayesian` (Int, `decide`, `omega`).

## Non-trivial Bayesian bridge

`AsymmetricInformation.BayesianLink.bridgeStrategy_isBNE` is certified by
`decide` on a closed instance (price `c_L`, seller always accepts). The
BNE is therefore **verified** in the `lean_game_defs_ext.Bayesian` semantics,
not a mere empty import.

## Build

```bash
cd MyIA.AI.Notebooks/GameTheory/asymmetric_information_lean
lake build                                       # 28/28 jobs SUCCESS
python scripts/lean/count_code_sorry.py --json   # distinct_code_sorry=0 (zero sorry)
python scripts/lean/check_i18n_siblings.py --all # 0 drift / 0 orphan
```

## Tools

- **Lake** 4.32.1 (toolchain pinned via `lean-toolchain`).
- **`lean_game_defs_ext`** (neighboring path dep) — provides `Bayesian.*`
  (game, strategies, `isBNE`, etc.).

## i18n convention

EPIC **#4980** (ratified by user 2026-07-04): sibling pair FR/EN. FR
docstrings in the own files (`*.lean`), EN mirror in `*_en.lean`
(byte-identical except docstrings). See `README.md` for the French version.

## Canonical sources (audit c.475)

- Akerlof (1970) *QJE* 83(3):488-500 — *The Market for Lemons*
- Spence (1973) *QJE* 87(3):355-374 — *Job Market Signaling*
- Rothschild-Stiglitz (1976) *QJE* 90(4):629-649 — *Equilibrium in Competitive Insurance Markets*
- Riley (1979) *Econometrica* 47(2):331-359 — *Informational Equilibrium*
- Wilson (1977) *JET* 16:167-207 — *A Model of Insurance Markets with Incomplete Information*
- Miyazaki (1977) *Bell J.* 8(2):394-418 — *The Rat Race Problem When Participation Is Unobservable*
- Holmström-Milgrom (1991) — principal-agent reference model
