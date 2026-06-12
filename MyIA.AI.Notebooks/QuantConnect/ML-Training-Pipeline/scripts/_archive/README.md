# scripts/_archive — superseded experiment scripts

Consolidation #1409 (2026-06-12). Each archived file carries a header with: date,
superseded-by, recorded verdict location, and a per-function disposition table
mapping every function of the old script to its successor (exact line numbers)
or to a documented ABANDONED reason — per the "Consolider != Archiver" discipline.

| Script | Verdict | Superseded by | Verdict recorded in |
|--------|---------|---------------|---------------------|
| `s2_vol_ensemble_dm.py` | NO BEATS (0/84 combos) | `scripts/s2_v2_vol_ensemble_dm.py` | `results/s2_vol_ensemble_dm/verdict.md`, `docs/RECAP_KEEPERS_V2.md` |
| `s2_gsp_cross_asset_vol.py` | NO BEATS (MSE -12%, no Sharpe translation) | none — closed dead-end | `docs/RECAP_KEEPERS_V2.md` |
| `s4_inverse_vol_ridge.py` | NO BEATS (+0.022, MaxDD -82.4%) | `scripts/s4_inverse_vol_ridge_v2.py` (KEEPER +0.325) | `docs/RECAP_KEEPERS_V2.md` |

Eligibility criteria applied (all three verified 2026-06-12):

1. NO BEATS verdict recorded in `docs/RECAP_KEEPERS_V2.md` (and `results/` where present)
2. Zero references from `docs/*.md`, `README.md`, `REGISTRY.md`
3. Zero imports from any other script in `scripts/`
4. A successor exists (or the line of work is explicitly closed)

NOT archived despite versioned names: `m11c_sharpe_test.py` and
`m11g_fee_aware_kelly.py` are **shared modules** imported by 15+ scripts;
`m11i_per_coin_attribution.py` and `m12_per_coin_attribution.py` are both
doc-referenced; `s7_composite.py` is imported by `L5_vol_targeted_composite.py`.

These files are retained for forensic reproducibility of their recorded verdicts
only. Do not import or extend them for new work.
