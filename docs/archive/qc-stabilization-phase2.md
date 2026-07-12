# QC Stabilization Phase 2 — Methodology

**Issue**: #667 (Phase 2), parent #623
**Date**: 2026-05-07
**Status**: Draft

---

## Problem

70+ open issues with ambiguous status — some strategies are intentionally broken for pedagogical purposes (demonstrating what NOT to do), while others have genuine bugs requiring fixes. Phase 1 cataloged maturity; Phase 2 classifies intent.

## Label Taxonomy

### BROKEN_PEDAGOGICAL (`pedagogical:broken-intentional`)

**Definition**: Strategy produces poor results (negative Sharpe, 0 trades, high drawdown) **by design** — the brokenness IS the lesson.

**Criteria**:
- Strategy demonstrates a known pitfall (overfitting, data snooping, look-ahead bias)
- Poor performance is expected and documented in README
- Used as a teaching example: "Here's what goes wrong when..."

**Examples**:
- ForexCarry (#17): Negative carry strategy demonstrates currency risk
- VIX-TermStructure (#18): Fixed but still Sharpe +0.05 — demonstrates contango/backwardation
- Composite FamaFrench (#44): Intentional baseline comparison
- Proposer nouvelles strategies (#35): Pedagogical brainstorm issue

### BROKEN_TO_FIX (`pedagogical:broken-to-fix`)

**Definition**: Strategy has a genuine bug or missing dependency that prevents proper evaluation. Performance may improve once fixed.

**Criteria**:
- Code error (0 trades due to signal logic bug, wrong universe, timing issue)
- Missing data source (CBOE VIX futures unavailable on QC Cloud)
- Architectural issue (indicator calculation, order placement, warmup period)

**Examples**:
- Crypto-MultiCanal (#34): Bug causing 0 trades
- Stoploss-Volatility-ML (#233): CBOE data unavailable

### Classification Decision Tree

```
Is the strategy runnable on QC Cloud?
├── YES → Does it produce trades?
│   ├── YES → Is Sharpe > 0.5?
│   │   ├── YES → Label: HEALTHY (iteration-N)
│   │   └── NO → Is the poor performance the POINT?
│   │       ├── YES → BROKEN_PEDAGOGICAL
│   │       └── NO → NEEDS_IMPROVEMENT (genuine attempt to beat market)
│   └── NO → Is it a code bug?
│       ├── YES → BROKEN_TO_FIX + bug label
│       └── NO → BROKEN_PEDAGOGICAL (intentional demo)
└── NO → Missing dependency?
    ├── YES → BROKEN_TO_FIX
    └── NO → Enhancement request (not broken)
```

## Revalidation Process

### Periodic Review (monthly)

1. **Batch audit**: `gh issue list --label "pedagogical:broken-intentional" --state open`
2. **Verify intent**: Check README and code for pedagogical documentation
3. **Check QC Cloud**: Re-run backtest if Cloud API available
4. **Promote**: If a pedagogical strategy gets genuine improvement PR → relabel as NEEDS_IMPROVEMENT

### Promotion Path

```
BROKEN_PEDAGOGICAL → NEEDS_IMPROVEMENT → HEALTHY
                  (genuine fix PR)      (Sharpe > 0.5)
```

### Demotion Path

```
HEALTHY → NEEDS_IMPROVEMENT → BROKEN_TO_FIX
        (QC API change)      (data source removed)
```

## Label Application Guide

| Label | Color | When to Apply |
|-------|-------|---------------|
| `pedagogical:broken-intentional` | Dark red | Strategy's poor result IS the lesson |
| `pedagogical:broken-to-fix` | Orange | Bug/dependency preventing evaluation |
| `bug` | Red | Code error in production code |
| `NEEDS_IMPROVEMENT` | Yellow | Runnable but below target metrics |
| `HEALTHY` | Green | Sharpe > 0.5, regular iterations |
| `stabilization-phase-1` | Blue | Cataloged in Phase 1 maturity matrix |

## Issue Triage Workflow

For each open QC strategy issue:

1. Check if strategy has QC Cloud project ID
2. If yes → verify latest backtest status via MCP
3. Apply label based on decision tree above
4. Add comment documenting classification rationale
5. Update catalog with broken_reason column

## Metrics

| Metric | Target | Current |
|--------|--------|---------|
| Issues classified | 70+ | ~7 done |
| BROKEN_PEDAGOGICAL tagged | -- | 4 (#17, #18, #44, #35) |
| BROKEN_TO_FIX tagged | -- | 2 (#34, #233) |
| Pedagogical README docs | All BROKEN_PEDAGOGICAL | Partial |

## References

- Issue #623: Stabilization Phase 1
- Issue #667: Stabilization Phase 2 (this doc)
- Issue #661: Catalog maturity classification (B-2)
- Issue #29: QC Strategy iterative improvement tracker
