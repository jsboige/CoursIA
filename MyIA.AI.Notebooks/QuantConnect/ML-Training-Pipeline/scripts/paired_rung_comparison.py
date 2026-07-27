"""Paired cross-rung comparison on per-seed edges (#8607, parent #1409).

Purpose
-------
``seed_significance.py`` (c.902, PR #8626) answers, per rung: "is this model
significantly below majority?" (one-sample t-test on the per-seed edge
``edge_s = DirAcc_s - majority``, n=5 seeds). The 3 foundation rungs are all
NO BEATS (Chronos degenerate, Kronos 6/9 SIG-negative, M15 9/9 SIG-negative).

This module answers the **next** question: **are two rungs significantly
different FROM EACH OTHER?** A zero-shot model (Kronos, AR sampling) and a
fine-tuned model (M15 LSTM) both fail to beat majority -- but does fine-tuning
change the directional edge relative to zero-shot, or do they land on the same
edge? This is a **paired** comparison on the aligned ``(symbol, horizon, seed)``
edges: for each of the 45 aligned observations (3 ETF x 3 horizons x 5 seeds)
we have ``edge_kronos`` and ``edge_m15``, and we test the per-pair difference
``d = edge_B - edge_A`` against 0 (paired t-test + Wilcoxon + sign + CI95%).

This is NOT the full Diebold-Mariano test. DM is paired **by observation**
(per-window / per-step forecast errors with a HAC variance correction) and
requires the per-window DirAcc series, which is NOT committed (Kronos only
dumps the fold-aggregated ``avg_direction_accuracy`` per seed). The true DM
therefore remains a multi-cycle residual (re-run dumping per-window DirAcc).
This paired-by-(config, seed) test is the strongest cross-rung comparison
available from the committed per-seed edges -- no re-run needed.

Honest scope
------------
- **Kronos <-> M15**: clean 45-pair alignment (both SPY/TLT/GLD x h={24,66,132}
  x seeds {0,1,7,42,99}). This is the primary result.
- **Chronos**: deterministic (std_edge=0, 1 edge per config, 7 configs) so it
  has no per-seed variance -> paired comparison vs Chronos is done against the
  Kronos/M15 **per-seed** edges with Chronos as a constant, reported separately
  and interpreted cautiously (C893-L: deterministic rung).

Usage
-----
    python paired_rung_comparison.py <rungA.json> <rungB.json> [--alpha 0.05]

Outputs ``paired_comparison.json`` + ``paired_comparison.md`` next to rungB's
results (convention: the comparison artefacts live under the rung being
compared-against). With ``--out`` the artefacts go to an explicit folder.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Optional

import numpy as np
from scipy import stats

ALPHA = 0.05  # two-sided significance level


# ---------------------------------------------------------------------------
# Per-seed extraction (preserves seed identity, unlike seed_significance.auto_extract)
# ---------------------------------------------------------------------------

def _kronos_per_seed(sweep: list) -> dict[tuple, float]:
    """Kronos: sweep[i].seed_results[j] -> {(symbol, pred_len, seed): edge}."""
    out: dict[tuple, float] = {}
    for cfg in sweep:
        sym = cfg.get("symbol")
        h = cfg.get("pred_len")
        cfg_maj = cfg.get("majority_baseline", {}).get("majority_class_accuracy")
        for s in cfg.get("seed_results", []):
            seed = s.get("seed")
            edge = s.get("edge_vs_majority")
            if edge is None:
                # Fallback: DirAcc - majority (some schemas omit edge_vs_majority).
                da = s.get("avg_direction_accuracy")
                maj = s.get("majority_baseline")
                if maj is None:
                    maj = cfg_maj  # fall back to config-level majority
                if da is not None and maj is not None:
                    edge = float(da) - float(maj)
            if seed is not None and edge is not None:
                out[(sym, h, int(seed))] = float(edge)
    return out


def _m15_per_seed(combos: list) -> dict[tuple, float]:
    """M15: combos[i] -> {(symbol, horizon, seed): edge}."""
    out: dict[tuple, float] = {}
    for c in combos:
        sym = c.get("symbol")
        h = c.get("horizon")
        seed = c.get("seed")
        edge = c.get("edge_vs_majority")
        if edge is None:
            da = c.get("direction_accuracy")
            maj = c.get("majority_baseline", {}).get("majority_class_accuracy")
            if da is not None and maj is not None:
                edge = float(da) - float(maj)
        if seed is not None and edge is not None:
            out[(sym, h, int(seed))] = float(edge)
    return out


def _chronos_per_config(sweep: list) -> dict[tuple, float]:
    """Chronos: deterministic -> {(symbol, pred_len, None): edge}."""
    out: dict[tuple, float] = {}
    for cfg in sweep:
        sym = cfg.get("symbol")
        h = cfg.get("pred_len")
        edge = cfg.get("edge")
        if edge is None:
            edge = cfg.get("mean_edge")
        if edge is not None:
            out[(sym, h, None)] = float(edge)
    return out


def extract_per_seed(doc: dict) -> tuple[dict[tuple, float], str, bool]:
    """Auto-detect rung format -> (edges_by_key, model_name, is_deterministic)."""
    model = doc.get("model", "")
    sweep = doc.get("sweep")
    if sweep and isinstance(sweep, list) and sweep and "seed_results" in sweep[0]:
        return _kronos_per_seed(sweep), "Kronos", False
    if sweep and isinstance(sweep, list) and sweep and "diracc" in sweep[0]:
        return _chronos_per_config(sweep), "Chronos-Bolt", True
    if "combos" in doc:
        return _m15_per_seed(doc["combos"]), "M15", False
    raise ValueError("Unrecognized results.json format (expected Kronos/Chronos/M15)")


# ---------------------------------------------------------------------------
# Paired battery
# ---------------------------------------------------------------------------

def paired_battery(diffs: np.ndarray, alpha: float = ALPHA) -> dict:
    """Paired tests on the per-pair difference series d = edge_B - edge_A."""
    diffs = diffs[np.isfinite(diffs)]
    n = len(diffs)
    mean_d = float(np.mean(diffs)) if n else float("nan")
    # ddof=1 sample std of the differences
    std_d = float(np.std(diffs, ddof=1)) if n >= 2 else 0.0
    out = {
        "n_pairs": n,
        "mean_diff": mean_d,
        "std_diff": std_d,
        "median_diff": float(np.median(diffs)) if n else float("nan"),
    }
    if n < 2:
        out.update({"verdict": "n<2: paired test undefined",
                    "significant_at_alpha": False})
        return out
    se = std_d / math.sqrt(n)
    if se > 1e-12:
        t_stat = mean_d / se
    elif abs(mean_d) > 1e-15:
        # Zero variance but nonzero effect -> infinitely significant.
        t_stat = float("inf") * math.copysign(1, mean_d)
    else:
        # Zero variance AND zero effect (e.g. all diffs exactly 0) -> no effect.
        t_stat = 0.0
    t_p = 2.0 * stats.t.sf(abs(t_stat), df=n - 1)
    tcrit = stats.t.ppf(1 - alpha / 2, df=n - 1)
    ci_low = mean_d - tcrit * se
    ci_high = mean_d + tcrit * se
    # Wilcoxon signed-rank (on |d| > 0). scipy warns if zeros; guard.
    nz = diffs[diffs != 0]
    if len(nz) == 0:
        # All differences exactly zero -> cannot reject, perfectly balanced.
        wilcoxon_stat = float("nan")
        wilcoxon_p = 1.0
    elif np.all(nz[0] == nz):  # all identical non-zero
        wilcoxon_p = 0.0 if abs(nz[0]) > 0 else 1.0
        wilcoxon_stat = float("nan")
    else:
        try:
            w_stat, wilcoxon_p = stats.wilcoxon(diffs, zero_method="wilcox",
                                                correction=False,
                                                alternative="two-sided")
            wilcoxon_stat = float(w_stat)
        except ValueError:
            wilcoxon_stat = float("nan")
            wilcoxon_p = float("nan")
    # Sign (binomial) test on the differences vs 0
    n_pos = int(np.sum(diffs > 0))
    n_neg = int(np.sum(diffs < 0))
    n_nonzero = n_pos + n_neg
    if n_nonzero == 0:
        sign_p = 1.0
    else:
        k = min(n_pos, n_neg)
        sign_p = min(1.0, 2.0 * stats.binom.cdf(k, n_nonzero, 0.5))
    # Effect size: mean diff in DirAcc percentage points
    out.update({
        "t_stat": float(t_stat),
        "t_p_value": float(t_p),
        "df": n - 1,
        "ci95_low": float(ci_low),
        "ci95_high": float(ci_high),
        "wilcoxon_stat": wilcoxon_stat,
        "wilcoxon_p_value": float(wilcoxon_p),
        "sign_n_pos": n_pos,
        "sign_n_neg": n_neg,
        "sign_p_value": float(sign_p),
    })
    sig = bool(t_p < alpha)
    if not math.isfinite(t_p):
        sig = abs(mean_d) > 0
    direction = "B worse than A (more negative edge)" if mean_d < 0 else \
                ("B better than A (less negative edge)" if mean_d > 0 else "no difference")
    verdict = (
        f"{'SIGNIFICANT' if sig else 'not significant'}: mean paired diff "
        f"{mean_d:+.5f} (CI95 [{ci_low:+.5f}, {ci_high:+.5f}]), t={t_stat:+.3f} "
        f"(p={t_p:.4g}), {direction}"
    )
    out["significant_at_alpha"] = sig
    out["direction"] = direction
    out["verdict"] = verdict
    return out


def compare(rung_a: dict, rung_b: dict, alpha: float = ALPHA) -> dict:
    """Compare two rung docs. Returns the full structured verdict."""
    edges_a, name_a, det_a = extract_per_seed(rung_a)
    edges_b, name_b, det_b = extract_per_seed(rung_b)

    # Align on (symbol, horizon) first, then on seed.
    # Case 1: both per-seed (Kronos/M15) -> align (symbol, horizon, seed).
    # Case 2: one deterministic (Chronos, seed=None) -> align (symbol, horizon)
    #         and pair the deterministic constant against each per-seed edge.
    if not det_a and not det_b:
        common = sorted(set(edges_a) & set(edges_b))
        pairs = [(k, edges_a[k], edges_b[k]) for k in common]
    else:
        # Collapse the deterministic side to (symbol, horizon) and the other
        # side keeps per-seed; pair each seed against the constant.
        det_edges, det_name = (edges_a, name_a) if det_a else (edges_b, name_b)
        seed_edges, seed_name = (edges_b, name_b) if det_a else (edges_a, name_a)
        det_by_sh = {(k[0], k[1]): v for k, v in det_edges.items()}
        pairs = []
        for (sym, h, seed), sev in seed_edges.items():
            if (sym, h) in det_by_sh:
                a_val = det_by_sh[(sym, h)] if det_a else sev
                b_val = sev if det_a else det_by_sh[(sym, h)]
                pairs.append(((sym, h, seed), a_val, b_val))
        common = [p[0] for p in pairs]

    diffs = np.array([b - a for (_, a, b) in pairs], dtype=float) if pairs else \
        np.array([], dtype=float)
    battery = paired_battery(diffs, alpha=alpha)

    return {
        "rung_a": name_a,
        "rung_b": name_b,
        "rung_a_deterministic": det_a,
        "rung_b_deterministic": det_b,
        "alpha": alpha,
        "n_common_keys": len(common),
        "common_keys": [
            {"symbol": k[0], "horizon": k[1], "seed": k[2]} for k in common
        ],
        "pairs": [
            {"symbol": k[0], "horizon": k[1], "seed": k[2],
             "edge_a": a, "edge_b": b, "diff": b - a}
            for (k, a, b) in pairs
        ],
        "mean_edge_a": float(np.mean([a for (_, a, _) in pairs])) if pairs else float("nan"),
        "mean_edge_b": float(np.mean([b for (_, _, b) in pairs])) if pairs else float("nan"),
        "battery": battery,
    }


def render_md(out: dict) -> str:
    b = out["battery"]
    lines = []
    lines.append(f"# Paired cross-rung comparison -- {out['rung_a']} vs {out['rung_b']} (#8607)\n")
    det = ""
    if out["rung_a_deterministic"] or out["rung_b_deterministic"]:
        det = (f" ({'A' if out['rung_a_deterministic'] else 'B'}="
               f"{'Chronos' if out['rung_a_deterministic'] else 'Chronos'} "
               f"deterministic, paired vs per-seed)")
    lines.append(f"**Question**: is {out['rung_b']} significantly different from "
                 f"{out['rung_a']} on the directional edge?{det}\n")
    lines.append(f"**Alignment**: {out['n_common_keys']} paired (symbol, horizon, seed) "
                 f"observations. mean edge A={out['mean_edge_a']:+.5f}, "
                 f"mean edge B={out['mean_edge_b']:+.5f}.\n")
    lines.append("| metric | value |")
    lines.append("|--------|-------|")
    lines.append(f"| n pairs | {b['n_pairs']} |")
    lines.append(f"| mean diff (B-A) | {b['mean_diff']:+.5f} |")
    lines.append(f"| std diff | {b['std_diff']:.5f} |")
    lines.append(f"| paired t-stat (df={b.get('df','-')}) | {b.get('t_stat', float('nan')):+.3f} |")
    lines.append(f"| t p-value | {b.get('t_p_value', float('nan')):.4g} |")
    lines.append(f"| CI95 (mean diff) | [{b.get('ci95_low', float('nan')):+.5f}, {b.get('ci95_high', float('nan')):+.5f}] |")
    lines.append(f"| Wilcoxon p | {b.get('wilcoxon_p_value', float('nan')):.4g} |")
    lines.append(f"| sign p (n+={b.get('sign_n_pos','-')}, n-={b.get('sign_n_neg','-')}) | {b.get('sign_p_value', float('nan')):.4g} |")
    lines.append(f"| direction | {b.get('direction','-')} |")
    lines.append(f"| **verdict (alpha={out['alpha']})** | {b.get('verdict','-')} |")
    lines.append("")
    lines.append("## Interpretation\n")
    lines.append("Both rungs are individually NO BEATS vs majority (cf "
                 "`seed_significance_verdict.md`). This paired test asks whether they "
                 "differ **from each other**. A non-significant paired difference means "
                 "fine-tuning (B) did not change the directional edge relative to zero-shot "
                 "(A) -- reinforcing the #1409 conclusion that directional forecasting "
                 "edge is absent regardless of the forecasting paradigm; alpha comes from "
                 "**action policies** (L4-DT), not price-direction prediction.")
    lines.append("\n## Scope / residual\n")
    lines.append("- This is a paired-by-(config, seed) test on committed per-seed edges, "
                 "**not** a full Diebold-Mariano by-observation test. The true DM needs the "
                 "per-window DirAcc series (Kronos dumps only the fold aggregate) -> "
                 "multi-cycle residual (re-run dumping per-window forecasts).")
    return "\n".join(lines) + "\n"


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Paired cross-rung comparison on per-seed edges (#8607).")
    p.add_argument("rung_a", type=Path, help="Path to rung A results.json.")
    p.add_argument("rung_b", type=Path, help="Path to rung B results.json.")
    p.add_argument("--alpha", type=float, default=ALPHA)
    p.add_argument("--out", type=Path, default=None,
                   help="Output folder (default: rung_b's folder).")
    args = p.parse_args(argv)

    doc_a = json.loads(args.rung_a.read_text(encoding="utf-8"))
    doc_b = json.loads(args.rung_b.read_text(encoding="utf-8"))
    out = compare(doc_a, doc_b, alpha=args.alpha)
    out_folder = args.out if args.out is not None else args.rung_b.parent
    out_folder.mkdir(parents=True, exist_ok=True)
    (out_folder / "paired_comparison.json").write_text(
        json.dumps(out, indent=2), encoding="utf-8")
    (out_folder / "paired_comparison.md").write_text(
        render_md(out), encoding="utf-8")
    print(render_md(out))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
