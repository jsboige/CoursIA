"""Seed-level significance test for the foundation-model rungs (#8607).

Addresses the documented #8607 residual -- a proper t-stat cross-seed -- for the
STOCHASTIC foundation rungs (Kronos, M15), where the per-seed edge is a real
random variable. For the DETERMINISTIC rung (Chronos-Bolt, std_edge=0, C893-L)
the test is degenerate and is reported as such.

Why a NEW script (not diebold_mariano.py / dm_test.py)
------------------------------------------------------
The Diebold-Mariano test compares TWO forecasts' per-observation error series
(it needs paired loss differentials). That is NOT the question here. The
question here is: *is the model's cross-seed directional edge statistically
different from zero?* -- i.e. a one-sample test on the per-seed edge
``edge_s = DirAcc_s - majority`` across the ``n_seeds`` seeds. That is a
distinct statistical tool, so it lives in its own module rather than being
bolted onto the DM infrastructure (C898-L: do not mangle an imported helper's
contract; here we simply do not touch the DM scripts).

What it refines
---------------
The rungs' ``beats_valid`` gate encodes a 2-sigma heuristic:
``mean_edge >= 2 * std_edge``. That is a z-rule. With n=5 seeds the proper
reference distribution is Student's t with df=n-1=4 (heavier tails -> harder to
reject). This script reports the formal one-sample t-stat / p-value, a sign
(binomial) test, a Wilcoxon signed-rank test, and the 95% CI on the mean edge,
so the NO-BEATS verdict is backed by proper small-n statistics rather than a
point estimate.

Usage
-----
    # Kronos (committed on main)
    python seed_significance.py results/kronos_zeroshot/results.json

    # M15 (after #8625 merges)
    python seed_significance.py results/m15_lstm_etf/results.json

    # Chronos (deterministic -> reported degenerate)
    python seed_significance.py results/chronos_bolt/results.json

Output: <results_dir>/seed_significance.json + .md (verdict table).

Env: conda coursia-ml-training (scipy 1.17, numpy, pandas).
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

import numpy as np
from scipy import stats  # noqa: E402  (scipy is a core dep of the ML env)

ALPHA = 0.05  # two-sided significance level


def _extract_kronos(sweep: list) -> list[dict]:
    """Kronos results.json: sweep[i] has seed_results with avg_direction_accuracy."""
    rows = []
    for cfg in sweep:
        sym = cfg.get("symbol")
        h = cfg.get("pred_len")
        maj = cfg.get("majority_baseline", {}).get("majority_class_accuracy")
        sr = cfg.get("seed_results", [])
        diraccs = [float(s.get("avg_direction_accuracy", float("nan"))) for s in sr]
        rows.append({"symbol": sym, "horizon": h, "majority": maj, "diraccs": diraccs})
    return rows


def _extract_m15(summary: list, combos: list) -> list[dict]:
    """M15 results.json: combos are per (symbol, horizon, seed) with direction_accuracy."""
    by_key: dict[tuple, list[float]] = {}
    majority_by_key: dict[tuple, float] = {}
    for c in combos:
        k = (c.get("symbol"), c.get("horizon"))
        by_key.setdefault(k, []).append(float(c["direction_accuracy"]))
        majority_by_key[k] = float(c.get("majority_baseline", {}).get(
            "majority_class_accuracy", float("nan")))
    rows = []
    for (sym, h), diraccs in by_key.items():
        rows.append({"symbol": sym, "horizon": h,
                     "majority": majority_by_key.get((sym, h)),
                     "diraccs": diraccs})
    return rows


def _extract_chronos(sweep: list) -> list[dict]:
    """Chronos results.json: deterministic. sweep[i] has a single diracc + std_edge=0."""
    rows = []
    for cfg in sweep:
        rows.append({
            "symbol": cfg.get("symbol"),
            "horizon": cfg.get("pred_len"),
            "majority": cfg.get("majority"),
            "diraccs": [float(cfg.get("diracc", float("nan")))],
            "deterministic": True,
            "std_edge_committed": float(cfg.get("std_edge", 0.0)),
        })
    return rows


def auto_extract(doc: dict) -> tuple[list[dict], str]:
    """Auto-detect the rung format and return (rows, model_name)."""
    model = doc.get("model", "")
    sweep = doc.get("sweep")
    if sweep and isinstance(sweep, list) and sweep and "seed_results" in sweep[0]:
        return _extract_kronos(sweep), "Kronos"
    if sweep and isinstance(sweep, list) and sweep and "diracc" in sweep[0]:
        return _extract_chronos(sweep), "Chronos-Bolt"
    if "combos" in doc and "summary" in doc:
        return _extract_m15(doc["summary"], doc["combos"]), "M15"
    raise ValueError("Unrecognized results.json format (expected Kronos/Chronos/M15)")


def sign_test(edges: np.ndarray, ref: float = 0.0) -> dict:
    """Two-sided sign (binomial) test: are edges on either side of ref balanced?"""
    valid = edges[~np.isnan(edges)]
    n = len(valid)
    if n == 0:
        return {"n": 0, "p_value": float("nan")}
    n_pos = int(np.sum(valid > ref))
    n_neg = int(np.sum(valid < ref))
    n_nonzero = n_pos + n_neg
    if n_nonzero == 0:
        return {"n": n, "n_pos": n_pos, "n_neg": n_neg, "p_value": 1.0}
    # two-sided binomial p-value vs p=0.5
    k = min(n_pos, n_neg)
    p_one = stats.binom.cdf(k, n_nonzero, 0.5)
    p_value = min(1.0, 2.0 * p_one)
    return {"n": n, "n_pos": n_pos, "n_neg": n_neg, "p_value": float(p_value)}


def analyze_config(symbol, horizon, majority, diraccs,
                   deterministic: bool = False) -> dict:
    """Compute the significance battery for one (symbol, horizon)."""
    diraccs = np.asarray(diraccs, dtype=float)
    diraccs = diraccs[np.isfinite(diraccs)]
    n = len(diraccs)
    maj = float(majority) if majority is not None and math.isfinite(float(majority)) else 0.5

    edges = diraccs - maj
    mean_edge = float(np.mean(edges)) if n else float("nan")
    std_edge = float(np.std(edges, ddof=1)) if n >= 2 else 0.0

    result = {
        "symbol": symbol,
        "horizon": horizon,
        "majority": maj,
        "n_seeds": n,
        "diraccs": [float(x) for x in diraccs],
        "mean_edge": mean_edge,
        "std_edge": std_edge,
        "deterministic": deterministic,
    }

    if deterministic or n < 2:
        # Degenerate: deterministic model (std_edge=0, C893-L) or single value.
        # No meaningful cross-seed variance -> t-test undefined.
        result.update({
            "t_stat": float("nan"),
            "t_p_value": float("nan"),
            "ci95_low": float("nan"),
            "ci95_high": float("nan"),
            "wilcoxon_p_value": float("nan"),
            "sign": {"n": n, "p_value": float("nan")},
            "verdict": "DEGENERATE (deterministic / n<2): no cross-seed variance, "
                       "t-test undefined (cf C893-L for the Chronos case)",
            "significant_at_alpha": False,
        })
        return result

    se = std_edge / math.sqrt(n)
    t_stat = mean_edge / se if se > 1e-12 else float("inf") * math.copysign(1, mean_edge)
    df = n - 1
    t_p = float(2.0 * stats.t.sf(abs(t_stat), df)) if math.isfinite(t_stat) else (0.0 if t_stat != 0 else 1.0)
    tcrit = float(stats.t.ppf(1 - ALPHA / 2, df))
    ci_low = mean_edge - tcrit * se
    ci_high = mean_edge + tcrit * se

    # Wilcoxon signed-rank (needs scipy; falls back to NaN if all-identical)
    try:
        if np.all(edges == edges[0]):
            wilcoxon_p = float("nan")
        else:
            wilcoxon_p = float(stats.wilcoxon(edges, zero_method="wilcox").pvalue)
    except Exception:
        wilcoxon_p = float("nan")

    sgn = sign_test(edges)

    # Verdict: significant if t-test rejects (two-sided) AND the point estimate
    # is on the same side. Report the DIRECTION explicitly (positive edge would
    # be a BEATS signal; negative is under-majority).
    significant = bool(t_p < ALPHA)
    if significant and mean_edge > 0:
        verdict = "SIGNIFICANT-POSITIVE (t-test): edge > 0 statistically -- BEATS signal"
    elif significant and mean_edge < 0:
        verdict = "SIGNIFICANT-NEGATIVE (t-test): edge < 0 statistically -- reliably under majority"
    else:
        verdict = (f"NOT SIGNIFICANT (t_p={t_p:.3f} >= {ALPHA}): edge not distinguishable "
                   f"from 0 at n={n} -- consistent with NO BEATS (low power)")

    result.update({
        "t_stat": float(t_stat),
        "t_p_value": t_p,
        "df": df,
        "ci95_low": float(ci_low),
        "ci95_high": float(ci_high),
        "wilcoxon_p_value": wilcoxon_p,
        "sign": sgn,
        "verdict": verdict,
        "significant_at_alpha": significant,
    })
    return result


def run(results_path: Path, alpha: float = ALPHA) -> dict:
    global ALPHA
    ALPHA = alpha
    doc = json.loads(results_path.read_text(encoding="utf-8"))
    rows, model = auto_extract(doc)
    configs = []
    for r in rows:
        configs.append(analyze_config(
            r["symbol"], r["horizon"], r["majority"], r["diraccs"],
            deterministic=r.get("deterministic", False),
        ))

    n_sig = sum(1 for c in configs if c["significant_at_alpha"])
    n_sig_pos = sum(1 for c in configs if c["significant_at_alpha"] and c["mean_edge"] > 0)
    n_deg = sum(1 for c in configs if "DEGENERATE" in c["verdict"])

    out = {
        "model": model,
        "source_file": str(results_path.name),
        "test": "one-sample t-test + sign + Wilcoxon on per-seed edge vs majority",
        "alpha": alpha,
        "n_configs": len(configs),
        "n_significant": n_sig,
        "n_significant_positive": n_sig_pos,
        "n_degenerate": n_deg,
        "summary_verdict": (
            f"{model}: {n_sig}/{len(configs) - n_deg} stochastic configs statistically "
            f"significant (alpha={alpha}); {n_sig_pos} with positive edge. "
            f"{n_deg} degenerate (deterministic/n<2)."
        ),
        "configs": configs,
    }
    return out


def render_md(out: dict) -> str:
    lines = [
        f"# Seed-level significance -- {out['model']}",
        "",
        f"**Source**: `{out['source_file']}`  |  **Test**: {out['test']}  |  **alpha**: {out['alpha']}",
        "",
        f"**Summary**: {out['summary_verdict']}",
        "",
        "| Symbol | Horizon | n_seeds | DirAccs | mean_edge | std_edge | t_stat | t_p | 95% CI | verdict |",
        "|--------|---------|---------|---------|-----------|----------|--------|-----|--------|---------|",
    ]
    for c in out["configs"]:
        if "DEGENERATE" in c["verdict"]:
            lines.append(
                f"| {c['symbol']} | {c['horizon']} | {c['n_seeds']} | "
                f"{[round(x,3) for x in c['diraccs']]} | {c['mean_edge']:+.4f} | "
                f"{c['std_edge']:.4f} | - | - | - | DEGENERATE |"
            )
        else:
            ci = f"[{c['ci95_low']:+.4f}, {c['ci95_high']:+.4f}]"
            lines.append(
                f"| {c['symbol']} | {c['horizon']} | {c['n_seeds']} | "
                f"{[round(x,3) for x in c['diraccs']]} | {c['mean_edge']:+.4f} | "
                f"{c['std_edge']:.4f} | {c['t_stat']:+.3f} | {c['t_p_value']:.3f} | "
                f"{ci} | {'SIG' if c['significant_at_alpha'] else 'ns'} |"
            )
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Seed-level significance test for foundation rungs (#8607 residual)"
    )
    parser.add_argument("results_json", type=Path, help="Path to a rung's results.json")
    parser.add_argument("--alpha", type=float, default=ALPHA, help="Two-sided alpha (default 0.05)")
    args = parser.parse_args()

    out = run(args.results_json, alpha=args.alpha)
    out_dir = args.results_json.parent
    (out_dir / "seed_significance.json").write_text(
        json.dumps(out, indent=2), encoding="utf-8")
    (out_dir / "seed_significance.md").write_text(render_md(out), encoding="utf-8")

    print(render_md(out))
    print(f"\nSaved: {out_dir / 'seed_significance.json'} (+ .md)")


if __name__ == "__main__":
    main()
