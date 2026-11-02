"""DM comparison of MoE-regime runs differing only by HMM label decode (#21054 case 4).

Reads the two multiseed JSONs produced by ``train_moe_regimes.py`` (same
symbol, expert, seeds; only ``--regime-decode`` differs), pools the
per-observation OOS squared errors recorded in ``fold_details``, and runs a
paired Diebold-Mariano test per seed on the precision loss (``loss_fn="mse"``)
via the canonical ``dm_test.diebold_mariano_test``.

Verdict convention (regle C, honest reporting):
- "FILTER_BETTER"  : median DM p < 0.05 AND mean loss diff favors filter
                     (filter strictly more precise under causal labels);
- "FILTER_WORSE"   : median DM p < 0.05 AND favors viterbi;
- "INCONCLUSIVE"   : median DM p >= 0.05 -- the routing/precision of the
                     regime-routed MoE is statistically indistinguishable
                     between retrospective and causal labels.

Usage:
    python moe_regimes_decode_dm.py \
        --viterbi ../results/moe_regimes_21054_viterbi/moe_regimes_SPY_lstm_hmm_multiseed.json \
        --filter   ../results/moe_regimes_21054_filter/moe_regimes_SPY_lstm_hmm_multiseed.json

Env: coursia-ml-training (numpy only at analysis time).
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from dm_test import diebold_mariano_test  # noqa: E402


def _load(path: Path) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    if "seeds" not in data or "summary" not in data:
        raise ValueError(f"{path}: not a train_moe_regimes multiseed JSON")
    return data


def _pooled_sq_errors(seed_result: dict) -> np.ndarray:
    """Concatenate per-fold OOS squared errors (paired position-wise across runs)."""
    parts = [f["oos_sq_errors"] for f in seed_result.get("fold_details", [])]
    if not parts:
        raise ValueError("seed result carries no oos_sq_errors (re-run with the #21054 recorder)")
    return np.concatenate([np.asarray(p, dtype=float) for p in parts])


def _pooled_mean(seed_result: dict, key: str) -> float:
    """Mean of a per-fold scalar, weighted by that fold's test_size.

    Le biais signe se moyenne sur les observations, pas sur les folds : les
    folds n'ont pas tous le meme nombre de tests sur la derniere fenetre.
    """
    folds = seed_result.get("fold_details", [])
    if not folds or key not in folds[0]:
        raise ValueError(
            f"seed result carries no '{key}' (re-run with the #23171 bias recorder)"
        )
    weights = np.asarray([f["test_size"] for f in folds], dtype=float)
    values = np.asarray([f[key] for f in folds], dtype=float)
    return float(np.sum(values * weights) / np.sum(weights))


def _check_compatible(vit: dict, fil: dict) -> None:
    sv, sf = vit["summary"], fil["summary"]
    for key in ("symbol", "expert_type", "regime_method", "seeds"):
        if sv.get(key) != sf.get(key):
            raise ValueError(
                f"incompatible runs on '{key}': {sv.get(key)!r} vs {sf.get(key)!r}"
            )
    if sv.get("regime_decode") != "viterbi" or sf.get("regime_decode") != "filter":
        raise ValueError(
            "expected the viterbi file to carry regime_decode=viterbi and the "
            f"filter file regime_decode=filter (got {sv.get('regime_decode')!r} "
            f"and {sf.get('regime_decode')!r})"
        )


def compare(viterbi_path: Path, filter_path: Path) -> dict:
    vit = _load(viterbi_path)
    fil = _load(filter_path)
    _check_compatible(vit, fil)

    per_seed = []
    for rv, rf in zip(vit["seeds"], fil["seeds"]):
        seed = rv["config"]["seed"]
        e_vit = _pooled_sq_errors(rv)
        e_fil = _pooled_sq_errors(rf)
        if len(e_vit) != len(e_fil):
            raise ValueError(
                f"seed {seed}: pooled OOS lengths differ ({len(e_vit)} vs "
                f"{len(e_fil)}) -- runs must share folds and data"
            )
        dm = diebold_mariano_test(e_fil, e_vit, loss_fn="mse", alternative="two-sided")

        # Biais signe (#23171 point 3) : mean(e) par bras, et la meme mesure
        # ramenee dans l'espace des signes pour etre comparable a la baseline
        # majorite, qui predit une CLASSE et non une valeur.
        sign_target = _pooled_mean(rv, "sign_target_mean")
        baseline_sign = 1.0 if rv.get("majority_class") == 1 else -1.0

        per_seed.append({
            "seed": seed,
            "n_observations": int(dm.n_observations),
            "dm_statistic": round(float(dm.dm_statistic), 4),
            "dm_p_value": round(float(dm.p_value), 6),
            "mean_sqerr_filter": round(float(np.mean(e_fil)), 8),
            "mean_sqerr_viterbi": round(float(np.mean(e_vit)), 8),
            "mean_loss_diff_filter_minus_viterbi": round(float(dm.mean_loss_diff), 8),
            "mean_err_filter": round(_pooled_mean(rf, "signed_bias"), 8),
            "mean_err_viterbi": round(_pooled_mean(rv, "signed_bias"), 8),
            "mean_err_diff_filter_minus_viterbi": round(
                _pooled_mean(rf, "signed_bias") - _pooled_mean(rv, "signed_bias"), 8
            ),
            "sign_bias_filter": round(_pooled_mean(rf, "sign_bias"), 6),
            "sign_bias_viterbi": round(_pooled_mean(rv, "sign_bias"), 6),
            "sign_bias_baseline": round(baseline_sign - sign_target, 6),
            "sign_target_mean": round(sign_target, 6),
            "diracc_filter": rf["moe_mean_diracc"],
            "diracc_viterbi": rv["moe_mean_diracc"],
            "beats_majority_filter": rf["beats_majority"],
            "beats_majority_viterbi": rv["beats_majority"],
        })

    p_values = [s["dm_p_value"] for s in per_seed]
    median_p = float(np.median(p_values))
    favours_filter = float(np.mean([s["mean_loss_diff_filter_minus_viterbi"] for s in per_seed])) < 0
    if median_p < 0.05:
        verdict = "FILTER_BETTER" if favours_filter else "FILTER_WORSE"
    else:
        verdict = "INCONCLUSIVE"

    return {
        "symbol": vit["summary"]["symbol"],
        "expert_type": vit["summary"]["expert_type"],
        "regime_method": vit["summary"]["regime_method"],
        "seeds": vit["summary"]["seeds"],
        "per_seed": per_seed,
        "dm_p_median": round(median_p, 6),
        "verdict": verdict,
        "mean_err_filter": round(float(np.mean([s["mean_err_filter"] for s in per_seed])), 8),
        "mean_err_viterbi": round(float(np.mean([s["mean_err_viterbi"] for s in per_seed])), 8),
        "sign_bias_filter": round(float(np.mean([s["sign_bias_filter"] for s in per_seed])), 6),
        "sign_bias_viterbi": round(float(np.mean([s["sign_bias_viterbi"] for s in per_seed])), 6),
        "sign_bias_baseline": round(float(np.mean([s["sign_bias_baseline"] for s in per_seed])), 6),
        "note": (
            "Paired DM on pooled per-observation OOS squared errors, per seed; "
            "verdict from the median p (regle C). INCONCLUSIVE means the "
            "regime-routed MoE's precision is indistinguishable between the "
            "retrospective and causal decodes. mean_err_* is the signed OOS "
            "bias mean(pred - y) of each arm; sign_bias_* is the same bias in "
            "sign space (sign(pred) - sign(y)), the scale on which the "
            "majority baseline -- a class predictor, not a value predictor -- "
            "is comparable."
        ),
    }


def build_aggregate(vit: dict, fil: dict, comparison: dict,
                    commands: dict | None = None) -> dict:
    """Agregat falsifiable et commitable des deux bras (#23171 point 1).

    Les multiseed JSON portent la serie complete des erreurs OOS (300 Ko par
    bras) : elle n'a pas sa place dans le depot. Cet agregat garde tout ce qui
    permet de RECOMPTER les nombres du body -- provenance, configuration
    d'entrainement, scalaires par fold (mse, biais signe, cible moyenne),
    diracc par seed et verdict DM -- et cite la serie complete hors depot.
    """
    _FOLD_KEYS = (
        "fold", "test_size", "direction_accuracy", "mse", "n_experts",
        "mean_target", "mean_pred", "signed_bias", "sign_bias",
        "sign_target_mean",
    )
    _RUN_KEYS = (
        "symbol", "expert_type", "regime_method", "regime_decode",
        "regime_decode_causal", "regime_lookback", "regime_n_states",
        "lookahead_note", "device", "data_hash", "n_folds", "n_samples",
        "n_features", "seq_len", "majority_baseline_acc", "majority_class",
        "target_balance",
    )

    def _arm(data: dict) -> dict:
        first = data["seeds"][0]
        summary = data["summary"]
        # La provenance vit par seed dans les runs reels ; la forme condensee
        # ne la porte que dans le summary -- on accepte les deux.
        return {
            "provenance": {k: first.get(k, summary.get(k)) for k in _RUN_KEYS},
            "train_config": first.get("config"),
            "summary": {
                k: summary.get(k) for k in (
                    "n_seeds", "seeds", "mean_diracc", "std_diracc",
                    "majority_baseline", "improvement_pct", "t_stat",
                    "p_value", "significant", "per_seed_diraccs",
                )
            },
            "per_seed": [
                {
                    "seed": sr["config"]["seed"],
                    "moe_mean_diracc": sr.get("moe_mean_diracc"),
                    "moe_std_diracc": sr.get("moe_std_diracc"),
                    "beats_majority": sr.get("beats_majority"),
                    "folds": [
                        {k: f.get(k) for k in _FOLD_KEYS}
                        for f in sr.get("fold_details", [])
                    ],
                }
                for sr in data["seeds"]
            ],
        }

    return {
        "case": "#21054 case 4 -- regime decode viterbi vs filter (regle C)",
        "falsifiability": (
            "Chaque nombre du body de la PR se recompte depuis ce fichier : "
            "diracc par seed et par fold, mse, biais signe mean(pred-y) et "
            "biais en espace de signe, cible moyenne, p-value DM et p median. "
            "La serie complete par observation (oos_sq_errors, ~300 Ko/bras) "
            "reste hors depot : chemin GDrive cite dans le body de la PR."
        ),
        "commands": commands or {},
        "viterbi": _arm(vit),
        "filter": _arm(fil),
        "comparison": {
            "per_seed": comparison["per_seed"],
            "dm_p_median": comparison["dm_p_median"],
            "verdict": comparison["verdict"],
            "mean_err_filter": comparison["mean_err_filter"],
            "mean_err_viterbi": comparison["mean_err_viterbi"],
            "sign_bias_filter": comparison["sign_bias_filter"],
            "sign_bias_viterbi": comparison["sign_bias_viterbi"],
            "sign_bias_baseline": comparison["sign_bias_baseline"],
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Paired DM: MoE-regime decode viterbi vs filter (#21054)"
    )
    parser.add_argument("--viterbi", type=Path, required=True,
                        help="multiseed JSON produced with --regime-decode viterbi")
    parser.add_argument("--filter", type=Path, required=True,
                        help="multiseed JSON produced with --regime-decode filter")
    parser.add_argument("--out", type=Path, default=None,
                        help="optional output JSON for the comparison")
    parser.add_argument("--aggregate", type=Path, default=None,
                        help="optional compact, committable aggregate of both arms")
    parser.add_argument("--command", action="append", default=None,
                        metavar="LABEL=CMD",
                        help="exact command line that produced an arm (repeatable), "
                             "recorded verbatim in the aggregate")
    args = parser.parse_args()

    result = compare(args.viterbi, args.filter)

    print(f"\n{'=' * 64}")
    print(f"MoE-regime decode comparison: {result['symbol']} "
          f"({result['expert_type']}, {result['regime_method']})")
    print(f"{'=' * 64}")
    for s in result["per_seed"]:
        print(
            f"seed {s['seed']:>3}: DM p={s['dm_p_value']:.4f}  "
            f"sqerr filter={s['mean_sqerr_filter']:.6f} viterbi={s['mean_sqerr_viterbi']:.6f}  "
            f"diracc filter={s['diracc_filter']:.4f} viterbi={s['diracc_viterbi']:.4f}  "
            f"bias filter={s['mean_err_filter']:+.6f} viterbi={s['mean_err_viterbi']:+.6f} "
            f"baseline={s['sign_bias_baseline']:+.4f}"
        )
    print(f"\ndm_p_median = {result['dm_p_median']:.4f}")
    print(f"VERDICT: {result['verdict']}")
    print(f"{'=' * 64}")

    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(result, indent=2), encoding="utf-8")
        print(f"Saved: {args.out}")

    if args.aggregate:
        commands = {}
        for item in args.command or []:
            label, _, cmd = item.partition("=")
            if not cmd:
                raise SystemExit(f"--command expects LABEL=CMD, got {item!r}")
            commands[label] = cmd
        aggregate = build_aggregate(
            _load(args.viterbi), _load(args.filter), result, commands
        )
        args.aggregate.parent.mkdir(parents=True, exist_ok=True)
        args.aggregate.write_text(
            json.dumps(aggregate, indent=2, ensure_ascii=False), encoding="utf-8"
        )
        print(f"Saved aggregate: {args.aggregate}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
