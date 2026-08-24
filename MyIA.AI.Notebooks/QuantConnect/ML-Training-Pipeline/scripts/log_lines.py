"""Shared log-line formatters for the vol-forecasting harness (#12681).

The DM verdict is computed on the ALIGNED error sample, while the walk-forward
aggregate the harness also reports is a different number. Printing only the
aggregate next to the verdict let a reader invert the model-vs-baseline
comparison: in the M15 ETF logs, 10 of 12 checkpoint lines showed a model
MSE sitting BETWEEN the aggregate and the aligned baseline MSE, so the
side-by-side reading gave the opposite conclusion of the verdict itself.

These formatters keep, next to the verdict, the number the verdict is
actually computed on. `format_har_baseline_line` labels the aggregate as
such so it can no longer be mistaken for the verdict's baseline.
"""

from __future__ import annotations


def format_har_baseline_line(
    h: int,
    har_mse_aggregate: float,
    har_bias_oos: float,
    n_preds: int,
) -> str:
    return (
        f"  h={h} HAR MSE(agrege)={har_mse_aggregate:.5f} "
        f"bias_OOS={har_bias_oos:+.5f} ({n_preds} preds)"
    )


def format_dm_verdict_line(
    model_label: str,
    h: int,
    seed: int,
    model_mse: float,
    mse_baseline_aligned: float,
    bias: float,
    dm_stat: float,
    p_value: float,
    verdict: str,
) -> str:
    return (
        f"  h={h} seed={seed} {model_label} MSE={model_mse:.5f} "
        f"vs HAR aligne {mse_baseline_aligned:.5f} "
        f"bias={bias:+.5f} DM={dm_stat:.3f} "
        f"p={p_value:.4f} -> {verdict}"
    )
