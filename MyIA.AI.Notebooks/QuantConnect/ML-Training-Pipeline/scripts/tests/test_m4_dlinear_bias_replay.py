"""Tests for the M4 bias re-validation (`docs/M4_DLINEAR_VOL.md`, Epic #1454).

M4 publishes raw `BEATS` on BTC (all horizons) and ETH/SOL at h=1. The M5
family anchors measured `har_bias_oos` at −0.23…−0.45 on BTC (growing with
horizon), and `MSE = bias^2 + variance` means a raw-MSE edge can be the
baseline's miscalibration rather than the model's precision. The keeper run of
2026-09-22 (BTC+ETH+SOL, 4 seeds, 3 horizons) recomputes the raw leg
identically (anchor verified: BTC h=1 `mean_har_bias_oos = −0.226587`
reproduces the published M5 value to the 6th digit) and adds the de-biased
leg through the SHARED state machine `_aggregate_state` in `bias_metrics.py`
(extracted from `hmm_regime_vol.py` for this run).

What is tested here: the artifact reproduces the doc table (every published
verdict is replayed from the JSON, not read back from prose), and the M4
config-level discriminations hold -- BTC h=10 `refuted-de-biased` (the most
spectacular raw edge is the one with the largest HAR bias), ETH h=1
`refuted-de-biased`, BTC h=1/h=5 surviving the precision control.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from bias_metrics import _aggregate_state  # noqa: E402

ARTIFACT = (
    Path(__file__).resolve().parent.parent / "results"
    / "m4_dlinear_vol_debiased_3coin.json"
)
assert ARTIFACT.is_file(), f"artifact manquant: {ARTIFACT}"

# The published table of docs/M4_DLINEAR_VOL.md « Re-validation hors biais »
# (keeper run 2026-09-22): (coin, horizon, n_beats_centered, n_beaten_centered,
# dm_centered_p_median, n_beats_raw, published de-biased verdict)
PUBLISHED_M4_DEBIASED = [
    ("BTC-USD", 1, 4, 0, 2.27e-09, 4, "BEATS"),
    ("BTC-USD", 5, 4, 0, 9.14e-05, 4, "BEATS"),
    ("BTC-USD", 10, 1, 0, 5.98e-02, 4, "refuted-de-biased"),
    ("ETH-USD", 1, 0, 0, 1.27e-01, 4, "refuted-de-biased"),
    ("ETH-USD", 5, 0, 0, 8.68e-01, 0, "INCONCLUSIVE"),
    ("ETH-USD", 10, 0, 0, 8.94e-01, 0, "INCONCLUSIVE"),
    ("SOL-USD", 1, 1, 0, 9.80e-02, 0, "INCONCLUSIVE"),
    ("SOL-USD", 5, 0, 0, 6.72e-01, 0, "INCONCLUSIVE"),
    ("SOL-USD", 10, 0, 0, 8.39e-01, 0, "INCONCLUSIVE"),
]


@pytest.fixture(scope="module")
def artifact():
    with open(ARTIFACT, encoding="utf-8") as fh:
        return json.load(fh)


class TestArtifactReplaysDocTable:
    """The executable must reproduce the table the doc publishes."""

    def test_artifact_has_all_nine_configs(self, artifact):
        keys = {(a["coin"], a["horizon"]) for a in artifact["aggregated"]}
        expected = {(c, h) for c, h, *_ in PUBLISHED_M4_DEBIASED}
        assert keys == expected

    @pytest.mark.parametrize(
        "coin,horizon,n_beats,n_beaten,p_median,n_beats_raw,published",
        PUBLISHED_M4_DEBIASED,
    )
    def test_reproduces_every_published_verdict(
        self, artifact, coin, horizon, n_beats, n_beaten, p_median,
        n_beats_raw, published,
    ):
        row = next(
            a for a in artifact["aggregated"]
            if a["coin"] == coin and a["horizon"] == horizon
        )
        # the artifact's own fields replay through the shared state machine
        assert _aggregate_state(
            n_beats=row["n_beats_centered"],
            n_beaten=row["n_beaten_centered"],
            n_seeds=row["n_seeds"],
            dm_p_median=row["dm_centered_p_median"],
            n_beats_parent=row["n_beats_raw"],
        ) == row["aggregate_verdict_debiased"] == published
        # and the doc's hand-copied numbers match the artifact
        assert row["n_beats_centered"] == n_beats
        assert row["n_beaten_centered"] == n_beaten
        assert row["n_beats_raw"] == n_beats_raw
        assert row["dm_centered_p_median"] == pytest.approx(p_median, rel=0.02)


class TestM4Anchors:
    """Family anchors the doc cites verbatim."""

    def test_btc_h1_har_bias_anchor(self, artifact):
        """BTC h=1 mean_har_bias_oos reproduces the published M5 anchor
        (−0.226587) -- the instrument measures the same baseline."""
        row = next(
            a for a in artifact["aggregated"]
            if a["coin"] == "BTC-USD" and a["horizon"] == 1
        )
        assert row["mean_har_bias_oos"] == pytest.approx(-0.226587, abs=1e-4)

    def test_har_bias_share_grows_with_horizon_on_btc(self, artifact):
        """The doc's reading #2: « l'effet croît avec l'horizon » was really
        « le biais HAR croît avec l'horizon ». The share of bias^2 in HAR's
        MSE must be strictly increasing on BTC."""
        shares = {
            a["horizon"]: a["mean_har_bias_share_of_mse"]
            for a in artifact["aggregated"] if a["coin"] == "BTC-USD"
        }
        assert shares[1] < shares[5] < shares[10]

    def test_most_spectacular_raw_edge_is_the_most_biased(self, artifact):
        """BTC h=10 pairs the largest raw edge with the largest |HAR bias|
        -- and is exactly the config the precision leg refutes."""
        btc = [a for a in artifact["aggregated"] if a["coin"] == "BTC-USD"]
        worst = max(btc, key=lambda a: abs(a["mean_har_bias_oos"]))
        assert worst["horizon"] == 10
        assert worst["aggregate_verdict_debiased"] == "refuted-de-biased"

    def test_dlinear_bias_sign_flips_by_coin(self, artifact):
        """The doc's closing note: DLinear is unbiased on BTC (|bias| < 0.01)
        but over-estimates volatility on ETH and SOL (bias > 0)."""
        for a in artifact["aggregated"]:
            if a["coin"] == "BTC-USD":
                assert abs(a["mean_dlinear_bias_oos"]) < 0.01
            else:
                assert a["mean_dlinear_bias_oos"] > 0


class TestStateMachineM4Shapes:
    """Negative controls on the M4-specific verdict shapes (Tell c.856-L1:
    every silence is paired with a mutation that must make the control
    speak)."""

    def test_btc_h10_refutation_collapses_without_unanimous_raw_win(self):
        """The same counts with n_beats_raw=3 (not 4) must fall back to
        INCONCLUSIVE -- `refuted-de-biased` requires the parent leg to have
        been a unanimous win."""
        assert _aggregate_state(
            n_beats=1, n_beaten=0, n_seeds=4,
            dm_p_median=5.98e-02, n_beats_parent=3,
        ) == "INCONCLUSIVE"
        assert _aggregate_state(
            n_beats=1, n_beaten=0, n_seeds=4,
            dm_p_median=5.98e-02, n_beats_parent=4,
        ) == "refuted-de-biased"

    def test_sol_h1_single_centered_win_is_not_enough(self):
        """1/4 BEATS on the centered leg with a 4/4 raw win elsewhere must not
        leak into `refuted-de-biased` (SOL h=1 raw leg was NOT 4/4 in this
        keeper run -- n_beats_raw=0 -- so the verdict stays INCONCLUSIVE)."""
        assert _aggregate_state(
            n_beats=1, n_beaten=0, n_seeds=4,
            dm_p_median=9.80e-02, n_beats_parent=0,
        ) == "INCONCLUSIVE"


class TestNanmeanRepli:
    """The NaN fallback (#1454): an unmeasured leg must serialize as JSON
    `null`, not as a bare `NaN` token.

    The three bias keys are absent when a row predates the bias leg (or comes
    from a caller building synthetic rows), so `r.get(key, nan)` yields an
    all-NaN list. `np.nanmean` on it emits `RuntimeWarning: Mean of empty
    slice` and returns `nan`, which `json.dump` writes as the bare token
    `NaN` -- outside the JSON specification, and unreadable by a strict
    parser. The warning is the tell; the invalid document is the defect.
    """

    def test_all_nan_is_none_not_nan(self):
        from dlinear_vol import _nanmean_or_none
        assert _nanmean_or_none([float("nan")] * 4) is None

    def test_empty_is_none(self):
        from dlinear_vol import _nanmean_or_none
        assert _nanmean_or_none([]) is None

    def test_mixed_ignores_nan(self):
        from dlinear_vol import _nanmean_or_none
        assert _nanmean_or_none([0.1, float("nan"), 0.3]) == pytest.approx(0.2)

    def test_unmeasured_leg_raises_no_warning(self):
        """The control that would fail on the pre-fix code: no warning at all."""
        import warnings

        from dlinear_vol import _nanmean_or_none
        with warnings.catch_warnings():
            warnings.simplefilter("error")
            assert _nanmean_or_none([float("nan")]) is None


class TestAggregateStaysStrictJsonWithoutBiasLeg:
    """End-to-end: drive `aggregate_verdicts` with rows whose bias keys were
    removed, and require a document a strict parser accepts."""

    @staticmethod
    def _aggregate_without_bias_keys(artifact):
        import copy

        from dlinear_vol import aggregate_verdicts
        rows = copy.deepcopy(artifact["rows"])
        for row in rows:
            for key in ("dlinear_bias_oos", "har_bias_oos", "har_bias_share_of_mse"):
                row.pop(key, None)
        return aggregate_verdicts(rows)

    def test_bias_aggregates_are_null(self, artifact):
        for row in self._aggregate_without_bias_keys(artifact):
            assert row["mean_dlinear_bias_oos"] is None
            assert row["mean_har_bias_oos"] is None
            assert row["mean_har_bias_share_of_mse"] is None

    def test_document_is_strict_json(self, artifact):
        """`allow_nan=False` is the assertion: it raises on a bare `NaN`,
        which is exactly what the pre-fix code emitted here."""
        import json as _json
        dumped = _json.dumps(
            self._aggregate_without_bias_keys(artifact), allow_nan=False,
        )
        assert "NaN" not in dumped
        assert _json.loads(dumped)

    def test_verdicts_are_unaffected_by_the_missing_bias_leg(self, artifact):
        """The precision leg's verdict rests on the centered DM fields, not on
        the bias aggregates: removing the latter must not move a verdict."""
        mutated = {
            (r["coin"], r["horizon"]): r["aggregate_verdict_debiased"]
            for r in self._aggregate_without_bias_keys(artifact)
        }
        published = {
            (c, h): v for c, h, *_rest, v in PUBLISHED_M4_DEBIASED
        }
        assert mutated == published

