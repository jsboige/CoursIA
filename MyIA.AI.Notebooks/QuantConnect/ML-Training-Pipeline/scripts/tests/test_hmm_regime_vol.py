"""Tests for the M5 bias instrumentation in `scripts/hmm_regime_vol.py` (#1454).

M5 publishes a live `BEATS` (ETH-USD h=1) against a classic-HAR baseline. The
same family of baselines was measured at `har_bias_oos = -0.227` in #12745, and
`MSE = bias^2 + variance` means a raw-error DM cannot tell a precision win from
a calibration artefact. This module tests the control that separates them.

The pure helpers `_mse_decomposition` / `_dm_centered_mse` also have coverage in
`test_btc_vol.py` (they originate there, PR #12742). What is tested HERE is what
those tests cannot cover: that the control actually DISCRIMINATES, and that the
M5 return contract carries it.

Validation shape (Tell c.856-L1): every silence is paired with a mutation that
changes only the property under test and must make the control speak. A control
that is never shown firing is not a control -- it is a green light with no wire
behind it.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

# Make the parent directory importable.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import hmm_regime_vol  # noqa: E402
from hmm_regime_vol import (  # noqa: E402
    _aggregate_debiased_state,
    _dm_centered_mse,
    _is_beaten,
    _is_beats,
    _mse_decomposition,
    _require_hmmlearn,
    walk_forward_regime_switching,
)


# --------------------------------------------------------------------------
# Synthetic panels
# --------------------------------------------------------------------------

def _two_regime_rv(n: int = 300, seed: int = 3, switch_p: float = 0.03) -> pd.Series:
    """A daily RV series with two latent volatility regimes.

    Regime-switching HAR should have a real edge on this by construction --
    which is what makes it a usable POSITIVE control: an edge that is genuine
    must survive centering.
    """
    rng = np.random.default_rng(seed)
    state = np.zeros(n, dtype=int)
    for i in range(1, n):
        state[i] = state[i - 1] if rng.random() > switch_p else 1 - state[i - 1]
    log_rv = np.where(state == 1, -6.5, -8.0) + rng.normal(0.0, 0.35, n)
    return pd.Series(
        np.exp(log_rv), index=pd.date_range("2020-01-01", periods=n, freq="D"),
    )


# --------------------------------------------------------------------------
# _is_beats
# --------------------------------------------------------------------------

class TestIsBeats:
    """`dm_verdict` emits exactly three strings; only one of them is a win."""

    def test_beats_is_a_win(self):
        assert _is_beats("BEATS baseline") is True

    def test_beaten_is_not_a_win(self):
        # The substring "BEATS" does NOT appear in "BEATEN BY baseline", but the
        # exclusion is kept because a future verdict wording could reintroduce
        # it. Pinning it here makes any such change fail loudly.
        assert _is_beats("BEATEN BY baseline") is False

    def test_inconclusive_is_not_a_win(self):
        assert _is_beats("INCONCLUSIVE") is False

    def test_exclusion_is_load_bearing(self):
        """Mutation: a wording where the naive substring test WOULD misfire."""
        assert "BEATS" in "BEATS baseline (was BEATEN last seed)"
        assert _is_beats("BEATS baseline (was BEATEN last seed)") is False


# --------------------------------------------------------------------------
# The control must discriminate -- both directions
# --------------------------------------------------------------------------

class TestCenteredDmDiscriminates:
    """The negative and the positive, on the same instrument.

    Showing only that the control stays quiet on a pure-bias edge proves
    nothing: a control wired to nothing is quiet on everything. The pair is
    the evidence.
    """

    def test_pure_bias_edge_does_not_survive_centering(self):
        """NEGATIVE: identical dispersion, baseline offset by a constant.

        The raw DM declares a win because `MSE = bias^2 + variance` and the
        baseline carries a bias the model does not. Centering removes exactly
        that term, and nothing is left -- which is the correct answer, because
        the two models are equally *precise*.
        """
        from dm_test import dm_verdict

        rng = np.random.default_rng(0)
        e_model = rng.normal(0.0, 1.0, 4000)
        e_base = e_model + 0.5  # same dispersion, pure calibration gap

        raw = dm_verdict(e_model, e_base, horizon=1)
        centered = _dm_centered_mse(e_model, e_base, horizon=1)

        assert _is_beats(raw["verdict"]), "the raw leg must see this edge"
        assert raw["p_value"] < 1e-6
        assert not _is_beats(centered["dm_verdict"]), (
            "an edge made only of the baseline's bias must NOT survive centering"
        )
        assert centered["dm_stat"] == pytest.approx(0.0, abs=1e-9)

    def test_genuine_precision_edge_does_survive_centering(self):
        """POSITIVE: the mutation that must make the control speak.

        Only the dispersion changes -- both series are unbiased, so centering
        is a near no-op and the win stands. If this test ever goes quiet at the
        same time as the one above, the control has stopped being wired.
        """
        rng = np.random.default_rng(0)
        e_model = rng.normal(0.0, 0.5, 4000)
        e_base = rng.normal(0.0, 1.0, 4000)

        centered = _dm_centered_mse(e_model, e_base, horizon=1)
        assert _is_beats(centered["dm_verdict"])
        assert centered["dm_pvalue"] < 0.01

    def test_centering_is_not_a_no_op_on_the_statistic(self):
        """Guard against the mislabel the family artefacts already contain.

        `btc_vol` routes BOTH its `dm_centered` and its `dm_raw` legs through
        `_dm_centered_mse`, feeding the second a pre-de-biased series -- and
        centering annihilates exactly the constant that distinguished them, so
        the two statistics come out bit-identical (measured on
        `results/m4_dlinear_vol_btc_sc_debiased_recentered.json`:
        -6.228784907758055 vs -6.228784907758053). A raw leg that silently
        centers is not a raw leg. This pins the two apart for M5.
        """
        from dm_test import dm_verdict

        rng = np.random.default_rng(7)
        e_model = rng.normal(0.0, 1.0, 2000)
        e_base = rng.normal(0.3, 1.0, 2000)  # biased baseline

        raw = dm_verdict(e_model, e_base, horizon=1)
        centered = _dm_centered_mse(e_model, e_base, horizon=1)

        assert abs(raw["dm_statistic"] - centered["dm_stat"]) > 1e-3, (
            "raw and centered must not be the same computation under a different name"
        )

    @pytest.mark.parametrize("baseline_bias", [0.3, 0.0])
    def test_the_gap_between_the_two_legs_IS_the_bias_gap(self, baseline_bias):
        """The exact identity behind the whole control, in both regimes.

        With `loss_fn="mse"`:
            d_raw      = MSE_a - MSE_b
            d_centered = var(e_a) - var(e_b)
        and since `MSE = bias^2 + variance`,
            d_raw - d_centered = bias_a^2 - bias_b^2      (exactly)

        So the two legs differ by the bias gap and by nothing else. Asserting
        the identity is stronger than asserting a tolerance on the statistic:
        a tolerance is a guess about sampling noise, whereas this pins WHY the
        biased case separates the legs (gap = -0.0913 here) and the unbiased
        case does not (gap = +0.0016, ~60x smaller, pure sample-mean noise).
        """
        from dm_test import dm_verdict

        rng = np.random.default_rng(7)
        e_model = rng.normal(0.0, 1.0, 2000)
        e_base = rng.normal(baseline_bias, 1.0, 2000)

        raw = dm_verdict(e_model, e_base, horizon=1)
        centered = _dm_centered_mse(e_model, e_base, horizon=1)

        observed_gap = raw["mean_loss_diff"] - centered["mean_loss_diff"]
        bias_gap = float(np.mean(e_model) ** 2 - np.mean(e_base) ** 2)
        assert observed_gap == pytest.approx(bias_gap, abs=1e-12)

        # ... and the gap is material only when a bias is there to remove.
        if baseline_bias:
            assert abs(observed_gap) > 0.05
        else:
            assert abs(observed_gap) < 0.01

    def test_too_few_observations_refuses_a_verdict(self):
        out = _dm_centered_mse(np.zeros(5), np.ones(5), horizon=1)
        assert out["dm_verdict"] == "INSUFFICIENT_DATA"
        assert np.isnan(out["dm_stat"])

    def test_shape_mismatch_refuses_a_verdict(self):
        out = _dm_centered_mse(np.zeros(50), np.zeros(40), horizon=1)
        assert out["dm_verdict"] == "SHAPE_MISMATCH"


# --------------------------------------------------------------------------
# The M5 return contract
# --------------------------------------------------------------------------

class TestWalkForwardContract:
    """The instrumentation has to reach the caller, not just exist."""

    @pytest.fixture(scope="class")
    def result(self) -> dict:
        return walk_forward_regime_switching(
            _two_regime_rv(), horizon=1, seed=0, n_splits=3,
        )

    def test_published_fields_are_untouched(self, result):
        """The raw legs keep their original meaning.

        docs/M5_HMM_REGIME.md publishes these numbers. The control is ADDED
        beside them; renaming or redefining them would silently invalidate a
        published result instead of auditing it.
        """
        for key in ("regime_mse", "classic_mse", "mse_reduction_pct",
                    "dm_statistic", "dm_p_value", "dm_verdict"):
            assert key in result

    def test_bias_report_covers_model_and_baseline(self, result):
        """§C: "rapport de biais par modele ... modele ET baseline"."""
        for key in ("regime_bias_oos", "classic_bias_oos",
                    "regime_bias_sq", "classic_bias_sq_raw"):
            assert key in result
            assert np.isfinite(result[key])

    def test_mse_identity_holds_for_both_models(self, result):
        """`MSE = bias^2 + variance` -- the identity the whole control rests on."""
        assert result["regime_mse"] == pytest.approx(
            result["regime_bias_sq"] + result["regime_variance"], rel=1e-9,
        )
        assert result["classic_mse"] == pytest.approx(
            result["classic_bias_sq_raw"] + result["classic_variance_raw"], rel=1e-9,
        )

    def test_debiasing_removes_exactly_the_bias(self, result):
        """De-biased MSE is the variance, and the residual bias is zero."""
        assert result["classic_mse_debiased"] == pytest.approx(
            result["classic_variance_raw"], rel=1e-9,
        )
        assert result["classic_bias_sq_debiased"] == pytest.approx(0.0, abs=1e-20)

    def test_debiased_edge_is_never_flattered(self, result):
        """De-biasing the baseline can only make it harder to beat.

        A baseline with any bias at all has `MSE_debiased <= MSE_raw`, so the
        edge measured against it is <= the raw edge. A harness reporting the
        opposite would be crediting the model with the baseline's miscalibration.
        """
        assert result["classic_mse_debiased"] <= result["classic_mse"] + 1e-12
        assert (
            result["mse_reduction_pct_vs_debiased_classic"]
            <= result["mse_reduction_pct"] + 1e-9
        )

    def test_bias_share_is_a_fraction_of_the_baseline_mse(self, result):
        share = result["classic_bias_share_of_mse"]
        assert 0.0 <= share <= 1.0

    def test_centered_dm_reaches_the_caller(self, result):
        for key in ("dm_centered_stat", "dm_centered_pvalue",
                    "dm_centered_verdict", "dm_centered_mean_loss_diff"):
            assert key in result
        assert result["dm_centered_verdict"] in (
            "BEATS baseline", "BEATEN BY baseline", "INCONCLUSIVE",
        )

    def test_regime_edge_survives_on_a_two_regime_panel(self, result):
        """End-to-end positive control on data built to have a real edge.

        Not a claim about markets -- a claim that the wiring transmits a real
        signal. If the plumbing were broken, this synthetic edge would vanish.
        """
        assert _is_beats(result["dm_verdict"])
        assert _is_beats(result["dm_centered_verdict"])

    def test_series_are_aligned_and_complete(self, result):
        s = result["_series"]
        n = result["n_preds"]
        assert len(s["dates"]) == n
        assert len(s["regime"]) == n
        assert len(s["classic"]) == n
        assert len(s["target"]) == n

    def test_short_series_is_refused(self):
        rv = _two_regime_rv(n=150)
        with pytest.raises(ValueError, match="need >=200"):
            walk_forward_regime_switching(rv, horizon=1, seed=0, n_splits=3)


# --------------------------------------------------------------------------
# The artefact must not carry the series
# --------------------------------------------------------------------------

class TestArtefactStaysLean:
    """`_series` is popped before the JSON dump, on purpose.

    24 runs x ~1.1k predictions is ~2 MB of committed artefact, and the family's
    artefacts (`m4_*_debiased_recentered.json`, `m15_*/results.json`) carry
    decompositions rather than series. The series stay reachable through
    `--dump-series`, which writes a separate CSV.
    """

    def test_json_dump_has_no_series_and_csv_has_them(self, tmp_path):
        from hmm_regime_vol import main

        out_json = tmp_path / "results.json"
        out_csv = tmp_path / "series.csv"

        # The real panels need Bitstamp/Binance data on disk; when it is absent
        # `main` exits before doing any work, and this assertion has nothing to
        # measure. Skipping is honest; passing on an empty run would not be.
        try:
            main([
                "--coins", "ETH-USD", "--horizons", "1", "--seeds", "0",
                "--out", str(out_json), "--dump-series", str(out_csv),
            ])
        except SystemExit as exc:  # "No data loaded, aborting."
            pytest.skip(f"panel data unavailable in this environment: {exc}")

        payload = json.loads(out_json.read_text())
        per_seed = [r for r in payload["results"] if r.get("seed") != "aggregate"]
        assert per_seed, "at least one per-seed row expected"
        for row in per_seed:
            assert "_series" not in row, "the series must not bloat the artefact"
            assert "dm_centered_verdict" in row

        # The published tables carry a "seeds BEATEN (rec.)" column; it has to
        # be readable back from the artefact, not only recomputable by hand.
        aggregate = [r for r in payload["results"] if r.get("seed") == "aggregate"]
        assert aggregate, "an aggregate row is expected"
        for row in aggregate:
            assert "n_beaten_seeds_centered" in row
            n_beats, n_seeds = (int(x) for x in row["n_beats_seeds_centered"].split("/"))
            n_beaten, n_seeds_b = (int(x) for x in row["n_beaten_seeds_centered"].split("/"))
            assert n_seeds == n_seeds_b == row["n_seeds"]
            assert n_beats + n_beaten <= n_seeds, "a seed cannot both win and lose"

        frame = pd.read_csv(out_csv)
        assert set(frame.columns) >= {
            "coin", "horizon", "seed", "date", "pred_regime", "pred_classic", "target",
        }
        assert len(frame) == per_seed[0]["n_preds"]


# --------------------------------------------------------------------------
# The optional-dependency guard
#
# `hmm_regime_vol` used to `sys.exit(...)` at import time when hmmlearn was
# absent. Importing it from a test module then raised SystemExit during pytest
# COLLECTION, which aborts the entire session with INTERNALERROR -- every other
# suite in this directory dies with it, and the log blames a stack of pytest
# internals rather than the missing package. These two tests pin the repaired
# contract: importing is safe, using without the dependency is not.
# --------------------------------------------------------------------------

class TestHmmlearnGuard:
    def test_import_does_not_abort_collection(self):
        """The module is importable. Reaching this line is the assertion.

        If `hmm_regime_vol` regressed to an import-time `sys.exit`, this file
        could not be collected at all and the failure would surface as an
        INTERNALERROR, not as a red test.
        """
        assert hmm_regime_vol.__name__ == "hmm_regime_vol"

    def test_guard_still_exits_when_dependency_is_absent(self, monkeypatch):
        """Deferring the failure must not SILENCE it.

        Simulates the absent dependency and asserts the guard still stops the
        run with the same message the import-time exit used to print.
        """
        monkeypatch.setattr(hmm_regime_vol, "GaussianHMM", None)
        with pytest.raises(SystemExit) as excinfo:
            _require_hmmlearn()
        assert "hmmlearn not found" in str(excinfo.value)

        # ... and reaches CLI callers before any data is loaded.
        with pytest.raises(SystemExit):
            hmm_regime_vol.main(["--coins", "BTC-USD", "--horizons", "1", "--seeds", "0"])

    def test_guard_is_transparent_when_dependency_is_present(self):
        """The mutation above must be what makes it fire -- not the call itself."""
        assert hmm_regime_vol.GaussianHMM is not None, "hmmlearn absent in this env"
        _require_hmmlearn()  # must not raise


# --------------------------------------------------------------------------
# The aggregated state machine
#
# The de-biased leg had three states and none of them was a loss: with no
# branch for "every seed is BEATEN", the four long-horizon configs published
# as `NO BEATS` were persisted as `INCONCLUSIVE`. The doc, the REGISTRY and
# the body said one thing, the executable said another -- and no test held
# the aggregation, only `_is_beats` and the per-seed legs. These tests pin
# the four states symmetrically, and each silence is paired with a mutation
# that changes only the count under test.
# --------------------------------------------------------------------------

# The published table of docs/M5_HMM_REGIME.md (de-biased leg, 4 seeds):
# (coin, horizon, n_beats_centered, n_beaten_centered, dm_centered_p_median,
#  n_beats_raw, published verdict)
PUBLISHED_DEBIASED = [
    ("BTC-USD", 1, 3, 0, 1.47e-03, 3, "INCONCLUSIVE"),
    ("BTC-USD", 5, 0, 4, 6.21e-06, 0, "NO BEATS"),
    ("BTC-USD", 10, 0, 4, 1.75e-09, 0, "NO BEATS"),
    ("ETH-USD", 1, 4, 0, 1.14e-05, 4, "BEATS"),
    ("ETH-USD", 5, 0, 4, 6.16e-04, 0, "NO BEATS"),
    ("ETH-USD", 10, 0, 4, 4.10e-05, 0, "NO BEATS"),
]


class TestIsBeaten:
    """The mirror of `TestIsBeats`: a loss must be counted as a loss."""

    def test_beaten_is_a_loss(self):
        assert _is_beaten("BEATEN BY baseline")

    def test_beats_is_not_a_loss(self):
        """The token that made `_is_beats` need an exclusion clause."""
        assert not _is_beaten("BEATS baseline")

    def test_inconclusive_is_not_a_loss(self):
        assert not _is_beaten("INCONCLUSIVE")

    @pytest.mark.parametrize("sentinel", ["SHAPE_MISMATCH", "INSUFFICIENT_DATA"])
    def test_sentinels_are_neither_win_nor_loss(self, sentinel):
        """A refused verdict must not be silently counted on either side."""
        assert not _is_beats(sentinel)
        assert not _is_beaten(sentinel)


class TestAggregatedDebiasedState:
    @pytest.mark.parametrize(
        "coin,horizon,n_beats,n_beaten,p_median,n_beats_raw,published",
        PUBLISHED_DEBIASED,
    )
    def test_reproduces_every_published_verdict(
        self, coin, horizon, n_beats, n_beaten, p_median, n_beats_raw, published,
    ):
        """The executable must reproduce the table the doc publishes.

        This is the defect this class closes: the four `NO BEATS` rows came
        out of the harness as `INCONCLUSIVE`, so the published verdict was not
        reproducible from the deliverable that produced it.
        """
        assert _aggregate_debiased_state(
            n_beats_centered=n_beats,
            n_beaten_centered=n_beaten,
            n_seeds=4,
            dm_centered_p_median=p_median,
            n_beats_raw=n_beats_raw,
        ) == published

    def test_unanimous_loss_is_no_beats(self):
        assert _aggregate_debiased_state(
            n_beats_centered=0, n_beaten_centered=4, n_seeds=4,
            dm_centered_p_median=1e-04, n_beats_raw=0,
        ) == "NO BEATS"

    def test_majority_loss_is_not_no_beats(self):
        """The mandatory negative control: only the count changes.

        3/4 BEATEN is the same configuration as the test above with one seed
        moved out of the loss column. An exemption that cannot close again is
        not an exemption -- so the state must fall back to INCONCLUSIVE.
        """
        assert _aggregate_debiased_state(
            n_beats_centered=0, n_beaten_centered=3, n_seeds=4,
            dm_centered_p_median=1e-04, n_beats_raw=0,
        ) == "INCONCLUSIVE"

    def test_majority_win_is_not_beats(self):
        """The symmetric negative control on the winning side."""
        assert _aggregate_debiased_state(
            n_beats_centered=3, n_beaten_centered=0, n_seeds=4,
            dm_centered_p_median=1e-04, n_beats_raw=3,
        ) == "INCONCLUSIVE"

    def test_refuted_when_the_raw_leg_won_alone(self):
        """A raw 4/4 win that the precision leg does not confirm."""
        assert _aggregate_debiased_state(
            n_beats_centered=2, n_beaten_centered=0, n_seeds=4,
            dm_centered_p_median=0.30, n_beats_raw=4,
        ) == "refuted-de-biased"

    def test_no_beats_outranks_refuted_when_both_apply(self):
        """Precedence, decided once and sealed here.

        A raw 4/4 win whose precision leg significantly REVERSES it satisfies
        both branches. `NO BEATS` wins: "refuted" says a claim is unconfirmed,
        the measurement says the model loses, and reporting the weaker of the
        two would soften a measured loss. The refutation stays visible because
        the summary row prints the raw verdict beside it.
        """
        assert _aggregate_debiased_state(
            n_beats_centered=0, n_beaten_centered=4, n_seeds=4,
            dm_centered_p_median=1e-06, n_beats_raw=4,
        ) == "NO BEATS"

    @pytest.mark.parametrize(
        "n_beats,n_beaten", [(4, 0), (0, 4)],
    )
    def test_insignificant_median_blocks_both_unanimous_states(self, n_beats, n_beaten):
        """The significance clause applies to the loss exactly as to the win."""
        state = _aggregate_debiased_state(
            n_beats_centered=n_beats, n_beaten_centered=n_beaten, n_seeds=4,
            dm_centered_p_median=0.20, n_beats_raw=0,
        )
        assert state == "INCONCLUSIVE"

    def test_zero_seeds_is_not_a_vacuous_unanimity(self):
        """`0 == 0` must not read as "every seed agreed"."""
        assert _aggregate_debiased_state(
            n_beats_centered=0, n_beaten_centered=0, n_seeds=0,
            dm_centered_p_median=float("nan"), n_beats_raw=0,
        ) == "INCONCLUSIVE"

    def test_every_state_is_reachable(self):
        """The four documented states, and no fifth one."""
        reached = {
            _aggregate_debiased_state(
                n_beats_centered=b, n_beaten_centered=n, n_seeds=4,
                dm_centered_p_median=p, n_beats_raw=r,
            )
            for b, n, p, r in [
                (4, 0, 1e-06, 4), (0, 4, 1e-06, 0), (2, 0, 0.30, 4), (1, 1, 0.30, 0),
            ]
        }
        assert reached == {"BEATS", "NO BEATS", "refuted-de-biased", "INCONCLUSIVE"}
