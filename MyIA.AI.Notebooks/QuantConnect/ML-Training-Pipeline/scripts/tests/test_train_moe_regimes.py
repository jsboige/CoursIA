"""Tests for train_moe_regimes.py -- regime decode plumbing (#21054 case 4).

Covers the opt-in causal decode added for the walk-forward re-measure:
- ``regime_decode`` reaches the ``detect_regimes`` call only for
  ``regime_method="hmm"`` (price labels are causal by construction);
- the decode + causality provenance land in the per-seed result JSON and in
  the multiseed summary;
- torch seeding makes same-seed runs reproducible (no silent init noise
  mixing with the decode effect);
- the walk-forward records the per-observation OOS squared errors that the
  paired DM comparison (``moe_regimes_decode_dm.py``) consumes.
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

import train_moe_regimes as tmr


# ---------------------------------------------------------------------------
# Fixtures / helpers
# ---------------------------------------------------------------------------

@pytest.fixture
def synthetic_raw():
    np.random.seed(0)
    return tmr.generate_synthetic_data(560)


def _fake_walk_forward(n_folds=2):
    """Minimal fold list matching the recorder contract (no torch)."""
    return [
        {
            "fold": i,
            "train_end": 100 * (i + 1),
            "test_size": 40,
            "direction_accuracy": 0.5,
            "mse": 1.0,
            "n_experts": 1,
            "expert_regimes": ["bull"],
            "expert_stats": {},
            "regime_pred_counts": {"bull": 40},
            "oos_sq_errors": [0.5, 0.25] * 20,
        }
        for i in range(n_folds)
    ]


def _run_pipeline(monkeypatch, raw, *, regime_method, regime_decode="viterbi",
                  captured=None):
    def fake_detect(prices, method="price", **kwargs):
        if captured is not None:
            captured["method"] = method
            captured["kwargs"] = dict(kwargs)
        # Deterministic 2-regime labels aligned with the price index.
        labels = pd.Series(
            np.where(np.arange(len(prices)) % 7 < 4, "bull", "bear"),
            index=prices.index,
        )
        return labels

    monkeypatch.setattr(tmr, "detect_regimes", fake_detect)
    monkeypatch.setattr(
        tmr, "train_moe_regimes_walk_forward", lambda *a, **k: _fake_walk_forward()
    )
    return tmr.train_moe_regimes_pipeline(
        raw_data=raw,
        regime_method=regime_method,
        regime_decode=regime_decode,
        epochs=1,
        n_folds=2,
        min_samples=5,
    )


# ---------------------------------------------------------------------------
# Decode plumbing
# ---------------------------------------------------------------------------

class TestRegimeDecodePlumbing:
    def test_filter_decode_reaches_hmm_call(self, monkeypatch, synthetic_raw):
        captured: dict = {}
        result = _run_pipeline(
            monkeypatch, synthetic_raw,
            regime_method="hmm", regime_decode="filter", captured=captured,
        )
        assert captured["method"] == "hmm"
        assert captured["kwargs"].get("decode_mode") == "filter"
        assert result["regime_decode"] == "filter"
        assert result["regime_decode_causal"] is True
        assert "viterbi" in result["lookahead_note"].lower()

    def test_lookback_and_n_states_reach_hmm_call(self, monkeypatch, synthetic_raw):
        captured: dict = {}
        result = _run_pipeline(
            monkeypatch, synthetic_raw,
            regime_method="hmm", regime_decode="filter", captured=captured,
        )
        # Defaults: the detector window is exposed so the labeling can span
        # the walk-forward (#21054 case 4 -- default 400 pads the rest).
        assert captured["kwargs"].get("lookback") == 400
        assert captured["kwargs"].get("n_states") == 3
        assert result["regime_lookback"] == 400
        assert result["regime_n_states"] == 3

    def test_default_viterbi_reaches_hmm_call(self, monkeypatch, synthetic_raw):
        captured: dict = {}
        result = _run_pipeline(
            monkeypatch, synthetic_raw,
            regime_method="hmm", regime_decode="viterbi", captured=captured,
        )
        assert captured["kwargs"].get("decode_mode") == "viterbi"
        assert result["regime_decode"] == "viterbi"
        assert result["regime_decode_causal"] is False

    def test_price_method_gets_no_decode_kwarg(self, monkeypatch, synthetic_raw):
        captured: dict = {}
        result = _run_pipeline(
            monkeypatch, synthetic_raw,
            regime_method="price", regime_decode="filter", captured=captured,
        )
        assert "decode_mode" not in captured["kwargs"]
        assert result["regime_decode"] == "n/a"
        assert result["regime_decode_causal"] is True

    def test_multiseed_summary_carries_decode(self, monkeypatch, synthetic_raw):
        def fake_pipeline(**kwargs):
            return {
                "moe_mean_diracc": 0.5,
                "majority_baseline_acc": 0.5,
                "regime_decode": kwargs.get("regime_decode", "viterbi"),
            }

        monkeypatch.setattr(tmr, "train_moe_regimes_pipeline", fake_pipeline)
        summary = tmr.run_multiseed(
            seeds=[0, 1],
            raw_data=synthetic_raw,
            regime_method="hmm",
            regime_decode="filter",
            epochs=1,
            n_folds=2,
            min_samples=5,
        )
        assert summary["regime_decode"] == "filter"


# ---------------------------------------------------------------------------
# Seeding reproducibility
# ---------------------------------------------------------------------------

class TestSeeding:
    def test_torch_manual_seed_called_with_seed(self, monkeypatch, synthetic_raw):
        import torch

        calls: list[int] = []
        real_manual_seed = torch.manual_seed

        def spy(seed):
            calls.append(int(seed))
            return real_manual_seed(seed)

        monkeypatch.setattr(torch, "manual_seed", spy)
        _run_pipeline(monkeypatch, synthetic_raw, regime_method="price", regime_decode="viterbi")
        assert 42 in calls  # pipeline default seed (numpy seed was already seeded; torch now too)

    def test_same_seed_same_fold_losses(self, synthetic_raw):
        """Real (unmocked) tiny walk-forward: same seed twice -> identical losses."""
        r1 = tmr.train_moe_regimes_pipeline(
            raw_data=synthetic_raw, regime_method="price", seed=7,
            epochs=2, n_folds=2, min_samples=5,
        )
        r2 = tmr.train_moe_regimes_pipeline(
            raw_data=synthetic_raw, regime_method="price", seed=7,
            epochs=2, n_folds=2, min_samples=5,
        )
        e1 = [f["oos_sq_errors"] for f in r1["fold_details"]]
        e2 = [f["oos_sq_errors"] for f in r2["fold_details"]]
        assert len(e1) > 0 and len(e1) == len(e2)
        for a, b in zip(e1, e2):
            assert a == pytest.approx(b, rel=1e-9, abs=1e-12)


# ---------------------------------------------------------------------------
# Recorder contract for the DM comparison
# ---------------------------------------------------------------------------

class TestOosRecorder:
    def test_walk_forward_records_paired_losses(self, synthetic_raw):
        """The recorder output feeds moe_regimes_decode_dm.py: lengths must match y_test."""
        X, y, _cols = tmr.build_sequences(
            tmr.FeatureEngineer(lookback=20).transform(synthetic_raw), seq_len=20
        )
        labels = np.full(len(y), "bull")
        folds = tmr.train_moe_regimes_walk_forward(
            X, y, labels, expert_type="lstm", epochs=2, n_folds=2,
            min_samples=5, device="cpu",
        )
        assert folds, "expected at least one fold on 560 synthetic rows"
        for f in folds:
            assert len(f["oos_sq_errors"]) == f["test_size"]
            assert all(e >= 0 for e in f["oos_sq_errors"])

    def test_walk_forward_records_signed_bias(self, synthetic_raw):
        """#23171 point 3 : mean(e) n'est pas reconstructible depuis e^2.

        Un run dont le MSE est identique peut porter un biais oppose : le
        recoder doit donc ecrire le biais signe a cote de la perte, sinon la
        lecture d'un verdict DM ne dit rien de la direction de l'erreur.
        """
        X, y, _cols = tmr.build_sequences(
            tmr.FeatureEngineer(lookback=20).transform(synthetic_raw), seq_len=20
        )
        labels = np.full(len(y), "bull")
        folds = tmr.train_moe_regimes_walk_forward(
            X, y, labels, expert_type="lstm", epochs=2, n_folds=2,
            min_samples=5, device="cpu",
        )
        assert folds
        for f in folds:
            for key in ("mean_target", "mean_pred", "signed_bias", "sign_bias",
                        "sign_target_mean"):
                assert key in f, f"missing '{key}' (recorder contract #23171)"
            # signed_bias est exactement mean(pred) - mean(y)
            np.testing.assert_allclose(
                f["signed_bias"], f["mean_pred"] - f["mean_target"], atol=1e-8
            )
            # et la perte reste coherente avec la serie d'erreurs carrees
            np.testing.assert_allclose(
                f["mse"], float(np.mean(f["oos_sq_errors"])), atol=1e-6
            )
            # biais en espace de signe : |(+/-1) - (+/-1)| <= 2
            assert abs(f["sign_bias"]) <= 2.0 + 1e-9


# ---------------------------------------------------------------------------
# Biais signe dans la comparaison DM (#23171 point 3)
# ---------------------------------------------------------------------------

class TestDecodeDmSignedBias:
    """Le biais de chaque bras ET celui de la baseline majorite sont reportes."""

    _SQ = {
        "viterbi": [0.0100, 0.0110, 0.0120, 0.0090] * 10,
        "filter": [0.0120, 0.0115, 0.0140, 0.0100] * 10,
    }

    @classmethod
    def _multiseed(cls, decode, signed_bias, sign_bias,
                   majority_class=1, sign_target=0.1042):
        base = cls._SQ[decode]
        fold = {
            "fold": 0,
            "train_end": 100,
            "test_size": len(base),
            "direction_accuracy": 0.5,
            "mse": float(np.mean(base)),
            "n_experts": 1,
            "expert_regimes": ["bull"],
            "expert_stats": {},
            "regime_pred_counts": {"bull": len(base)},
            "oos_sq_errors": base,
            "mean_target": 0.1042,
            "mean_pred": 0.1042 + signed_bias,
            "signed_bias": signed_bias,
            "sign_bias": sign_bias,
            "sign_target_mean": sign_target,
        }
        return {
            "summary": {
                "symbol": "SPY",
                "expert_type": "lstm",
                "regime_method": "hmm",
                "seeds": [0],
                "regime_decode": decode,
            },
            "seeds": [{
                "config": {"seed": 0},
                "fold_details": [fold],
                "moe_mean_diracc": 0.5,
                "beats_majority": False,
                "majority_class": majority_class,
            }],
        }

    def _compare(self, tmp_path, majority_class):
        import json

        import moe_regimes_decode_dm as dmd

        vit = self._multiseed("viterbi", -0.0020, -0.20, majority_class)
        fil = self._multiseed("filter", +0.0030, +0.30, majority_class)
        pv = tmp_path / "vit.json"
        pf = tmp_path / "fil.json"
        pv.write_text(json.dumps(vit), encoding="utf-8")
        pf.write_text(json.dumps(fil), encoding="utf-8")
        return dmd.compare(pv, pf)

    def test_signed_bias_per_arm_and_baseline(self, tmp_path):
        res = self._compare(tmp_path, majority_class=1)
        s = res["per_seed"][0]
        np.testing.assert_allclose(s["mean_err_viterbi"], -0.0020, atol=1e-9)
        np.testing.assert_allclose(s["mean_err_filter"], +0.0030, atol=1e-9)
        np.testing.assert_allclose(
            s["mean_err_diff_filter_minus_viterbi"], +0.0050, atol=1e-9
        )
        np.testing.assert_allclose(s["sign_bias_filter"], +0.30, atol=1e-9)
        np.testing.assert_allclose(s["sign_bias_viterbi"], -0.20, atol=1e-9)
        # baseline majorite = classe 1 -> prediction constante +1 en signe
        np.testing.assert_allclose(
            s["sign_bias_baseline"], 1.0 - 0.1042, atol=1e-9
        )
        # les agregats portent les memes grandeurs
        np.testing.assert_allclose(res["mean_err_filter"], +0.0030, atol=1e-9)
        np.testing.assert_allclose(res["sign_bias_baseline"], 1.0 - 0.1042, atol=1e-9)

    def test_baseline_bias_follows_the_majority_class(self, tmp_path):
        """Temoin negatif : classe 0 -> prediction -1, donc l'autre signe.

        Sans ce temoin, une baseline codee en dur a +1 passerait le test
        precedent sans jamais dependre de ``majority_class``.
        """
        res = self._compare(tmp_path, majority_class=0)
        np.testing.assert_allclose(
            res["per_seed"][0]["sign_bias_baseline"], -1.0 - 0.1042, atol=1e-9
        )

    def test_aggregate_is_committable_and_keeps_the_recountables(self, tmp_path):
        """#23171 point 1 : l'agregat commite doit suffire a recompter le body.

        Deux exigences opposees : la serie complete (~300 Ko/bras) ne doit PAS
        entrer dans le depot, et tout ce qui recompte les nombres publies doit
        y etre. Un agregat qui perd le biais signe ne repond pas a la demande ;
        un agregat qui embarque oos_sq_errors viole la politique d'artefacts.
        """
        import json

        import moe_regimes_decode_dm as dmd

        vit = self._multiseed("viterbi", -0.0020, -0.20)
        fil = self._multiseed("filter", +0.0030, +0.30)
        pv = tmp_path / "vit.json"
        pf = tmp_path / "fil.json"
        pv.write_text(json.dumps(vit), encoding="utf-8")
        pf.write_text(json.dumps(fil), encoding="utf-8")
        comp = dmd.compare(pv, pf)

        agg = dmd.build_aggregate(vit, fil, comp, {"viterbi": "cmd-v"})

        # La politique porte sur les CLES, pas sur la prose : la note de
        # falsifiabilite nomme legitimement le champ laisse hors depot.
        def _keys(obj):
            if isinstance(obj, dict):
                for k, v in obj.items():
                    yield k
                    yield from _keys(v)
            elif isinstance(obj, list):
                for item in obj:
                    yield from _keys(item)

        assert "oos_sq_errors" not in set(_keys(agg)), (
            "la serie complete ne doit pas etre committee"
        )
        # Controle positif : l'instrument sait voir la cle quand elle est la.
        # Un detecteur incapable de rougir ne prouve rien.
        assert "oos_sq_errors" in set(_keys(vit))

        fold = agg["viterbi"]["per_seed"][0]["folds"][0]
        for key in ("mse", "signed_bias", "sign_bias", "test_size",
                    "direction_accuracy", "mean_target", "mean_pred"):
            assert key in fold, f"agregat sans '{key}' : le body devient non recomptable"

        assert agg["commands"]["viterbi"] == "cmd-v"
        assert agg["filter"]["provenance"]["regime_decode"] == "filter"
        assert agg["comparison"]["dm_p_median"] == comp["dm_p_median"]
        assert agg["comparison"]["verdict"] in (
            "FILTER_BETTER", "FILTER_WORSE", "INCONCLUSIVE"
        )
