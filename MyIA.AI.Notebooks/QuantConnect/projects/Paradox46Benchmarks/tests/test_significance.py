"""Tests CPU de significance.py : pas de Lean, pas de reseau (numpy, scipy, pandas, pytest)."""
import datetime as dt
import json
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import significance as sig  # noqa: E402


def _sessions(n):
    day, out = dt.date(2020, 1, 2), []
    while len(out) < n:
        if day.weekday() < 5:
            out.append(day)
        day += dt.timedelta(days=1)
    return out


def _chart(days, equity):
    """Graphique shadow : la seance k dans e{k % 5}, horodatee a 20:00 UTC (apres la cloture)."""
    series = {f"e{k}": {"values": []} for k in range(5)}
    for k, (day, value) in enumerate(zip(days, equity)):
        ts = int(dt.datetime(day.year, day.month, day.day, 20, tzinfo=dt.timezone.utc).timestamp())
        series[f"e{k % 5}"]["values"].append([ts, float(value)])
    return {"series": series}


def _equity(returns):
    return 100000.0 * np.concatenate([[1.0], np.cumprod(1.0 + returns)])


def test_two_sided_p_matches_normal_quantile():
    assert sig.two_sided_p(1.959964) == pytest.approx(0.05, abs=1e-6)
    assert sig.two_sided_p(-1.959964) == pytest.approx(0.05, abs=1e-6)
    assert sig.two_sided_p(0.0) == pytest.approx(1.0)


def test_holm_adjustment_is_monotone_and_capped():
    adj = sig.holm({"a": 0.01, "b": 0.025, "c": 0.02, "d": 0.5})
    assert adj["a"] == pytest.approx(0.04)
    assert adj["c"] == pytest.approx(0.06)
    assert adj["b"] == pytest.approx(0.06)
    assert adj["d"] == pytest.approx(0.5)
    assert sig.holm({"x": 0.6, "y": 0.7})["x"] == 1.0


def test_paired_returns_refuses_mismatched_sessions():
    days = [str(d) for d in _sessions(4)]
    with pytest.raises(ValueError, match="session dates differ"):
        sig.paired_returns(days, [1, 2, 3, 4], days[:3] + ["2030-01-01"], [1, 2, 3, 4])


def test_paired_returns_are_simple_returns():
    days = [str(d) for d in _sessions(3)]
    r_a, r_b = sig.paired_returns(days, [100, 110, 99], days, [100, 100, 101])
    assert r_a == pytest.approx([0.10, -0.10])
    assert r_b == pytest.approx([0.0, 0.01])


def test_strong_edge_is_detected_by_all_three_tests():
    rng = np.random.default_rng(1)
    common = rng.normal(0.0, 0.01, 600)
    r_b = common
    r_a = common + 0.002 + rng.normal(0.0, 0.002, 600)
    res = sig.compare(r_a, r_b, n_boot=200, mean_block=10.0, seed=0)
    assert res["sharpe_diff"] > 0
    assert res["ledoit_wolf"]["p_two_sided"] < 0.01
    assert res["mean_diff"]["p_two_sided"] < 0.01
    assert not res["bootstrap"]["ci95_contains_zero"]


def test_no_edge_is_not_detected():
    rng = np.random.default_rng(2)
    r_a = rng.normal(0.0004, 0.01, 600)
    r_b = rng.normal(0.0004, 0.01, 600)
    res = sig.compare(r_a, r_b, n_boot=200, mean_block=10.0, seed=0)
    assert res["ledoit_wolf"]["p_two_sided"] > 0.05
    assert res["mean_diff"]["p_two_sided"] > 0.05
    assert res["bootstrap"]["ci95_contains_zero"]
    assert res["correlation"] == pytest.approx(0.0, abs=0.15)


def test_run_end_to_end_on_shadow_charts(tmp_path):
    rng = np.random.default_rng(3)
    days = _sessions(301)
    common = rng.normal(0.0003, 0.01, 300)
    paths = {}
    for name, r in {"strat": common + rng.normal(0.0, 0.004, 300),
                    "spy": common,
                    "6040": 0.6 * common + rng.normal(0.0001, 0.002, 300)}.items():
        paths[name] = tmp_path / f"{name}.json"
        paths[name].write_text(json.dumps(_chart(days, _equity(r))), encoding="utf-8")
    res = sig.run(paths["strat"], {"spy": paths["spy"], "6040": paths["6040"]}, n_boot=100)
    assert res["first_session"] == str(days[0])
    assert res["last_session"] == str(days[-1])
    assert set(res["p_raw"]) == {f"{b}/{t}" for b in ("spy", "6040")
                                 for t in ("ledoit_wolf", "bootstrap", "mean_diff")}
    assert all(res["p_holm"][k] >= res["p_raw"][k] for k in res["p_raw"])
    assert res["comparisons"]["spy"]["sessions"] == 301


def test_run_refuses_a_broken_shadow_trace(tmp_path):
    days = _sessions(30)
    eq = _equity(np.full(29, 0.001))
    good = _chart(days, eq)
    broken = _chart(days, eq)
    broken["series"]["e2"]["values"].pop(1)  # une seance perdue casse l'alternance
    (tmp_path / "s.json").write_text(json.dumps(good), encoding="utf-8")
    (tmp_path / "b.json").write_text(json.dumps(broken), encoding="utf-8")
    with pytest.raises(ValueError, match="interleaving"):
        sig.run(tmp_path / "s.json", {"spy": tmp_path / "b.json"}, n_boot=10)
