"""Tests for league_correlation.py — weekly league correlation matrix (#19821 brick 4, #20083).

The decisive tests are `test_weekend_points_do_not_move_the_week_close` (crypto and equity
series are read on the same Friday) and `test_missing_week_is_skipped_not_merged` (a gap
never becomes a two-week return).
"""

from __future__ import annotations

import datetime as dt
import json

import numpy as np
import pytest

import league_correlation as lc


def _chart(dates: list[str], values: list[float], prefix: str = "e") -> dict:
    """Graphique `shadow` minimal : la séance k va dans la série `{prefix}{k % 5}`."""
    series = {f"{prefix}{k}": {"values": []} for k in range(5)}
    for i, (d, v) in enumerate(zip(dates, values)):
        ts = int(dt.datetime.fromisoformat(d + "T17:00:00+00:00").timestamp())
        series[f"{prefix}{i % 5}"]["values"].append([ts, v])
    return {"name": "shadow", "series": series}


def _days(start: str, n: int, weekends: bool = False) -> list[str]:
    d, out = dt.date.fromisoformat(start), []
    while len(out) < n:
        if weekends or d.weekday() < 5:
            out.append(d.isoformat())
        d += dt.timedelta(days=1)
    return out


def test_week_key_maps_to_friday():
    assert lc.week_key("2026-10-05") == "2026-10-09"  # lundi
    assert lc.week_key("2026-10-09") == "2026-10-09"  # vendredi
    assert lc.week_key("2026-10-10") == "2026-10-16"  # samedi -> vendredi suivant
    assert lc.week_key("2026-10-11") == "2026-10-16"  # dimanche -> vendredi suivant


def test_weekly_returns_use_friday_closes_and_drop_last_week():
    dates = _days("2026-09-07", 15)  # trois semaines pleines, lundi -> vendredi
    equity = [100.0 + i for i in range(15)]
    r = lc.weekly_returns(dates, equity)
    # clôtures : 104 (11/09), 109 (18/09), 114 (25/09) ; la dernière semaine est retirée
    assert list(r) == ["2026-09-18"]
    assert r["2026-09-18"] == pytest.approx(109 / 104 - 1)


def test_weekend_points_do_not_move_the_week_close():
    weekdays = _days("2026-09-07", 20)
    alldays = _days("2026-09-07", 26, weekends=True)
    value = {d: 100.0 + i for i, d in enumerate(alldays)}
    equity_r = lc.weekly_returns(weekdays, [value[d] for d in weekdays])
    crypto_r = lc.weekly_returns(alldays, [value[d] for d in alldays])
    common = sorted(equity_r.keys() & crypto_r.keys())
    assert common
    for w in common:
        assert crypto_r[w] == pytest.approx(equity_r[w])


def test_missing_week_is_skipped_not_merged():
    dates = [d for d in _days("2026-09-07", 25) if lc.week_key(d) != "2026-09-25"]
    r = lc.weekly_returns(dates, [100.0 + i for i in range(len(dates))])
    assert "2026-09-25" not in r
    assert "2026-10-02" not in r  # pas de rendement 18/09 -> 02/10 sur deux semaines
    assert "2026-09-18" in r


def test_bootstrap_identical_and_opposite_series():
    rng = np.random.default_rng(1)
    x = rng.normal(size=200)
    same = lc.block_bootstrap_corr(x, x, draws=300)
    assert same["observed"] == pytest.approx(1.0)
    assert same["ci95"] == pytest.approx([1.0, 1.0])
    opp = lc.block_bootstrap_corr(x, -x, draws=300)
    assert opp["observed"] == pytest.approx(-1.0)
    assert opp["ci95"] == pytest.approx([-1.0, -1.0])


def test_bootstrap_is_paired_and_reproducible():
    rng = np.random.default_rng(2)
    x = rng.normal(size=300)
    y = 0.6 * x + 0.8 * rng.normal(size=300)
    a = lc.block_bootstrap_corr(x, y, draws=500)
    b = lc.block_bootstrap_corr(x, y, draws=500)
    assert a == b
    lo, hi = a["ci95"]
    assert lo < a["observed"] < hi
    assert lo > 0.3  # appariement : un rééchantillonnage indépendant donnerait un IC autour de 0
    z = rng.normal(size=300)
    lo, hi = lc.block_bootstrap_corr(x, z, draws=500)["ci95"]
    assert lo < 0 < hi


def test_constant_draws_are_counted_not_quantiled():
    x = np.zeros(120)
    x[:8] = np.linspace(-0.02, 0.025, 8)
    y = np.random.default_rng(3).normal(size=120)
    res = lc.block_bootstrap_corr(x, y, draws=400)
    assert res["undefined_draws"] > 0
    assert all(np.isfinite(res["ci95"]))


def test_pair_requires_min_weeks():
    weeks = [(dt.date(2020, 1, 3) + dt.timedelta(weeks=i)).isoformat() for i in range(150)]
    rng = np.random.default_rng(4)
    a = dict(zip(weeks, rng.normal(size=150)))
    b = dict(zip(weeks[100:], rng.normal(size=50)))
    res = lc.pair(a, b)
    assert res["observed"] is None and res["weeks"] == 50
    assert "fewer than" in res["reason"]
    full = lc.pair(a, dict(zip(weeks, rng.normal(size=150))), draws=200)
    assert full["weeks"] == 150 and full["first"] == weeks[0]


def test_position_flags_fragile_estimates():
    assert lc.position({"observed": 0.5, "ci95": [0.3, 0.65]}) == "sous 0.7"
    assert lc.position({"observed": 0.65, "ci95": [0.5, 0.8]}) == "sous 0.7 (fragile)"
    assert lc.position({"observed": 0.9, "ci95": [0.8, 0.95]}) == "au-dessus de 0.7"
    assert lc.position({"observed": None}) == "non mesurée"


def test_member_returns_reads_held_reference_series(tmp_path):
    dates = _days("2026-01-05", 60)
    strat = [100.0 + i for i in range(60)]
    held = [200.0 - i for i in range(60)]
    chart = _chart(dates, strat)
    chart["series"].update(_chart(dates, held, prefix="b")["series"])
    (tmp_path / "x" / "base").mkdir(parents=True)
    (tmp_path / "x" / "base" / "chart.json").write_text(json.dumps(chart), encoding="utf-8")
    e = lc.member_returns(tmp_path, {"id": "s", "trace": "x/base"})
    b = lc.member_returns(tmp_path, {"id": "h", "trace": "x/base", "series": "b"})
    assert e.keys() == b.keys()
    assert all(v > 0 for v in e.values()) and all(v < 0 for v in b.values())


def test_members_file_is_well_formed():
    members = lc.load_members()
    ids = [m["id"] for m in members]
    assert len(set(ids)) == len(ids)
    for m in members:
        assert m["role"] in {"candidate", "reference", "core"}
        assert m["trace"].count("/") == 1 and m.get("series", "e") in {"e", "b"}


def test_active_share_counts_invested_weeks():
    assert lc.active_share({"a": 0.0, "b": 0.01, "c": 0.0, "d": -0.02}) == pytest.approx(0.5)
    assert lc.active_share({}) == 0.0
