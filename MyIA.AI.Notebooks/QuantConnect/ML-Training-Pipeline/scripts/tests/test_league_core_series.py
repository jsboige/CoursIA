"""Tests for league_core_series.py (#20365) on synthetic series, without network."""

from __future__ import annotations

import json
import math

import numpy as np
import pandas as pd
import pytest

import league_core_series as lcs
import league_correlation as lc
import shadow_inverse_vol as siv


def _market():
    idx = pd.bdate_range("2025-06-02", "2026-12-31")
    rng = np.random.default_rng(5)

    def walk(vol, start=100.0):
        return pd.Series(start * np.cumprod(1.0 + rng.normal(0.0, vol / math.sqrt(252), len(idx))),
                         index=idx)

    closes = {s: walk(v) for s, v in [("SPY", 0.18), ("QQQ", 0.24), ("IEF", 0.07), ("GLD", 0.15)]}
    return closes, walk(0.08, start=1.15)


@pytest.fixture
def market(monkeypatch, tmp_path):
    closes, fx = _market()
    calls = []

    def fake_fetch(start, end, folder):
        calls.append((start, end, folder))
        (folder / "SPY_x.csv").write_text("Date,Close\n", encoding="utf-8")
        return closes, fx

    monkeypatch.setattr(siv, "fetch_closes", fake_fetch)
    return closes, fx, calls


def test_series_is_the_usd_account_replay(market, tmp_path):
    closes, fx, calls = market
    out_dir, closes_dir = tmp_path / "core", tmp_path / "closes"
    closes_dir.mkdir()
    assert lcs.main(["--out", str(out_dir), "--closes-dir", str(closes_dir),
                     "--start", "2025-09-01", "--end", "2026-10-01"]) == 0
    assert calls == [("2025-09-01", "2026-10-01", closes_dir)]
    want = siv.replay(closes, fx, "2025-09-01", "2026-10-01", "U", 0.025, account="USD")
    dates, equity = lc.local_daily_equity(out_dir / lcs.SERIES)
    assert dates == want["dates"]
    assert equity == pytest.approx(list(np.cumprod(1.0 + np.asarray(want["net_returns"]))))
    prov = json.loads((out_dir / lcs.PROVENANCE).read_text(encoding="utf-8"))
    assert prov["account"] == "USD" and prov["target"] == 0.025
    assert prov["sessions"] == len(want["dates"]) and prov["last"] == want["dates"][-1]
    # the closes read are fingerprinted, so that a second reading can check it replays them
    assert set(prov["closes"]) == {"SPY_x.csv"}
    assert prov["series_sha256"] == lcs.sha256(out_dir / lcs.SERIES)


def test_euro_account_is_a_sensitivity_not_the_default(market, tmp_path):
    closes_dir = tmp_path / "closes"
    closes_dir.mkdir()
    usd = lcs.core_series("2025-09-01", "2026-10-01", closes_dir)
    eur = lcs.core_series("2025-09-01", "2026-10-01", closes_dir, account="EUR")
    assert usd["dates"] == eur["dates"]
    assert usd["turnover"][0] == pytest.approx(eur["turnover"][0])
    assert usd["net_returns"] != pytest.approx(eur["net_returns"])


def test_written_series_feeds_the_league_matrix(market, tmp_path):
    root = tmp_path / "traces"
    out_dir = root / "20365-league-core" / "core-equity"
    closes_dir = tmp_path / "closes"
    closes_dir.mkdir()
    lcs.main(["--out", str(out_dir), "--closes-dir", str(closes_dir),
              "--start", "2025-09-01", "--end", "2026-10-01"])
    weekly = lc.member_returns(root, {"id": "core-equity", "kind": "local",
                                      "trace": "20365-league-core/core-equity"})
    assert len(weekly) > 40
    assert all(lc.week_key(w) == w for w in weekly)
