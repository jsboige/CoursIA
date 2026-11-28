"""Tests for shadow_etf_rotation.py (#28992) on synthetic series, without network."""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

import shadow_etf_rotation as ser
import shadow_replay

# daily drift of each pocket: two up strongly, one up slightly, three down
DRIFTS = dict(zip(ser.POCKETS, [0.0010, 0.0008, 0.0002, -0.0003, -0.0005, -0.0007]))


def _closes(start: str = "2025-01-01", end: str = "2026-12-31", drifts: dict | None = None,
            noise: float = 0.0) -> dict[str, pd.Series]:
    idx = pd.bdate_range(start, end)
    rng = np.random.default_rng(0)
    out = {}
    for sym, mu in (drifts or DRIFTS).items():
        steps = 1.0 + mu + rng.normal(0.0, noise, len(idx))
        out[sym] = pd.Series(100.0 * np.cumprod(steps), index=idx)
    out[ser.WAITING] = pd.Series(100.0 * np.cumprod(np.full(len(idx), 1.0001)), index=idx)
    return out


def _dates(index) -> list[str]:
    return [d.strftime("%Y-%m-%d") for d in index]


# ---------------------------------------------------------------- calendar


def test_schedule_opens_on_start_then_complete_month_ends():
    idx = pd.bdate_range("2026-08-03", "2026-11-06")
    # 2026-10-03 is a Saturday: the first session is Monday 2026-10-05
    assert _dates(ser.schedule_dates(idx, "2026-10-03", "2026-11-02")) == ["2026-10-05", "2026-10-30"]


def test_schedule_skips_the_month_of_end():
    idx = pd.bdate_range("2026-08-03", "2026-11-30")
    assert _dates(ser.schedule_dates(idx, "2026-10-05", "2026-11-16")) == ["2026-10-05", "2026-10-30"]


def test_schedule_without_session_raises():
    idx = pd.bdate_range("2026-08-03", "2026-10-02")
    with pytest.raises(ValueError):
        ser.schedule_dates(idx, "2026-10-03", "2026-10-05")


def test_panel_keeps_common_pocket_sessions_and_carries_the_waiting_line():
    closes = _closes("2026-01-05", "2026-01-30")
    closes[ser.POCKETS[0]] = closes[ser.POCKETS[0]].drop(pd.Timestamp("2026-01-12"))
    closes[ser.WAITING] = closes[ser.WAITING].drop(pd.Timestamp("2026-01-20"))
    panel = ser.build_panel(closes)
    # a session missing for one pocket is not a common session
    assert pd.Timestamp("2026-01-12") not in panel.index
    # a session missing for the waiting line only keeps its last close
    assert panel.loc["2026-01-20", ser.WAITING] == closes[ser.WAITING].loc["2026-01-19"]
    assert not panel.isna().any().any()


def test_panel_without_a_line_raises():
    closes = _closes("2026-01-05", "2026-01-30")
    del closes[ser.WAITING]
    with pytest.raises(ValueError):
        ser.build_panel(closes)


# ---------------------------------------------------------------- the rule


def test_momentum_runs_from_month_end_t_minus_9_to_t_minus_1():
    closes = _closes("2025-01-01", "2026-12-31", noise=0.01)
    panel = ser.build_panel(closes)
    anchors = ser.complete_month_ends(panel.index, "2026-12-01")
    t = pd.Timestamp("2026-11-30")
    got = ser.momentum(panel[ser.POCKETS], anchors, t)
    k = list(anchors).index(t)
    want = panel.loc[anchors[k - 1], ser.POCKETS] / panel.loc[anchors[k - 9], ser.POCKETS] - 1.0
    assert anchors[k - 1] == pd.Timestamp("2026-10-30")
    assert anchors[k - 9] == pd.Timestamp("2026-02-27")
    assert np.allclose(got.to_numpy(), want.to_numpy())
    # the last month is skipped: changing the November closes does not move the signal
    moved = panel.copy()
    moved.loc["2026-11-02":"2026-11-30", ser.POCKETS] *= 3.0
    again = ser.momentum(moved[ser.POCKETS], anchors, t)
    assert np.allclose(again.to_numpy(), got.to_numpy())


def test_momentum_mid_month_uses_the_last_complete_month_end():
    panel = ser.build_panel(_closes(noise=0.01))
    anchors = ser.complete_month_ends(panel.index, "2026-12-20")
    mid = ser.momentum(panel[ser.POCKETS], anchors, pd.Timestamp("2026-12-01"))
    end = ser.momentum(panel[ser.POCKETS], anchors, pd.Timestamp("2026-11-30"))
    assert np.allclose(mid.to_numpy(), end.to_numpy())


def test_momentum_without_nine_month_ends_raises():
    panel = ser.build_panel(_closes("2026-01-01", "2026-12-31"))
    anchors = ser.complete_month_ends(panel.index, "2026-12-01")
    with pytest.raises(ValueError):
        ser.momentum(panel[ser.POCKETS], anchors, pd.Timestamp("2026-09-30"))


def test_weights_take_the_two_best_positive_pockets():
    mom = pd.Series(dict(zip(ser.POCKETS, [0.05, 0.20, -0.10, 0.15, 0.01, -0.30])))
    w = ser.target_weights(mom)
    assert w[ser.POCKETS[1]] == 0.5 and w[ser.POCKETS[3]] == 0.5
    assert w[ser.WAITING] == 0.0
    assert sum(v for k, v in w.items() if k not in (ser.POCKETS[1], ser.POCKETS[3])) == 0.0


def test_a_chosen_pocket_without_positive_momentum_leaves_its_share_waiting():
    mom = pd.Series(dict(zip(ser.POCKETS, [0.04, 0.0, -0.10, -0.15, -0.01, -0.30])))
    w = ser.target_weights(mom)
    # the second best has a momentum of exactly 0: not strictly positive
    assert w[ser.POCKETS[0]] == 0.5 and w[ser.POCKETS[1]] == 0.0
    assert w[ser.WAITING] == 0.5
    all_down = ser.target_weights(pd.Series(dict(zip(ser.POCKETS, [-0.01] * 6))))
    assert all_down[ser.WAITING] == 1.0


def test_ties_follow_the_order_of_the_pockets():
    mom = pd.Series(dict(zip(ser.POCKETS, [0.1, 0.1, 0.1, 0.1, 0.1, 0.1])))
    w = ser.target_weights(mom)
    assert [k for k, v in w.items() if v > 0] == ser.POCKETS[:2]


# ---------------------------------------------------------------- replay


def test_window_is_half_open_and_opens_with_the_allocation_fee():
    closes = _closes()
    out = ser.replay(closes, "2026-06-03", "2026-09-01")
    assert out["dates"][0] == "2026-06-03"
    assert out["dates"][-1] == "2026-08-31"
    assert all("2026-06-03" <= d < "2026-09-01" for d in out["dates"])
    assert len(out["dates"]) == len(out["net_returns"]) == len(out["turnover"])
    # opening: the two rising pockets, half each, nothing held before the close
    assert out["turnover"][0] == pytest.approx(1.0)
    assert out["net_returns"][0] == pytest.approx(-ser.FEE)
    traded = {d for d, t in zip(out["dates"], out["turnover"]) if t > 0}
    assert traded <= {"2026-06-03", "2026-06-30", "2026-07-31", "2026-08-31"}


def test_the_rotation_holds_the_two_best_pockets():
    closes = _closes()
    out = ser.replay(closes, "2026-06-03", "2026-09-01")
    panel = ser.build_panel(closes)
    held = panel.pct_change().loc["2026-06-04":"2026-06-30", ser.POCKETS[:2]].mean(axis=1)
    got = pd.Series(out["net_returns"], index=pd.DatetimeIndex(out["dates"])).loc["2026-06-04":"2026-06-29"]
    # between rebalances the portfolio drifts: its return stays close to the equal mix of the two
    assert np.allclose(got.to_numpy(), held.loc[got.index].to_numpy(), atol=2e-5)


def test_falling_markets_wait_on_the_waiting_line():
    drifts = dict.fromkeys(ser.POCKETS, -0.0005)
    closes = _closes(drifts=drifts)
    out = ser.replay(closes, "2026-06-03", "2026-07-01")
    rets = np.asarray(out["net_returns"][1:])
    assert np.allclose(rets, 0.0001)


def test_fees_are_measured_on_the_starting_equity():
    closes = _closes(noise=0.01)
    out = ser.replay(closes, "2026-02-02", "2026-12-01")
    equity = np.cumprod(1.0 + np.asarray(out["net_returns"]))
    rate = np.asarray(out["turnover"]) * ser.FEE
    assert out["fees"] == pytest.approx(float((equity / (1.0 - rate) * rate).sum()))


def test_not_enough_history_raises():
    with pytest.raises(ValueError):
        ser.replay(_closes("2026-01-01", "2026-12-31"), "2026-06-03", "2026-09-01")


def test_bad_parameters_raise():
    closes = _closes()
    with pytest.raises(ValueError):
        ser.replay(closes, "2026-06-03", "2026-09-01", top=0)
    with pytest.raises(ValueError):
        ser.replay(closes, "2026-06-03", "2026-09-01", look=3, skip=3)


def test_entry_point_meets_the_shadow_contract(monkeypatch, capsys):
    closes = _closes(noise=0.01)

    def fake_fetch(start, end, folder):
        print("download noise")
        return closes

    monkeypatch.setattr(ser, "fetch_closes", fake_fetch)
    out = ser.etf_rotation(start="2026-06-03", end="2026-09-01")
    assert set(out) == {"dates", "net_returns", "turnover", "fees"}
    # the shadow driver parses stdout as JSON: the entry point must not write to it
    captured = capsys.readouterr()
    assert captured.out == ""
    assert "download noise" in captured.err
    row = shadow_replay.metrics(out["dates"], out["net_returns"], out["turnover"], out["fees"])
    assert row["n_days"] == len(out["dates"])
    assert row["sharpe_net"] is not None
