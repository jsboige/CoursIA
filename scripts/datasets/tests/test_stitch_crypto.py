#!/usr/bin/env python3
"""Tests pour scripts/datasets/stitch_crypto.py — BTC/USD continuous-series
stitcher (EPIC #4208 reproducible-data). Famille datasets/crypto, was 0 tests.

Couvre les fonctions pures hermétiques : load_bitstamp_1h (CSV parse + transform),
load_binance_hourly_from_zip (zip parse), validate_overlap (close-diff %),
stitch_datasets (concat/dedup/sort priority), quality_report (gaps/sources/yearly).
load_yfinance_btc + main (réseau) sont exclus / mockés.
"""

import io
import sys
import zipfile
from pathlib import Path

import pandas as pd
import pytest

HERE = Path(__file__).resolve().parent
DATASETS_DIR = HERE.parent
sys.path.insert(0, str(DATASETS_DIR))

import stitch_crypto as sc  # noqa: E402

pd = pytest.importorskip("pandas")


def _bitstamp_csv(rows):
    """Construit un CSV Bitstamp (reverse-chrono, header sur ligne 0 réelle,
    skiprows=1 dans le loader). rows = liste de tuples
    (unix, date_iso, symbol, open, high, low, close, vol_btc, vol_usd)."""
    out = io.StringIO()
    out.write("comment row to skip\n")
    out.write("unix,date,symbol,open,high,low,close,Volume BTC,Volume USD\n")
    for r in rows:
        out.write(",".join(str(x) for x in r) + "\n")
    return out.getvalue()


def _binance_zip(rows, tmp_path, name="bin.zip"):
    """Construit un zip contenant un CSV Binance (no header, format
    'YYYYMMDD HH:MM,open,high,low,close,volume'). rows = tuples."""
    p = tmp_path / name
    lines = []
    for r in rows:
        lines.append(",".join(str(x) for x in r))
    csv_content = "\n".join(lines) + "\n"
    with zipfile.ZipFile(p, "w") as zf:
        zf.writestr("data.csv", csv_content)
    return p


# --------------------------------------------------------------------------
# load_bitstamp_1h — CSV parse, reverse-chrono -> sorted, column renames
# --------------------------------------------------------------------------

def test_load_bitstamp_sorts_reverse_chronological(tmp_path):
    # Rows en ordre inverse-chronologique (comme la source réelle).
    csv = _bitstamp_csv([
        (1000, "2020-01-02 00:00:00", "BTCUSD", 100, 101, 99, 100.5, 1, 100.5),
        (999, "2020-01-01 00:00:00", "BTCUSD", 95, 96, 94, 95.5, 2, 191),
    ])
    p = tmp_path / "bs.csv"
    p.write_text(csv, encoding="utf-8")
    df = sc.load_bitstamp_1h(str(p))
    # Trié par timestamp croissant.
    assert df["timestamp"].iloc[0] < df["timestamp"].iloc[1]
    assert df["timestamp"].is_monotonic_increasing
    assert df["source"].iloc[0] == "bitstamp"


def test_load_bitstamp_column_renames_and_subset(tmp_path):
    csv = _bitstamp_csv([
        (1, "2020-01-01 00:00:00", "BTCUSD", 100, 110, 90, 105, 1.5, 157.5),
    ])
    p = tmp_path / "bs.csv"
    p.write_text(csv, encoding="utf-8")
    df = sc.load_bitstamp_1h(str(p))
    # Colonnes renommées.
    assert list(df.columns) == ["timestamp", "open", "high", "low", "close",
                                "volume_btc", "volume_usd", "source"]
    assert df["close"].iloc[0] == pytest.approx(105)
    assert df["volume_btc"].iloc[0] == pytest.approx(1.5)


def test_load_bitstamp_coerces_non_numeric_to_nan(tmp_path):
    csv = _bitstamp_csv([
        (1, "2020-01-01 00:00:00", "BTCUSD", "bad", 110, 90, 105, 1, 105),
    ])
    p = tmp_path / "bs.csv"
    p.write_text(csv, encoding="utf-8")
    df = sc.load_bitstamp_1h(str(p))
    assert pd.isna(df["open"].iloc[0])  # 'bad' -> NaN via errors='coerce'
    assert df["close"].iloc[0] == pytest.approx(105)


# --------------------------------------------------------------------------
# load_binance_hourly_from_zip — zip + no-header CSV parse
# --------------------------------------------------------------------------

def test_load_binance_zip_parses_and_adds_usd(tmp_path):
    # Format Binance : 'YYYYMMDD HH:MM',open,high,low,close,volume
    p = _binance_zip([
        ("20200101 00:00", 9000, 9100, 8900, 9050, 0.5),
        ("20200101 01:00", 9050, 9200, 9000, 9150, 0.3),
    ], tmp_path)
    df = sc.load_binance_hourly_from_zip(str(p))
    assert len(df) == 2
    assert df["source"].iloc[0] == "binance"
    assert df["timestamp"].is_monotonic_increasing
    # volume_usd = close * volume_usdt ; volume_btc = volume_usdt (alias).
    assert df["volume_usd"].iloc[0] == pytest.approx(9050 * 0.5)
    assert df["volume_btc"].iloc[0] == pytest.approx(0.5)


def test_load_binance_zip_datetime_format(tmp_path):
    p = _binance_zip([("20200615 12:00", 1, 2, 3, 4, 5)], tmp_path)
    df = sc.load_binance_hourly_from_zip(str(p))
    assert df["timestamp"].iloc[0] == pd.Timestamp("2020-06-15 12:00:00")


# --------------------------------------------------------------------------
# validate_overlap — close-diff %, has_overlap, within_threshold
# --------------------------------------------------------------------------

def _df(timestamps, closes, source="a"):
    return pd.DataFrame({"timestamp": pd.to_datetime(timestamps),
                         "close": closes, "source": source})


def test_validate_overlap_no_temporal_overlap():
    a = _df(["2020-01-01", "2020-01-02"], [100, 101])
    b = _df(["2021-01-01", "2021-01-02"], [200, 201])
    res = sc.validate_overlap(a, b)
    assert res["has_overlap"] is False


def test_validate_overlap_no_common_timestamps():
    a = _df(["2020-01-01 00:00", "2020-01-01 02:00"], [100, 101])
    b = _df(["2020-01-01 01:00", "2020-01-01 03:00"], [100.5, 101.5])
    res = sc.validate_overlap(a, b)
    assert res["has_overlap"] is False  # overlap period exists but no common ts


def test_validate_overlap_close_prices_within_threshold():
    a = _df(["2020-01-01", "2020-01-02"], [100, 101])
    b = _df(["2020-01-01", "2020-01-02"], [100.1, 101.2])  # ~0.1-0.2% diff
    res = sc.validate_overlap(a, b, max_close_diff_pct=0.5)
    assert res["has_overlap"] is True
    assert res["common_points"] == 2
    assert res["within_threshold"] is True
    assert res["mean_diff_pct"] < 0.5
    assert res["max_diff_pct"] < 0.5


def test_validate_overlap_exceeds_threshold():
    # Plage 2-points (overlap_start < overlap_end requis par le module).
    a = _df(["2020-01-01", "2020-01-02"], [100, 95])
    b = _df(["2020-01-01", "2020-01-02"], [100, 100])  # jan2: |95-100|/100 = 5%
    res = sc.validate_overlap(a, b, max_close_diff_pct=0.5)
    assert res["has_overlap"] is True
    assert res["within_threshold"] is False  # 5% > 0.5%
    assert res["max_diff_pct"] > 0.5


def test_validate_overlap_diff_is_absolute_value():
    """diff_pct est abs(a-b)/b*100 ; vérifie que négatif est pris en valeur absolue."""
    a = _df(["2020-01-01", "2020-01-02"], [100, 95])
    b = _df(["2020-01-01", "2020-01-02"], [100, 100])  # jan2: |95-100|/100 = 5%
    res = sc.validate_overlap(a, b, max_close_diff_pct=10)
    assert res["max_diff_pct"] == pytest.approx(5.0)
    assert res["within_threshold"] is True


# --------------------------------------------------------------------------
# stitch_datasets — concat, dedup keep=first (priority ordering), sort
# --------------------------------------------------------------------------

def test_stitch_priority_first_source_wins_on_duplicate():
    a = _df(["2020-01-01", "2020-01-02"], [100, 101], source="bitstamp")
    b = _df(["2020-01-01", "2020-01-03"], [999, 102], source="binance")
    out = sc.stitch_datasets([a, b])
    assert len(out) == 3  # 2020-01-01 dédupliqué
    # Le 1er source (bitstamp) gagne sur le timestamp commun.
    row_jan1 = out[out["timestamp"] == pd.Timestamp("2020-01-01")].iloc[0]
    assert row_jan1["close"] == 100
    assert row_jan1["source"] == "bitstamp"


def test_stitch_sorted_by_timestamp():
    # Passés dans l'ordre inverse, doivent resortir triés.
    b = _df(["2020-01-03"], [103], source="b")
    a = _df(["2020-01-01"], [101], source="a")
    out = sc.stitch_datasets([b, a])
    assert out["timestamp"].is_monotonic_increasing


def test_stitch_empty_list_raises():
    """Le module ne garde pas contre une liste vide : pd.concat([]) lève
    ValueError (comportement réel documenté)."""
    with pytest.raises(ValueError, match="No objects to concatenate"):
        sc.stitch_datasets([])


def test_stitch_no_duplicates_concatenates_all():
    a = _df(["2020-01-01"], [100], source="a")
    b = _df(["2020-01-02"], [101], source="b")
    out = sc.stitch_datasets([a, b])
    assert len(out) == 2


# --------------------------------------------------------------------------
# quality_report — total_rows, gaps, sources, price sanity, yearly coverage
# --------------------------------------------------------------------------

def test_quality_report_continuous_no_gaps():
    # Série continue horaire (pas de gaps > 1.5h).
    ts = pd.date_range("2020-01-01", periods=10, freq="h")
    df = pd.DataFrame({"timestamp": ts, "close": range(100, 110), "source": "a"})
    rep = sc.quality_report(df)
    assert rep["total_rows"] == 10
    assert rep["num_gaps"] == 0
    assert rep["min_close"] == 100.0
    assert rep["max_close"] == 109.0
    assert rep["nan_close"] == 0
    assert rep["sources"] == {"a": 10}


def test_quality_report_detects_gap():
    # Série avec un gap (saute 2020-01-01 03:00 et 04:00 -> gap 3h).
    ts = list(pd.date_range("2020-01-01 00:00", periods=3, freq="h")) + \
        list(pd.date_range("2020-01-01 05:00", periods=2, freq="h"))
    df = pd.DataFrame({"timestamp": ts, "close": [100, 101, 102, 103, 104], "source": "a"})
    rep = sc.quality_report(df)
    assert rep["num_gaps"] >= 1
    assert "max_gap" in rep
    assert "gap_details" in rep
    # Détail du gap : duration en heures.
    assert rep["gap_details"][0]["duration_hours"] >= 2


def test_quality_report_yearly_coverage():
    ts = list(pd.date_range("2019-12-31 23:00", periods=1, freq="h")) + \
        list(pd.date_range("2020-01-01 00:00", periods=3, freq="h"))
    df = pd.DataFrame({"timestamp": ts, "close": [100, 101, 102, 103], "source": "a"})
    rep = sc.quality_report(df)
    assert rep["yearly_hours"].get(2019) == 1
    assert rep["yearly_hours"].get(2020) == 3


def test_quality_report_nan_close_counted():
    ts = pd.date_range("2020-01-01", periods=3, freq="h")
    df = pd.DataFrame({"timestamp": ts, "close": [100, None, 102], "source": "a"})
    rep = sc.quality_report(df)
    assert rep["nan_close"] == 1


def test_quality_report_source_breakdown():
    ts = pd.date_range("2020-01-01", periods=4, freq="h")
    df = pd.DataFrame({"timestamp": ts, "close": [100, 101, 102, 103],
                       "source": ["a", "a", "b", "b"]})
    rep = sc.quality_report(df)
    assert rep["sources"] == {"a": 2, "b": 2}


def test_quality_report_does_not_mutate_input():
    """La fonction ajoute/supprime une colonne _year interne : ne doit pas
    laisser de trace sur le DataFrame d'entrée."""
    ts = pd.date_range("2020-01-01", periods=3, freq="h")
    df = pd.DataFrame({"timestamp": ts, "close": [100, 101, 102], "source": "a"})
    cols_before = list(df.columns)
    sc.quality_report(df)
    assert list(df.columns) == cols_before  # pas de _year résiduel


# --------------------------------------------------------------------------
# Constantes / garde-fous anti-biais
# --------------------------------------------------------------------------

def test_forbidden_symbols_excludes_mag7():
    """Le symbole interdit (anti-biais FAANG/Mag7) est bien dans l'ensemble."""
    assert {"AAPL", "MSFT", "GOOG", "AMZN", "NVDA", "TSLA", "META"} == sc.FORBIDDEN_SYMBOLS


def test_default_start_date_is_2013():
    """2011/2012 exclus (coverage faible) -> défaut 2013-01-01."""
    assert sc.DEFAULT_START_DATE == "2013-01-01"
