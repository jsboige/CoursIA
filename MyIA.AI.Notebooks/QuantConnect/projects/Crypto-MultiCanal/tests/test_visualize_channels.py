# -*- coding: utf-8 -*-
"""Unit tests for ``Crypto-MultiCanal/visualize_channels.py`` leaf helpers.

``visualize_channels.py`` builds 3-level ZigZag channel envelopes (macro/meso/
micro) and renders them with matplotlib. The orchestration entry points
(``build_channels_3level``, ``visualize_asset``, ``plot_*``) pull live market
data via ``yfinance`` and drive matplotlib axes -- they are exercised through
the script's ``__main__`` run and are out of scope for unit tests.

The three **pure leaf helpers** they compose from -- the Series->dict anchor
normalizer, the two-anchor -> slope/intercept line fitter, and the
channel-dict -> sorted anchor-times extractor -- carry the geometry glue and
had **zero direct coverage**. This file pins their contracts in isolation.

Run from the repo root::

    python -m pytest MyIA.AI.Notebooks/QuantConnect/projects/Crypto-MultiCanal/tests/test_visualize_channels.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

import pandas as pd
import pytest

# Make the sibling ``visualize_channels.py`` importable (no package __init__).
# ``visualize_channels`` itself imports ``channel_helpers`` via a sys.path
# insert on its own dir, so pointing at the project dir resolves both.
_HERE = Path(__file__).resolve().parent
_SRC = _HERE.parent
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from visualize_channels import (  # noqa: E402
    _get_anchor_times,
    _get_line_mc,
    _to_dict,
)


# ---------------------------------------------------------------------------
# _to_dict
# ---------------------------------------------------------------------------
def test_to_dict_valid_series_returns_normalized_dict():
    """A well-formed Series -> dict with price/time_numeric coerced to float."""
    s = pd.Series({"time": "2024-01-01", "price": 100.5, "time_numeric": 1.0})
    d = _to_dict(s)
    assert d == {"time": "2024-01-01", "price": 100.5, "time_numeric": 1.0}
    # The two numeric fields are run through float() so numpy scalars survive.
    assert isinstance(d["price"], float)
    assert isinstance(d["time_numeric"], float)


def test_to_dict_none_returns_none():
    """None input -> None (no exception)."""
    assert _to_dict(None) is None


def test_to_dict_wrong_type_returns_none():
    """A non-Series value (string, dict, list) -> None."""
    assert _to_dict("not a series") is None
    assert _to_dict({"price": 1}) is None
    assert _to_dict([1, 2, 3]) is None


def test_to_dict_missing_any_field_returns_none():
    """A Series lacking time / price / time_numeric -> None (incomplete anchor)."""
    # Missing time_numeric.
    assert _to_dict(pd.Series({"time": "2024", "price": 100})) is None
    # Missing price.
    assert _to_dict(pd.Series({"time": "2024", "time_numeric": 1.0})) is None
    # Missing time.
    assert _to_dict(pd.Series({"price": 100, "time_numeric": 1.0})) is None


def test_to_dict_none_value_coerced_to_nan_passes_through():
    """A field built as None alongside numeric siblings -> pandas float64 NaN.

    When a Series mixes ``None`` with numeric values, pandas upcasts the whole
    Series to float64 and turns ``None`` into ``NaN``. ``Series.get`` then
    returns ``NaN`` (not Python ``None``), so the ``if t is None`` guard in
    ``_to_dict`` does NOT fire -- the anchor passes through with ``time=NaN``.

    This pins the actual pandas-coercion behavior: the ``is None`` guard catches
    a MISSING key (``Series.get`` default), not a NaN-valued present key.
    """
    import math
    s = pd.Series({"time": None, "price": 100, "time_numeric": 1.0})
    d = _to_dict(s)
    assert d is not None
    assert math.isnan(d["time"])
    assert d["price"] == 100.0
    assert d["time_numeric"] == 1.0


# ---------------------------------------------------------------------------
# _get_line_mc
# ---------------------------------------------------------------------------
def test_get_line_mc_normal_line():
    """Two anchors (0,100)-(10,200) -> slope=10, intercept=100."""
    p1 = {"time_numeric": 0, "price": 100}
    p2 = {"time_numeric": 10, "price": 200}
    assert _get_line_mc(p1, p2) == (10.0, 100.0)


def test_get_line_mc_descending_line():
    """Descending anchors (0,200)-(10,100) -> slope=-10, intercept=200."""
    p1 = {"time_numeric": 0, "price": 200}
    p2 = {"time_numeric": 10, "price": 100}
    assert _get_line_mc(p1, p2) == (-10.0, 200.0)


def test_get_line_mc_either_none_returns_none():
    """If either anchor dict is None -> None (degenerate channel side)."""
    p2 = {"time_numeric": 10, "price": 200}
    assert _get_line_mc(None, p2) is None
    assert _get_line_mc(p2, None) is None
    assert _get_line_mc(None, None) is None


def test_get_line_mc_vertical_returns_none():
    """Two anchors at the same time (vertical line, m=inf) -> None.

    A vertical line cannot seed a y = m*t + c regression; the helper mirrors
    ``get_line_params_time``'s inf-slope signal and drops the line.
    """
    p1 = {"time_numeric": 5, "price": 100}
    p2 = {"time_numeric": 5, "price": 200}
    assert _get_line_mc(p1, p2) is None


# ---------------------------------------------------------------------------
# _get_anchor_times
# ---------------------------------------------------------------------------
def test_get_anchor_times_collects_and_sorts_all_four():
    """A full channel (res+sup, 2 anchors each) -> sorted list of 4 timestamps.

    Input is deliberately unsorted to verify the in-place ``times.sort()``.
    """
    ch = {
        "resistance": ({"time_numeric": 10, "price": 1}, {"time_numeric": 2, "price": 1}),
        "support": ({"time_numeric": 8, "price": 1}, {"time_numeric": 4, "price": 1}),
    }
    assert _get_anchor_times(ch) == [2, 4, 8, 10]


def test_get_anchor_times_skips_none_and_partial_anchors():
    """None anchors and anchors lacking ``time_numeric`` are dropped, rest sorted."""
    ch = {
        "resistance": (None, {"time_numeric": 2, "price": 1}),
        "support": ({"price": 1}, {"time_numeric": 5, "price": 1}),  # first lacks time_numeric
    }
    assert _get_anchor_times(ch) == [2, 5]


def test_get_anchor_times_all_none_returns_empty():
    """A channel with no valid anchors -> empty list (nesting falls back)."""
    ch = {"resistance": (None, None), "support": (None, None)}
    assert _get_anchor_times(ch) == []


def test_get_anchor_times_empty_channel_sides():
    """A freshly-seeded channel ``{(None,None),(None,None)}`` -> [] (no crash)."""
    # Mirrors the ``ch = {'resistance': (None, None), 'support': (None, None)}``
    # seed in ``_fit_scale`` before ``find_envelope_line`` populates it.
    ch = {"resistance": (None, None), "support": (None, None)}
    assert _get_anchor_times(ch) == []
