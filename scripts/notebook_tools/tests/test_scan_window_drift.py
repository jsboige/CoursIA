"""Tests pour scripts/notebook_tools/scan_window_drift.py -- detecteur advisory
de derive de fenetre QC (forme de la borne, D2 #9768/#10230).

Couvre les 4 verdicts (DRIFT/PINNED/INDÉTERMINÉ/N-A), les 4 formes de drift
(T=timedelta, L=lookback, N=now, S=set_start_sans_end), les discriminations
anti-FP (now() dans un print n'est pas une borne ; self.History d'un backtest
n'est pas du drift ; variable litterale resolue -> PINNED), et le CLI
(advisory exit 0 ; --check exit 1 sur DRIFT ; --json shape).

Fragments synthetiques (pas de couplage a un vrai notebook) pour l'isolation.
See #10230, #9772, #9768.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_window_drift import classify_notebook  # noqa: E402


def _nb(cells: list[tuple[str, str]]) -> dict:
    """Construit un notebook minimal depuis une liste (cell_type, source)."""
    return {
        "cells": [
            {"cell_type": ct, "source": src.splitlines(keepends=True), "metadata": {},
             "outputs": [] if ct == "code" else None}
            for ct, src in cells
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }


def _write(tmp_path: Path, cells: list[tuple[str, str]]) -> Path:
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(_nb(cells)), encoding="utf-8")
    return p


# --- N-A : aucune API QC -------------------------------------------------

def test_na_no_qc_api(tmp_path):
    """Un notebook sans aucune API QC -> N-A (set_end_date non-applicable)."""
    p = _write(tmp_path, [
        ("markdown", "# Recherche ML"),
        ("code", "import pandas as pd\ndf = pd.read_parquet('data.pq')\nprint(df.shape)"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "N-A"
    assert r["forms"] == []


# --- DRIFT forme T : timedelta ------------------------------------------

def test_drift_form_timedelta(tmp_path):
    """qb.History(sym, timedelta(252*12), ...) -> DRIFT forme T (#10230 c3)."""
    p = _write(tmp_path, [
        ("code", "qb = QuantBook()\nsym = qb.add_equity('SPY').symbol"),
        ("code", "h = qb.History(sym, timedelta(252 * 12), Resolution.Daily)"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "DRIFT"
    assert "T" in r["forms"]


# --- DRIFT forme L : lookback entier ------------------------------------

def test_drift_form_lookback(tmp_path):
    """qb.history(syms, 2520, Resolution) -> DRIFT forme L (N barres depuis now)."""
    p = _write(tmp_path, [
        ("code", "qb = QuantBook()\nsymbols = {'SPY': qb.add_equity('SPY').symbol}"),
        ("code", "history = qb.history(list(symbols.values()), 2520, Resolution.DAILY)"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "DRIFT"
    assert "L" in r["forms"]


# --- DRIFT forme N : now() borne ----------------------------------------

def test_drift_form_now_assignment(tmp_path):
    """end_date = datetime.now() -> DRIFT forme N (borne ancrée sur l'horloge)."""
    p = _write(tmp_path, [
        ("code", "qb = QuantBook()\nstart = datetime(2020, 1, 1)"),
        ("code", "end_date = datetime.now()\nh = qb.History('SPY', start, end_date)"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "DRIFT"
    assert "N" in r["forms"]


def test_now_in_print_is_not_a_bound(tmp_path):
    """now() dans un en-tete de log print() n'est PAS une borne -> pas forme N.

    FP guard (QC-Py-40/41, #10230) : la forme N discrimine par CONTEXTE
    (affectation d'une borne ou arg de history), pas par le pattern now() seul.
    """
    p = _write(tmp_path, [
        ("code", "qb = QuantBook()\nprint(f\"Run - {datetime.now().strftime('%Y-%m-%d')}\")"),
        ("code", "h = qb.History('SPY', datetime(2020,1,1), datetime(2024,1,1))"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "PINNED"
    assert "N" not in r["forms"]


# --- DRIFT forme S : set_start_date sans set_end_date -------------------

def test_drift_form_set_start_no_end_qcalgorithm(tmp_path):
    """self.set_start_date(...) sans set_end_date dans un QCAlgorithm -> DRIFT S.

    Cas QC-Py-Cloud-03 (#10230) : un backtest d'algorithme à fin ouverte dérive.
    Forme S évaluée sur TOUT le code, QCAlgorithm inclus.
    """
    p = _write(tmp_path, [
        ("code", "class Algo(QCAlgorithm):\n    def initialize(self):\n        self.set_start_date(2015, 1, 1)\n        self.add_equity('SPY')"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "DRIFT"
    assert "S" in r["forms"]


# --- PINNED --------------------------------------------------------------

def test_pinned_set_end_date(tmp_path):
    """set_end_date présent + bornes litterales (pas de forme de drift) -> PINNED.

    NB : set_end_date NE neutralise PAS un appel ``history(..., timedelta(...))``
    qui dérive par ailleurs (forme T dominante). Ce test isole le pin pur.
    """
    p = _write(tmp_path, [
        ("code", "qb = QuantBook()\nqb.set_start_date(2020, 1, 1)\nqb.set_end_date(2024, 1, 1)"),
        ("code", "h = qb.History('SPY', datetime(2020, 1, 1), datetime(2024, 1, 1), Resolution.Daily)"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "PINNED"


def test_set_end_date_does_not_neutralize_timedelta(tmp_path):
    """Falsifiabilité : set_end_date présent MAIS history(timedelta) -> DRIFT.

    La forme T dérive indépendamment de set_end_date : il faut passer start/end
    explicites à history(), pas compter sur set_end_date pour figer (#10230).
    """
    p = _write(tmp_path, [
        ("code", "qb = QuantBook()\nqb.set_start_date(2020, 1, 1)\nqb.set_end_date(2024, 1, 1)"),
        ("code", "h = qb.History('SPY', timedelta(365), Resolution.Daily)"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "DRIFT"
    assert "T" in r["forms"]


def test_pinned_literal_date_args(tmp_path):
    """qb.History(sym, datetime(2015,1,1), datetime(2020,1,1)) -> PINNED
    (bornes litterales, fenetre figee meme sans set_end_date)."""
    p = _write(tmp_path, [
        ("code", "qb = QuantBook()"),
        ("code", "h = qb.History('SPY', datetime(2015, 1, 1), datetime(2020, 1, 1), Resolution.Daily)"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "PINNED"


def test_pinned_literal_date_variables(tmp_path):
    """start=datetime(2015,1,1); end=date(2020,1,1); qb.History(sym,start,end)
    -> PINNED par resolution de variable-borne litterale (Crypto-MultiCanal)."""
    p = _write(tmp_path, [
        ("code", "qb = QuantBook()\nstart_date = datetime(2022, 1, 1)\nend_date = datetime(2025, 4, 21)"),
        ("code", "h = qb.History('BTC', start_date, end_date, Resolution.Hour)"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "PINNED"


# --- Falsifiabilité : self.History d'un backtest n'est PAS du drift ------

def test_self_history_in_qcalgorithm_not_drift(tmp_path):
    """self.History(sym, N) dans un QCAlgorithm s'ancre sur self.Time (backtest
    loop) -> lookback glissant INTENDU, pas du drift. Receiver 'self' exclu."""
    p = _write(tmp_path, [
        ("code", "class Algo(QCAlgorithm):\n    def initialize(self):\n        self.set_start_date(2015, 1, 1)\n        self.set_end_date(2024, 1, 1)\n    def on_data(self, data):\n        h = self.History('SPY', 252, Resolution.Daily)"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "PINNED"
    assert "L" not in r["forms"]


# --- INDÉTERMINÉ ---------------------------------------------------------

def test_indetermine_qc_api_no_form(tmp_path):
    """API QC présente mais aucune forme résolue et pas de set_end -> INDÉTERMINÉ."""
    p = _write(tmp_path, [
        ("code", "qb = QuantBook()"),
        ("code", "# configure les données plus loin, fenêtre non résolue statiquement\npass"),
    ])
    r = classify_notebook(p)
    assert r["verdict"] == "INDÉTERMINÉ"


# --- CLI -----------------------------------------------------------------

def test_cli_advisory_exit_zero(tmp_path):
    """Sans --check, le detecteur advisory exit 0 meme avec du drift."""
    import subprocess
    nb = _write(tmp_path, [("code", "qb = QuantBook()\nh = qb.History('SPY', timedelta(365), Resolution.Daily)")])
    r = subprocess.run(
        [sys.executable, str(Path(__file__).resolve().parent.parent / "scan_window_drift.py"),
         str(nb)],
        capture_output=True, text=True,
    )
    assert r.returncode == 0


def test_cli_check_exit_one_on_drift(tmp_path):
    """--check exit 1 si au moins un DRIFT (CI-ready)."""
    import subprocess
    nb = _write(tmp_path, [("code", "qb = QuantBook()\nh = qb.History('SPY', timedelta(365), Resolution.Daily)")])
    r = subprocess.run(
        [sys.executable, str(Path(__file__).resolve().parent.parent / "scan_window_drift.py"),
         str(nb), "--check", "--json"],
        capture_output=True, text=True,
    )
    assert r.returncode == 1
    payload = json.loads(r.stdout)
    assert payload["records"][0]["verdict"] == "DRIFT"
