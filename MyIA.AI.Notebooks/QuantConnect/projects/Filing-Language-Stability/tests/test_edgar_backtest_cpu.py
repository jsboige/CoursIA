"""Tests CPU du producteur historique et du contrat du backtest EDGAR-2."""

from __future__ import annotations

import csv
import json
import sys
from datetime import date
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
PROJECT_ROOT = HERE.parent
sys.path.insert(0, str(PROJECT_ROOT))

import edgar_signal as es  # noqa: E402


CIK = 9999999
TICKER = "TEST"
FILINGS = [
    {
        "accession": f"0000999999-{year % 100:02d}-000001",
        "primary_document": f"annual-{year}.htm",
        "filing_date": f"{year}-10-31",
        "report_date": f"{year}-09-30",
        "acceptance": f"{year}-10-31T21:15:00.000Z",
    }
    for year in range(2020, 2026)
]


def _columnar(rows: list[dict]) -> dict:
    return {
        "form": ["10-K"] * len(rows),
        "accessionNumber": [row["accession"] for row in rows],
        "primaryDocument": [row["primary_document"] for row in rows],
        "filingDate": [row["filing_date"] for row in rows],
        "reportDate": [row["report_date"] for row in rows],
        "acceptanceDateTime": [row["acceptance"] for row in rows],
    }


def _html(year: int) -> bytes:
    section = (
        "Our operations depend on resilient cloud services and stable suppliers. "
        f"The annual risk vocabulary marker is year {year}. "
        "Cybersecurity, competition, litigation, currency and rates may affect us. "
    ) * 90
    return (
        "<html><body>Item 1A. Risk Factors "
        + section
        + " Item 1B. Unresolved Staff Comments</body></html>"
    ).encode("utf-8")


@pytest.fixture()
def historical_sec(monkeypatch):
    recent = FILINGS[3:]
    archived = FILINGS[:4]  # 2023 duplicate verifies accession deduplication.
    root = {
        "filings": {
            "recent": _columnar(recent),
            "files": [{"name": "CIK0000999999-submissions-001.json"}],
        }
    }
    store = {
        es._SUBMISSIONS_URL.format(cik=CIK): json.dumps(root).encode("utf-8"),
        es._SUBMISSIONS_ARCHIVE_URL.format(
            name="CIK0000999999-submissions-001.json"
        ): json.dumps(_columnar(archived)).encode("utf-8"),
    }
    for row in FILINGS:
        store[
            es._ARCHIVES_URL.format(
                cik=CIK,
                acc=row["accession"].replace("-", ""),
                doc=row["primary_document"],
            )
        ] = _html(int(row["filing_date"][:4]))

    calls = []

    def fake_get(url: str, **_kwargs) -> bytes:
        calls.append(url)
        return store[url]

    monkeypatch.setattr(es, "_http_get", fake_get)
    return calls


def test_list_history_lit_recent_et_archive_flat(historical_sec, tmp_path):
    rows = es.list_10k_history(CIK, cache_dir=tmp_path)

    assert len(rows) == 6
    assert len({row.accession for row in rows}) == 6
    assert [row.filing_date.year for row in rows] == [2025, 2024, 2023, 2022, 2021, 2020]
    assert es._SUBMISSIONS_ARCHIVE_URL.format(
        name="CIK0000999999-submissions-001.json"
    ) in historical_sec


def test_history_since_conserve_une_ancre(historical_sec, tmp_path):
    rows = es.list_10k_history(CIK, since=date(2023, 1, 1), cache_dir=tmp_path)

    assert [row.filing_date.year for row in rows] == [2025, 2024, 2023, 2022]


def test_build_history_produit_toutes_les_paires_adjacentes(
    historical_sec, tmp_path
):
    pairs = es.build_history(
        TICKER, CIK, since=date(2021, 1, 1), cache_dir=tmp_path
    )

    assert len(pairs) == 5
    assert [(pair.newer.filing_date.year, pair.older.filing_date.year) for pair in pairs] == [
        (2025, 2024),
        (2024, 2023),
        (2023, 2022),
        (2022, 2021),
        (2021, 2020),
    ]
    assert all(pair.status == "item_1a" for pair in pairs)
    assert all(pair.similarity is not None for pair in pairs)
    assert all(pair.available_at >= pair.newer.acceptance_timestamp for pair in pairs)

    document_calls = [url for url in historical_sec if "/Archives/" in url]
    assert len(document_calls) == 6, "chaque 10-K doit etre telecharge une seule fois"


def test_history_csv_est_deterministe_et_point_in_time(historical_sec, tmp_path):
    pairs = es.build_history(TICKER, CIK, cache_dir=tmp_path)
    first = tmp_path / "first.csv"
    second = tmp_path / "second.csv"

    es.write_csv(pairs, first)
    es.write_csv(pairs, second)

    assert first.read_bytes() == second.read_bytes()
    with first.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
    assert tuple(reader.fieldnames or ()) == es.CSV_COLUMNS
    assert len(rows) == 5
    assert rows[0]["available_at"] == "2025-10-31T21:15:00"
    assert rows[0]["similarity"] not in ("", "0", "None")


def test_cloud_module_filtre_les_echecs_et_reste_deterministe(
    historical_sec, tmp_path
):
    pairs = es.build_history(TICKER, CIK, cache_dir=tmp_path)
    pairs[0].similarity = None
    pairs[0].status = "failed"
    first = tmp_path / "first.py"
    second = tmp_path / "second.py"

    assert es.write_cloud_module(reversed(pairs), first) == 4
    assert es.write_cloud_module(pairs[1:], second) == 4

    assert first.read_bytes() == second.read_bytes()
    text = first.read_text(encoding="utf-8")
    assert "EDGAR_SIGNALS = [" in text
    assert "None" not in text
    assert "Risk Factors" not in text


def test_since_apres_dernier_filing_ne_fabrique_aucune_paire(
    historical_sec, tmp_path
):
    pairs = es.build_history(
        TICKER, CIK, since=date(2026, 1, 1), cache_dir=tmp_path
    )
    assert pairs == []
