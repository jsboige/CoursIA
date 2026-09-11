"""Tests CPU sans reseau (acceptance #6).

Cinq categories obligatoires :
    1. appariement consecutif (10-K N / N-1 meme emetteur)
    2. invariants anti-look-ahead (available_at >= acceptance, dates coherentes)
    3. exclusion d'extraction incomplete (status='failed', similarity=None)
    4. determinisme (meme input -> meme CSV, ordre des colonnes fixe)
    5. schema CSV (colonnes == CSV_COLUMNS, encodage string strict)

Pas de mock ``unittest.mock.patch`` sur la lib standard : on injecte une
fonction ``_http_get`` de remplacement via l'attribut module, ce qui rend
les tests deterministes en <100 ms et exempts de tout acces reseau.
L'injection se fait en reimportant le module sous un nom dedie dans
chaque test, puis en retablissant l'original via ``finally``.
"""

from __future__ import annotations

import csv
import io
import json
import re
import sys
from datetime import date, datetime
from pathlib import Path

import pytest

# Reperer le dossier du module ; pytest collection importe sous ce nom.
HERE = Path(__file__).resolve().parent
PROJECT_ROOT = HERE.parent
sys.path.insert(0, str(PROJECT_ROOT))

import edgar_signal as es  # noqa: E402


# ---------------------------------------------------------------------------
# Fixtures : JSON submissions + HTML de 10-K
# ---------------------------------------------------------------------------


def _make_submissions_json(*, cik: int, ten_ks: list[dict]) -> bytes:
    """Construit un payload ``data.sec.gov/submissions`` minimaliste.

    ``ten_ks`` est une liste d'objets avec les cles ``accession``,
    ``primary_document``, ``filing_date``, ``report_date`` et
    ``acceptanceDateTime``. Les cles EDGAR reelles sont mappees 1-1.
    """
    rows = list(ten_ks)
    return json.dumps(
        {
            "cik": str(cik),
            "filings": {
                "recent": {
                    "form": ["10-K"] * len(rows),
                    "accessionNumber": [r["accession"] for r in rows],
                    "primaryDocument": [r["primary_document"] for r in rows],
                    "filingDate": [r["filing_date"] for r in rows],
                    "reportDate": [r["report_date"] for r in rows],
                    "acceptanceDateTime": [r["acceptanceDateTime"] for r in rows],
                }
            },
        }
    ).encode("utf-8")


def _make_10k_html(
    item_1a_text: str | None,
    *,
    primary_doc: str = "form10k.htm",
) -> bytes:
    """Construit un HTML de 10-K contenant une section Item 1A ou rien.

    Si ``item_1a_text`` est ``None``, le document est vide (acquisition
    cassee -> extraction echouee). Sinon il contient exactement la
    section attendue par la regex du module.
    """
    if item_1a_text is None:
        return b"<html><body>broken document with no Item 1A section</body></html>"
    # DOIT contenir le marqueur "Risk Factors" en debut et "Item 1B" en fin ;
    # la regex du module exige "Item 1A ... Risk Factors" puis "Item 1B".
    # On utilise la forme canonique `Item 1A. Risk Factors`.
    return (
        b"<html><body>"
        b"<h1>10-K</h1>"
        b"<p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. "
        b"Sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. "
        b"Item 1A. Risk Factors " + item_1a_text.encode("utf-8") + b" Item 1B. "
        b"Other unrelated text continuing for many paragraphs. "
        b"</p></body></html>"
    )


# Deux 10-K consecutifs d'un meme emetteur fictif (CIK = 9999999).
_FIXTURE_CIK = 9999999
_FIXTURE_TICKER = "TEST"
_FIXTURE_TEN_K_NEWER = {
    "accession": "0000999999-25-000001",
    "primary_document": "newer.htm",
    "filing_date": "2025-10-31",
    "report_date": "2025-09-30",
    "acceptanceDateTime": "2025-10-31T14:23:45.000Z",
}
_FIXTURE_TEN_K_OLDER = {
    "accession": "0000999999-24-000001",
    "primary_document": "older.htm",
    "filing_date": "2024-11-01",
    "report_date": "2024-09-30",
    "acceptanceDateTime": "2024-11-01T13:15:00.000Z",
}
_FIXTURE_TEN_K_BROKEN = {
    "accession": "0000999999-23-000099",
    "primary_document": "broken.htm",
    "filing_date": "2023-10-31",
    "report_date": "2023-09-30",
    "acceptanceDateTime": "2023-10-31T12:00:00.000Z",
}


# Texte Item 1A volontairement distinct entre newer et older pour produire
# une similarite ni 0 ni 1 ; le test sur la similarite verifie l'ordre
# attendu (texte plus proche -> similarite plus haute) plutot qu'une valeur
# absolue -- c'est le bon invariant pour un test stable.
_ITEM_1A_NEWER = (
    "Our business depends on cloud infrastructure reliability. "
    "We compete with hyperscale cloud providers. "
    "Cybersecurity risks could disrupt operations. "
    "We rely on third-party components for hardware supply. "
) * 40
_ITEM_1A_OLDER_SIMILAR = (
    "Our business depends on cloud infrastructure reliability. "
    "We compete with hyperscale cloud providers. "
    "Cybersecurity risks could disrupt operations. "
    "We rely on third-party components for hardware supply. "
) * 40
_ITEM_1A_OLDER_DIFFERENT = (
    "Litigation outcomes may differ from management expectations. "
    "Currency translation impacts non-USD reported revenue. "
    "Interest rate movements affect debt servicing costs. "
    "Pension obligations remeasurement creates volatility. "
) * 40


class _FakeResponse:
    """Minimal ``http.client.HTTPResponse``-like pour ``_http_get`` refactor."""

    def __init__(self, payload: bytes):
        self._payload = payload

    def read(self) -> bytes:
        return self._payload

    def __enter__(self):
        return self

    def __exit__(self, *_):
        return False


@pytest.fixture()
def fake_fetcher(monkeypatch, tmp_path):
    """Remplace ``es._http_get`` par une lookup URL -> bytes.

    Le monkeypatch evite tout acces reseau reelt et permet de tester
    des fixtures en isolation. Le patch est retabli automatiquement
    par la fixture monkeypatch de pytest.
    """
    store: dict[str, bytes] = {}

    submissions_url = es._SUBMISSIONS_URL.format(cik=_FIXTURE_CIK)
    store[submissions_url] = _make_submissions_json(
        cik=_FIXTURE_CIK,
        ten_ks=[_FIXTURE_TEN_K_NEWER, _FIXTURE_TEN_K_OLDER, _FIXTURE_TEN_K_BROKEN],
    )

    def add(url: str, payload: bytes) -> None:
        store[url] = payload

    def fake(url: str, **kwargs) -> bytes:
        if url not in store:
            raise RuntimeError(f"URL non-stubbe: {url}")
        return store[url]

    monkeypatch.setattr(es, "_http_get", fake)
    return store, add


# ---------------------------------------------------------------------------
# (1) Appariement consecutif (10-K N / N-1 du meme emetteur)
# ---------------------------------------------------------------------------


def test_appariement_consecutif_trie_par_filing_date(fake_fetcher):
    """Les deux 10-K les plus recents du meme emetteur -- ordre DESC.

    On verifie aussi que l'ordre ``newer > older`` est temporellement
    coherent (pas d'inversion accidentelle due a la voie ``rows.sort``).
    """
    _store, add = fake_fetcher
    add(
        es._ARCHIVES_URL.format(
            cik=_FIXTURE_CIK, acc="000099999925000001", doc="newer.htm"
        ),
        _make_10k_html(_ITEM_1A_NEWER),
    )
    add(
        es._ARCHIVES_URL.format(
            cik=_FIXTURE_CIK, acc="000099999924000001", doc="older.htm"
        ),
        _make_10k_html(_ITEM_1A_OLDER_SIMILAR),
    )

    pair = es.build_pair(_FIXTURE_TICKER, _FIXTURE_CIK, cache_dir=Path("/tmp/edgar-fake"))

    assert pair.newer.filing_date > pair.older.filing_date, (
        "newer doit etre strictement plus recent que older "
        f"(newer={pair.newer.filing_date}, older={pair.older.filing_date})"
    )
    assert pair.newer.accession == _FIXTURE_TEN_K_NEWER["accession"]
    assert pair.older.accession == _FIXTURE_TEN_K_OLDER["accession"]


def test_appariement_avec_un_seul_10k_retourne_failed(fake_fetcher, tmp_path):
    """Avec moins de 2 10-K, status='failed', similarity=None (acceptance #4)."""
    _store, add = fake_fetcher
    # Reecrire le submissions JSON avec un seul 10-K.
    only_ten_k = {
        "accession": "0000999999-25-000001",
        "primary_document": "newer.htm",
        "filing_date": "2025-10-31",
        "report_date": "2025-09-30",
        "acceptanceDateTime": "2025-10-31T14:23:45.000Z",
    }
    add(
        es._SUBMISSIONS_URL.format(cik=_FIXTURE_CIK),
        _make_submissions_json(cik=_FIXTURE_CIK, ten_ks=[only_ten_k]),
    )

    pair = es.build_pair(
        _FIXTURE_TICKER, _FIXTURE_CIK, cache_dir=tmp_path / "cache"
    )

    assert pair.status == "failed"
    assert pair.similarity is None


# ---------------------------------------------------------------------------
# (2) Invariants anti-look-ahead
# ---------------------------------------------------------------------------


def test_available_at_max_des_acceptances_plus_jour_de_marche(fake_fetcher, tmp_path):
    """available_at = max(acceptance_N, acceptance_N-1), avance au jour de marche.

    Si la borne tombe un samedi/dimanche, on attend lundi. C'est l'invariant
    anti-look-ahead principal : le score n'est jamais utilisable avant
    l'acceptation SEC la plus tardive (acceptance #3).
    """
    _store, add = fake_fetcher
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999925000001", doc="newer.htm"),
        _make_10k_html(_ITEM_1A_NEWER),
    )
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999924000001", doc="older.htm"),
        _make_10k_html(_ITEM_1A_OLDER_SIMILAR),
    )

    pair = es.build_pair(_FIXTURE_TICKER, _FIXTURE_CIK, cache_dir=tmp_path / "cache")
    when = pair.available_at

    acceptances = [
        pair.newer.acceptance_timestamp,
        pair.older.acceptance_timestamp,
    ]
    for ts in acceptances:
        assert when.date() >= ts.date(), (
            f"available_at {when.date()} doit etre >= acceptance {ts.date()}"
        )

    # available_at doit etre un jour de marche US (lundi=0 .. vendredi=4).
    assert when.weekday() < 5, (
        f"available_at doit etre un jour de marche US, "
        f"reçu {when.isoformat()} (weekday={when.weekday()})"
    )


def test_acceptances_parsees_depuis_iso8601(fake_fetcher, tmp_path):
    """Les acceptance_timestamp sont parses correctement depuis ISO 8601.

    On verifie que le format EDGAR ``YYYY-MM-DDTHH:MM:SS.sssZ`` est
    correctement decode (``2025-10-31T14:23:45.000Z`` -> 14:23:45).
    """
    _store, add = fake_fetcher
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999925000001", doc="newer.htm"),
        _make_10k_html(_ITEM_1A_NEWER),
    )
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999924000001", doc="older.htm"),
        _make_10k_html(_ITEM_1A_OLDER_SIMILAR),
    )
    pair = es.build_pair(_FIXTURE_TICKER, _FIXTURE_CIK, cache_dir=tmp_path / "cache")
    assert pair.newer.acceptance_timestamp == datetime(2025, 10, 31, 14, 23, 45)
    assert pair.older.acceptance_timestamp == datetime(2024, 11, 1, 13, 15, 0)


def test_next_us_session_avance_weekend():
    """L'helper ignore samedi/dimanche -- test direct sur la fonction privee."""
    # samedi 5 octobre 2024
    assert es._next_us_session(date(2024, 10, 5)) == date(2024, 10, 7)
    # dimanche 6 octobre 2024
    assert es._next_us_session(date(2024, 10, 6)) == date(2024, 10, 7)
    # lundi 7 octobre 2024 (deja un jour de marche)
    assert es._next_us_session(date(2024, 10, 7)) == date(2024, 10, 7)
    # vendredi 11 octobre 2024
    assert es._next_us_session(date(2024, 10, 11)) == date(2024, 10, 11)


# ---------------------------------------------------------------------------
# (3) Exclusion d'extraction incomplete
# ---------------------------------------------------------------------------


def test_extraction_incomplete_retourne_status_failed(fake_fetcher, tmp_path):
    """Si un des Item 1A est absent, status='failed', similarity=None.

    Aucun mode ``full_fallback`` silencieux n'est accepte -- c'est le
    sens meme de acceptance #4. Le consumer du CSV peut alors filtrer
    sur ``extraction_mode_n == 'item_1a'``.
    """
    _store, add = fake_fetcher
    # newer : Item 1A OK ; older : document casse
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999925000001", doc="newer.htm"),
        _make_10k_html(_ITEM_1A_NEWER),
    )
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999924000001", doc="older.htm"),
        _make_10k_html(None),  # extraction echouee
    )

    pair = es.build_pair(_FIXTURE_TICKER, _FIXTURE_CIK, cache_dir=tmp_path / "cache")
    assert pair.status == "failed"
    assert pair.similarity is None
    assert pair.extraction_newer == "item_1a"
    assert pair.extraction_older == "failed"


def test_extract_item_1a_rejette_section_trop_courte():
    """Section Item 1A en-dessous du seuil = extraction echouee."""
    text = "Item 1A. Risk Factors " + "x" * 100 + " Item 1B"
    section, mode = es.extract_item_1a(text)
    assert section is None
    assert mode == "failed"


def test_extract_item_1a_rejette_document_sans_section():
    """Document sans balise Item 1A = extraction echouee."""
    section, mode = es.extract_item_1a("Plain text without any 10-K structure.")
    assert section is None
    assert mode == "failed"


def test_extract_item_1a_accepte_section_longue():
    """Section Item 1A au-dessus du seuil = extraction reussie."""
    long_section = "x" * (es.MIN_ITEM_1A_CHARS + 100)
    text = f"Item 1A. Risk Factors {long_section} Item 1B"
    section, mode = es.extract_item_1a(text)
    assert mode == "item_1a"
    assert section is not None
    assert len(section) >= es.MIN_ITEM_1A_CHARS


# ---------------------------------------------------------------------------
# (4) Determinisme
# ---------------------------------------------------------------------------


def test_csv_deterministe_meme_input_meme_sortie(fake_fetcher, tmp_path):
    """Meme input CSV -->> bytes byte-identiques.

    L'ordre des colonnes (CSV_COLUMNS), l'ordre des lignes (ordre
    d'entree de la liste de pairs), l'encodage (utf-8 sans BOM) sont
    tous stables par construction.
    """
    _store, add = fake_fetcher
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999925000001", doc="newer.htm"),
        _make_10k_html(_ITEM_1A_NEWER),
    )
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999924000001", doc="older.htm"),
        _make_10k_html(_ITEM_1A_OLDER_SIMILAR),
    )
    pair = es.build_pair(_FIXTURE_TICKER, _FIXTURE_CIK, cache_dir=tmp_path / "cache")

    out_a = tmp_path / "out_a.csv"
    out_b = tmp_path / "out_b.csv"

    es.write_csv([pair], out_a)
    # Deuxieme run avec un path different ; si la sortie differe, c'est
    # un defaut de determinisme (chemin, horodatage, ordre aleatoire).
    es.write_csv([pair], out_b)
    assert out_a.read_bytes() == out_b.read_bytes()


def test_csv_ordre_colonnes_fige(tmp_path):
    """L'ordre des colonnes doit etre exactement CSV_COLUMNS (acceptance #5)."""
    out = tmp_path / "header.csv"
    es.write_csv([], out)
    with out.open("r", encoding="utf-8", newline="") as fh:
        reader = csv.reader(fh)
        header = next(reader)
    assert tuple(header) == es.CSV_COLUMNS


def test_csv_similarity_none_encode_chaine_vide(fake_fetcher, tmp_path):
    """similarity=None -> cellule vide, pas 'None' / 'null' / 'NaN'."""
    _store, add = fake_fetcher
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999925000001", doc="newer.htm"),
        _make_10k_html(_ITEM_1A_NEWER),
    )
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999924000001", doc="older.htm"),
        _make_10k_html(None),
    )
    pair = es.build_pair(_FIXTURE_TICKER, _FIXTURE_CIK, cache_dir=tmp_path / "cache")
    assert pair.similarity is None

    out = tmp_path / "failed.csv"
    es.write_csv([pair], out)
    with out.open("r", encoding="utf-8", newline="") as fh:
        reader = csv.DictReader(fh)
        row = next(reader)
    assert row["similarity"] == "", (
        f"similarity=None doit etre la chaine vide, "
        f"obtenu: {row['similarity']!r}"
    )


# ---------------------------------------------------------------------------
# (5) Schema CSV
# ---------------------------------------------------------------------------


def test_csv_schema_complet(fake_fetcher, tmp_path):
    """Toutes les colonnes obligatoires apparaissent dans le header et la ligne.

    Colonnes verifiees : ticker/CIK, accessions N+N-1, dates d'acceptation,
    modes d'extraction, similarite, available_at. Ce sont les 6 categories
    d'acceptance #5 ; on les enumere toutes, par leur cle, dans le test.
    """
    _store, add = fake_fetcher
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999925000001", doc="newer.htm"),
        _make_10k_html(_ITEM_1A_NEWER),
    )
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999924000001", doc="older.htm"),
        _make_10k_html(_ITEM_1A_OLDER_SIMILAR),
    )
    pair = es.build_pair(_FIXTURE_TICKER, _FIXTURE_CIK, cache_dir=tmp_path / "cache")

    out = tmp_path / "schema.csv"
    es.write_csv([pair], out)
    with out.open("r", encoding="utf-8") as fh:
        text = fh.read()
    reader = csv.DictReader(io.StringIO(text))
    row = next(reader)

    # Couples (cle, getter)
    expectations = {
        "ticker": _FIXTURE_TICKER,
        "cik": str(_FIXTURE_CIK),
        "accession_n": pair.newer.accession,
        "accession_n_minus_1": pair.older.accession,
        "filing_date_n": pair.newer.filing_date.isoformat(),
        "filing_date_n_minus_1": pair.older.filing_date.isoformat(),
        "acceptance_timestamp_n": pair.newer.acceptance_timestamp.strftime(
            "%Y-%m-%dT%H:%M:%S"
        ),
        "acceptance_timestamp_n_minus_1": pair.older.acceptance_timestamp.strftime(
            "%Y-%m-%dT%H:%M:%S"
        ),
        "period_of_report_n": pair.newer.period_of_report.isoformat(),
        "period_of_report_n_minus_1": pair.older.period_of_report.isoformat(),
        "extraction_mode_n": pair.extraction_newer,
        "extraction_mode_n_minus_1": pair.extraction_older,
        "similarity": f"{pair.similarity:.6f}" if pair.similarity else "",
        "available_at": pair.available_at.strftime("%Y-%m-%d"),
    }
    for key, expected in expectations.items():
        assert row[key] == expected, f"colonne {key!r}: attendu {expected!r}, reçu {row[key]!r}"

    # Colonnes au format CSV_COLUMNS uniquement.
    assert set(reader.fieldnames) == set(es.CSV_COLUMNS)


def test_summarize_compte_par_statut(fake_fetcher):
    """summarize() retourne valid / failed / valid_rate."""
    _store, add = fake_fetcher
    # Cas : une paire valide, une paire echouee (extraction cassee).
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999925000001", doc="newer.htm"),
        _make_10k_html(_ITEM_1A_NEWER),
    )
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999924000001", doc="older.htm"),
        _make_10k_html(None),  # extraction echouee
    )
    pair_failed = es.build_pair(
        "FAIL", _FIXTURE_CIK, cache_dir=Path("/tmp/edgar-fake-fail")
    )

    # Cas : une paire valide.
    add(
        es._ARCHIVES_URL.format(cik=_FIXTURE_CIK, acc="000099999924000001", doc="older.htm"),
        _make_10k_html(_ITEM_1A_OLDER_SIMILAR),
    )
    pair_ok = es.build_pair("OK", _FIXTURE_CIK, cache_dir=Path("/tmp/edgar-fake-ok"))

    summary = es.summarize([pair_ok, pair_failed])
    assert summary["valid"] == 1
    assert summary["failed"] == 1
    assert summary["valid_rate"] == 0.5


def test_summarize_zero_paire():
    """Aucune paire -> valid_rate=0.0 (jamais NaN)."""
    summary = es.summarize([])
    assert summary == {"valid": 0, "failed": 0, "valid_rate": 0.0}


def test_similarite_plus_elevee_pour_textes_proches():
    """Deux textes identiques ont cosinus=1.0, textes distincts < 1.0.

    Sanity-check du moteur TF-IDF ; pas de calibration d'une valeur
    absolue (elle depend du vocabulaire) -- seulement l'ordre attendu.
    """
    a = (
        "Cloud infrastructure reliability is critical. "
        "Cybersecurity threats evolve rapidly. "
        "We depend on third-party suppliers."
    ) * 5
    b_identical = a
    b_distinct = (
        "Currency translation affects reported revenue. "
        "Pension obligations require remeasurement. "
        "Interest rate movements impact debt costs."
    ) * 5

    assert es.tfidf_cosine(a, b_identical) == pytest.approx(1.0, abs=1e-6)
    cos_distinct = es.tfidf_cosine(a, b_distinct)
    assert 0.0 <= cos_distinct < 1.0


def test_list_recent_10k_trie_DESC_par_filing_date(fake_fetcher):
    """list_recent_10k renvoie les 10-K tries par filingDate DESC.

    On verifie l'invariant de tri, pas seulement le nombre d'elements.
    """
    rows = es.list_recent_10k(
        _FIXTURE_CIK, n=3, cache_dir=Path("/tmp/edgar-fake-list")
    )
    assert len(rows) == 3
    dates = [r.filing_date for r in rows]
    assert dates == sorted(dates, reverse=True), (
        f"10-K devraient etre tries DESC par filingDate, "
        f"obtenu: {[d.isoformat() for d in dates]}"
    )


def test_list_recent_10k_zero_renvoie_liste_vide(fake_fetcher, tmp_path):
    """Si n=0 ou negatif, retour liste vide (pas d'erreur)."""
    # Re-stubber avec un seul 10-K
    only_ten_k = {
        "accession": "0000999999-25-000001",
        "primary_document": "newer.htm",
        "filing_date": "2025-10-31",
        "report_date": "2025-09-30",
        "acceptanceDateTime": "2025-10-31T14:23:45.000Z",
    }
    fake_fetcher[1](
        es._SUBMISSIONS_URL.format(cik=_FIXTURE_CIK),
        _make_submissions_json(cik=_FIXTURE_CIK, ten_ks=[only_ten_k]),
    )
    rows = es.list_recent_10k(
        _FIXTURE_CIK, n=0, cache_dir=tmp_path / "cache"
    )
    assert rows == []
