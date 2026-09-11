"""Materialisation point-in-time du signal EDGAR Lazy Prices.

Substitut libre et local au dataset ``BrainCompanyFilingLanguageMetricsUniverseAll``
de QuantConnect (cf issue #15544, option 3). Pour chaque emetteur couvert, on
telecharge les deux 10-K annuels consecutifs depuis les endpoints publics
SEC EDGAR, on extrait la section ``Item 1A -- Risk Factors`` par regex, puis on
calcule la similarite TF-IDF cosinus entre annees voisines.

Le resultat est expose comme un CSV deterministe (cf schema ``CSV_COLUMNS``)
accompagne de metadonnees anti-look-ahead : la disponibilite du score est
``max(acceptance_timestamp, prochaine seance US)``, jamais la periode
comptable du filing.

Aucune performance ni equivalence exacte avec Brain n'est claimsee. Le module
est concu pour etre branche ulterieurement comme custom data dans un backtest
QC (grain de suivi hors scope de cette tranche).

Conventions :
    - Python 3.10+, PEP 8 (snake_case).
    - Pas d'import ambigu, pas de secret inline ; ``SEC_USER_AGENT`` peut etre
      surcharge par la variable d'environnement ``EDGAR_USER_AGENT``.
    - Cache HTTP local gitignore (cf ``.gitignore`` du dossier) : la cle est
      le SHA-1 de l'URL, le contenu est la reponse brute.
"""

from __future__ import annotations

import csv
import hashlib
import html as ihtml
import json
import os
import re
import time
import urllib.error
import urllib.request
from dataclasses import asdict, dataclass, field
from datetime import date, datetime, timedelta
from pathlib import Path
from typing import Iterable

try:
    from sklearn.feature_extraction.text import TfidfVectorizer
    from sklearn.metrics.pairwise import cosine_similarity
except ImportError as exc:  # pragma: no cover - dependance runtime explicite
    raise ImportError(
        "edgar_signal.py requiert scikit-learn (TF-IDF + cosine_similarity). "
        "Installez-le via `pip install scikit-learn`."
    ) from exc


# ---------------------------------------------------------------------------
# Configuration HTTP / throttling / cache
# ---------------------------------------------------------------------------

#: User-Agent identifiant le caller ; requis par la politique SEC EDGAR
#: (cf https://www.sec.gov/os/accessing-edgar-data).
#: Surchargeable par la variable d'environnement ``EDGAR_USER_AGENT`` ; le
#: fallback est explicitement non-secret : pas de cle API, juste un contact.
DEFAULT_USER_AGENT = "CoursIA Filing-Language-Stability research@example.com"

#: Duree minimale entre deux requetes sortantes. SEC tolere ~10 req/s ; on
#: reste un ordre de grandeur en dessous par courtoisie.
MIN_REQUEST_INTERVAL_SECONDS = 0.4

#: Chemin du cache HTTP local (gitignored). Les cles sont des SHA-1 d'URL.
DEFAULT_CACHE_DIR = Path(__file__).resolve().parent / "cache"

#: Fenetre Item 1A minimale pour considerer l'extraction reussie. En dessous,
#: on declare ``status='failed'`` (extraction incomplete) -- un mode
#: ``full_fallback`` silencieux est explicitement exclu : il introduirait du
#: bruit dans le signal et masquerait des extractions cassees.
MIN_ITEM_1A_CHARS = 5_000

#: Profondeur de troncature pour les textes conserves en memoire (octets).
#: Les 10-K font 1 a 8 Mo ; on garde la zone Item 1A extraite, pas le HTML
#: integral. La borne sert uniquement de filet de securite.
MAX_TEXT_CHARS = 1_000_000


# ---------------------------------------------------------------------------
# Constantes CSV
# ---------------------------------------------------------------------------

#: Ordre des colonnes du CSV produit par ``build_pair_record``. Stabilise
#: dans le temps (acceptance #5) ; tout ajout futur se fait en fin de liste,
#: jamais par reordonnancement.
CSV_COLUMNS: tuple[str, ...] = (
    "ticker",
    "cik",
    "accession_n",
    "accession_n_minus_1",
    "filing_date_n",
    "filing_date_n_minus_1",
    "acceptance_timestamp_n",
    "acceptance_timestamp_n_minus_1",
    "period_of_report_n",
    "period_of_report_n_minus_1",
    "extraction_mode_n",
    "extraction_mode_n_minus_1",
    "similarity",
    "available_at",
)


# ---------------------------------------------------------------------------
# Structures de donnees
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FilingRecord:
    """Metadonnees d'un 10-K, point-in-time safe.

    ``acceptance_timestamp`` est l'horodatage d'acceptation SEC du filing
    (disponible via ``data.sec.gov/submissions``). Le score derive de ce
    filing ne devient utilisable qu'a partir de cette date (anti-look-ahead
    -- acceptance #3) ; voir ``FilingPair.available_at``.
    """

    cik: int
    accession: str
    primary_document: str
    filing_date: date
    period_of_report: date
    acceptance_timestamp: datetime

    def accession_nodash(self) -> str:
        """Accession sans separateurs (forme d'URL d'Archives EDGAR)."""
        return self.accession.replace("-", "")


@dataclass
class FilingPair:
    """Paire (N, N-1) d'un meme emetteur, ordre temporel strict.

    ``status`` est ``"item_1a"`` (les deux extractions reussies) ou
    ``"failed"`` (au moins une extraction incomplete). Aucun autre mode
    n'est accepte -- acceptance #4. ``similarity`` n'est significative
    que pour ``status="item_1a"`` ; sinon ``None``.
    """

    ticker: str
    newer: FilingRecord
    older: FilingRecord
    extraction_newer: str  # "item_1a" | "failed"
    extraction_older: str  # "item_1a" | "failed"
    similarity: float | None
    status: str  # "item_1a" | "failed"

    @property
    def available_at(self) -> datetime:
        """Date ET heure de disponibilite du score (anti-look-ahead, acceptance #3).

        On prend le max des deux acceptance_timestamp (EDGAR publie un
        timestamp a la seconde, pas une date). On avance au prochain
        JOUR de marche US si la date tombe un week-end, mais l'heure est
        preservee : un 10-K accepte a 23h30 vendredi n'est pas
        miraculeusement disponible a minuit le meme jour, et un 10-K
        accepte a 10h01 mardi reste 10h01 mardi. Sans preservation de
        l'heure, le consommateur du CSV ne peut pas reconstruire la
        disponibilite reelle -- Hermes review PR #15584 (point 1).

        Pas de garde sur les jours feries US : un utilisateur du signal
        peut consulter le calendrier NYSE ulterieurement ; on ne pretend
        pas le faire ici.
        """
        ts = max(self.newer.acceptance_timestamp, self.older.acceptance_timestamp)
        next_date = _next_us_session(ts.date())
        return datetime.combine(next_date, ts.time())


def _next_us_session(d: date) -> date:
    """Avance ``d`` au prochain jour de marche US (lundi-vendredi)."""
    while d.weekday() >= 5:  # samedi=5, dimanche=6
        d += timedelta(days=1)
    return d


# ---------------------------------------------------------------------------
# HTTP + cache
# ---------------------------------------------------------------------------


def _user_agent() -> str:
    return os.environ.get("EDGAR_USER_AGENT", DEFAULT_USER_AGENT).strip()


def _cache_path(url: str, cache_dir: Path) -> Path:
    key = hashlib.sha1(url.encode("utf-8")).hexdigest()
    return cache_dir / f"{key}.raw"


def _http_get(
    url: str,
    *,
    cache_dir: Path,
    min_interval: float = MIN_REQUEST_INTERVAL_SECONDS,
    last_request_at: list[float] | None = None,
    max_retries: int = 3,
    timeout: float = 60.0,
) -> bytes:
    """GET un URL avec cache fichier, throttling et retries exponentiels.

    ``last_request_at`` est une liste mutable d'un float (timestamp monotone)
    partagee entre appels pour appliquer le throttling ; ce design permet
    d'injecter un faux horloge dans les tests CPU sans ``monkeypatch`` de
    ``time.sleep`` (acceptance #6 -- determinisme).
    """
    cache_dir.mkdir(parents=True, exist_ok=True)
    path = _cache_path(url, cache_dir)

    if path.exists():
        return path.read_bytes()

    if last_request_at is not None and last_request_at:
        elapsed = time.monotonic() - last_request_at[0]
        if elapsed < min_interval:
            time.sleep(min_interval - elapsed)

    req = urllib.request.Request(url, headers={"User-Agent": _user_agent()})
    attempt = 0
    backoff = 1.0
    while True:
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                payload = resp.read()
            break
        except (urllib.error.HTTPError, urllib.error.URLError):
            attempt += 1
            if attempt >= max_retries:
                raise
            time.sleep(backoff)
            backoff *= 2

    path.write_bytes(payload)
    if last_request_at is not None:
        last_request_at[0] = time.monotonic()
    return payload


# ---------------------------------------------------------------------------
# Endpoints SEC
# ---------------------------------------------------------------------------

_SUBMISSIONS_URL = "https://data.sec.gov/submissions/CIK{cik:010d}.json"
_ARCHIVES_URL = "https://www.sec.gov/Archives/edgar/data/{cik}/{acc}/{doc}"

# Regex Item 1A. Le pattern matche ``Item 1A`` (ou avec points espaces)
# suivi de ``Risk Factors`` puis d'au moins un blanc non chiffre en
# premiere position significative. Le discriminant cle est le
# lookahead negatif ``(?!\\d)`` apres les blancs : la table des
# matieres ecrit "Item 1A. Risk Factors  5  Item 1B. ..." tout sur
# une ligne (= range de pages, le premier caractere significatif
# apres ``Risk Factors`` est un chiffre), tandis que la section
# reelle debute par du texte narratif (lettre). Hermes review
# PR #15584 (point 2) -- verifier byte-level sur AAPL 2025-10-31 : la
# TOC a l'offset 19 123 ("...Item 1A. Risk Factors 5 Item 1B. ..."),
# la section reelle a l'offset 38 434 ("...Item 1A. Risk Factors The
# following summarizes..."). L'ancien pattern matchait la TOC, ce qui
# capturait 87 KB de boilerplate au lieu des Risk Factors reels.
_ITEM_1A_RE = re.compile(
    # Atomic group (?>[ \t]+) : pas de backtrack -- un TOC "Risk Factors  5" serait
    # sinon accepte par backtrack (1 espace + ' ' qui passe le (?!\d)).
    r"Item\s*1A\b[^a-zA-Z0-9]{0,40}Risk\s*Factors(?>[ \t]+)(?!\d)(.{200,}?)Item\s*1B\b",
    re.IGNORECASE | re.DOTALL,
)
_TAG_RE = re.compile(r"<[^>]+>")
#: Normalise les espaces multiples en un seul SAUF les sauts de ligne :
#: la regex d'extraction Item 1A utilise ``\n`` apres ``Risk Factors``
#: comme discriminant anti-TOC (Hermes review PR #15584 point 2), donc
#: on preserve la frontiere de paragraphe ici. ``[^\S\n]+`` = whitespace
#: qui n'est PAS un saut de ligne.
_WS_RE = re.compile(r"[^\S\n]+")


def list_recent_10k(
    cik: int, n: int = 2, *, cache_dir: Path = DEFAULT_CACHE_DIR
) -> list[FilingRecord]:
    """Renvoie les ``n`` 10-K les plus recents pour un emetteur.

    Trie par date de depot DESC ; ne garde que les 10-K ; parse le JSON
    submissions. Les ``acceptance_timestamp`` sont lus dans le bloc filing
    (EDGAR publie ``acceptanceDateTime`` au format ISO 8601). Si ce champ
    est absent pour un filing -- cas rare -- on fallback sur la fin de
    journee de la ``filingDate`` ; c'est une borne conservative qui
    preserve l'invariant "dispo apres acceptation".
    """
    if n < 1:
        return []
    url = _SUBMISSIONS_URL.format(cik=cik)
    payload = _http_get(url, cache_dir=cache_dir)
    data = json.loads(payload)
    recent = data["filings"]["recent"]
    rows: list[FilingRecord] = []
    for form, acc, doc, filed, period, accept in zip(
        recent["form"],
        recent["accessionNumber"],
        recent["primaryDocument"],
        recent["filingDate"],
        recent["reportDate"],
        recent.get("acceptanceDateTime", [None] * len(recent["form"])),
    ):
        if form != "10-K":
            continue
        rows.append(
            FilingRecord(
                cik=cik,
                accession=acc,
                primary_document=doc,
                filing_date=datetime.strptime(filed, "%Y-%m-%d").date(),
                period_of_report=datetime.strptime(period, "%Y-%m-%d").date()
                if period
                else datetime.strptime(filed, "%Y-%m-%d").date(),
                acceptance_timestamp=_parse_acceptance(accept, filed),
            )
        )
        if len(rows) == n:
            break
    # Tri defensif (l'ordre EDGAR est DESC par filingDate mais on ne
    # fait pas confiance en cas de quirk).
    rows.sort(key=lambda r: r.filing_date, reverse=True)
    return rows


def _parse_acceptance(raw: str | None, fallback_filed: str) -> datetime:
    if raw:
        # Format ISO 8601 ``2024-11-01T14:23:45.000Z``
        try:
            return datetime.strptime(raw[:19], "%Y-%m-%dT%H:%M:%S")
        except ValueError:
            pass
    # Fallback : fin de journee de la filingDate (borne conservative).
    return datetime.strptime(fallback_filed + "T23:59:59", "%Y-%m-%dT%H:%M:%S")


def fetch_10k_text(
    filing: FilingRecord, *, cache_dir: Path = DEFAULT_CACHE_DIR
) -> str:
    """Telecharge le document primaire d'un 10-K et extrait le texte."""
    url = _ARCHIVES_URL.format(
        cik=filing.cik, acc=filing.accession_nodash(), doc=filing.primary_document
    )
    raw = _http_get(url, cache_dir=cache_dir).decode("utf-8", errors="replace")
    text = _WS_RE.sub(" ", _TAG_RE.sub(" ", ihtml.unescape(raw)))
    return text[:MAX_TEXT_CHARS]


#: Causes d'echec distinctes pour ``extract_item_1a``. La valeur de
#: retour reste binaire (text | None) pour la compatibilite des
#: consommateurs existants (FilingPair.extraction_*), mais la cause
#: precise est exposee via ``extract_item_1a_failure_reason(text)`` --
#: Hermes review PR #15584 (point 3) : un echec "regex n'a pas matche"
#: n'est pas la meme cause qu'un "section trop courte" ; distinguer
#: permet d'expliquer le taux 4/5 sans ambigulte.
EXTRACTION_FAILURE_NO_MATCH = "item_1a_absent"
EXTRACTION_FAILURE_TOO_SHORT = "section_too_short"
EXTRACTION_FAILURE_REASON_LABELS = {
    EXTRACTION_FAILURE_NO_MATCH: "regex n'a matche aucune section Item 1A..1B",
    EXTRACTION_FAILURE_TOO_SHORT: "section matchee mais sous MIN_ITEM_1A_CHARS",
}


def extract_item_1a(text: str) -> tuple[str | None, str]:
    """Extrait la section Item 1A.

    Renvoie ``(text, "item_1a")`` si l'extraction depasse ``MIN_ITEM_1A_CHARS``
    caracteres, ``(None, "failed")`` sinon. Aucun mode intermediaire
    (``full_fallback``) n'est accepte -- acceptance #4.

    L'ancrage du regex en debut de ligne (``^|\\n``) exclut la TOC :
    une table des matieres contient "Item 1A ... Item 1B" tout sur une
    ligne (= range de pages), la section reelle debute en debut de
    paragraphe apres un retour a la ligne. Voir Hermes review
    PR #15584 (point 2).
    """
    m = _ITEM_1A_RE.search(text)
    if m is None:
        return None, "failed"
    section = m.group(1)
    if len(section) < MIN_ITEM_1A_CHARS:
        return None, "failed"
    return section, "item_1a"


def extract_item_1a_failure_reason(text: str) -> str:
    """Diagnostique la cause d'echec d'``extract_item_1a`` sur un texte.

    Renvoie :
      - ``""`` si l'extraction a reussi (status serait ``item_1a``) ;
      - ``item_1a_absent`` si le regex n'a pas matche ;
      - ``section_too_short`` si le match existe mais est sous le seuil.
    """
    m = _ITEM_1A_RE.search(text)
    if m is None:
        return EXTRACTION_FAILURE_NO_MATCH
    if len(m.group(1)) < MIN_ITEM_1A_CHARS:
        return EXTRACTION_FAILURE_TOO_SHORT
    return ""


# ---------------------------------------------------------------------------
# Similarite
# ---------------------------------------------------------------------------


def tfidf_cosine(a: str, b: str) -> float:
    """TF-IDF (mots, 1-2 grammes, sublinear) + cosinus, identique a
    ``research.ipynb`` cellule 3 (verification micro-pipeline)."""
    vec = TfidfVectorizer(
        stop_words="english", ngram_range=(1, 2), max_features=60_000, sublinear_tf=True
    )
    mat = vec.fit_transform([a, b])
    return float(cosine_similarity(mat[0], mat[1])[0, 0])


# ---------------------------------------------------------------------------
# Construction d'une paire
# ---------------------------------------------------------------------------


def build_pair(
    ticker: str,
    cik: int,
    *,
    cache_dir: Path = DEFAULT_CACHE_DIR,
) -> FilingPair:
    """Construit la paire (N, N-1) la plus recente pour un ticker.

    Si le nombre de 10-K est inferieur a 2, le statut est ``"failed"``
    avec similarite ``None``. Si l'extraction de l'un des deux Item 1A
    echoue, le statut reste ``"failed"`` -- pas de ``full_fallback``
    (acceptance #4), et la similarite reste ``None``.
    """
    rows = list_recent_10k(cik, n=2, cache_dir=cache_dir)
    if len(rows) < 2:
        empty = FilingRecord(
            cik=cik,
            accession="",
            primary_document="",
            filing_date=date(1970, 1, 1),
            period_of_report=date(1970, 1, 1),
            acceptance_timestamp=datetime(1970, 1, 1, 0, 0, 0),
        )
        return FilingPair(
            ticker=ticker,
            newer=empty,
            older=empty,
            extraction_newer="failed",
            extraction_older="failed",
            similarity=None,
            status="failed",
        )

    newer, older = rows[0], rows[1]

    text_newer = fetch_10k_text(newer, cache_dir=cache_dir)
    section_newer, mode_newer = extract_item_1a(text_newer)

    text_older = fetch_10k_text(older, cache_dir=cache_dir)
    section_older, mode_older = extract_item_1a(text_older)

    if mode_newer == "item_1a" and mode_older == "item_1a":
        sim = tfidf_cosine(section_newer, section_older)
        return FilingPair(
            ticker=ticker,
            newer=newer,
            older=older,
            extraction_newer=mode_newer,
            extraction_older=mode_older,
            similarity=sim,
            status="item_1a",
        )

    return FilingPair(
        ticker=ticker,
        newer=newer,
        older=older,
        extraction_newer=mode_newer,
        extraction_older=mode_older,
        similarity=None,
        status="failed",
    )


# ---------------------------------------------------------------------------
# CSV
# ---------------------------------------------------------------------------


def _format_dt(value: datetime) -> str:
    """Format ISO 8601 sans fuseau (coherent avec EDGAR qui omet le Z)."""
    return value.strftime("%Y-%m-%dT%H:%M:%S")


def _format_d(value: date) -> str:
    return value.strftime("%Y-%m-%d")


def _row_from_pair(pair: FilingPair) -> dict[str, str]:
    """Aplatit un ``FilingPair`` en ligne CSV conforme a ``CSV_COLUMNS``.

    Le format est 100% string pour stabilite de parsing downstream (un
    consumer peut ``csv.DictReader`` sans typer chaque colonne ; les
    similary None sont encodes ``""`` -- jamais ``"None"`` qui ferait
    croire a une string).
    """
    sim = "" if pair.similarity is None else f"{pair.similarity:.6f}"
    return {
        "ticker": pair.ticker,
        "cik": str(pair.newer.cik),
        "accession_n": pair.newer.accession,
        "accession_n_minus_1": pair.older.accession,
        "filing_date_n": _format_d(pair.newer.filing_date),
        "filing_date_n_minus_1": _format_d(pair.older.filing_date),
        "acceptance_timestamp_n": _format_dt(pair.newer.acceptance_timestamp),
        "acceptance_timestamp_n_minus_1": _format_dt(pair.older.acceptance_timestamp),
        "period_of_report_n": _format_d(pair.newer.period_of_report),
        "period_of_report_n_minus_1": _format_d(pair.older.period_of_report),
        "extraction_mode_n": pair.extraction_newer,
        "extraction_mode_n_minus_1": pair.extraction_older,
        "similarity": sim,
        "available_at": _format_dt(pair.available_at),
    }


def write_csv(pairs: Iterable[FilingPair], path: Path | str) -> int:
    """Ecrit un CSV deterministe ; renvoie le nombre de lignes (data).

    L'ordre des lignes suit l'ordre d'entree de ``pairs``. L'ordre des
    colonnes est fige par ``CSV_COLUMNS`` (acceptance #5).
    """
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    written = 0
    with path.open("w", encoding="utf-8", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(CSV_COLUMNS))
        writer.writeheader()
        for pair in pairs:
            writer.writerow(_row_from_pair(pair))
            written += 1
    return written


# ---------------------------------------------------------------------------
# Helper de rapport (acceptance #7)
# ---------------------------------------------------------------------------


def summarize(pairs: Iterable[FilingPair]) -> dict[str, int | float]:
    """Compte par statut et taux de paires valides (status='item_1a').

    Sortie ``{"valid": N, "failed": M, "valid_rate": N/(N+M)}``. Si aucun
    pair n'est passe, ``valid_rate`` est 0.0 (et non NaN -- les consumers
    ne doivent pas tester ``math.isnan``).
    """
    valid = 0
    failed = 0
    for pair in pairs:
        if pair.status == "item_1a":
            valid += 1
        else:
            failed += 1
    total = valid + failed
    rate = valid / total if total else 0.0
    return {"valid": valid, "failed": failed, "valid_rate": rate}


__all__ = [
    "CSV_COLUMNS",
    "DEFAULT_CACHE_DIR",
    "DEFAULT_USER_AGENT",
    "FilingPair",
    "FilingRecord",
    "MAX_TEXT_CHARS",
    "MIN_ITEM_1A_CHARS",
    "MIN_REQUEST_INTERVAL_SECONDS",
    "build_pair",
    "extract_item_1a",
    "extract_item_1a_failure_reason",
    "fetch_10k_text",
    "list_recent_10k",
    "summarize",
    "tfidf_cosine",
    "write_csv",
    "EXTRACTION_FAILURE_NO_MATCH",
    "EXTRACTION_FAILURE_TOO_SHORT",
    "EXTRACTION_FAILURE_REASON_LABELS",
]
