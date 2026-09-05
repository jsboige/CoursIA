"""Lecture a la demande de l'archive UCR Anomaly (Wu & Keogh, 2021).

L'archive `UCR_TimeSeriesAnomalyDatasets2021.zip` pese 184 Mo et n'est
couverte par **aucune licence de redistribution** : la page de l'archive
n'enonce qu'une citation suggeree. Les series ne sont donc **jamais**
recopiees dans le depot (cf. `.claude/rules/bibliography-hygiene.md`) ;
elles sont lues a l'execution par requetes HTTP `Range`, qui permettent
d'extraire une seule serie sans telecharger l'archive entiere.

Mecanique : un fichier ZIP se lit depuis la fin. On recupere le
`End Of Central Directory`, qui donne la position du repertoire central,
puis l'entree de la serie voulue, puis ses seuls octets compresses.
Cout typique : quelques centaines de kilo-octets au lieu de 184 Mo.

Reference de l'archive :
    Wu, R. & Keogh, E. « Current Time Series Anomaly Detection Benchmarks
    are Flawed and are Creating the Illusion of Progress »,
    IEEE TKDE, 2021 (arXiv:2009.13807).
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import struct
import tempfile
import urllib.request
import zlib

ARCHIVE_URL = (
    "https://www.cs.ucr.edu/~eamonn/time_series_data_2018/"
    "UCR_TimeSeriesAnomalyDatasets2021.zip"
)

_EOCD_SIG = b"PK\x05\x06"
_CEN_SIG = b"PK\x01\x02"
_TIMEOUT = 60
_MANIFEST_PATH = os.path.join(os.path.dirname(__file__), "ucr_anomaly_manifest.json")


class UcrFetchError(RuntimeError):
    """Echec de lecture de l'archive UCR.

    Levee telle quelle : aucune serie de substitution n'est fabriquee.
    Un benchmark sur des donnees inventees ne demontrerait rien -- c'est
    precisement le travers que ce notebook documente.
    """


def _http_range(url: str, start: int, end: int) -> bytes:
    """Lire les octets [start, end] (bornes incluses) d'une URL."""
    req = urllib.request.Request(
        url,
        headers={"Range": f"bytes={start}-{end}", "User-Agent": "CoursIA/ML-10"},
    )
    try:
        resp = urllib.request.urlopen(req, timeout=_TIMEOUT)
    except Exception as exc:
        raise UcrFetchError(
            f"requete Range vers {url} impossible ({type(exc).__name__}: {exc}). "
            "Verifier l'acces reseau a cs.ucr.edu."
        ) from exc
    if resp.status != 206:
        raise UcrFetchError(
            f"le serveur a repondu {resp.status} au lieu de 206 (Partial Content) : "
            "les requetes Range ne sont pas honorees, la lecture partielle est impossible."
        )
    return resp.read()


def _content_length(url: str) -> int:
    """Taille totale de l'archive, lue dans l'en-tete Content-Range."""
    req = urllib.request.Request(
        url,
        headers={"Range": "bytes=0-0", "User-Agent": "CoursIA/ML-10"},
    )
    try:
        resp = urllib.request.urlopen(req, timeout=_TIMEOUT)
        content_range = resp.headers.get("Content-Range", "")
    except Exception as exc:
        raise UcrFetchError(
            f"archive UCR injoignable ({type(exc).__name__}: {exc})."
        ) from exc
    m = re.search(r"/(\d+)$", content_range)
    if not m:
        raise UcrFetchError(f"en-tete Content-Range inexploitable : {content_range!r}.")
    return int(m.group(1))


def _central_directory(url: str, total: int) -> dict[str, tuple[int, int, int]]:
    """Repertoire central du ZIP : nom -> (offset local, taille compressee, methode)."""
    tail_len = min(66_000, total)
    tail = _http_range(url, total - tail_len, total - 1)
    pos = tail.rfind(_EOCD_SIG)
    if pos < 0:
        raise UcrFetchError("signature End Of Central Directory introuvable.")
    cen_size, cen_offset = struct.unpack("<II", tail[pos + 12 : pos + 20])
    blob = _http_range(url, cen_offset, cen_offset + cen_size - 1)

    entries: dict[str, tuple[int, int, int]] = {}
    i = 0
    while i + 46 <= len(blob) and blob[i : i + 4] == _CEN_SIG:
        (method,) = struct.unpack("<H", blob[i + 10 : i + 12])
        (comp_size,) = struct.unpack("<I", blob[i + 20 : i + 24])
        n_len, x_len, c_len = struct.unpack("<HHH", blob[i + 28 : i + 34])
        (local_off,) = struct.unpack("<I", blob[i + 42 : i + 46])
        name = blob[i + 46 : i + 46 + n_len].decode("utf-8", "replace")
        entries[name] = (local_off, comp_size, method)
        i += 46 + n_len + x_len + c_len
    if not entries:
        raise UcrFetchError("repertoire central vide ou illisible.")
    return entries


def _read_member(url: str, local_off: int, comp_size: int, method: int) -> bytes:
    """Lire et decompresser un membre du ZIP a partir de son en-tete local."""
    header = _http_range(url, local_off, local_off + 29)
    n_len, x_len = struct.unpack("<HH", header[26:30])
    data_off = local_off + 30 + n_len + x_len
    raw = _http_range(url, data_off, data_off + comp_size - 1)
    if method == 0:
        return raw
    if method == 8:
        return zlib.decompress(raw, -zlib.MAX_WBITS)
    raise UcrFetchError(f"methode de compression ZIP non geree : {method}.")


def _load_manifest() -> dict[str, dict[str, int | str]]:
    """Charger les tailles et empreintes des series utilisees par ML-10."""
    try:
        with open(_MANIFEST_PATH, encoding="utf-8") as fh:
            manifest = json.load(fh)
    except (OSError, json.JSONDecodeError) as exc:
        raise UcrFetchError(
            f"manifeste d'integrite UCR illisible "
            f"({type(exc).__name__} sur {os.path.basename(_MANIFEST_PATH)})."
        ) from exc
    if not isinstance(manifest, dict):
        raise UcrFetchError("manifeste d'integrite UCR invalide : objet JSON attendu.")
    for name, metadata in manifest.items():
        if (
            not isinstance(name, str)
            or not isinstance(metadata, dict)
            or not isinstance(metadata.get("size"), int)
            or metadata["size"] <= 0
            or not isinstance(metadata.get("sha256"), str)
            or re.fullmatch(r"[0-9a-f]{64}", metadata["sha256"]) is None
        ):
            raise UcrFetchError(
                f"entree invalide dans le manifeste d'integrite UCR : {name!r}."
            )
    return manifest


_MANIFEST = _load_manifest()
_CACHE: dict[str, bytes] = {}


def _verify_blob(name: str, blob: bytes, source: str) -> bytes:
    """Refuser une serie absente du manifeste ou dont les octets ont derive."""
    expected = _MANIFEST.get(name)
    if expected is None:
        raise UcrFetchError(
            f"serie {name!r} non autorisee : aucune empreinte dans le manifeste UCR."
        )
    expected_size = expected.get("size")
    expected_sha256 = expected.get("sha256")
    actual_size = len(blob)
    actual_sha256 = hashlib.sha256(blob).hexdigest()
    if actual_size != expected_size or actual_sha256 != expected_sha256:
        raise UcrFetchError(
            f"integrite UCR invalide pour {name!r} depuis {source}: "
            f"taille {actual_size} (attendue {expected_size}), SHA-256 "
            f"{actual_sha256} (attendu {expected_sha256})."
        )
    return blob


def _write_cache(cache_dir: str, name: str, blob: bytes) -> None:
    """Publier atomiquement une serie verifiee dans le cache local."""
    os.makedirs(cache_dir, exist_ok=True)
    temporary_path: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="wb",
            dir=cache_dir,
            prefix=f".{name}.",
            suffix=".tmp",
            delete=False,
        ) as fh:
            temporary_path = fh.name
            fh.write(blob)
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(temporary_path, os.path.join(cache_dir, name))
    finally:
        if temporary_path and os.path.exists(temporary_path):
            os.remove(temporary_path)


def fetch_raw(name: str, cache_dir: str | None = None) -> bytes:
    """Octets bruts d'une serie UCR, depuis le cache local puis le reseau.

    `cache_dir` (non versionne) evite de retelecharger entre deux cellules
    ou deux executions du notebook. Seules les series epinglees dans le
    manifeste sont acceptees ; cache et reseau subissent la meme verification.
    """
    if name not in _MANIFEST:
        raise UcrFetchError(
            f"serie {name!r} non autorisee : aucune empreinte dans le manifeste UCR."
        )
    if name in _CACHE:
        return _verify_blob(name, _CACHE[name], "cache memoire")

    if cache_dir:
        cached = os.path.join(cache_dir, name)
        if os.path.exists(cached):
            with open(cached, "rb") as fh:
                blob = fh.read()
            blob = _verify_blob(name, blob, "cache disque")
            _CACHE[name] = blob
            return blob

    total = _content_length(ARCHIVE_URL)
    entries = _central_directory(ARCHIVE_URL, total)
    match = next((k for k in entries if k.rsplit("/", 1)[-1] == name), None)
    if match is None:
        raise UcrFetchError(
            f"serie {name!r} absente de l'archive ({len(entries)} entrees listees)."
        )
    blob = _verify_blob(
        name,
        _read_member(ARCHIVE_URL, *entries[match]),
        f"archive reseau {ARCHIVE_URL!r}",
    )

    if cache_dir:
        _write_cache(cache_dir, name, blob)
    _CACHE[name] = blob
    return blob
