"""Systeme d'extracts a tiers pour la jambe C3 de la strate 6 (issue #7742).

Port S6-B du systeme d'extracts EPITA vers CoursIA. Le design et le scaffold
proviennent de ``jsboigeEpita/2025-Epita-Intelligence-Symbolique`` (design :
``docs/coursia_contrib/s6_b_port_extracts_design.md`` ; scaffold :
``scripts/coursia_s6b/validate_fables_tier.py``), dont le differement etait
conditionne a l'acceptation de S6-A1 -- PR #1516, MERGEE le 2026-07-24.

QUATRE TIERS (source d'autorite : body #7742, table « Corpus — quatre tiers ») :

===============  ============================================  ==============================
Tier             Contenu                                       Forme dans le depot
===============  ============================================  ==============================
``public_clear`` oeuvres du domaine public (La Fontaine)      texte versionne, clair
``encrypted_``   Anschluss 1938, Matsui 1933                   blob ``*.json.gz.enc``,
``historical``                                                 passphrase distribuee au cours
``reference_``   temoins Chaplin (*Le Dictateur*, 1940)        jamais vendore -- droits
``fetch_runtime``                                               Roy Export S.A.S. ; fiches de
                                                                source + fetch runtime
``excluded_``    le reste du corpus EPITA                      reste chez EPITA, chiffre,
``external``                                                    non enumere
===============  ============================================  ==============================

CONTRAT DE FORMAT (interop EPITA, ne pas reimplenter ailleurs) :
le blob chiffre est ``json.dumps(payload).encode("utf-8")`` puis
``gzip.compress`` puis ``Fernet.encrypt``, la cle Fernet etant derivee par
``PBKDF2HMAC(SHA256, length=32, salt=FIXED_SALT, iterations=480_000)`` puis
``base64.urlsafe_b64encode`` -- exactement
``argumentation_analysis/core/utils/crypto_utils.py`` (repo EPITA, fonctions
``derive_encryption_key`` / ``encrypt_data_with_fernet`` / ``decrypt_data_with_
fernet_detailed``) et ``argumentation_analysis/core/io_manager.py``
(``save_extract_definitions`` / ``load_extract_definitions``). La derivation
etant deterministe (sel public constant), un blob ecrit ici se dechiffre par
le pipeline EPITA et reciproquement, a passphrase egale.

INVARIANTS VIE PRIVEE (design S6-B, « privacy HARD ») :

1. Le loader public filtre le tier ``public_clear`` et retire tout
   ``host_parts`` qui revelerait une trace d'URL reelle.
2. Les ids du cote public sont opaques et prefixes (``fable_*``, ``myth_*``,
   ``legend_*`` ; temoins : ``witness_*``) -- pas de nom reel sur cette
   surface.
3. Tout artefact EMIS (summaries, stdout de validation) est opaque-id-only :
   les champs ``text`` / ``full_text`` y sont retires avant emission
   (``strip_text_fields`` ; le scaffold EPITA a mesure que ``embed_full_text``
   ne couvrait que ``full_text`` et laissait fuiter ``text`` -- les deux sont
   retires ici).
4. Le tier references ne porte JAMAIS de texte, seulement des fiches de
   source (``fetch_method`` + cible).

GARDE ANTI-DEPOT (miroir de la garde EPITA « refuse de lire un texte suivi
par git ») : le constructeur de blob refuse de consommer une source en clair
qui serait suivie par git (``assert_not_git_tracked``), pour que le texte
historique ne puisse pas entrer accidentellement dans le depot en clair.

La passphrase ne vit JAMAIS dans le depot : elle vient de l'argument direct
ou de la variable d'environnement ``ICT_S6B_PASSPHRASE`` (sans valeur par
defaut -- cf. regle secrets-hygiene, pattern ``os.getenv`` nu).
"""

from __future__ import annotations

import base64
import gzip
import json
import os
import re
import subprocess
import tempfile
from enum import Enum
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple, Union

from cryptography.fernet import Fernet, InvalidToken
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

__all__ = [
    "Tier",
    "CLASSIFY_TIER_FIELD",
    "classify_extract",
    "derive_fernet_key",
    "encrypt_payload",
    "decrypt_payload",
    "load_public_definitions",
    "load_encrypted_definitions",
    "load_fetch_references",
    "build_encrypted_tier",
    "strip_text_fields",
    "opaque_summary",
    "assert_not_git_tracked",
]

# ---------------------------------------------------------------------------
# Constantes du contrat
# ---------------------------------------------------------------------------

#: Champ d'aiguillage explicite ; a defaut, la classification heuristique
#: (``public_domain`` / ``deposit_form``) decide, en fail-closed vers
#: ``EXCLUDED_EXTERNAL``.
CLASSIFY_TIER_FIELD = "tier"

#: Sel public du contrat EPITA (``crypto_utils.FIXED_SALT``) -- constant PAR
#: DESIGN (rend la derivation deterministe et l'interop possible) ; ce n'est
#: pas un secret, la passphrase est le secret.
FIXED_SALT = b"q\x8b\t\x97\x8b\xe9\xa3\xf2\xe4\x8e\xea\xf5\xe8\xb7\xd6\x8c"

PBKDF2_ITERATIONS = 480_000
PBKDF2_KEY_LENGTH = 32  # bits -> 32 octets = cle Fernet 256 bits

#: Chemin accepte par les loaders/builder (str ou PathLike).
PathOrStr = Union[str, "os.PathLike[str]"]

#: Variable d'environnement lue par ``load_encrypted_definitions`` quand
#: aucune passphrase directe n'est fournie. Sans valeur par defaut.
PASSPHRASE_ENV_VAR = "ICT_S6B_PASSPHRASE"

#: Schema des definitions d'extrait (contrat ``io_manager`` EPITA :
#: ``load_extract_definitions`` exige ces cles par source).
EXTRACT_DEFINITION_SCHEMA = "extract_definition_v1"
REQUIRED_SOURCE_KEYS: Tuple[str, ...] = (
    "source_name",
    "source_type",
    "schema",
    "host_parts",
    "path",
    "extracts",
)

#: Prefixes d'ids opaques admis par surface (design S6-B, axe « schema doc »).
OPAQUE_ID_PREFIXES_PUBLIC = ("fable_", "myth_", "legend_")
OPAQUE_ID_PREFIXES_WITNESS = ("witness_",)
#: Champs retirés de tout artefact émis (privacy HARD ; le scaffold EPITA a
#: mesure que couvrir ``full_text`` seul laissait fuiter ``text``).
PLAINTEXT_FIELDS = ("text", "full_text")


class Tier(Enum):
    """Les quatre tiers du corpus #7742."""

    PUBLIC_CLEAR = "public_clear"
    ENCRYPTED_HISTORICAL = "encrypted_historical"
    REFERENCE_FETCH_RUNTIME = "reference_fetch_runtime"
    EXCLUDED_EXTERNAL = "excluded_external"


# ---------------------------------------------------------------------------
# Classification
# ---------------------------------------------------------------------------

def classify_extract(entry: Mapping[str, Any]) -> Tier:
    """Route une entree de corpus vers son tier.

    Ordre de decision :

    1. champ explicite ``tier`` (present dans nos fichiers corpus) ;
    2. heuristique metadata : ``deposit_form`` puis ``public_domain`` ;
    3. fail-closed : tout ce qui n'est pas positivement routable est
       ``EXCLUDED_EXTERNAL`` (le tier qui reste chez EPITA).

    Le fail-closed est deliberé : une entite mal etiquetee ne doit jamais
    atterrir du cote public ou chiffre par defaut.
    """
    explicit = entry.get(CLASSIFY_TIER_FIELD)
    if isinstance(explicit, str):
        try:
            return Tier(explicit)
        except ValueError:
            return Tier.EXCLUDED_EXTERNAL

    deposit_form = entry.get("deposit_form")
    if deposit_form == "clear_text" and entry.get("public_domain") is True:
        return Tier.PUBLIC_CLEAR
    if deposit_form == "json.gz.enc":
        return Tier.ENCRYPTED_HISTORICAL
    if deposit_form == "fetch_runtime":
        return Tier.REFERENCE_FETCH_RUNTIME
    return Tier.EXCLUDED_EXTERNAL


# ---------------------------------------------------------------------------
# Adaptateur de format (contrat EPITA, cite -- ne pas diverger)
# ---------------------------------------------------------------------------

def derive_fernet_key(passphrase: str) -> bytes:
    """Derive la cle Fernet (urlsafe-b64) depuis la passphrase.

    Reproduction exacte de ``crypto_utils.derive_encryption_key`` (EPITA) :
    PBKDF2-HMAC-SHA256, 32 octets, sel constant public, 480 000 iterations.
    Deterministe : meme passphrase, meme cle, des deux cotes du port.
    """
    if not passphrase:
        raise ValueError("passphrase vide -- refus de deriver une cle")
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=PBKDF2_KEY_LENGTH,
        salt=FIXED_SALT,
        iterations=PBKDF2_ITERATIONS,
        backend=default_backend(),
    )
    return bytes(base64.urlsafe_b64encode(kdf.derive(passphrase.encode("utf-8"))))


def encrypt_payload(payload: Any, passphrase: str) -> bytes:
    """Chiffre un payload JSON-serialisable au format ``.json.gz.enc``.

    Etages exacts de ``io_manager.save_extract_definitions`` : JSON UTF-8
    (``ensure_ascii=False``), compression gzip, chiffrement Fernet.
    """
    json_data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    compressed = gzip.compress(json_data)
    return bytes(Fernet(derive_fernet_key(passphrase)).encrypt(compressed))


def decrypt_payload(blob: bytes, passphrase: str) -> Any:
    """Déchiffre un blob ``.json.gz.enc`` (miroir exact du chiffrement).

    Leve ``InvalidToken`` (mauvaise passphrase / blob corrompu) tel quel :
    l'appelant distingue l'absence de passphrase (``ValueError`` avant) du
    mauvais jeton, miroir des causes nommées EPITA.
    """
    compressed = Fernet(derive_fernet_key(passphrase)).decrypt(blob)
    return json.loads(gzip.decompress(compressed).decode("utf-8"))


# ---------------------------------------------------------------------------
# Vie privee : invariants sur les artefacts emis
# ---------------------------------------------------------------------------

def strip_text_fields(definitions: Iterable[Mapping[str, Any]]) -> List[Dict[str, Any]]:
    """Retire ``text`` / ``full_text`` de toute entree (privacy HARD).

    Miroir du ``_strip_text_fields`` du scaffold EPITA, les deux champs
    couverts (le scaffold a mesure la fuite de ``text`` seul).
    """
    cleaned: List[Dict[str, Any]] = []
    for d in definitions:
        d_clean = {k: v for k, v in d.items() if k not in PLAINTEXT_FIELDS}
        extracts = [
            {k: v for k, v in ext.items() if k not in PLAINTEXT_FIELDS}
            for ext in d_clean.get("extracts", [])
            if isinstance(ext, Mapping)
        ]
        d_clean["extracts"] = extracts
        cleaned.append(d_clean)
    return cleaned


def opaque_summary(definitions: Iterable[Mapping[str, Any]]) -> Dict[str, Any]:
    """Resume opaque-id-only : jamais de texte, jamais de traces d'URL.

    C'est la SEULE forme de summary que ce module emet ; le stdout du
    validateur et tout log doivent passer par ici.
    """
    defs = list(definitions)
    stripped = strip_text_fields(defs)
    return {
        "n_sources": len(stripped),
        "n_extracts_total": sum(len(d.get("extracts", [])) for d in stripped),
        "source_names": [d.get("source_name") for d in stripped],
    }


def _assert_opaque_ids(source: Mapping[str, Any], allowed_prefixes: Iterable[str]) -> None:
    name = str(source.get("source_name", ""))
    if not any(name.startswith(p) for p in allowed_prefixes):
        raise ValueError(
            f"source_name {name!r} hors prefixes opaques admis {tuple(allowed_prefixes)} "
            "-- le cote public ne porte pas de nom reel"
        )
    for ext in source.get("extracts", []):
        if isinstance(ext, Mapping):
            ext_id = str(ext.get("extract_id", ""))
            if not any(ext_id.startswith(p) for p in allowed_prefixes):
                raise ValueError(
                    f"extract_id {ext_id!r} hors prefixes opaques admis "
                    f"{tuple(allowed_prefixes)}"
                )


#: Traces d'URL reelles recherchees dans un ``host_parts`` public : schema,
#: marqueur www, adresse email, ou domaine nu (foo.com / foo.org / ...).
_URL_TRACE_RE = re.compile(
    r"(https?://|www\.|@|\b[\w-]+\.(?:com|org|net|fr|edu|gov|io|co)\b)",
    re.IGNORECASE,
)


def _assert_no_url_traces(host_parts: Iterable[str]) -> None:
    for p in host_parts:
        if _URL_TRACE_RE.search(str(p)):
            raise ValueError(
                f"host_parts {str(p)!r} laisse passer une trace d'URL reelle "
                "-- la surface publique n'expose aucune provenance"
            )


# ---------------------------------------------------------------------------
# Gardes anti-depot
# ---------------------------------------------------------------------------

def assert_not_git_tracked(path: Path) -> None:
    """Refuse une source en clair qui serait suivie par git.

    Miroir de la garde EPITA « refuse de lire un texte suivi par git » : le
    texte historique destine au blob chiffre ne doit JAMAIS exister en clair
    dans le depot. La verification est ``git ls-files --error-unmatch`` depuis
    le repertoire de la cible ; un echec de git lui-meme leve (fail-closed).
    """
    resolved = Path(path).resolve()
    try:
        result = subprocess.run(
            ["git", "ls-files", "--error-unmatch", str(resolved)],
            cwd=str(resolved.parent),
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:  # pragma: no cover
        raise RuntimeError(f"garde anti-depot : git injoignable ({exc})") from exc
    if result.returncode == 0:
        raise ValueError(
            f"refus : {resolved.name} est suivi par git -- le texte en clair "
            "n'entre pas dans le depot (garde anti-depot S6-B)"
        )


# ---------------------------------------------------------------------------
# Loaders par tier
# ---------------------------------------------------------------------------

def load_public_definitions(corpus_dir: PathOrStr) -> List[Dict[str, Any]]:
    """Loader public : filtre ``public_clear``, ids opaques, zero URL.

    Shim du design S6-B : ne sert QUE le tier public (fables et consœurs du
    domaine public), verifie le schema ``extract_definition_v1`` et les
    prefixes d'ids opaques, et retire les ``host_parts`` de ce qu'il rend --
    la surface publique ne expose aucune trace de provenance URL.
    """
    corpus = Path(corpus_dir)
    out: List[Dict[str, Any]] = []
    for json_path in sorted((corpus / "public").glob("*.json")):
        manifest = json.loads(json_path.read_text(encoding="utf-8"))
        for source in manifest.get("sources", []):
            # le tier explicite de la SOURCE prime ; a defaut celui du
            # manifeste ; a defaut les heuristiques -- jamais une disjonction
            # qui servirait une source etiquetee ailleurs.
            if CLASSIFY_TIER_FIELD in source:
                tier = classify_extract(source)
            else:
                tier = classify_extract(manifest)
            if tier is not Tier.PUBLIC_CLEAR:
                continue
            missing = [k for k in REQUIRED_SOURCE_KEYS if k not in source]
            if missing:
                raise ValueError(f"{json_path.name} : source sans cles requises {missing}")
            if source.get("schema") != EXTRACT_DEFINITION_SCHEMA:
                raise ValueError(
                    f"{json_path.name} : schema {source.get('schema')!r} != {EXTRACT_DEFINITION_SCHEMA!r}"
                )
            _assert_opaque_ids(source, OPAQUE_ID_PREFIXES_PUBLIC)
            for ext in source.get("extracts", []):
                _assert_no_url_traces(ext.get("host_parts", []))
            served = {k: v for k, v in source.items() if k != "host_parts"}
            for ext in served.get("extracts", []):
                ext.pop("host_parts", None)
            out.append(served)
    return out


def load_encrypted_definitions(
    blob_path: PathOrStr,
    passphrase: Optional[str] = None,
) -> List[Dict[str, Any]]:
    """Charge le tier chiffre ; passphrase par argument ou ``ICT_S6B_PASSPHRASE``.

    Ne loggue JAMAIS le texte decrypte (les appelants doivent passer par
    ``opaque_summary`` pour toute emission). Sans passphrase disponible :
    ``RuntimeError`` nommant la variable d'environnement, pas de valeur par
    defaut silencieuse.
    """
    if passphrase is None:
        passphrase = os.getenv(PASSPHRASE_ENV_VAR)
    if not passphrase:
        raise RuntimeError(
            f"passphrase absente : fournir l'argument ou definir {PASSPHRASE_ENV_VAR} "
            "(jamais de valeur par defaut dans le depot)"
        )
    blob = Path(blob_path).read_bytes()
    try:
        payload = decrypt_payload(blob, passphrase)
    except InvalidToken as exc:
        raise InvalidToken(
            f"{Path(blob_path).name} : mauvaise passphrase ou blob corrompu"
        ) from exc
    sources = payload.get("sources", []) if isinstance(payload, Mapping) else payload
    return list(sources)


def load_fetch_references(corpus_dir: PathOrStr) -> List[Dict[str, Any]]:
    """Charge les fiches du tier reference (JAMAIS de texte).

    Verifie l'invariant : aucune fiche ne porte ``text`` / ``full_text`` --
    un temoin dont le texte aurait ete vendore par erreur fait echouer le
    chargement plutot que d'entrer silencieusement dans le depot.
    """
    corpus = Path(corpus_dir)
    out: List[Dict[str, Any]] = []
    for json_path in sorted((corpus / "references").glob("*.json")):
        manifest = json.loads(json_path.read_text(encoding="utf-8"))
        for item in manifest.get("items", []):
            leaked = [k for k in PLAINTEXT_FIELDS if k in item]
            if leaked:
                raise ValueError(
                    f"{json_path.name} : fiche {item.get('reference_id')!r} porte {leaked} "
                    "-- le tier reference n'expose jamais de texte (droits)"
                )
            _assert_opaque_ids(
                {"source_name": item.get("reference_id", ""), "extracts": []},
                OPAQUE_ID_PREFIXES_WITNESS,
            )
            out.append(item)
    return out


# ---------------------------------------------------------------------------
# Constructeur du tier chiffre
# ---------------------------------------------------------------------------

def build_encrypted_tier(
    definitions: Sequence[Mapping[str, Any]],
    out_path: PathOrStr,
    passphrase: str,
    plaintext_sources: Optional[List[PathOrStr]] = None,
) -> Dict[str, Any]:
    """Construit un blob ``*.json.gz.enc`` depuis des definitions.

    Chaque source en clair listee dans ``plaintext_sources`` passe la garde
    anti-depot (``assert_not_git_tracked``) AVANT tout chiffrement : le texte
    historique doit vivre hors depot, et le geste qui l'importe doit le
    verifier au moment ou il le fait -- pas apres coup.

    Retourne un resume opaque (``opaque_summary``), seule emission permise.
    """
    for src in plaintext_sources or []:
        assert_not_git_tracked(Path(src))
    for source in definitions:
        missing = [k for k in REQUIRED_SOURCE_KEYS if k not in source]
        if missing:
            raise ValueError(f"definition sans cles requises {missing}")

    manifest: Dict[str, Any] = {
        "schema": "coursia_corpus_manifest_v1",
        "tier": Tier.ENCRYPTED_HISTORICAL.value,
        "sources": [dict(s) for s in definitions],
    }
    out = Path(out_path)
    out.parent.mkdir(parents=True, exist_ok=True)
    blob = encrypt_payload(manifest, passphrase)
    tmp_fd, tmp_name = tempfile.mkstemp(dir=str(out.parent), suffix=".tmp")
    os.close(tmp_fd)
    try:
        Path(tmp_name).write_bytes(blob)
        os.replace(tmp_name, str(out))
    finally:
        if os.path.exists(tmp_name):
            os.unlink(tmp_name)
    return opaque_summary(manifest["sources"])
