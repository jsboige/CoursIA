"""Speaker name normalization for Boule de Suif audiobook pipeline.

Maps 33+ raw speaker variants found in text annotations to 14 canonical
speaker identifiers used throughout the v4 pipeline (P0-P7).
"""
from __future__ import annotations

from pathlib import Path

from .schemas import CanonicalSpeaker, SpeakerCatalog

# ── Raw variant → canonical speaker ──

RAW_TO_CANONICAL: dict[str, CanonicalSpeaker] = {
    # narrateur (case handled by .lower() in normalize_speaker)
    "narrateur": "narrateur",
    "le narrateur": "narrateur",
    # elisabeth_rousset
    "elisabeth rousset": "elisabeth_rousset",
    "boule de suif": "elisabeth_rousset",
    "elisabeth": "elisabeth_rousset",
    "mlle elisabeth rousset": "elisabeth_rousset",
    "elizabeth rousset": "elisabeth_rousset",
    # loiseau
    "loiseau": "loiseau",
    "monsieur loiseau": "loiseau",
    "m. loiseau": "loiseau",
    "m loiseau": "loiseau",
    # madame_loiseau
    "madame loiseau": "madame_loiseau",
    "mme loiseau": "madame_loiseau",
    # comte
    "comte hubert de breville": "comte",
    "le comte": "comte",
    "comte": "comte",
    "comte de breville": "comte",
    "comte hubert de bréville": "comte",
    # comtesse
    "comtesse de breville": "comtesse",
    "la comtesse": "comtesse",
    "comtesse": "comtesse",
    "comtesse de bréville": "comtesse",
    "mme de bréville": "comtesse",
    # cornudet
    "cornudet": "cornudet",
    # carre_lamadon
    "carre-lamadon": "carre_lamadon",
    "carre lamadon": "carre_lamadon",
    "carré-lamadon": "carre_lamadon",
    "m. carré-lamadon": "carre_lamadon",
    # madame_carre_lamadon
    "madame carré-lamadon": "madame_carre_lamadon",
    "mme carré-lamadon": "madame_carre_lamadon",
    "madame carre-lamadon": "madame_carre_lamadon",
    # soeurs
    "les bonnes soeurs": "soeurs",
    "les soeurs": "soeurs",
    "soeurs": "soeurs",
    "bonne soeur": "soeurs",
    "religieuse": "soeurs",
    "les religieuses": "soeurs",
    # follenvie
    "follenvie": "follenvie",
    "m. follenvie": "follenvie",
    "m follenvie": "follenvie",
    # madame_follenvie
    "madame follenvie": "madame_follenvie",
    "mme follenvie": "madame_follenvie",
    # officier
    "officier prussien": "officier",
    "l'officier prussien": "officier",
    "l'officier": "officier",
    "officier": "officier",
}

# ── Figurant speakers (minor / crowd voices) ──

FIGURANT_NAMES: set[str] = {
    "cocher", "bedeau",
    "un homme", "un autre homme", "un troisième homme", "homme",
    "dames",
    "voix du dehors", "voix du dedans",
    "moi",
    "georges garin",
    "l'anglais", "la petite anglaise",
}

# Pre-compute lowercase figurant set for fast lookup
_FIGURANT_LOWER: set[str] = {n.lower().strip() for n in FIGURANT_NAMES}


def normalize_speaker(raw: str) -> CanonicalSpeaker:
    """Normalize a raw speaker string to a canonical identifier.

    Resolution order:
      1. Exact match in RAW_TO_CANONICAL (case-insensitive)
      2. Partial match (alias substring of raw, or raw substring of alias)
      3. Figurant detection
      4. Fallback to "narrateur"
    """
    key = raw.lower().strip()

    # 1. Direct lookup
    if key in RAW_TO_CANONICAL:
        return RAW_TO_CANONICAL[key]

    # 2. Figurant exact match
    if key in _FIGURANT_LOWER:
        return "figurant"

    # 3. Partial match against known aliases
    for alias, canonical in RAW_TO_CANONICAL.items():
        if alias in key or key in alias:
            return canonical

    # 4. Partial match against figurants
    for fig in _FIGURANT_LOWER:
        if fig in key or key in fig:
            return "figurant"

    # 5. Default fallback
    return "narrateur"


# ── Speaker catalog integration ──

_V4_DIR = Path(__file__).resolve().parent
_CATALOG_PATH = _V4_DIR / "outputs" / "speaker_catalog.json"
_cached_catalog: SpeakerCatalog | None = None


def load_catalog(path: str | Path | None = None) -> SpeakerCatalog:
    """Load and cache the speaker catalog from P1.5.

    Returns None-wrapped: raises FileNotFoundError if catalog missing.
    """
    global _cached_catalog
    if _cached_catalog is not None:
        return _cached_catalog

    resolved = Path(path) if path is not None else _CATALOG_PATH
    if not resolved.exists():
        raise FileNotFoundError(
            f"speaker_catalog.json introuvable : {resolved}\n"
            "Lancez d'abord la phase P1.5 (speaker catalog)."
        )

    _cached_catalog = SpeakerCatalog.model_validate_json(
        resolved.read_text(encoding="utf-8")
    )
    return _cached_catalog


def resolve_figurant(raw: str, catalog: SpeakerCatalog | None = None) -> str:
    """Try to resolve a raw speaker name to a figurant archetype via catalog.

    Returns the voice_archetype if found in catalog, else empty string.
    """
    if catalog is None:
        try:
            catalog = load_catalog()
        except FileNotFoundError:
            return ""

    norm = raw.lower().strip()
    for fig in catalog.figurants:
        fig_norm = fig.raw_name.lower().strip()
        if fig_norm == norm or fig_norm in norm or norm in fig_norm:
            return fig.voice_archetype

    return ""
