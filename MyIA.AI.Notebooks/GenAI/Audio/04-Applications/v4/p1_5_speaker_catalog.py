"""P1.5 -- Speaker Catalog for the v4 FishAudio audiobook pipeline.

Reads the source text "Boule de Suif" and identifies ALL speakers including
minor figurants, assigning voice archetypes for TTS voice selection.

Steps:
1. Filter source text to Boule de Suif only (lines 1-1595)
2. Split into paragraphs and chunk (40 paragraphs per chunk)
3. LLM identifies every speaker with context per chunk
4. Merge and deduplicate figurant lists
5. Assign voice_archetype via heuristic rules
6. Build figurant_voice_map to reference_ids

Output: outputs/speaker_catalog.json
"""
from __future__ import annotations

import re
from pathlib import Path

from pydantic import BaseModel, Field

from .schemas import (
    CanonicalSpeaker,
    CharacterProfile,
    FigurantProfile,
    SpeakerAppearance,
    SpeakerCatalog,
)
from .llm_client import call_structured
from .context_injector import build_context_block
from .canonical import normalize_speaker, RAW_TO_CANONICAL

BASE_DIR = Path(__file__).parent
OUTPUTS = BASE_DIR / "outputs"
OUTPUTS.mkdir(exist_ok=True)

SOURCE_TEXT = Path(__file__).parent.parent / "boule_de_suif_full.txt"

# BdS ends around line 1595; other Maupassant stories follow.
BDS_MAX_LINE = 1595

CHUNK_SIZE = 40  # paragraphs per LLM call
OVERLAP = 4

# ── Voice archetype heuristic mapping ──

_GENDER_KEYWORDS: dict[str, list[str]] = {
    "male": [
        "monsieur", "m.", "homme", "cocher", "bedeau", "officier", "comte",
        "cure", "pretre", "cur", "gars", "serviteur", " domestique",
        "soldat", "prussien",
    ],
    "female": [
        "madame", "mme", "femme", "demoiselle", "religieuse", "soeur",
        "bonne", "servante", "dame", "fille",
    ],
}

_ROLE_KEYWORDS: dict[str, str] = {
    "male_gruff": ["cocher", "bedeau", "soldat", "prussien", " domestique"],
    "male_refined": ["monsieur", "comte", "officier", "cure", "pretre", "cur"],
    "male_neutral": ["homme", "gars", "voix"],
    "female_warm": ["madame", "femme", "bonne", "servante", "mere"],
    "female_cold": ["comtesse", "demoiselle"],
    "female_neutral": ["religieuse", "soeur", "fille", "dame"],
}


# ── Pydantic model for LLM structured output ──

class _FigurantItem(BaseModel):
    raw_name: str
    description: str = ""
    first_paragraph: int = 0
    total_appearances: int = 1
    is_direct_speech: bool = False
    emotion_hint: str = ""
    context_snippet: str = ""


class FigurantBatch(BaseModel):
    figurants: list[_FigurantItem]


# ── LLM prompt templates ──

SYSTEM_PROMPT = """Tu es un expert en analyse textuelle litteraire francaise.

Ton but est d'identifier TOUS les locuteurs du texte, y compris les personnages
mineurs qui ne parlent qu'une seule fois (figurants).

Pour chaque locuteur identifie, fournis :
1. raw_name : le nom exact tel qu'il apparait dans le texte
2. description : une breve description du personnage (role, statut social)
3. first_paragraph : le numero du paragraphe ou il apparait pour la premiere fois
4. total_appearances : nombre estimé d'apparitions (parole directe ou mention)
5. is_direct_speech : true si le personnage parle directement au moins une fois
6. emotion_hint : emotion dominante dans ses repliques
7. context_snippet : un court extrait (~100 caracteres) d'une de ses repliques

IMPORTANT :
- Inclus les personnages deja listes dans le contexte ET les nouveaux figurants
- Les "figurants" sont des personnages qui parlent mais ne sont pas nommes
  (ex: "une voix", "un homme", "le cocher")
- Ne pas inclure le narrateur
- Cherche les mentions indirectes : "dit X", "repondit Y", "murmura Z"
- Normalise les noms : "M. Follenvie" et "Follenvie" = meme personnage"""

USER_PROMPT_TEMPLATE = """Voici un extrait de "Boule de Suif" de Maupassant.

{context_section}

Locuteurs deja identifies dans les chunks precedents :
{known_figurants_section}

Paragraphes a analyser :

{paragraphs_text}

Identifie TOUS les locuteurs dans cet extrait, y compris les figurants mineurs.
Reponds au format JSON avec la structure FigurantBatch : {{"figurants": [...]}}."""


# ── Text filtering ──


def _filter_bds_text(full_text: str, max_line: int = BDS_MAX_LINE) -> str:
    """Keep only the Boule de Suif portion of the source file."""
    lines = full_text.split("\n")
    return "\n".join(lines[:max_line])


# ── Chunking ──


def _split_paragraphs(text: str) -> list[dict]:
    """Split text into paragraphs with IDs."""
    raw = [p.strip() for p in text.split("\n\n") if p.strip()]
    return [{"paragraph_id": i, "text": p} for i, p in enumerate(raw)]


def _build_chunks(
    paragraphs: list[dict],
    chunk_size: int = CHUNK_SIZE,
    overlap: int = OVERLAP,
) -> list[list[dict]]:
    """Split paragraphs into overlapping chunks."""
    if not paragraphs:
        return []

    chunks = []
    step = max(1, chunk_size - overlap)
    for start in range(0, len(paragraphs), step):
        chunk = paragraphs[start : start + chunk_size]
        if chunk:
            chunks.append(chunk)
        if start + chunk_size >= len(paragraphs):
            break

    return chunks


# ── Voice archetype assignment ──


def _infer_gender(raw_name: str) -> str:
    """Infer gender from the raw name using keyword matching."""
    lower = raw_name.lower()
    for gender, keywords in _GENDER_KEYWORDS.items():
        for kw in keywords:
            if kw in lower:
                return gender
    return "male"  # default


def _assign_voice_archetype(raw_name: str, description: str = "") -> str:
    """Assign a voice archetype based on name and description heuristics."""
    lower = raw_name.lower()
    desc_lower = description.lower()

    for archetype, keywords in _ROLE_KEYWORDS.items():
        for kw in keywords:
            if kw in lower or kw in desc_lower:
                return archetype

    gender = _infer_gender(raw_name)
    return f"{gender}_neutral"


# ── Deduplication ──


def _normalize_name(name: str) -> str:
    """Normalize a name for deduplication comparison."""
    n = name.lower().strip()
    n = re.sub(r"[.'\-]", " ", n)
    n = re.sub(r"\s+", " ", n).strip()
    return n


def _merge_figurants(
    existing: list[_FigurantItem],
    new_items: list[_FigurantItem],
) -> list[_FigurantItem]:
    """Merge new figurant items into existing list, deduplicating by name."""
    by_name: dict[str, _FigurantItem] = {}

    for item in existing:
        key = _normalize_name(item.raw_name)
        if key not in by_name:
            by_name[key] = item
        else:
            prev = by_name[key]
            prev.total_appearances += item.total_appearances
            if item.first_paragraph > 0 and (
                prev.first_paragraph == 0
                or item.first_paragraph < prev.first_paragraph
            ):
                prev.first_paragraph = item.first_paragraph
            if item.is_direct_speech:
                prev.is_direct_speech = True
            if not prev.description and item.description:
                prev.description = item.description
            if not prev.context_snippet and item.context_snippet:
                prev.context_snippet = item.context_snippet

    for item in new_items:
        key = _normalize_name(item.raw_name)

        if key in by_name:
            prev = by_name[key]
            prev.total_appearances += item.total_appearances
            if item.first_paragraph > 0 and (
                prev.first_paragraph == 0
                or item.first_paragraph < prev.first_paragraph
            ):
                prev.first_paragraph = item.first_paragraph
            if item.is_direct_speech:
                prev.is_direct_speech = True
            if not prev.description and item.description:
                prev.description = item.description
            if not prev.context_snippet and item.context_snippet:
                prev.context_snippet = item.context_snippet
        else:
            by_name[key] = item

    return sorted(by_name.values(), key=lambda x: x.first_paragraph)


# ── Build known figurants summary for context ──


def _format_known_figurants(figurants: list[_FigurantItem]) -> str:
    """Format already-identified figurants for prompt context."""
    if not figurants:
        return "(aucun figurant identifie pour l'instant)"

    lines = []
    for f in figurants:
        lines.append(
            f"- {f.raw_name} ({f.total_appearances} apparitions, "
            f"parole directe: {'oui' if f.is_direct_speech else 'non'})"
        )
    return "\n".join(lines)


def _format_paragraphs_text(paragraphs: list[dict]) -> str:
    """Format paragraphs for LLM prompt."""
    lines = []
    for p in paragraphs:
        lines.append(f"[Paragraphe {p['paragraph_id']}]")
        lines.append(p["text"])
        lines.append("")
    return "\n".join(lines)


# ── LLM speaker identification ──


def _identify_speakers_chunk(
    chunk: list[dict],
    known_figurants: list[_FigurantItem],
) -> list[_FigurantItem]:
    """Run LLM speaker identification on a single chunk."""
    context_block = build_context_block("segmentation")
    context_section = f"<context>\n{context_block}\n</context>"
    known_section = _format_known_figurants(known_figurants)
    paragraphs_text = _format_paragraphs_text(chunk)

    user_prompt = USER_PROMPT_TEMPLATE.format(
        context_section=context_section,
        known_figurants_section=known_section,
        paragraphs_text=paragraphs_text,
    )

    result = call_structured(
        FigurantBatch,
        SYSTEM_PROMPT,
        user_prompt,
        context_block=context_block,
    )

    batch = FigurantBatch.model_validate(result)
    return batch.figurants


# ── Build final catalog ──


def _build_catalog(
    figurant_items: list[_FigurantItem],
    narrative_context_path: Path | None = None,
) -> SpeakerCatalog:
    """Build the final SpeakerCatalog from merged figurant items."""
    from .context_injector import load_narrative_context

    canonical_speakers: dict[str, CharacterProfile] = {}
    try:
        ctx = load_narrative_context(str(narrative_context_path) if narrative_context_path else None)
        canonical_speakers = dict(ctx.characters)
    except FileNotFoundError:
        pass

    # Filter out canonical speakers from figurant items
    canonical_names_lower: set[str] = set()
    for key, char in canonical_speakers.items():
        canonical_names_lower.add(key.lower())
        for alias in char.aliases:
            canonical_names_lower.add(alias.lower())
    # Also include all RAW_TO_CANONICAL keys
    for alias in RAW_TO_CANONICAL:
        canonical_names_lower.add(alias.lower())

    figurants: list[FigurantProfile] = []
    figurant_voice_map: dict[str, str] = {}
    total_dialogue = 0

    for item in figurant_items:
        norm = _normalize_name(item.raw_name)

        # Skip if this is a known canonical speaker
        is_canonical = False
        for canon_key in canonical_names_lower:
            if canon_key in norm or norm in canon_key:
                is_canonical = True
                break
        if is_canonical:
            continue

        # Resolve canonical speaker
        resolved = normalize_speaker(item.raw_name)
        if resolved != "figurant":
            continue

        archetype = _assign_voice_archetype(item.raw_name, item.description)

        appearances = []
        if item.is_direct_speech:
            appearances.append(
                SpeakerAppearance(
                    paragraph_id=item.first_paragraph,
                    context_snippet=item.context_snippet,
                    is_direct_speech=True,
                    emotion_hint=item.emotion_hint,
                )
            )
            total_dialogue += item.total_appearances

        profile = FigurantProfile(
            raw_name=item.raw_name,
            canonical="figurant",
            voice_archetype=archetype,
            first_paragraph=item.first_paragraph,
            total_appearances=item.total_appearances,
            appearances=appearances,
            description=item.description,
        )
        figurants.append(profile)
        figurant_voice_map[item.raw_name] = archetype

    # Count total speakers (canonical + unique figurants)
    total_speakers = len(canonical_speakers) + len(figurants)

    return SpeakerCatalog(
        canonical_speakers=canonical_speakers,
        figurants=figurants,
        figurant_voice_map=figurant_voice_map,
        total_speakers=total_speakers,
        total_dialogue_segments=total_dialogue,
    )


# ── Main entry point ──


def run(force: bool = False) -> Path:
    """Run P1.5 -- speaker catalog. Returns path to speaker_catalog.json."""
    output_path = OUTPUTS / "speaker_catalog.json"

    if output_path.exists() and not force:
        print(f"[P1.5] Cached: {output_path}")
        return output_path

    print("[P1.5] Running speaker catalog...")

    # Step 1: Load and filter source text
    print("[P1.5] Step 1: Loading source text (BdS only)...")
    if not SOURCE_TEXT.exists():
        raise FileNotFoundError(f"Source text not found: {SOURCE_TEXT}")

    full_text = SOURCE_TEXT.read_text(encoding="utf-8")
    bds_text = _filter_bds_text(full_text)
    paragraphs = _split_paragraphs(bds_text)
    print(f"  {len(paragraphs)} paragraphs (BdS only)")

    # Step 2: Build chunks
    print("[P1.5] Step 2: Building chunks...")
    chunks = _build_chunks(paragraphs)
    print(f"  {len(chunks)} chunks ({CHUNK_SIZE} paragraphs, {OVERLAP} overlap)")

    # Step 3: LLM identification per chunk
    print("[P1.5] Step 3: LLM speaker identification...")
    all_figurants: list[_FigurantItem] = []

    for i, chunk in enumerate(chunks):
        chunk_paras = ", ".join(str(p["paragraph_id"]) for p in chunk)
        print(f"  Chunk {i + 1}/{len(chunks)} (paragraphs {chunk_paras})...")

        new_items = _identify_speakers_chunk(chunk, all_figurants)
        all_figurants = _merge_figurants(all_figurants, new_items)

        print(f"    Found {len(new_items)} speakers, total unique: {len(all_figurants)}")

    print(f"  Total unique figurant candidates: {len(all_figurants)}")

    # Step 4: Build final catalog (filter canonical speakers)
    print("[P1.5] Step 4: Building speaker catalog...")
    catalog = _build_catalog(all_figurants)

    # Step 5: Save
    output_path.write_text(
        catalog.model_dump_json(indent=2),
        encoding="utf-8",
    )

    print(f"[P1.5] Saved: {output_path}")
    print(f"  Canonical speakers: {len(catalog.canonical_speakers)}")
    print(f"  Figurants: {len(catalog.figurants)}")
    print(f"  Total speakers: {catalog.total_speakers}")
    print(f"  Voice archetypes: {set(f.voice_archetype for f in catalog.figurants)}")

    return output_path


if __name__ == "__main__":
    from dotenv import load_dotenv

    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
