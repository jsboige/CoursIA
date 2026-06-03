"""P2 -- Text Segmentation for the v4 FishAudio audiobook pipeline.

Reads the source text "Boule de Suif" by Maupassant, splits it into
paragraphs, then uses chunked LLM processing to produce Pydantic-validated
segments with speaker attribution, type classification, and verbatim text.

Steps:
1. Load source text and split into paragraphs with IDs
2. Chunk paragraphs (8 per chunk, 2 overlap for continuity)
3. LLM segments each chunk with context injection + rolling summary
4. Validate output as SegmentBatch (Pydantic model)
5. Post-validation coverage check

Output: outputs/segments_v4.json
"""
from __future__ import annotations

import json
from pathlib import Path

from dotenv import load_dotenv

from .schemas import Segment, SegmentBatch
from .llm_client import call_structured
from .context_injector import build_context_block
from .canonical import normalize_speaker, RAW_TO_CANONICAL, load_catalog

BASE_DIR = Path(__file__).parent
OUTPUTS = BASE_DIR / "outputs"
OUTPUTS.mkdir(exist_ok=True)

SOURCE_TEXT = Path(__file__).parent.parent / "boule_de_suif_full.txt"

# ── Chunking constants ──

CHUNK_SIZE = 8       # paragraphs per LLM call
OVERLAP = 2          # paragraphs overlapping between chunks for continuity

# ── LLM prompt templates ──

SYSTEM_PROMPT = """Tu es un expert en analyse textuelle litteraire francaise.

Tu decoupes un texte en segments pour un audiobook expressif. Chaque segment
doit etre verbatim (copie exacte du texte source, sans reformulation).

Regles strictes :
1. `text` doit etre VERBATIM du texte source (mot pour mot, ponctuation comprise)
2. Pas de type "mixed" -- decoupe les paragraphes mixtes en segments distincts
3. Le locuteur doit etre dans la liste canonique (voir ci-dessous)
4. 15-60 mots par segment, couper aux frontieres de phrases
5. Type "thought" pour les passages de monologue interieur
6. Chaque segment doit avoir un `paragraph_id` correspondant au paragraphe source

Types de segment :
- narration : texte narratif (narrateur omniscient)
- dialogue : parole directe d'un personnage (entre guillemets)
- thought : monologue interieur / pensee d'un personnage

Locuteurs canoniques : narrateur, elisabeth_rousset, loiseau, madame_loiseau,
comte, comtesse, cornudet, carre_lamadon, madame_carre_lamadon, soeurs,
follenvie, madame_follenvie, officier, figurant

IMPORTANT : le speaker_raw est le nom tel qu'il apparait dans le texte ;
speaker est la forme canonique normalisee.

{figurant_section}"""

USER_PROMPT_TEMPLATE = """Voici un extrait de "Boule de Suif" de Maupassant.

{context_section}

{rolling_summary_section}

Paragraphes a segmenter :

{paragraphs_text}

Decoupe ces paragraphes en segments. Reponds au format JSON avec la structure
SegmentBatch : {{"segments": [...]}}.

Chaque segment : {{"seg_index": int, "type": "narration|dialogue|thought",
"speaker_raw": "...", "speaker": "<canonique>", "text": "...", "paragraph_id": int}}

Assure-toi que :
- Le texte est VERBATIM (copie exacte du texte source)
- Les segments couvrent l'integralite du texte fourni (rien d'omettre)
- Les index sont sequentiels a partir de {start_index}
- Les paragraph_id correspondent aux numeros fournis"""


# ── Pre-processing ──


def load_source_text(path: Path = SOURCE_TEXT) -> str:
    """Load the full source text file.

    Raises:
        FileNotFoundError: If the source text file does not exist.
    """
    if not path.exists():
        raise FileNotFoundError(
            f"Source text not found: {path}\n"
            "Place boule_de_suif_full.txt in the 04-Applications directory."
        )
    return path.read_text(encoding="utf-8")


def split_into_paragraphs(text: str) -> list[dict]:
    """Split source text into paragraphs with assigned IDs.

    Returns a list of dicts with keys: paragraph_id, text.
    Blank lines and pure whitespace are discarded.
    """
    raw_paragraphs = [p.strip() for p in text.split("\n\n") if p.strip()]
    return [
        {"paragraph_id": i, "text": para}
        for i, para in enumerate(raw_paragraphs)
    ]


def build_chunks(
    paragraphs: list[dict],
    chunk_size: int = CHUNK_SIZE,
    overlap: int = OVERLAP,
) -> list[list[dict]]:
    """Split paragraphs into overlapping chunks for LLM processing.

    Each chunk contains up to `chunk_size` paragraphs. Consecutive chunks
    overlap by `overlap` paragraphs to maintain narrative continuity and
    prevent boundary artifacts.
    """
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


# ── Rolling summary ──


def build_rolling_summary(segments: list[Segment], max_chars: int = 600) -> str:
    """Build a rolling summary from previously segmented content.

    Provides character state tracking and narrative context for continuity
    across chunk boundaries. Includes speaker distribution and last few
    segments' text for narrative coherence.
    """
    if not segments:
        return ""

    # Speaker distribution in recent segments
    speaker_counts: dict[str, int] = {}
    for seg in segments[-20:]:
        speaker_counts[seg.speaker] = speaker_counts.get(seg.speaker, 0) + 1

    recent_text = " ".join(seg.text for seg in segments[-5:])
    if len(recent_text) > max_chars:
        recent_text = recent_text[-max_chars:]

    active_speakers = sorted(speaker_counts, key=speaker_counts.get, reverse=True)

    lines = [
        "## Resume des segments precedents",
        f"Locuteurs actifs : {', '.join(active_speakers[:6])}",
        f"Derniers segments ({len(segments)} au total) :",
        recent_text,
    ]
    return "\n".join(lines)


# ── LLM segmentation ──


def format_paragraphs_text(paragraphs: list[dict]) -> str:
    """Format paragraphs for inclusion in the LLM prompt."""
    lines = []
    for p in paragraphs:
        lines.append(f"[Paragraphe {p['paragraph_id']}]")
        lines.append(p["text"])
        lines.append("")
    return "\n".join(lines)


def segment_chunk(
    chunk: list[dict],
    start_seg_index: int,
    previous_segments: list[Segment],
) -> list[Segment]:
    """Segment a single chunk of paragraphs via LLM.

    Args:
        chunk: List of paragraph dicts with paragraph_id and text.
        start_seg_index: The seg_index to assign to the first new segment.
        previous_segments: Segments from prior chunks (for rolling summary).

    Returns:
        List of validated Segment instances.
    """
    context_block = build_context_block("segmentation")
    rolling_summary = build_rolling_summary(previous_segments)

    # Build figurant section if speaker catalog is available
    figurant_section = ""
    try:
        catalog = load_catalog()
        if catalog.figurants:
            fig_lines = ["Figurants identifies dans le texte :"]
            for fig in catalog.figurants:
                fig_lines.append(
                    f"- {fig.raw_name} ({fig.voice_archetype}, "
                    f"{fig.total_appearances} apparitions)"
                )
            figurant_section = "\n".join(fig_lines)
    except FileNotFoundError:
        pass

    system_prompt = SYSTEM_PROMPT.format(figurant_section=figurant_section)

    context_section = f"<context>\n{context_block}\n</context>"
    rolling_summary_section = (
        f"<resume_precedent>\n{rolling_summary}\n</resume_precedent>"
        if rolling_summary
        else ""
    )

    paragraphs_text = format_paragraphs_text(chunk)

    user_prompt = USER_PROMPT_TEMPLATE.format(
        context_section=context_section,
        rolling_summary_section=rolling_summary_section,
        paragraphs_text=paragraphs_text,
        start_index=start_seg_index,
    )

    result = call_structured(
        SegmentBatch,
        system_prompt,
        user_prompt,
        context_block=context_block,
    )

    batch = SegmentBatch.model_validate(result)

    # Post-process: normalize speaker_raw through canonical mapper
    normalized_segments = []
    for seg in batch.segments:
        raw = seg.speaker_raw
        canonical = normalize_speaker(raw)
        # Re-validate with normalized speaker
        seg_data = seg.model_dump()
        seg_data["speaker"] = canonical
        try:
            normalized = Segment.model_validate(seg_data)
        except Exception:
            # If validation fails after normalization (e.g. dialogue+narrateur),
            # fall back to the LLM-provided speaker
            seg_data["speaker"] = seg.speaker
            normalized = Segment.model_validate(seg_data)
        normalized_segments.append(normalized)

    return normalized_segments


# ── Coverage check ──


def compute_coverage(segments: list[Segment], source_text: str) -> dict:
    """Compute rough coverage metrics: concatenated segment text vs source.

    Returns a dict with total source chars, total segment chars, and
    coverage ratio. This is a heuristic check, not an exact match,
    because LLM segmentation may split/merge slightly differently.
    """
    source_clean = " ".join(source_text.split())
    segments_text = " ".join(seg.text for seg in segments)
    segments_clean = " ".join(segments_text.split())

    source_len = len(source_clean)
    segments_len = len(segments_clean)

    if source_len == 0:
        return {"source_chars": 0, "segment_chars": 0, "coverage_ratio": 0.0}

    coverage = segments_len / source_len
    return {
        "source_chars": source_len,
        "segment_chars": segments_len,
        "coverage_ratio": round(coverage, 3),
    }


# ── Deduplication ──


def deduplicate_overlaps(
    all_segments: list[Segment],
    overlap: int = OVERLAP,
) -> list[Segment]:
    """Remove duplicate segments produced by overlapping chunks.

    Overlapping chunks produce duplicate paragraph_ids. We keep the
    segments from the later chunk (which had more context) and discard
    the earlier ones for the overlapping paragraph_ids.
    """
    if not all_segments:
        return []

    # Group segments by paragraph_id
    by_paragraph: dict[int, list[Segment]] = {}
    for seg in all_segments:
        by_paragraph.setdefault(seg.paragraph_id, []).append(seg)

    # For each paragraph with duplicates, keep only the later ones
    deduped: list[Segment] = []
    seen_paragraphs: set[int] = set()

    for seg in all_segments:
        pid = seg.paragraph_id
        if pid in seen_paragraphs:
            continue

        candidates = by_paragraph[pid]
        if len(candidates) == 1:
            deduped.append(candidates[0])
        else:
            # Keep the last occurrence (from the later chunk with more context)
            deduped.append(candidates[-1])

        seen_paragraphs.add(pid)

    # Re-index segments sequentially
    reindexed = []
    for i, seg in enumerate(deduped):
        seg_data = seg.model_dump()
        seg_data["seg_index"] = i
        reindexed.append(Segment.model_validate(seg_data))

    return reindexed


# ── Main entry point ──


def run(force: bool = False) -> Path:
    """Run P2 -- text segmentation. Returns path to segments_v4.json.

    Args:
        force: If True, re-run even if cached output exists.

    Returns:
        Path to the saved segments_v4.json file.
    """
    output_path = OUTPUTS / "segments_v4.json"

    if output_path.exists() and not force:
        print(f"[P2] Cached: {output_path}")
        return output_path

    print("[P2] Running text segmentation...")

    # Step 1: Load and split source text
    print("[P2] Step 1: Loading source text...")
    source_text = load_source_text()
    paragraphs = split_into_paragraphs(source_text)
    print(f"  {len(paragraphs)} paragraphs")

    # Step 2: Build overlapping chunks
    print("[P2] Step 2: Building chunks...")
    chunks = build_chunks(paragraphs)
    print(f"  {len(chunks)} chunks ({CHUNK_SIZE} paragraphs, {OVERLAP} overlap)")

    # Step 3: LLM segmentation per chunk
    print("[P2] Step 3: LLM segmentation...")
    all_segments: list[Segment] = []
    seg_index = 0

    for i, chunk in enumerate(chunks):
        chunk_paras = ", ".join(str(p["paragraph_id"]) for p in chunk)
        print(f"  Chunk {i + 1}/{len(chunks)} (paragraphs {chunk_paras})...")

        new_segments = segment_chunk(
            chunk=chunk,
            start_seg_index=seg_index,
            previous_segments=all_segments,
        )

        all_segments.extend(new_segments)
        seg_index += len(new_segments)

    print(f"  Raw segments: {len(all_segments)}")

    # Step 4: Deduplicate overlapping regions
    print("[P2] Step 4: Deduplicating overlaps...")
    segments = deduplicate_overlaps(all_segments)
    print(f"  Deduplicated segments: {len(segments)}")

    # Step 5: Coverage check
    print("[P2] Step 5: Coverage check...")
    coverage = compute_coverage(segments, source_text)
    print(f"  Source: {coverage['source_chars']:,} chars")
    print(f"  Segments: {coverage['segment_chars']:,} chars")
    print(f"  Coverage ratio: {coverage['coverage_ratio']:.1%}")

    if coverage["coverage_ratio"] < 0.85:
        print(f"  WARNING: Low coverage ({coverage['coverage_ratio']:.1%}). "
              "Some text may not be represented in segments.")

    # Step 6: Save as SegmentBatch JSON (compatible with downstream P3/P4)
    batch = SegmentBatch(segments=segments)

    output_path.write_text(
        batch.model_dump_json(indent=2),
        encoding="utf-8",
    )
    print(f"[P2] Saved: {output_path}")
    print(f"  Segments: {len(segments)}")
    print(f"  Coverage: {coverage['coverage_ratio']:.1%}")

    return output_path


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
