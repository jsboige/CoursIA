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


def load_source_text(path: Path | None = None) -> str:
    """Load the full source text file.

    Reads the module-level ``SOURCE_TEXT`` at call time (an orchestrator may
    override it after import; a default-argument binding would freeze the
    original path).

    Raises:
        FileNotFoundError: If the source text file does not exist.
    """
    resolved = SOURCE_TEXT if path is None else path
    if not resolved.exists():
        raise FileNotFoundError(
            f"Source text not found: {resolved}\n"
            "Place boule_de_suif_full.txt in the 04-Applications directory."
        )
    return resolved.read_text(encoding="utf-8")


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

# Seuil de couverture partage avec l'ancien avertissement : le seuil n'est
# pas change par cette PR, seule sa consequence l'est (avertissement -> blocage).
COVERAGE_MIN_RATIO = 0.85


class IncompleteSegmentationError(RuntimeError):
    """La segmentation ne couvre pas le texte source.

    levee par :func:`run` quand le ratio de couverture passe sous
    :data:`COVERAGE_MIN_RATIO`. Le fichier de segments est ecrit AVANT
    l'elevation : les artefacts sont conserves, la phase ne declare pas une
    reussite qu'elle n'a pas mesuree.
    """


def compute_coverage(
    segments: list[Segment],
    source_text: str,
    paragraphs: list[dict] | None = None,
) -> dict:
    """Compute rough coverage metrics: concatenated segment text vs source.

    Returns a dict with total source chars, total segment chars, and
    coverage ratio. This is a heuristic check, not an exact match,
    because LLM segmentation may split/merge slightly differently.

    When ``paragraphs`` is given, the report also names the source paragraphs
    that carry no segment at all: the ratio says *how much* text is missing,
    the paragraph list says *where*. It is a locator, not a criterion -- a
    paragraph merged into a neighbour legitimately carries the neighbour's
    ``paragraph_id``, and its text is then present without its own id.
    """
    source_clean = " ".join(source_text.split())
    segments_text = " ".join(seg.text for seg in segments)
    segments_clean = " ".join(segments_text.split())

    source_len = len(source_clean)
    segments_len = len(segments_clean)

    covered = {seg.paragraph_id for seg in segments}
    if paragraphs is None:
        paragraphs_expected = None
        paragraphs_covered = None
        missing_paragraphs: list[int] = []
    else:
        expected_ids = {p["paragraph_id"] for p in paragraphs}
        paragraphs_expected = len(expected_ids)
        paragraphs_covered = len(expected_ids & covered)
        missing_paragraphs = sorted(expected_ids - covered)

    if source_len == 0:
        return {
            "source_chars": 0,
            "segment_chars": 0,
            "coverage_ratio": 0.0,
            "paragraphs_expected": paragraphs_expected,
            "paragraphs_covered": paragraphs_covered,
            "missing_paragraphs": missing_paragraphs,
        }

    coverage = segments_len / source_len
    return {
        "source_chars": source_len,
        "segment_chars": segments_len,
        "coverage_ratio": round(coverage, 3),
        "paragraphs_expected": paragraphs_expected,
        "paragraphs_covered": paragraphs_covered,
        "missing_paragraphs": missing_paragraphs,
    }


# ── Deduplication ──


def _last_chunk_per_paragraph(
    all_segments: list[Segment],
    chunk_sizes: list[int],
) -> list[int]:
    """Indexes of the segments kept when the chunk boundaries are known.

    A paragraph covered by several chunks is segmented once per chunk. The
    rule is to keep every segment of the LAST chunk that produced it.
    """
    chunk_of: list[int] = []
    for chunk_index, size in enumerate(chunk_sizes):
        chunk_of.extend([chunk_index] * size)

    if len(chunk_of) != len(all_segments):
        raise ValueError(
            f"chunk_sizes describes {len(chunk_of)} segments "
            f"but {len(all_segments)} segments were produced"
        )

    last_chunk: dict[int, int] = {}
    for seg, chunk_index in zip(all_segments, chunk_of):
        current = last_chunk.get(seg.paragraph_id, -1)
        if chunk_index > current:
            last_chunk[seg.paragraph_id] = chunk_index

    return [
        i
        for i, seg in enumerate(all_segments)
        if chunk_of[i] == last_chunk[seg.paragraph_id]
    ]


def _last_occurrence_by_text(all_segments: list[Segment]) -> list[int]:
    """Indexes of the segments kept when the chunk boundaries are unknown.

    Fallback: two segments are duplicates only when they share their
    ``(paragraph_id, text)``. A segment whose text is unique to its paragraph
    is never dropped -- the paragraph may legitimately yield several segments.
    """
    last: dict[tuple[int, str], int] = {}
    for i, seg in enumerate(all_segments):
        last[(seg.paragraph_id, seg.text)] = i

    return [
        i
        for i, seg in enumerate(all_segments)
        if last[(seg.paragraph_id, seg.text)] == i
    ]


def deduplicate_overlaps(
    all_segments: list[Segment],
    chunk_sizes: list[int] | None = None,
) -> list[Segment]:
    """Remove the segments produced twice by the overlapping chunks.

    A paragraph covered by two chunks is segmented twice. The rule is to keep
    EVERY segment of the LAST chunk that produced the paragraph: a paragraph
    legitimately yields several segments (SYSTEM_PROMPT rules 2 and 4 -- a
    mixed paragraph is cut into distinct segments of 15 to 60 words, all
    carrying the same ``paragraph_id``), so keeping a single one drops the
    rest of the paragraph without a word of warning.

    Args:
        all_segments: all the segments, chunk by chunk, in order.
        chunk_sizes: number of segments produced by each chunk, in order.
            When given, the paragraph overlap is resolved at the chunk
            boundary. When omitted, the fallback is segment-level (see
            :func:`_last_occurrence_by_text`).

    Returns:
        The deduplicated segments, re-indexed from 0.
    """
    if not all_segments:
        return []

    if chunk_sizes is None:
        kept_indexes = _last_occurrence_by_text(all_segments)
    else:
        kept_indexes = _last_chunk_per_paragraph(all_segments, chunk_sizes)

    deduped = [all_segments[i] for i in kept_indexes]

    # Re-index segments sequentially
    reindexed = []
    for i, seg in enumerate(deduped):
        seg_data = seg.model_dump()
        seg_data["seg_index"] = i
        reindexed.append(Segment.model_validate(seg_data))

    return reindexed


# ── Main entry point ──


def _check_cached_completeness(output_path: Path) -> None:
    """Check a cached segmentation before handing it to the next phase.

    An incomplete segmentation is written before the phase raises: without
    this check, a rerun without ``--force`` would hand that same incomplete
    file to the next phase, silently. A cache with no report (written before
    this contract existed) is returned as it was.
    """
    report_path = output_path.parent / "segmentation_report.json"
    if not report_path.exists():
        return

    try:
        report = json.loads(report_path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return

    if report.get("complete") is False:
        ratio = report.get("coverage_ratio", 0.0)
        raise IncompleteSegmentationError(
            f"Segmentation incomplete (cache) : couverture {ratio:.1%} "
            f"< {COVERAGE_MIN_RATIO:.0%} -- voir {report_path.name}. "
            "Relancer avec force=True pour refaire la segmentation."
        )


def run(force: bool = False, allow_incomplete: bool = False) -> Path:
    """Run P2 -- text segmentation. Returns path to segments_v4.json.

    Args:
        force: If True, re-run even if cached output exists.
        allow_incomplete: If True, a segmentation that does not cover the
            source text is reported but does not raise. The default is to
            raise :class:`IncompleteSegmentationError`: a segmentation that
            lost text must not be handed to the next phase as a success.

    Returns:
        Path to the saved segments_v4.json file.
    """
    output_path = OUTPUTS / "segments_v4.json"

    if output_path.exists() and not force:
        print(f"[P2] Cached: {output_path}")
        _check_cached_completeness(output_path)
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
    chunk_segment_counts: list[int] = []
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
        chunk_segment_counts.append(len(new_segments))
        seg_index += len(new_segments)

    print(f"  Raw segments: {len(all_segments)}")

    # Step 4: Deduplicate overlapping regions
    print("[P2] Step 4: Deduplicating overlaps...")
    segments = deduplicate_overlaps(all_segments, chunk_sizes=chunk_segment_counts)
    print(f"  Deduplicated segments: {len(segments)}")

    # Step 5: Coverage check
    print("[P2] Step 5: Coverage check...")
    coverage = compute_coverage(segments, source_text, paragraphs=paragraphs)
    print(f"  Source: {coverage['source_chars']:,} chars")
    print(f"  Segments: {coverage['segment_chars']:,} chars")
    print(f"  Coverage ratio: {coverage['coverage_ratio']:.1%}")

    complete = coverage["coverage_ratio"] >= COVERAGE_MIN_RATIO

    report = {
        "source_chars": coverage["source_chars"],
        "segment_chars": coverage["segment_chars"],
        "coverage_ratio": coverage["coverage_ratio"],
        "coverage_min_ratio": COVERAGE_MIN_RATIO,
        "complete": complete,
        "segments": len(segments),
        "paragraphs_expected": coverage["paragraphs_expected"],
        "paragraphs_covered": coverage["paragraphs_covered"],
        "missing_paragraphs": coverage["missing_paragraphs"],
    }
    report_path = OUTPUTS / "segmentation_report.json"
    report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")

    if coverage["missing_paragraphs"]:
        print(f"  WARNING: {len(coverage['missing_paragraphs'])} paragraph(s) without any "
              f"segment (first ids: {coverage['missing_paragraphs'][:10]}) "
              f"-- see {report_path.name}")

    if not complete:
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

    # Step 7: the phase does not report a success it did not measure
    if not complete:
        print(f"  INCOMPLETE: coverage {coverage['coverage_ratio']:.1%} "
              f"< {COVERAGE_MIN_RATIO:.0%} -- report: {report_path.name}")
        if not allow_incomplete:
            raise IncompleteSegmentationError(
                f"Segmentation incomplete : couverture {coverage['coverage_ratio']:.1%} "
                f"(< {COVERAGE_MIN_RATIO:.0%}), {len(coverage['missing_paragraphs'])} "
                f"paragraphe(s) sans segment. Les segments sont ecrits dans "
                f"{output_path.name} et le rapport dans {report_path.name}. "
                "Relancer avec allow_incomplete=True pour un run de diagnostic."
            )

    return output_path


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
