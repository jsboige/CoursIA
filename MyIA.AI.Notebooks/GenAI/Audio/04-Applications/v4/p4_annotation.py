"""P4 -- Prosodic Annotation for the v4 FishAudio audiobook pipeline.

Takes segments (from P2) and dramatic context (from P3), then produces
annotated segments with inline prosody tags via batched LLM calls.

Steps:
1. Load segments from outputs/segments_v4.json
2. Load dramatic context from outputs/dramatic_context.json
3. Batch 10 segments per LLM call with narrative context
4. Each batch gets context from context_injector.build_context_block
5. Post-process tags into FishAudio-compatible format

Output: outputs/annotated_v4.json
"""
from __future__ import annotations

import json
import re
from pathlib import Path

from dotenv import load_dotenv

from .schemas import (
    Segment,
    SegmentBatch,
    DramaticContext,
    DramaticContextBatch,
    AnnotatedSegment,
    AnnotatedBatch,
    ALL_PROSODY_TAGS,
)
from .llm_client import call_structured
from .context_injector import build_context_block

BASE_DIR = Path(__file__).parent
OUTPUTS = BASE_DIR / "outputs"
OUTPUTS.mkdir(exist_ok=True)

# ── Constants ──

BATCH_SIZE = 10
MAX_TAGS_PER_SEGMENT = 3

INPUT_SEGMENTS = OUTPUTS / "segments_v4.json"
INPUT_DRAMATIC = OUTPUTS / "dramatic_context.json"
OUTPUT_ANNOTATED = OUTPUTS / "annotated_v4.json"

# ── FishAudio tag conversion map ──

TAG_TO_FISHAUDIO: dict[str, str] = {
    # Voice modes
    "whisper": "(whispering)",
    "shout": "(shouting)",
    "scream": "(screaming)",
    # Affect
    "cold": "(in a cold tone)",
    "warm": "(in a warm tone)",
    "onctuous": "(in a smooth, ingratiating tone)",
    "indignant": "(indignantly)",
    "mocking": "(mockingly)",
    "angry": "(angrily)",
    "sad": "(sadly)",
    "nervous": "(nervously)",
    "excited": "(excitedly)",
    "gentle": "(gently)",
    "firm": "(firmly)",
    "timid": "(timidly)",
    # Non-verbal
    "laugh": "(laughing)",
    "sigh": "(sighing)",
    "sob": "(sobbing)",
    "gasp": "(gasping)",
    "breath": "(taking a breath)",
    # Tempo
    "slow": "(speaking slowly)",
    "fast": "(speaking quickly)",
    "pause": "...",
}

# ── LLM prompt templates ──

SYSTEM_PROMPT = """Tu es un expert en annotation prosodique pour la synthese vocale.
Tu recevras un batch de segments texte avec leur contexte dramatique.
Ta tache est d'inserer des balises de prosodie inline dans le texte.

## Balises disponibles (22 tags)

Modes vocaux : [whisper] [shout] [scream]
Affect : [cold] [warm] [onctuous] [indignant] [mocking] [angry] [sad] [nervous] [excited] [gentle] [firm] [timid]
Non-verbal : [laugh] [sigh] [sob] [gasp] [breath]
Tempo : [slow] [fast] [pause]

## Regles de placement

1. Tags mode vocale ([whisper], [shout]) AVANT la clause affectee
2. Tags affect ([cold], [onctuous], etc.) AU DEBUT du segment
3. [pause] inline n'importe ou pour marquer un silence dramatique
4. Non-verbal ([sob], [sigh], [gasp]) au point exact du battement emotionnel
5. Maximum {max_tags} tags par segment
6. Certains segments ne necessitent AUCUN tag (narration neutre)

## Format de reponse

Pour chaque segment, retourne un objet JSON avec :
- seg_index : int (doit correspondre)
- type : "narration" | "dialogue" | "thought"
- speaker : nom canonique du locuteur
- text : texte original SANS modification
- annotated_text : texte avec balises [tag] inserees

Exemple :
  text: "Je ne peux pas accepter cela."
  annotated_text: "[firm] Je ne peux pas accepter cela. [pause] Jamais."

IMPORTANT : annotated_text doit contenir le MEME texte que text, avec seulement
des balises [tag] inserees. Ne pas modifier, traduire ou resumer le texte.
""".format(max_tags=MAX_TAGS_PER_SEGMENT)


USER_PROMPT_TEMPLATE = """## Segments a annoter (batch {batch_idx})

{segments_block}

Annote chaque segment avec les balises prosodiques appropriees.
Respecte les regles de placement et le maximum de {max_tags} tags par segment.
Retourne un objet JSON avec la cle "segments" contenant la liste des segments annotes."""


# ── Helper functions ──


def load_inputs() -> tuple[list[Segment], dict[int, DramaticContext]]:
    """Load segments and dramatic context from pipeline outputs.

    Returns:
        Tuple of (segments list, dramatic context dict keyed by seg_index).

    Raises:
        FileNotFoundError: If required input files are missing.
    """
    if not INPUT_SEGMENTS.exists():
        raise FileNotFoundError(
            f"segments_v4.json introuvable : {INPUT_SEGMENTS}\n"
            "Lancez d'abord la phase P2 (segmentation)."
        )
    if not INPUT_DRAMATIC.exists():
        raise FileNotFoundError(
            f"dramatic_context.json introuvable : {INPUT_DRAMATIC}\n"
            "Lancez d'abord la phase P3 (dramatic context)."
        )

    seg_data = json.loads(INPUT_SEGMENTS.read_text(encoding="utf-8"))
    segments = [Segment(**s) for s in seg_data.get("segments", seg_data) if isinstance(seg_data, dict)]

    # Handle both list and dict root
    if isinstance(seg_data, list):
        segments = [Segment(**s) for s in seg_data]
    elif "segments" in seg_data:
        segments = [Segment(**s) for s in seg_data["segments"]]

    ctx_data = json.loads(INPUT_DRAMATIC.read_text(encoding="utf-8"))
    if isinstance(ctx_data, dict) and "contexts" in ctx_data:
        contexts_list = [DramaticContext(**c) for c in ctx_data["contexts"]]
    elif isinstance(ctx_data, list):
        contexts_list = [DramaticContext(**c) for c in ctx_data]
    else:
        contexts_list = []

    contexts_by_idx = {c.seg_index: c for c in contexts_list}

    print(f"  Loaded {len(segments)} segments, {len(contexts_by_idx)} dramatic contexts")
    return segments, contexts_by_idx


def build_segment_block(segments: list[Segment], contexts: dict[int, DramaticContext]) -> str:
    """Format a batch of segments with their dramatic context for the LLM prompt.

    Args:
        segments: The segments in this batch.
        contexts: Dramatic context dict keyed by seg_index.

    Returns:
        Formatted text block for the user prompt.
    """
    lines: list[str] = []
    for seg in segments:
        ctx = contexts.get(seg.seg_index)
        lines.append(f"### Segment {seg.seg_index}")
        lines.append(f"Type: {seg.type} | Locuteur: {seg.speaker}")
        if ctx:
            lines.append(
                f"Contexte: {ctx.scene_label} | Acte: {ctx.act} | "
                f"Tension: {ctx.tension_0_10}/10 | Position: {ctx.narrative_position}"
            )
            if ctx.character_state:
                states = ", ".join(f"{k}: {v}" for k, v in ctx.character_state.items())
                lines.append(f"Etats emotionnels: {states}")
        lines.append(f"Texte: {seg.text}")
        lines.append("")
    return "\n".join(lines)


def annotate_batch(
    segments: list[Segment],
    contexts: dict[int, DramaticContext],
    batch_idx: int,
) -> list[AnnotatedSegment]:
    """Send a batch of segments to the LLM for prosodic annotation.

    Args:
        segments: Segments to annotate (typically 10).
        contexts: Dramatic context dict keyed by seg_index.
        batch_idx: Batch number (for logging).

    Returns:
        List of AnnotatedSegment instances.
    """
    start = segments[0].seg_index
    end = segments[-1].seg_index
    print(f"  [P4] Batch {batch_idx}: annotating segments {start}-{end} ({len(segments)} segments)")

    context_block = build_context_block("annotation", segment_range=(start, end))
    segments_block = build_segment_block(segments, contexts)
    user_prompt = USER_PROMPT_TEMPLATE.format(
        batch_idx=batch_idx,
        segments_block=segments_block,
        max_tags=MAX_TAGS_PER_SEGMENT,
    )

    result = call_structured(
        AnnotatedBatch,
        SYSTEM_PROMPT,
        user_prompt,
        context_block=context_block,
    )

    batch = AnnotatedBatch(**result)

    # Attach dramatic context references
    annotated: list[AnnotatedSegment] = []
    for seg in batch.segments:
        ctx = contexts.get(seg.seg_index)
        annotated.append(AnnotatedSegment(
            seg_index=seg.seg_index,
            type=seg.type,
            speaker=seg.speaker,
            text=seg.text,
            annotated_text=seg.annotated_text,
            tags_used=seg.tags_used,
            fishaudio_text=convert_tags_for_fishaudio(seg.annotated_text),
            dramatic_ref=ctx,
        ))

    tag_count = sum(len(s.tags_used) for s in annotated)
    tagged_segs = sum(1 for s in annotated if s.tags_used)
    print(f"    Tags: {tag_count} total, {tagged_segs}/{len(annotated)} segments tagged")

    return annotated


def convert_tags_for_fishaudio(annotated_text: str) -> str:
    """Convert bracket prosody tags to FishAudio-compatible inline format.

    Converts [tag] markers to parenthetical FishAudio directives:
    - [sob] -> (sobbing)
    - [gasp] -> (gasping)
    - [warm] -> (in a warm tone)
    - [pause] -> ...
    Unknown tags are left as-is.

    Args:
        annotated_text: Text with [tag] markers.

    Returns:
        Text with FishAudio-compatible directives.
    """
    def _replace_tag(match: re.Match) -> str:
        tag = match.group(1)
        return TAG_TO_FISHAUDIO.get(tag, match.group(0))

    return re.sub(r"\[(\w+)\]", _replace_tag, annotated_text)


# ── Main entry point ──


def run(force: bool = False) -> Path:
    """Run P4 -- prosodic annotation. Returns path to annotated_v4.json.

    Args:
        force: If True, re-run even if output already exists.

    Returns:
        Path to the generated annotated_v4.json file.
    """
    if OUTPUT_ANNOTATED.exists() and not force:
        print(f"[P4] Cached: {OUTPUT_ANNOTATED}")
        return OUTPUT_ANNOTATED

    print("[P4] Running prosodic annotation...")

    # Step 1: Load inputs
    print("[P4] Step 1: Loading segments and dramatic context...")
    segments, contexts = load_inputs()

    # Step 2: Batch annotation
    print(f"[P4] Step 2: Annotating {len(segments)} segments (batch size: {BATCH_SIZE})...")
    all_annotated: list[AnnotatedSegment] = []
    batch_count = 0

    for i in range(0, len(segments), BATCH_SIZE):
        batch = segments[i : i + BATCH_SIZE]
        batch_count += 1
        try:
            annotated = annotate_batch(batch, contexts, batch_count)
            all_annotated.extend(annotated)
        except Exception as e:
            print(f"  [P4] Batch {batch_count} FAILED: {e}")
            # Fallback: create untagged segments
            for seg in batch:
                all_annotated.append(AnnotatedSegment(
                    seg_index=seg.seg_index,
                    type=seg.type,
                    speaker=seg.speaker,
                    text=seg.text,
                    annotated_text=seg.text,
                    tags_used=[],
                    fishaudio_text=seg.text,
                    dramatic_ref=contexts.get(seg.seg_index),
                ))

    # Step 3: Sort by seg_index and save
    all_annotated.sort(key=lambda s: s.seg_index)
    batch_result = AnnotatedBatch(segments=all_annotated)

    OUTPUT_ANNOTATED.write_text(
        batch_result.model_dump_json(indent=2),
        encoding="utf-8",
    )

    total_tags = sum(len(s.tags_used) for s in all_annotated)
    tagged_segments = sum(1 for s in all_annotated if s.tags_used)
    print(f"[P4] Saved: {OUTPUT_ANNOTATED}")
    print(f"  Segments: {len(all_annotated)}")
    print(f"  Tagged: {tagged_segments}/{len(all_annotated)}")
    print(f"  Total tags: {total_tags}")
    print(f"  Batches: {batch_count}")

    return OUTPUT_ANNOTATED


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
