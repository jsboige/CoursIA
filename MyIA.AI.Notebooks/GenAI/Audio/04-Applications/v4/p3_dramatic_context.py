"""P3 -- Dramatic Context Builder for the v4 FishAudio audiobook pipeline.

Reads segments from P2 and assigns dramatic context to each segment:
act label, scene label, tension level, character emotional states,
and narrative position within the story arc.

Two-stage process:
  Stage 1 -- Scene calibration: map paragraphs to acts via one-shot LLM call.
  Stage 2 -- Per-segment context: batch 10 segments per LLM call, enriching
             each with dramatic context using the scene map and narrative
             knowledge from P0.

Output: outputs/dramatic_context.json
Cache:  outputs/p3_scene_map.json
"""
from __future__ import annotations

import json
from pathlib import Path

from dotenv import load_dotenv
from pydantic import BaseModel, Field

from .schemas import (
    Segment,
    SegmentBatch,
    DramaticContext,
    DramaticContextBatch,
    ActLabel,
    NarrativePosition,
)
from .llm_client import call_structured
from .context_injector import build_context_block

BASE_DIR = Path(__file__).parent
OUTPUTS = BASE_DIR / "outputs"
OUTPUTS.mkdir(exist_ok=True)

SEGMENTS_PATH = OUTPUTS / "segments_v4.json"
SCENE_MAP_PATH = OUTPUTS / "p3_scene_map.json"
DRAMATIC_CONTEXT_PATH = OUTPUTS / "dramatic_context.json"

BATCH_SIZE = 10

# ── Act tension defaults ──

ACT_TENSION_DEFAULTS: dict[ActLabel, int] = {
    "act1_diligence_aller": 3,
    "act2_auberge_jours": 5,
    "act3_pressing_collectif": 8,
    "act4_diligence_retour": 9,
}

ACT_DESCRIPTIONS: dict[ActLabel, str] = {
    "act1_diligence_aller": (
        "Le voyage aller en diligence. Solidarite forcee dans l'habitacle "
        "etroit. Atmosphere chaude et amicale malgre les differences de classe. "
        "Boule de Suif partage ses provisions. Tension basse, convivialite."
    ),
    "act2_auberge_jours": (
        "Les jours d'attente a l'auberge de Totes. L'officier prussien refuse "
        "de les laisser partir tant que Boule de Suif n'aura pas cede. "
        "L'impatience croit, la froideur s'installe progressivement."
    ),
    "act3_pressing_collectif": (
        "La pression collective pour convaincre Boule de Suif. Chacun utilise "
        "ses arguments : religion, patrie, charite, necessite. Manipulation "
        "onctueuse et collectivement orchestree."
    ),
    "act4_diligence_retour": (
        "Le voyage retour. Boule de Suif a cede mais est maintenant traitee "
        "avec mepris et exclusion par ceux-la meme qui l'ont poussee. "
        "Elle sanglote de rage et d'humiliation. Personne ne partage de nourriture."
    ),
}


# ── Intermediate schema for scene calibration ──


class SceneMapping(BaseModel):
    """Maps a single paragraph_id to an act label."""

    paragraph_id: int
    act: ActLabel
    reason: str = ""


class SceneMapResult(BaseModel):
    """LLM output for the scene calibration call."""

    mappings: list[SceneMapping]


# ── Stage 1: Scene calibration ──


def _load_segments() -> list[Segment]:
    """Load segments from P2 output."""
    if not SEGMENTS_PATH.exists():
        raise FileNotFoundError(
            f"segments_v4.json introuvable : {SEGMENTS_PATH}\n"
            "Lancez d'abord la phase P2 (segmentation) pour le generer."
        )
    data = json.loads(SEGMENTS_PATH.read_text(encoding="utf-8"))
    batch = SegmentBatch.model_validate(data)
    return batch.segments


def _build_paragraph_representations(segments: list[Segment]) -> dict[int, str]:
    """Build one representative text string per paragraph_id.

    Each paragraph is represented by concatenating the text of all its
    segments, truncated to ~200 chars so the LLM can process them all
    in a single call.
    """
    paragraphs: dict[int, list[str]] = {}
    for seg in segments:
        paragraphs.setdefault(seg.paragraph_id, []).append(seg.text)

    representations: dict[int, str] = {}
    for pid, texts in sorted(paragraphs.items()):
        combined = " ".join(texts)
        if len(combined) > 200:
            combined = combined[:197] + "..."
        representations[pid] = combined
    return representations


def calibrate_scenes(
    segments: list[Segment],
    force: bool = False,
) -> dict[int, ActLabel]:
    """Stage 1: map each paragraph to an act via one-shot LLM call.

    Returns a dict mapping paragraph_id -> ActLabel.
    """
    if SCENE_MAP_PATH.exists() and not force:
        print(f"  [P3] Cached scene map: {SCENE_MAP_PATH}")
        cached = json.loads(SCENE_MAP_PATH.read_text(encoding="utf-8"))
        return {int(k): v for k, v in cached.items()}

    print("  [P3] Stage 1: Scene calibration (one-shot LLM)...")

    representations = _build_paragraph_representations(segments)
    paragraphs_text = "\n".join(
        f"  [P{pid}] {text}"
        for pid, text in sorted(representations.items())
    )

    act_descriptions = "\n".join(
        f"  - {label}: {desc}"
        for label, desc in ACT_DESCRIPTIONS.items()
    )

    context_block = build_context_block("dramatic_context")

    system = (
        "Tu es un expert en analyse dramatique d'oeuvres litteraires francaises. "
        "Tu vas mapper chaque paragraphe de 'Boule de Suif' de Maupassant "
        "a l'un des 4 actes de la structure dramatique."
    )

    user = (
        f"Voici les paragraphes de 'Boule de Suif' (identifies par [Pn]):\n\n"
        f"{paragraphs_text}\n\n"
        f"Structure en 4 actes:\n{act_descriptions}\n\n"
        "Pour chaque paragraphe, indique a quel acte il appartient et pourquoi. "
        "Sois precis et coherent avec la progression narrative."
    )

    result = call_structured(
        SceneMapResult,
        system,
        user,
        context_block=context_block,
    )

    scene_map = {m["paragraph_id"]: m["act"] for m in result.get("mappings", [])}

    # Fill any gaps: assign segments without a mapping to the nearest mapped paragraph
    all_pids = sorted(set(seg.paragraph_id for seg in segments))
    mapped_pids = sorted(scene_map.keys())
    if mapped_pids:
        for pid in all_pids:
            if pid not in scene_map:
                nearest = min(mapped_pids, key=lambda m: abs(m - pid))
                scene_map[pid] = scene_map[nearest]

    # Cache
    SCENE_MAP_PATH.write_text(
        json.dumps({str(k): v for k, v in sorted(scene_map.items())}, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"  [P3] Scene map saved: {SCENE_MAP_PATH} ({len(scene_map)} paragraphs)")

    return scene_map


# ── Stage 2: Per-segment dramatic context ──


class _BatchContextResult(BaseModel):
    """LLM output schema for a single batch of segments."""

    contexts: list[DramaticContext]


def _build_batch_prompt(
    batch_segments: list[Segment],
    scene_map: dict[int, ActLabel],
    prior_context_summary: str,
) -> tuple[str, str]:
    """Build the system and user prompts for a batch of segments."""
    segments_text = "\n".join(
        f"  [S{seg.seg_index}] (P{seg.paragraph_id}, {seg.speaker}, {seg.type}): {seg.text}"
        for seg in batch_segments
    )

    batch_pids = sorted(set(seg.paragraph_id for seg in batch_segments))
    batch_acts = {scene_map.get(pid, "act1_diligence_aller") for pid in batch_pids}

    act_hints = "\n".join(
        f"  - {label}: tension de base {ACT_TENSION_DEFAULTS.get(label, 5)}/10"
        for label in sorted(batch_acts)
    )

    system = (
        "Tu es un expert en dramaturgie et analyse emotionnelle de textes litteraires. "
        "Pour chaque segment de texte, tu dois determiner:\n"
        "1. L'acte auquel il appartient (deja calibre, utilise la carte fournie)\n"
        "2. Un label de scene descriptif court (ex: 'partage_provisions', "
        "'attente_auberge_j2', 'plaidoyer_comte', 'sanglots_retour')\n"
        "3. Le niveau de tension (0-10, coherent avec l'acte mais nuance par le contenu)\n"
        "4. L'etat emotionnel de chaque personnage present dans le segment\n"
        "5. La position narrative (exposition, rising, climax, falling, resolution)\n"
        "6. Un 'prompt dramatique' : 1-2 phrases decrivant le contexte emotionnel, "
        "comme si tu parlais a un acteur. Ex: 'Boule de Suif, tremblante, est invitee "
        "a monter. Silence glacial.'\n"
        "7. 3-5 mots-cles emotionnels (ex: ['humiliation', 'silence', 'isolement'])\n\n"
        "IMPORTANT: character_state doit contenir une entree pour chaque personnage "
        "qui parle ou est mentionne dans le segment, mappee a une emotion concise."
    )

    prior_section = ""
    if prior_context_summary:
        prior_section = (
            f"\nContexte des segments precedents:\n{prior_context_summary}\n"
        )

    user = (
        f"Segments a analyser:\n{segments_text}\n\n"
        f"Actes correspondants pour ces paragraphes:\n{act_hints}\n"
        f"{prior_section}"
        "Pour chaque segment, fournis le contexte dramatique complet, "
        "INCLUANT le dramatic_prompt (1-2 phrases pour un acteur) et "
        "les emotional_keywords (3-5 mots-cles)."
    )

    return system, user


def _summarize_batch(contexts: list[DramaticContext], max_tokens: int = 500) -> str:
    """Build a compact summary of a batch for use as rolling context.

    Includes dramatic_prompt and emotional_keywords for downstream context.
    """
    lines: list[str] = []
    for ctx in contexts:
        chars_str = ", ".join(f"{k}={v}" for k, v in ctx.character_state.items())
        prompt_str = f" | Dramatic: {ctx.dramatic_prompt}" if ctx.dramatic_prompt else ""
        kw_str = f" | Keywords: {', '.join(ctx.emotional_keywords)}" if ctx.emotional_keywords else ""
        lines.append(
            f"S{ctx.seg_index}: {ctx.act}/{ctx.scene_label} "
            f"T={ctx.tension_0_10} {ctx.narrative_position} [{chars_str}]{prompt_str}{kw_str}"
        )

    summary = "\n".join(lines)

    # Truncate if too long (approx 4 chars per token for French)
    max_chars = max_tokens * 4
    if len(summary) > max_chars:
        # Keep the most recent entries
        while len(summary) > max_chars and lines:
            lines.pop(0)
            summary = "\n".join(lines)

    return summary


def build_dramatic_context(
    segments: list[Segment],
    scene_map: dict[int, ActLabel],
) -> DramaticContextBatch:
    """Stage 2: assign dramatic context to each segment via batched LLM calls."""
    print(f"  [P3] Stage 2: Per-segment context ({len(segments)} segments, "
          f"batches of {BATCH_SIZE})...")

    context_block = build_context_block("dramatic_context")
    all_contexts: list[DramaticContext] = []
    prior_context_summary = ""

    for batch_start in range(0, len(segments), BATCH_SIZE):
        batch_end = min(batch_start + BATCH_SIZE, len(segments))
        batch_segments = segments[batch_start:batch_end]
        batch_num = batch_start // BATCH_SIZE + 1
        total_batches = (len(segments) + BATCH_SIZE - 1) // BATCH_SIZE

        print(f"    Batch {batch_num}/{total_batches}: "
              f"segments {batch_segments[0].seg_index}-{batch_segments[-1].seg_index}")

        system, user = _build_batch_prompt(
            batch_segments, scene_map, prior_context_summary,
        )

        try:
            result = call_structured(
                _BatchContextResult,
                system,
                user,
                context_block=context_block,
            )
            batch_contexts = [
                DramaticContext(**c) for c in result.get("contexts", [])
            ]
        except Exception as exc:
            print(f"    WARNING: LLM call failed for batch {batch_num}: {exc}")
            print(f"    Using act-based defaults for segments "
                  f"{batch_segments[0].seg_index}-{batch_segments[-1].seg_index}")
            batch_contexts = _fallback_contexts(batch_segments, scene_map)

        # Ensure we have one context per segment
        if len(batch_contexts) != len(batch_segments):
            print(f"    WARNING: Expected {len(batch_segments)} contexts, "
                  f"got {len(batch_contexts)}. Padding with defaults.")
            existing_indices = {c.seg_index for c in batch_contexts}
            for seg in batch_segments:
                if seg.seg_index not in existing_indices:
                    batch_contexts.append(
                        _default_context(seg, scene_map),
                    )

        all_contexts.extend(batch_contexts)
        prior_context_summary = _summarize_batch(batch_contexts)

    # Sort by seg_index for deterministic output
    all_contexts.sort(key=lambda c: c.seg_index)

    return DramaticContextBatch(contexts=all_contexts)


# ── Fallback helpers ──


def _fallback_contexts(
    segments: list[Segment],
    scene_map: dict[int, ActLabel],
) -> list[DramaticContext]:
    """Generate default contexts when the LLM call fails."""
    return [_default_context(seg, scene_map) for seg in segments]


def _default_context(seg: Segment, scene_map: dict[int, ActLabel]) -> DramaticContext:
    """Build a single default DramaticContext from segment + scene map."""
    act = scene_map.get(seg.paragraph_id, "act1_diligence_aller")
    tension = ACT_TENSION_DEFAULTS.get(act, 5)
    return DramaticContext(
        seg_index=seg.seg_index,
        act=act,
        scene_label=f"seg_{seg.seg_index:03d}",
        tension_0_10=tension,
        character_state={seg.speaker: "neutral"},
        narrative_position="rising",
        dramatic_prompt="",
        emotional_keywords=[],
    )


# ── Main entry point ──


def run(force: bool = False) -> Path:
    """Run P3 -- dramatic context builder. Returns path to dramatic_context.json."""
    if DRAMATIC_CONTEXT_PATH.exists() and not force:
        print(f"[P3] Cached: {DRAMATIC_CONTEXT_PATH}")
        return DRAMATIC_CONTEXT_PATH

    print("[P3] Running dramatic context builder...")

    # Load segments from P2
    print("[P3] Loading segments from P2...")
    segments = _load_segments()
    print(f"  Loaded {len(segments)} segments")

    # Stage 1: Scene calibration
    print("[P3] Stage 1: Scene calibration...")
    scene_map = calibrate_scenes(segments, force=force)
    print(f"  Mapped {len(scene_map)} paragraphs to acts")

    # Stage 2: Per-segment dramatic context
    print("[P3] Stage 2: Per-segment dramatic context...")
    result = build_dramatic_context(segments, scene_map)

    # Save
    DRAMATIC_CONTEXT_PATH.write_text(
        result.model_dump_json(indent=2),
        encoding="utf-8",
    )

    # Summary
    act_counts: dict[str, int] = {}
    for ctx in result.contexts:
        act_counts[ctx.act] = act_counts.get(ctx.act, 0) + 1

    avg_tension = (
        sum(c.tension_0_10 for c in result.contexts) / len(result.contexts)
        if result.contexts
        else 0.0
    )

    print(f"[P3] Saved: {DRAMATIC_CONTEXT_PATH}")
    print(f"  Segments: {len(result.contexts)}")
    print(f"  Act distribution: {act_counts}")
    print(f"  Average tension: {avg_tension:.1f}/10")

    return DRAMATIC_CONTEXT_PATH


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
