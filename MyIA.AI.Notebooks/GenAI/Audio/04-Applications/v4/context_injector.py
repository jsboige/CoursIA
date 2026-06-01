"""Context injector for the v4 FishAudio audiobook pipeline.

Loads narrative_context.json once and builds per-phase context blocks
that are injected into every downstream LLM call.
"""
from __future__ import annotations

from pathlib import Path

from .schemas import (
    CanonicalSpeaker,
    DramaticContext,
    NarrativeContext,
    SpeakerCatalog,
)

_V4_DIR = Path(__file__).resolve().parent
_DEFAULT_PATH = _V4_DIR / "outputs" / "narrative_context.json"

_cached_context: NarrativeContext | None = None


# ── Public API ──


def load_narrative_context(path: str | Path | None = None) -> NarrativeContext:
    """Load and cache the narrative context JSON.

    Args:
        path: Override path to narrative_context.json.
              Defaults to ``v4/outputs/narrative_context.json``.

    Returns:
        Parsed NarrativeContext instance.

    Raises:
        FileNotFoundError: If the JSON file does not exist.
    """
    global _cached_context
    if _cached_context is not None:
        return _cached_context

    resolved = Path(path) if path is not None else _DEFAULT_PATH
    if not resolved.exists():
        raise FileNotFoundError(
            f"narrative_context.json introuvable : {resolved}\n"
            "Lancez d'abord la phase P0 (recherche narrative) pour le generer."
        )

    _cached_context = NarrativeContext.model_validate_json(resolved.read_text(encoding="utf-8"))
    return _cached_context


def build_context_block(
    phase: str,
    segment_range: tuple[int, int] | None = None,
    extra: str = "",
) -> str:
    """Build a French context block tailored to the requested pipeline phase.

    Args:
        phase: One of ``segmentation``, ``dramatic_context``,
               ``annotation``, ``voice_cloning``.
        segment_range: ``(start_idx, end_idx)`` for batch-aware context.
        extra: Arbitrary additional context appended at the end.

    Returns:
        A ~200-500 token French text block for LLM system prompts.
    """
    ctx = load_narrative_context()
    parts: list[str] = [_header_block(ctx)]

    if phase == "segmentation":
        parts.append(_format_character_list(ctx.characters))
    elif phase == "dramatic_context":
        parts.append(_format_act_structure(ctx.acts))
        parts.append(_format_character_emotions(ctx.characters, segment_range))
    elif phase == "annotation":
        parts.append(_format_prosody_guidance(ctx.prosody_guidance))
        if segment_range:
            parts.append(_format_character_emotions(ctx.characters, segment_range))
    elif phase == "voice_cloning":
        parts.append(_format_voice_registers(ctx.characters))
    else:
        raise ValueError(f"Phase inconnue : {phase!r}")

    if extra:
        parts.append(extra.strip())

    return "\n\n".join(parts)


# ── Header ──


def _header_block(ctx: NarrativeContext) -> str:
    themes = ", ".join(ctx.themes)
    return (
        f"## Oeuvre\n"
        f"Titre : {ctx.title} — Auteur : {ctx.author}\n"
        f"Contexte historique : {ctx.historical_context}\n"
        f"Themes : {themes}\n"
        f"Technique narrative : {ctx.narrative_technique}"
    )


# ── Helpers ──


def _format_character_list(characters: dict) -> str:
    """Format every character with aliases and relationships."""
    lines = ["## Personnages"]
    for _key, char in characters.items():
        aliases = f" (alias : {', '.join(char.aliases)})" if char.aliases else ""
        lines.append(f"- **{char.name}**{aliases} : {' ; '.join(char.traits)}")
        if char.relationships:
            for target, relation in char.relationships.items():
                lines.append(f"  - {relation} -> {target}")
    return "\n".join(lines)


def _format_act_structure(acts: dict) -> str:
    """Format the 4-act structure with tension baselines."""
    lines = ["## Structure dramatique (4 actes)"]
    for label, act in acts.items():
        lines.append(
            f"### {act.label}\n"
            f"{act.description}\n"
            f"Tension de base : {act.default_tension}/10 — "
            f"Emotions dominantes : {', '.join(act.dominant_emotions)}"
        )
    return "\n".join(lines)


def _format_prosody_guidance(guidance: dict) -> str:
    """Format emotion-to-prosody-tag mappings."""
    lines = ["## Guide prosodique"]
    lines.append("Correspondance emotion -> tag FishAudio :")
    for emotion, tag in guidance.items():
        lines.append(f"- {emotion} -> [{tag}]")
    return "\n".join(lines)


def _format_character_emotions(characters: dict, segment_range: tuple | None) -> str:
    """Character emotional state relevant to the given segment range."""
    if segment_range is None:
        return ""

    start, end = segment_range
    lines = [f"## Etats emotionnels (segments {start}-{end})"]
    for _key, char in characters.items():
        matching = {
            k: v for k, v in char.emotional_arc.items()
            if any(f"seg_{i}" == k or str(i) in k for i in range(start, end + 1))
        }
        if matching:
            states = ", ".join(f"{k}: {v}" for k, v in matching.items())
            lines.append(f"- {char.name} : {states}")
        else:
            prosody = ", ".join(char.prosody_defaults)
            lines.append(f"- {char.name} (defaut) : {prosody}")
    return "\n".join(lines)


def _format_voice_registers(characters: dict) -> str:
    """Format character voice registers and emotional arcs for cloning."""
    lines = ["## Registres vocaux"]
    for _key, char in characters.items():
        traits = ", ".join(char.traits)
        lines.append(
            f"### {char.name}\n"
            f"Registre : {char.voice_register}\n"
            f"Traits : {traits}\n"
            f"Prosodie par defaut : {', '.join(char.prosody_defaults)}"
        )
        if char.emotional_arc:
            arcs = "; ".join(f"{k} -> {v}" for k, v in char.emotional_arc.items())
            lines.append(f"Arc emotionnel : {arcs}")
    return "\n".join(lines)


# ── Per-segment context builder ──

_cached_catalog: SpeakerCatalog | None = None


def _load_catalog(path: str | Path | None = None) -> SpeakerCatalog | None:
    """Load speaker catalog if available, return None if not."""
    global _cached_catalog
    if _cached_catalog is not None:
        return _cached_catalog

    resolved = Path(path) if path is not None else _V4_DIR / "outputs" / "speaker_catalog.json"
    if not resolved.exists():
        return None

    _cached_catalog = SpeakerCatalog.model_validate_json(
        resolved.read_text(encoding="utf-8")
    )
    return _cached_catalog


def build_segment_context(
    phase: str,
    seg_index: int,
    dramatic_context: DramaticContext | None = None,
    speaker_catalog: SpeakerCatalog | None = None,
    speaker: CanonicalSpeaker | None = None,
    prior_summary: str = "",
    extra: str = "",
) -> str:
    """Build a per-segment context block for downstream LLM calls.

    This is the core "semantic-kernel plugin" that composes context from
    multiple sources: narrative context, dramatic context, speaker profile,
    and prior segment summary.

    Args:
        phase: Current pipeline phase (segmentation, dramatic_context, annotation).
        seg_index: Segment index for context scoping.
        dramatic_context: P3 dramatic context for this segment (if available).
        speaker_catalog: P1.5 speaker catalog (if available).
        speaker: Canonical speaker for this segment.
        prior_summary: Rolling summary from previous segments.
        extra: Arbitrary additional context.

    Returns:
        A structured context block (~200-400 tokens) for LLM system prompts.
    """
    ctx = load_narrative_context()
    parts: list[str] = [_header_block(ctx)]

    # Phase-specific guidance
    if phase == "segmentation":
        parts.append(_format_character_list(ctx.characters))
        catalog = speaker_catalog or _load_catalog()
        if catalog and catalog.figurants:
            parts.append(_format_figurant_list(catalog))
    elif phase == "dramatic_context":
        parts.append(_format_act_structure(ctx.acts))
    elif phase == "annotation":
        parts.append(_format_prosody_guidance(ctx.prosody_guidance))

    # Dramatic context for this segment
    if dramatic_context:
        parts.append(_format_dramatic_context(dramatic_context))

    # Speaker profile
    if speaker and speaker != "narrateur":
        catalog = speaker_catalog or _load_catalog()
        parts.append(_format_speaker_profile(speaker, ctx.characters, catalog))

    # Prior context
    if prior_summary:
        parts.append(f"## Contexte precedent\n{prior_summary}")

    if extra:
        parts.append(extra.strip())

    return "\n\n".join(parts)


def _format_figurant_list(catalog: SpeakerCatalog) -> str:
    """Format figurant speakers with descriptions and voice archetypes."""
    lines = ["## Figurants identifies"]
    for fig in catalog.figurants:
        lines.append(
            f"- **{fig.raw_name}** (archetype: {fig.voice_archetype}, "
            f"{fig.total_appearances} apparitions)"
        )
        if fig.description:
            lines.append(f"  {fig.description}")
    return "\n".join(lines)


def _format_dramatic_context(dc: DramaticContext) -> str:
    """Format dramatic context for a specific segment."""
    lines = [
        f"## Contexte dramatique (segment {dc.seg_index})",
        f"Acte : {dc.act} | Scene : {dc.scene_label}",
        f"Tension : {dc.tension_0_10}/10 | Position : {dc.narrative_position}",
    ]
    if dc.dramatic_prompt:
        lines.append(f"Prompt dramatique : {dc.dramatic_prompt}")
    if dc.emotional_keywords:
        lines.append(f"Mots-cles emotionnels : {', '.join(dc.emotional_keywords)}")
    if dc.character_state:
        states = ", ".join(f"{k}: {v}" for k, v in dc.character_state.items())
        lines.append(f"Etats personnages : {states}")
    return "\n".join(lines)


def _format_speaker_profile(
    speaker: CanonicalSpeaker,
    characters: dict,
    catalog: SpeakerCatalog | None = None,
) -> str:
    """Format the speaker profile for context injection."""
    lines = [f"## Locuteur : {speaker}"]

    char = characters.get(speaker)
    if char:
        lines.append(f"Traits : {', '.join(char.traits)}")
        lines.append(f"Registre vocal : {char.voice_register}")
        if char.prosody_defaults:
            lines.append(f"Prosodie par defaut : {', '.join(char.prosody_defaults)}")
        if char.relationships:
            for target, relation in char.relationships.items():
                lines.append(f"  {relation} -> {target}")
    elif speaker == "figurant" and catalog:
        lines.append("Figurant — profil generique")
        archetypes = set(f.voice_archetype for f in catalog.figurants)
        lines.append(f"Archetypes disponibles : {', '.join(sorted(archetypes))}")

    return "\n".join(lines)
