"""Pydantic v2 schemas for the v4 FishAudio audiobook pipeline.

Single source of truth for all data models used across P0-P7.
"""
from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, Field, model_validator


# ── Canonical speaker enum ──

CanonicalSpeaker = Literal[
    "narrateur", "elisabeth_rousset", "loiseau", "madame_loiseau",
    "comte", "comtesse", "cornudet", "carre_lamadon",
    "madame_carre_lamadon", "soeurs", "follenvie", "madame_follenvie",
    "officier", "figurant",
]

SegmentType = Literal["narration", "dialogue", "thought"]

ActLabel = Literal["act1_diligence_aller", "act2_auberge_jours", "act3_pressing_collectif", "act4_diligence_retour"]

NarrativePosition = Literal["exposition", "rising", "climax", "falling", "resolution"]

# FishAudio S2-Pro inline tags — official well-tested set from
# https://fish.audio/fr/blog/how-to-use-inline-tags-in-fish-audio-s2/
#
# S2-Pro also accepts free-form natural language in [brackets] (e.g.
# "[speaking slowly, almost hesitant]"), but the tags below are the
# officially tested ones that produce consistent results.
# The LLM may use free-form descriptions not in this set.
ProsodyTag = Literal[
    # Breathing & vocal reactions
    "clears throat", "inhale", "inhalation", "exhale", "sigh",
    "panting", "breathing", "gasp",
    # Vocal sounds
    "groan", "moaning", "sobbing", "crying", "laughing",
    "chuckling", "giggle",
    # Pacing
    "pause", "short pause", "long pause",
    # Voice style
    "whispering", "whispering voice", "soft voice", "low voice",
    "loud voice", "shouting",
    # Emotion (3 officially tested; free-form accepted for more)
    "excited", "angry", "sad",
    # Other
    "emphasis", "rustling sound",
]

ALL_PROSODY_TAGS: set[str] = set(ProsodyTag.__args__)  # type: ignore[attr-defined]


# ── P0: Narrative Research ──

class ActDefinition(BaseModel):
    label: str
    description: str
    default_tension: int = Field(ge=0, le=10)
    dominant_emotions: list[str]


class CharacterProfile(BaseModel):
    name: str
    aliases: list[str]
    traits: list[str]
    voice_register: str
    emotional_arc: dict[str, str]
    prosody_defaults: list[str]
    relationships: dict[str, str]


class NarrativeContext(BaseModel):
    title: str
    author: str
    historical_context: str
    themes: list[str]
    narrative_technique: str
    acts: dict[str, ActDefinition]
    characters: dict[str, CharacterProfile]
    prosody_guidance: dict[str, str]
    source_urls: list[str]


class SourceSelectionItem(BaseModel):
    url: str
    reason: str
    relevance_score: int = Field(ge=1, le=10)


class SourceSelection(BaseModel):
    selected: list[SourceSelectionItem]


# ── P1: Voice Cloning ──

class VoiceReference(BaseModel):
    reference_id: str
    speakers: list[str]
    register: str
    sample_text: str
    sample_mp3_path: str = ""
    status: str = "pending"


# ── P1.5: Speaker Catalog ──

class SpeakerAppearance(BaseModel):
    paragraph_id: int
    context_snippet: str = ""
    is_direct_speech: bool = False
    emotion_hint: str = ""


class FigurantProfile(BaseModel):
    raw_name: str
    canonical: CanonicalSpeaker = "figurant"
    voice_archetype: str = "male_gruff"
    first_paragraph: int = 0
    total_appearances: int = 1
    appearances: list[SpeakerAppearance] = Field(default_factory=list)
    description: str = ""
    relationships: dict[str, str] = Field(default_factory=dict)


class SpeakerCatalog(BaseModel):
    canonical_speakers: dict[str, CharacterProfile] = Field(default_factory=dict)
    figurants: list[FigurantProfile] = Field(default_factory=list)
    figurant_voice_map: dict[str, str] = Field(default_factory=dict)
    total_speakers: int = 0
    total_dialogue_segments: int = 0


# ── P2: Segmentation ──

class Segment(BaseModel):
    seg_index: int
    type: SegmentType
    speaker_raw: str
    speaker: CanonicalSpeaker
    text: str = Field(min_length=3)
    paragraph_id: int

    @model_validator(mode="after")
    def dialogue_cannot_be_narrateur(self) -> "Segment":
        if self.type == "dialogue" and self.speaker == "narrateur":
            raise ValueError(f"Segment {self.seg_index}: dialogue cannot have speaker='narrateur'")
        return self


class SegmentBatch(BaseModel):
    segments: list[Segment]


# ── P3: Dramatic Context ──

class DramaticContext(BaseModel):
    seg_index: int
    act: ActLabel
    scene_label: str
    tension_0_10: int = Field(ge=0, le=10)
    character_state: dict[str, str]
    narrative_position: NarrativePosition
    dramatic_prompt: str = ""
    emotional_keywords: list[str] = Field(default_factory=list)


class DramaticContextBatch(BaseModel):
    contexts: list[DramaticContext]


# ── P4: Prosodic Annotation ──

class AnnotatedSegment(BaseModel):
    seg_index: int
    type: SegmentType
    speaker: CanonicalSpeaker
    speaker_raw: str = ""
    text: str
    annotated_text: str
    prosody_tags: list[ProsodyTag] = Field(
        default_factory=list,
        description="Official S2-Pro tags chosen from the supported set. Max 3 per segment.",
    )
    tags_used: list[str] = Field(
        default_factory=list,
        description="All tags extracted from annotated_text (official + free-form).",
    )
    fishaudio_text: str = ""
    dramatic_ref: DramaticContext | None = None
    dramatic_prompt: str = ""
    tts_context_prefix: str = ""

    @model_validator(mode="after")
    def verify_tags_consistency(self) -> "AnnotatedSegment":
        found = set(re.findall(r"\[([^\]]+)\]", self.annotated_text))
        known = found & ALL_PROSODY_TAGS
        self.tags_used = sorted(found)
        return self


class AnnotatedBatch(BaseModel):
    segments: list[AnnotatedSegment]


# ── P5: TTS Generation ──

class TTSResult(BaseModel):
    seg_index: int
    speaker: CanonicalSpeaker
    reference_id: str
    mp3_path: str
    duration_s: float = 0.0
    seed: int = 0
    status: str = "pending"
    whisper_wer: float = -1.0
    attempts: int = 0


# ── P7: Quality Verification ──

class DiarizedSegment(BaseModel):
    speaker: str
    start: float
    end: float
    text: str


class DiarizationResult(BaseModel):
    seg_index: int
    mp3_path: str
    detected_speakers: list[str]
    segments: list[DiarizedSegment]
    speaker_count: int
    dominant_speaker: str = ""
    elapsed_s: float = 0.0
    error: str = ""


class QualityReport(BaseModel):
    wer: dict[str, float]
    diarization: dict[str, int | float]
    verdict: Literal["PASS", "NEEDS_REVIEW"]
