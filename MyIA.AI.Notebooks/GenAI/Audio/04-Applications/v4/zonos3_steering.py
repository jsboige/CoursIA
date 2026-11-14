"""ZONOS3 steering resolver — annotation sidecar -> generation payload.

The v4 pipeline annotates prosody with **FishAudio bracket tags**
(``p4_annotation.py:436`` ``convert_tags_for_fishaudio``): a discrete,
flat tag vocabulary carried inline in the text.  ZONOS3 consumes
something else: **measured direction vectors** with a continuous dose,
applied through the ``controls`` map of ``POST /v2/generate``
(``{"mood.valence": 3.2, "mood.arousal": 3.2}``), optionally restricted
to a **span** of the text via ``control_spans``.

This module is the seam between the two:

1. the **annotation sidecar** (see :mod:`v4.schemas`) records, per
   segment and per span, the *intent* in clear language plus the
   ``axis`` / ``value`` pair that expresses it;
2. this resolver turns that sidecar into a ``controls`` payload for
   the request, **and degrades honestly** when the served checkpoint
   does not expose the requested direction: an unserved axis falls
   back to its FishAudio tag equivalent (the ``fallback_tag`` field),
   it is never silently dropped and never invented.

Why this is a resolver and not a pass-through: the axis names the
pipeline reasons about (``arousal``, ``pace``, ``projection``) are
**semantic**, while the direction names the runtime serves
(``mood.arousal``, ``mood.tempo``, ``mood.loudness``) are **bundle
dependent** — the served set is read from ``GET /v2/controls`` at
runtime.  The mapping below is the *declared* correspondence between
the two, and every mapping is checked against what the server says it
serves before it is used.
"""
from __future__ import annotations

import logging
import re
from dataclasses import dataclass, field

from .schemas import Zonos3Annotation

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Axis -> served direction correspondence
# ---------------------------------------------------------------------------
# The pipeline reasons in semantic axes; the runtime serves measured
# directions whose names depend on the loaded steering bundle.  The
# ``mood`` bundle (assets/steering/emotion_directions_mect60k_axes_x10/)
# folds the style directions into orthogonal conceptual axes: valence,
# arousal, dominance, loudness, tempo, clarity and articulation.
#
# Only axes with a *measured* counterpart are mapped.  An axis with no
# counterpart is not a failure: it degrades to its FishAudio tag.
#
# ``dose_scale`` maps the pipeline's normalized axis value (-1.0..1.0)
# onto the runtime's raw dose unit.  The runtime's usable window is
# narrow ("a style that responds at one dose"), so the scale is
# deliberately conservative: the pipeline value is a *target*, the
# dose is the measured magnitude that reaches it.
#
# Source: ZONOS3-Mini docs/guide.md, section "Steering controls"
# (read 2026-11-12).

@dataclass(frozen=True)
class AxisMapping:
    """Declared correspondence between a pipeline axis and a served direction."""

    axis: str
    direction: str
    dose_scale: float = 1.0
    fallback_tag: str = ""
    description: str = ""


#: Semantic axis -> served ZONOS3 direction.  The ``mood`` bundle is the
#: one shipped by default; a server serving another bundle will not
#: advertise these directions and the resolver will degrade.
AXIS_MAPPINGS: tuple[AxisMapping, ...] = (
    AxisMapping(
        axis="arousal",
        direction="mood.arousal",
        dose_scale=3.2,
        fallback_tag="excited",
        description="Activation / energie de la livraison",
    ),
    AxisMapping(
        axis="valence",
        direction="mood.valence",
        dose_scale=3.2,
        fallback_tag="happy",
        description="Polarite affective de la livraison",
    ),
    AxisMapping(
        axis="dominance",
        direction="mood.dominance",
        dose_scale=3.2,
        fallback_tag="angry",
        description="Assertivite de la livraison",
    ),
    AxisMapping(
        axis="pace",
        direction="mood.tempo",
        dose_scale=2.0,
        fallback_tag="pause",
        description="Debit — affecte aussi la nettete et le pitch",
    ),
    AxisMapping(
        axis="projection",
        direction="mood.loudness",
        dose_scale=3.0,
        fallback_tag="loud voice",
        description="Souffle, resonance, effort",
    ),
    AxisMapping(
        axis="clarity",
        direction="mood.clarity",
        dose_scale=2.0,
        fallback_tag="emphasis",
        description="Articulation et intelligibilite",
    ),
    AxisMapping(
        axis="liveliness",
        direction="mood.articulation",
        dose_scale=2.0,
        fallback_tag="chuckling",
        description="Vivacite de l'elocution",
    ),
)

AXIS_TO_DIRECTION: dict[str, AxisMapping] = {m.axis: m for m in AXIS_MAPPINGS}


# ---------------------------------------------------------------------------
# Resolution result
# ---------------------------------------------------------------------------

@dataclass
class SteeringResolution:
    """Outcome of resolving an annotation sidecar against a served bundle.

    Attributes
    ----------
    controls:
        The ``controls`` payload for ``POST /v2/generate`` — direction
        name -> raw dose.  Empty when nothing resolved.
    control_spans:
        The ``control_spans`` payload — direction name -> list of
        character ranges.  Empty when no span-scoped annotation.
    fallback_tags:
        FishAudio bracket tags to use for the axes that could NOT be
        steered.  This is the honest degradation path: the intent is
        still expressed, with the tag vocabulary the existing engine
        understands.
    degraded_axes:
        The semantic axes that were requested but not steered, with
        the reason.  Reported, never hidden.
    """

    controls: dict[str, float] = field(default_factory=dict)
    control_spans: dict[str, list[list[int]]] = field(default_factory=dict)
    fallback_tags: list[str] = field(default_factory=list)
    degraded_axes: list[tuple[str, str]] = field(default_factory=list)

    @property
    def is_degraded(self) -> bool:
        """True when at least one requested axis fell back to a tag."""
        return bool(self.degraded_axes)

    @property
    def has_steering(self) -> bool:
        """True when at least one axis was actually steered."""
        return bool(self.controls)


#: A signed number at the end of a string — ``"pace-2"``, ``"+1.5"``,
#: ``"1.5"``, ``"arousal-1.5"``.  Reads the raw-magnitude form of an axis
#: value (an optional axis name precedes the signed number).
_SIGNED_NUMBER_RE = re.compile(r"[+-]?\d+(?:\.\d+)?\s*$")
# The runtime reports these axes on a raw scale ~8x the pipeline's
# normalized [-1, 1] dose; this divisor maps a parsed raw magnitude back
# into the normalized range (see parse_axis_value).
_RUNTIME_AXIS_UNIT_SCALE = 8.0


def parse_axis_value(value: object) -> float | None:
    """Coerce an annotation ``value`` into a float dose in ``[-1, 1]``.

    Accepts a float (``0.5``), an int, or a string (``"+1.5"``,
    ``"pace-2"``).  Returns ``None`` when the value cannot be read as a
    number — the caller then treats the axis as not steerable rather
    than guessing a dose.
    """
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        return max(-1.0, min(1.0, float(value)))
    if isinstance(value, str):
        text = value.strip().lower()
        if not text:
            return None
        # "pace-2" / "lively+8" / "arousal-1.5": an optional axis name
        # precedes a signed raw magnitude in the runtime's own unit; a
        # leading form ("+1.5") and a bare number ("1.5") are the same
        # pattern with an empty prefix.
        match = _SIGNED_NUMBER_RE.search(text)
        if match is None:
            return None
        try:
            magnitude = float(match.group(0))
        except ValueError:
            return None
        # The runtime unit for these axes is an order of magnitude larger
        # than the pipeline's normalized value; the mapping's dose_scale
        # carries that conversion, so normalize here.
        return max(-1.0, min(1.0, magnitude / _RUNTIME_AXIS_UNIT_SCALE))
    return None


def served_directions(controls_index: dict | None) -> set[str]:
    """Extract the direction names a server actually serves.

    ``GET /v2/controls`` lists the sets and the directions they hold.
    The shape is read defensively: the runtime may nest the directions
    under a set name, or return a flat mapping.  Anything that is not
    recognized yields an empty set, which makes the resolver degrade
    every axis rather than invent a direction.
    """
    if not controls_index:
        return set()

    found: set[str] = set()

    def _collect(node: object) -> None:
        if isinstance(node, dict):
            for key, value in node.items():
                if isinstance(value, (dict, list)):
                    _collect(value)
                elif isinstance(key, str) and "." in key:
                    found.add(key)
        elif isinstance(node, list):
            for item in node:
                if isinstance(item, str) and "." in item:
                    found.add(item)
                else:
                    _collect(item)

    _collect(controls_index)
    return found


def resolve_steering(
    annotations: list,
    controls_index: dict | None = None,
) -> SteeringResolution:
    """Resolve an annotation sidecar into a ZONOS3 steering payload.

    Parameters
    ----------
    annotations:
        The sidecar entries (:class:`v4.schemas.Zonos3Annotation` or any
        object exposing ``axis``, ``value``, ``span_start``, ``span_end``).
    controls_index:
        The parsed ``GET /v2/controls`` payload.  When ``None`` the
        served directions are unknown, so **every** axis degrades to its
        fallback tag: the resolver never steers an axis it cannot
        verify as served.

    Returns
    -------
    SteeringResolution
        The controls payload, the span payload, the fallback tags and
        the list of degraded axes.
    """
    resolution = SteeringResolution()
    served = served_directions(controls_index)

    for annotation in annotations:
        axis = getattr(annotation, "axis", "") or ""
        if not axis:
            continue

        mapping = AXIS_TO_DIRECTION.get(axis)
        if mapping is None:
            resolution.degraded_axes.append((axis, "axe inconnu du mapping"))
            continue

        raw_value = getattr(annotation, "value", None)
        dose_ratio = parse_axis_value(raw_value)
        if dose_ratio is None:
            resolution.degraded_axes.append(
                (axis, f"valeur illisible: {raw_value!r}")
            )
            continue

        if served and mapping.direction not in served:
            resolution.degraded_axes.append(
                (axis, f"direction non servie: {mapping.direction}")
            )
            if mapping.fallback_tag:
                resolution.fallback_tags.append(mapping.fallback_tag)
            continue

        if not served:
            # The bundle could not be read: degrade rather than guess.
            resolution.degraded_axes.append(
                (axis, "bundle de steering illisible")
            )
            if mapping.fallback_tag:
                resolution.fallback_tags.append(mapping.fallback_tag)
            continue

        dose = round(dose_ratio * mapping.dose_scale, 4)
        resolution.controls[mapping.direction] = dose

        span_start = getattr(annotation, "span_start", None)
        span_end = getattr(annotation, "span_end", None)
        if span_start is not None and span_end is not None and span_end > span_start:
            resolution.control_spans.setdefault(mapping.direction, []).append(
                [int(span_start), int(span_end)]
            )

    return resolution


def fallback_text(fallback_tags: list[str]) -> str:
    """Render the FishAudio fallback tags as a bracket-tag prefix.

    The FishAudio path reads its instructions from the text itself
    (``convert_tags_for_fishaudio``), so a degraded ZONOS3 request
    degrades to *text* instructions.  Returns an empty string when
    there is nothing to fall back to.
    """
    if not fallback_tags:
        return ""
    # Keep the order stable and drop duplicates: the same axis can be
    # degraded on several spans of the same segment.
    unique = list(dict.fromkeys(fallback_tags))
    return " ".join(f"[{tag}]" for tag in unique)


# ---------------------------------------------------------------------------
# Rule bridge: FishAudio tag -> continuous axis
# ---------------------------------------------------------------------------
# The FishAudio vocabulary is discrete; the runtime wants a continuous
# axis.  This is the deterministic bridge shared by P4 (which writes the
# sidecar) and the P5 rule fallback (when no sidecar entry is present).
# Only tags with an unambiguous continuous counterpart are mapped; the
# rest are skipped and stay on the FishAudio tag path — the honest thing,
# rather than inventing a dose.  The value is a conservative target in
# [-1, 1]; the axis' dose_scale carries it onto the runtime unit.

TAG_TO_AXIS: dict[str, tuple[str, float]] = {
    "excited": ("arousal", 0.6),
    "angry": ("dominance", 0.6),
    "sad": ("valence", -0.6),
    "whispering": ("projection", -0.6),
    "shouting": ("projection", 0.6),
    "emphasis": ("clarity", 0.4),
    "pause": ("pace", -0.4),
}


def annotations_from_tags(
    segment_id: int,
    tags: list[str],
    *,
    intent_prefix: str = "tag",
    confidence: float = 0.5,
) -> list[Zonos3Annotation]:
    """Derive rule-based steering annotations from FishAudio tags.

    Each mapped tag becomes one annotation on the nearest axis at a
    conservative dose, marked ``source="rule"`` so a disputed render
    traces to a rule, not to a silent LLM call. The original tag is
    kept as the annotation's ``fallback_tag``: if the served bundle
    cannot steer the axis, the segment degrades to exactly the tag it
    already had.
    """
    annotations: list[Zonos3Annotation] = []
    for tag in tags:
        mapping = TAG_TO_AXIS.get(tag)
        if mapping is None:
            continue
        axis, value = mapping
        annotations.append(
            Zonos3Annotation(
                segment_id=segment_id,
                axis=axis,
                value=value,
                intent=f"{intent_prefix} {tag}",
                confidence=confidence,
                source="rule",
                fallback_tag=tag,
            )
        )
    return annotations
