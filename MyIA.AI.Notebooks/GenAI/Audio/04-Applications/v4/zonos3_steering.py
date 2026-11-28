"""ZONOS3 steering resolver — annotation sidecar -> generation payload.

The v4 pipeline annotates prosody with **FishAudio bracket tags**
(``p4_annotation.py:436`` ``convert_tags_for_fishaudio``): a discrete,
flat tag vocabulary carried inline in the text.  ZONOS3 consumes
something else: **measured direction vectors** with a continuous dose,
applied through the ``controls`` field of ``POST /v2/generate``,
optionally restricted to a **span** of the text via ``control_spans``.

This module is the seam between the two:

1. the **annotation sidecar** (see :mod:`v4.schemas`) records, per
   segment and per span, the *intent* in clear language plus the
   ``axis`` / ``value`` pair that expresses it;
2. this resolver turns that sidecar into a ``controls`` / ``control_spans``
   payload for the request, **and degrades honestly** when the served
   bundle does not expose the requested direction: an unserved axis is
   reported in ``degraded_axes`` with its FishAudio tag equivalent (the
   ``fallback_tag`` field), it is never silently dropped and never
   invented.

Why this is a resolver and not a pass-through: the axis names the
pipeline reasons about (``arousal``, ``pace``, ``projection``) are
**semantic**, while the direction names the runtime serves
(``mood.arousal``, ``delivery.tempo``, ``delivery.loud``) are **bundle
dependent** — the served set is read from ``GET /v2/controls`` at
runtime.  The mapping below is the *declared* correspondence between
the two, and every mapping is checked against what the server says it
serves before it is used.

## The dose model (measured, 2026-11-27, on the delivered service)

A dose is a **calibrated absolute**, not a magnitude from zero.
``GET /v2/controls`` publishes two things this resolver reads and the
server applies neither:

- ``sets.<set>.calibration.default`` — the neutral dose of each mood
  direction (``4.0`` on arousal, valence, dominance, tempo and
  articulation, ``2.0`` on loudness and clarity).  The delta-steered sets
  (``delivery``, ``expressive``, ``emphasis_nv_nodur``, ...) publish no
  calibration and anchor at ``0.0``.  A raw dose of ``1.0`` on
  ``mood.arousal`` therefore sits three units *below* neutral and steers
  the opposite way from what ``arousal: +1`` means.
- ``ui.controls`` — the studio's own controls.  Each names the served
  direction(s) it moves (its ``map``, with the dose applied per unit of
  control value) and its recommended window (its ``safe`` range).

The resolver centres every dose on the served neutral and follows the
studio's own correspondence:

    value = ratio * span          dose = neutral + value * unit

``ratio`` is the annotation value normalized to ``[-1, 1]``
(:func:`parse_axis_value`), ``span`` the half-width of the published
``safe`` window on the side asked for, and ``unit`` the published dose
per control unit.  ``arousal: 0.5`` (window ``[-4, 4]``, neutral
``4.0``) asks ``mood.arousal = 6.0`` — the dose the studio sends for
its slider at ``+2``.

Two published controls are **one-sided** or **bifid**, and the table
below says so rather than flattening them: ``projection`` moves
``delivery.loud`` upward and ``delivery.whisper`` downward — two
directions, chosen by the sign — and ``emphasis`` moves
``emphasis_nv_nodur.emphasis`` (``4.0`` per unit) together with
``mood.arousal`` (``1.0`` per unit), positive only.  An annotation that
asks for the side a one-sided control does not have is degraded, not
inverted.

A ratio of ``0.0`` on a two-sided control therefore asks for the neutral
dose, not for an extreme negative one; that is the whole point of
centring.

## Two steering channels, and why a span never also sets the global

``controls`` applies a direction to the whole segment; ``control_spans``
applies it to a range of the text (code-point offsets into the text
**actually sent**, end exclusive, answered by the server with
``X-Control-Span-Follow: rate``).  The two channels **compose**: measured
at seed 42 with the same dose, "global only", "whole-text span only" and
"both" rendered three different audios (4.533 s, 4.667 s and 3.133 s), so
a direction sent through both steers harder than through either.  A
span-scoped annotation therefore feeds ``control_spans`` only; a
whole-segment annotation feeds ``controls`` only.
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
# directions whose names depend on the loaded steering bundle.  The table
# follows the controls the service's own studio publishes for these
# notions (``ui.controls`` of ``GET /v2/controls``, captured in
# ``tests/fixtures/zonos3_controls_studio_mect60k_x10.json``): ``span`` is
# the half-width of the control's ``safe`` window on that side and ``unit``
# the dose its ``map`` applies per control unit.
#
# ``dominance`` is the one axis with no published control: it is mapped to
# the mood direction of the same name, with the window of its siblings.
#
# Only axes with a *measured* counterpart are mapped.  An axis with no
# counterpart is not a failure: it degrades to its FishAudio tag.

#: Half-width of the ``safe`` window the studio publishes for its mood
#: controls ``valence`` and ``arousal`` (``[-4, 4]``).  ``dominance`` has
#: no control of its own and borrows it.
MOOD_DOSE_SPAN: float = 4.0


@dataclass(frozen=True)
class DirectionDose:
    """One served direction an axis steers, and how far it moves.

    ``sign`` is the branch the direction belongs to: ``0`` when one
    direction serves both signs (the control value moves it up or down
    from its neutral), ``+1`` / ``-1`` for a one-sided or bifid control
    whose two sides are two different directions — ``projection`` moves
    ``delivery.loud`` up and ``delivery.whisper`` down.
    """

    direction: str
    span: float = MOOD_DOSE_SPAN
    unit: float = 1.0
    sign: int = 0


@dataclass(frozen=True)
class AxisMapping:
    """Declared correspondence between a pipeline axis and served directions."""

    axis: str
    doses: tuple[DirectionDose, ...]
    fallback_tag: str = ""
    description: str = ""


#: Semantic axis -> served ZONOS3 directions, after the studio's controls
#: ``arousal``, ``valence``, ``pace``, ``projection``, ``emphasis`` and
#: ``lively``.  A server serving another bundle will not advertise these
#: directions and the resolver will degrade.
AXIS_MAPPINGS: tuple[AxisMapping, ...] = (
    AxisMapping(
        axis="arousal",
        doses=(DirectionDose("mood.arousal", span=4.0),),
        fallback_tag="excited",
        description="Activation / energie de la livraison",
    ),
    AxisMapping(
        axis="valence",
        doses=(DirectionDose("mood.valence", span=4.0),),
        fallback_tag="happy",
        description="Polarite affective de la livraison",
    ),
    AxisMapping(
        axis="dominance",
        doses=(DirectionDose("mood.dominance"),),
        fallback_tag="angry",
        description="Assertivite de la livraison (aucun controle publie)",
    ),
    AxisMapping(
        axis="pace",
        doses=(DirectionDose("delivery.tempo", span=2.0),),
        fallback_tag="pause",
        description="Debit de la livraison",
    ),
    AxisMapping(
        axis="projection",
        doses=(
            DirectionDose("delivery.loud", span=2.0, sign=1),
            DirectionDose("delivery.whisper", span=1.5, sign=-1),
        ),
        fallback_tag="loud voice",
        description="Souffle et resonance, deux directions selon le signe",
    ),
    AxisMapping(
        axis="clarity",
        doses=(
            DirectionDose("emphasis_nv_nodur.emphasis", span=6.0, unit=4.0, sign=1),
            DirectionDose("mood.arousal", span=6.0, unit=1.0, sign=1),
        ),
        fallback_tag="emphasis",
        description="Accentuation et intelligibilite, positif seulement",
    ),
    AxisMapping(
        axis="liveliness",
        doses=(DirectionDose("expressive.expressive", span=8.0),),
        fallback_tag="chuckling",
        description="Vivacite de l'elocution",
    ),
)

AXIS_TO_MAPPING: dict[str, AxisMapping] = {m.axis: m for m in AXIS_MAPPINGS}


# ---------------------------------------------------------------------------
# Resolution result
# ---------------------------------------------------------------------------

@dataclass
class SteeringResolution:
    """Outcome of resolving an annotation sidecar against a served bundle.

    Attributes
    ----------
    controls:
        The ``controls`` field for ``POST /v2/generate`` — direction
        name -> raw dose, for the axes steered over the whole segment.
        Empty when nothing resolved that way.
    control_spans:
        The ``control_spans`` field — ``[{"start", "end", "controls"}]``,
        code-point offsets into the text actually sent, end exclusive.
        One entry per distinct range.  Empty when no span-scoped
        annotation.
    fallback_tags:
        FishAudio bracket tags standing for the axes that could NOT be
        steered.  Reporting only: ZONOS3 reads the request text
        literally, so these tags are never injected into it (see
        :func:`fallback_text`).
    degraded_axes:
        The semantic axes that were requested but not steered, with
        the reason.  Reported, never hidden.
    """

    controls: dict[str, float] = field(default_factory=dict)
    control_spans: list[dict] = field(default_factory=list)
    fallback_tags: list[str] = field(default_factory=list)
    degraded_axes: list[tuple[str, str]] = field(default_factory=list)

    @property
    def is_degraded(self) -> bool:
        """True when at least one requested axis fell back to a tag."""
        return bool(self.degraded_axes)

    @property
    def has_steering(self) -> bool:
        """True when at least one axis was actually steered."""
        return bool(self.controls or self.control_spans)


#: A signed number at the end of a string — ``"pace-2"``, ``"+1.5"``,
#: ``"1.5"``, ``"arousal-1.5"``.  Reads the raw-magnitude form of an axis
#: value (an optional axis name precedes the signed number).
_SIGNED_NUMBER_RE = re.compile(r"[+-]?\d+(?:\.\d+)?\s*$")
#: The string form carries a signed magnitude on a fixed window: the full
#: width of the ``safe`` window the studio publishes for its mood controls
#: (valence and arousal, ``[-4, 4]``).  Dividing by it maps the magnitude
#: onto the normalized ratio ``[-1, 1]``.
_RUNTIME_AXIS_UNIT_SCALE = 2 * MOOD_DOSE_SPAN


def _is_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def parse_axis_value(value: object) -> float | None:
    """Coerce an annotation ``value`` into a float ratio in ``[-1, 1]``.

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
        return max(-1.0, min(1.0, magnitude / _RUNTIME_AXIS_UNIT_SCALE))
    return None


def served_directions(controls_index: dict | None) -> set[str]:
    """Extract the direction names a server actually serves.

    ``GET /v2/controls`` lists them under ``directions``, keyed by name;
    each value names the set and space of the direction.  That object is
    the only authority read here — the ``ui`` section also mentions
    direction names, in its control maps, but it lists only the controls
    the studio exposes, not every direction the bundle serves.

    A payload without a ``directions`` object yields an empty set, which
    makes the resolver degrade every axis rather than steer a direction
    it cannot verify.
    """
    if not controls_index:
        return set()
    directions = controls_index.get("directions")
    if not isinstance(directions, dict):
        return set()
    return {name for name in directions if isinstance(name, str) and "." in name}


def _set_of(controls_index: dict | None, direction: str) -> str | None:
    """Name of the bundle set holding ``direction``, from the index itself."""
    entry = ((controls_index or {}).get("directions") or {}).get(direction)
    if isinstance(entry, dict) and isinstance(entry.get("set"), str):
        return entry["set"]
    return direction.split(".", 1)[0] if "." in direction else None


def served_neutral_dose(direction: str, controls_index: dict | None) -> float:
    """Neutral dose the served calibration gives ``direction``.

    Read from ``sets.<set>.calibration.default.<axis>`` — the axis being
    the part of the direction name after the dot — then from the set's
    ``calibration.global_default``, then ``0.0`` for a set the bundle
    does not calibrate: the delta-steered sets (``delivery``, ``pitch``,
    ``accents_*``, ...) anchor their timing tables at 0.0, measured.

    Returns ``0.0`` when no index is available; the caller only reaches
    this function for a direction the index serves.
    """
    if not controls_index:
        return 0.0
    sets = controls_index.get("sets")
    set_name = _set_of(controls_index, direction)
    info = sets.get(set_name) if isinstance(sets, dict) and set_name else None
    calibration = info.get("calibration") if isinstance(info, dict) else None
    if isinstance(calibration, dict):
        axis = direction.split(".", 1)[1] if "." in direction else direction
        default = calibration.get("default")
        if isinstance(default, dict) and _is_number(default.get(axis)):
            return float(default[axis])
        if _is_number(calibration.get("global_default")):
            return float(calibration["global_default"])
    return 0.0


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
        The whole-segment controls, the span payload, the fallback tags
        and the list of degraded axes.

    Notes
    -----
    A span-scoped annotation feeds ``control_spans`` only — never also
    ``controls`` for the same direction, because the two channels
    compose (see the module docstring).  ``span_start`` / ``span_end``
    are code-point offsets into the text **the caller sends**; a
    resolver cannot re-base them, so the sidecar producer must compute
    them on that exact text.
    """
    resolution = SteeringResolution()
    served = served_directions(controls_index)
    # One entry per distinct range: several axes annotated on the same
    # span are applied by one server span, not by overlapping ones.
    spans: dict[tuple[int, int], dict[str, float]] = {}

    def _degrade(axis: str, reason: str, mapping: AxisMapping) -> None:
        resolution.degraded_axes.append((axis, reason))
        if mapping.fallback_tag:
            resolution.fallback_tags.append(mapping.fallback_tag)

    for annotation in annotations:
        axis = getattr(annotation, "axis", "") or ""
        if not axis:
            continue

        mapping = AXIS_TO_MAPPING.get(axis)
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

        if not served:
            # The bundle could not be read: degrade rather than guess.
            _degrade(axis, "bundle de steering illisible", mapping)
            continue

        missing = [d.direction for d in mapping.doses if d.direction not in served]
        if missing:
            # The published correspondence is only usable whole: steering
            # one direction of a two-direction control would not be the
            # control the studio defines.
            _degrade(
                axis,
                "direction non servie: " + ", ".join(missing),
                mapping,
            )
            continue

        if dose_ratio == 0.0 and all(d.sign for d in mapping.doses):
            # Neutral on a one-sided or bifid control: nothing to ask for.
            continue

        doses: dict[str, float] = {}
        for dose in mapping.doses:
            if dose.sign and dose.sign * dose_ratio <= 0:
                continue  # the other side of the control
            value = (abs(dose_ratio) if dose.sign else dose_ratio) * dose.span
            doses[dose.direction] = round(
                served_neutral_dose(dose.direction, controls_index)
                + value * dose.unit,
                4,
            )
        if not doses:
            # The side asked for does not exist on a one-sided control;
            # asking the opposite side would invert the intent.
            _degrade(axis, "sens non exprimable par ce bundle", mapping)
            continue

        span_start = getattr(annotation, "span_start", None)
        span_end = getattr(annotation, "span_end", None)
        has_span = (
            span_start is not None
            and span_end is not None
            and int(span_end) > int(span_start)
        )
        if has_span:
            spans.setdefault((int(span_start), int(span_end)), {}).update(doses)
        else:
            resolution.controls.update(doses)

    resolution.control_spans = [
        {"start": start, "end": end, "controls": dict(controls)}
        for (start, end), controls in sorted(spans.items())
    ]
    return resolution


def fallback_text(fallback_tags: list[str]) -> str:
    """Render the fallback tags as a bracket-tag string, for reporting.

    ZONOS3 reads the request text **literally**: it has no tag grammar.
    Measured at seed 42 (2026-11-27), prefixing ``"[excited] [pause] "``
    to a sentence lengthened the render by 0.87 s (4.867 s -> 5.733 s)
    and faster-whisper recovered the same sentence from both — the tags
    are spoken text or nothing, never a steering instruction.  This
    string is therefore for a log line or the manifest ("the intent is
    left to these tags"), never for the ZONOS3 request.  Returns an
    empty string when there is nothing to fall back to.
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
# rather than inventing a dose.  The value is a conservative ratio in
# [-1, 1]; the mapping's published window carries it onto the runtime's
# dose scale.

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
    conservative ratio, marked ``source="rule"`` so a disputed render
    traces to a rule, not to a silent LLM call. The original tag is
    kept as the annotation's ``fallback_tag``: if the served bundle
    cannot steer the axis, the degradation names exactly the tag it
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
