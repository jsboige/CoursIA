"""ZONOS3-Mini narrator seam (Issue #25835) — hermetic tests.

These tests exercise the *seam* of the ZONOS3 narrator: the routing
decision, the steering resolver (annotation sidecar -> ``controls``
payload, with honest degradation of unserved axes), the HTTP client
payload shape, and the tag->axis rule bridge. They run network-free:

- routing / steering / client payload tests mock ``requests`` (no live
  ZONOS3 runtime, no GPU, no 9 GB of weights);
- the ``_synthesize_narrator_zonos3`` guards that run before any
  network call (empty-text, no-audio, short-render) are exercised
  directly with the client stubbed.

The live measurement run (WER / RTF / VRAM, A/B axis comparison) is the
run-level evidence in the PR body; these tests guard the dispatch and
translation logic so a regression there is caught in CI, not in a
listening pass.

Run from the v4 directory:
    python -m pytest tests/test_zonos3_narrator.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path
from unittest import mock

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


def _build_seg(*, speaker: str, text: str = "x"):
    from v4.schemas import AnnotatedSegment

    return AnnotatedSegment(
        seg_index=1,
        speaker=speaker,
        type="narration" if speaker == "narrateur" else "dialogue",
        text=text,
        annotated_text=text,
    )


# The served steering payload, captured from the delivered service.  The
# resolver and the seam are tested against this shape, never a made-up
# one: the previous ``{"mood": [...]}`` stand-in advertised directions the
# server never had and hid the drift for the whole seam.
_FIXTURE = (
    Path(__file__).resolve().parent
    / "fixtures"
    / "zonos3_controls_studio_mect60k_x10.json"
)


def _controls_index() -> dict:
    """The ``GET /v2/controls`` payload the delivered service answers
    (captured 2026-11-27 — see ``fixtures/README.md``)."""
    import json

    return json.loads(_FIXTURE.read_text(encoding="utf-8"))


def _without(controls_index: dict, *directions: str) -> dict:
    """A copy of the served payload with some directions removed — the
    bundle of another checkpoint, which does not expose them."""
    import copy

    clone = copy.deepcopy(controls_index)
    for direction in directions:
        clone["directions"].pop(direction, None)
    return clone


def _annot(axis: str, value, span=None, **kw):
    from v4.schemas import Zonos3Annotation

    span_start, span_end = span if span else (None, None)
    return Zonos3Annotation(
        segment_id=1,
        span_start=span_start,
        span_end=span_end,
        axis=axis,
        value=value,
        **kw,
    )


# ---------------------------------------------------------------------------
# Routing (v4/p5_tts.py)
# ---------------------------------------------------------------------------

def test_zonos3_off_by_default():
    """ZONOS3 routing is OFF by default: the narrator engine does not
    change until the association's listening picks the winner (#17586)
    and the ZONOS3 service is deployed on a GPU node. No silent engine
    swap (acceptance #6 of #15002)."""
    from v4 import p5_tts

    assert p5_tts._NARRATOR_ZONOS3_ROUTING is False
    seg = _build_seg(speaker="narrateur")
    assert p5_tts._should_route_narrator_to("zonos3", seg) is False


def test_zonos3_routes_narrator_when_flag_on():
    """With NARRATOR_ZONOS3_ROUTING=1 (and no other engine selected),
    narrator segments route to ZONOS3 and to no other engine."""
    from v4 import p5_tts

    orig = (
        p5_tts._NARRATOR_QWEN_ROUTING,
        p5_tts._NARRATOR_COSYVOICE3_ROUTING,
        p5_tts._NARRATOR_CUSTOMVOICE_ROUTING,
        p5_tts._NARRATOR_ZONOS3_ROUTING,
    )
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = False
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = False
        p5_tts._NARRATOR_CUSTOMVOICE_ROUTING = False
        p5_tts._NARRATOR_ZONOS3_ROUTING = True
        seg = _build_seg(speaker="narrateur")
        assert p5_tts._should_route_narrator_to("zonos3", seg) is True
        assert p5_tts._should_route_narrator_to("qwen_voicedesign", seg) is False
        assert p5_tts._selected_narrator_engine() == "zonos3"
    finally:
        (
            p5_tts._NARRATOR_QWEN_ROUTING,
            p5_tts._NARRATOR_COSYVOICE3_ROUTING,
            p5_tts._NARRATOR_CUSTOMVOICE_ROUTING,
            p5_tts._NARRATOR_ZONOS3_ROUTING,
        ) = orig


def test_does_not_route_non_narrator_to_zonos3():
    """Acceptance #1 (carries over from #15002): routing is limited to
    the narrateur speaker. Every other speaker stays on FishAudio clone
    even when the ZONOS3 flag is ON."""
    from v4 import p5_tts

    original = p5_tts._NARRATOR_ZONOS3_ROUTING
    try:
        p5_tts._NARRATOR_ZONOS3_ROUTING = True
        for speaker in (
            "elisabeth_rousset",
            "loiseau",
            "comte",
            "comtesse",
            "cornudet",
            "officier",
            "figurant",
        ):
            seg = _build_seg(speaker=speaker)
            assert p5_tts._should_route_narrator_to("zonos3", seg) is False, (
                f"non-narrator speaker '{speaker}' must NOT route to zonos3"
            )
    finally:
        p5_tts._NARRATOR_ZONOS3_ROUTING = original


def test_zonos3_exclusivity_with_other_engines():
    """Two narrator engines active at once is a configuration error,
    never a silent precedence (no-silent-swap contract, #15002
    acceptance 6). Covers ZONOS3 against each of the other three."""
    from v4 import p5_tts

    orig = (
        p5_tts._NARRATOR_QWEN_ROUTING,
        p5_tts._NARRATOR_COSYVOICE3_ROUTING,
        p5_tts._NARRATOR_CUSTOMVOICE_ROUTING,
        p5_tts._NARRATOR_ZONOS3_ROUTING,
    )
    try:
        for other in ("qwen_voicedesign", "cosyvoice3", "customvoice"):
            p5_tts._NARRATOR_QWEN_ROUTING = other == "qwen_voicedesign"
            p5_tts._NARRATOR_COSYVOICE3_ROUTING = other == "cosyvoice3"
            p5_tts._NARRATOR_CUSTOMVOICE_ROUTING = other == "customvoice"
            p5_tts._NARRATOR_ZONOS3_ROUTING = True
            try:
                p5_tts._selected_narrator_engine()
            except ValueError:
                pass  # success: exclusivity raises
            else:
                raise AssertionError(
                    f"two active narrator engines (zonos3 + {other}) did not raise"
                )
    finally:
        (
            p5_tts._NARRATOR_QWEN_ROUTING,
            p5_tts._NARRATOR_COSYVOICE3_ROUTING,
            p5_tts._NARRATOR_CUSTOMVOICE_ROUTING,
            p5_tts._NARRATOR_ZONOS3_ROUTING,
        ) = orig


def test_engine_reference_table_covers_all_four_engines():
    """The engine -> reference-id sentinel table now covers all four
    narrator engines (ZONOS3 is the fifth seam member), and it must
    describe exactly the same set as the routing flags: an extra key the
    router never selects would serve one engine's cache to another."""
    from v4 import p5_tts

    assert set(p5_tts._NARRATOR_ENGINE_REFERENCE_IDS) == {
        "qwen_voicedesign",
        "cosyvoice3",
        "customvoice",
        "zonos3",
    }
    assert set(p5_tts._narrator_engine_flags()) == set(
        p5_tts._NARRATOR_ENGINE_REFERENCE_IDS
    )


def test_zonos3_reference_id_is_engine_specific():
    """The narrator cache is keyed on reference_id. A ZONOS3 MP3 must
    carry its own sentinel, distinct from the other three engines, so a
    future engine swap cannot silently re-serve a stale MP3 from a
    previous engine."""
    from v4 import p5_tts

    zonos3 = p5_tts._NARRATOR_ENGINE_REFERENCE_IDS["zonos3"]
    assert zonos3 != p5_tts._QWEN_NARRATOR_REFERENCE_ID
    assert zonos3 != p5_tts._CV3_NARRATOR_REFERENCE_ID
    assert zonos3 != p5_tts._CUSTOMVOICE_NARRATOR_REFERENCE_ID
    assert not zonos3.startswith("v4_")  # not a FishAudio voice id


def test_zonos3_unavailable_is_runtime_error():
    """NarratorZonos3Unavailable must be a RuntimeError so callers can
    catch a single class for any ZONOS3-side failure (transport 4xx/5xx,
    empty render, degenerate short render)."""
    from v4.p5_tts import NarratorZonos3Unavailable

    assert issubclass(NarratorZonos3Unavailable, RuntimeError)
    try:
        raise NarratorZonos3Unavailable("test")
    except RuntimeError as exc:
        assert str(exc) == "test"


def test_synthesize_narrator_zonos3_raises_on_empty_input():
    """If upstream P4 produces no renderable text, _synthesize_narrator_zonos3
    must raise NarratorZonos3Unavailable rather than write an empty file
    or silently fall back. This guard runs before any network import, so
    it is exercisable with no service and no pydub."""
    from v4.p5_tts import (
        NarratorZonos3Unavailable,
        _synthesize_narrator_zonos3,
    )

    seg = _build_seg(speaker="narrateur", text="")
    try:
        _synthesize_narrator_zonos3(
            seg=seg,
            fishaudio_text="   \n  [whispering]",
            mp3_path=Path("/tmp/should_never_be_written_zonos3.mp3"),
            seed=42,
            text_hash="deadbeef",
        )
    except NarratorZonos3Unavailable:
        return  # success: raised as designed
    raise AssertionError("NarratorZonos3Unavailable not raised on empty input")


def test_synthesize_batch_propagates_zonos3_hard_failure():
    """A ZONOS3 narrator failure must ABORT the batch, not be absorbed
    into a survivable status="failed" record. Same contract as the Qwen
    and CustomVoice propagation tests: the typed exception is re-raised
    by the batch handler instead of being swallowed by the generic
    `except Exception` (which would ship an audiobook with the narrator
    segments missing)."""
    from v4 import p5_tts
    from v4.schemas import AnnotatedSegment

    text = "Un texte narrateur volontairement non cache."
    seg = AnnotatedSegment(
        seg_index=987656,  # distinctive: no cached mp3 can match it
        speaker="narrateur",
        type="narration",
        text=text,
        annotated_text=text,
    )

    def _boom(_seg, _text):
        raise p5_tts.NarratorZonos3Unavailable("ZONOS3 :1919 unreachable")

    original_seg, original_thermal = (
        p5_tts._synthesize_segment,
        p5_tts.thermal_wait,
    )
    try:
        p5_tts._synthesize_segment = _boom
        p5_tts.thermal_wait = lambda *a, **k: None
        p5_tts._synthesize_batch([(seg, text)])
    except p5_tts.NarratorZonos3Unavailable:
        return  # success: propagated instead of degraded
    finally:
        p5_tts._synthesize_segment = original_seg
        p5_tts.thermal_wait = original_thermal
    raise AssertionError(
        "NarratorZonos3Unavailable was absorbed by the generic handler -- the "
        "pass would ship an audiobook with narrator segments missing"
    )


def _render_zonos3(*, seed_used, duration, text="Un texte de test.",
                   pydub_absent=False):
    """Drive _synthesize_narrator_zonos3 to completion with the ZONOS3 client
    stubbed (no network, no GPU): zonos3_tts -> fixed blob + the reported
    X-Seed, audio_duration_wav -> fixed duration, steering kept empty. When
    pydub_absent, pydub is hidden so the .wav fallback branch is taken. The
    fake audio blob is not a decodable WAV, so a present pydub also falls
    through to that branch."""
    import v4.p5_tts as p5_tts

    seg = _build_seg(speaker="narrateur", text=text)
    pydub_ctx = (mock.patch.dict(sys.modules, {"pydub": None})
                 if pydub_absent else mock.MagicMock())
    with pydub_ctx, \
         mock.patch("v4.zonos3_client.zonos3_ensure_up", return_value=True), \
         mock.patch("v4.zonos3_client.zonos3_tts",
                    return_value=(b"FAKEWAV", seed_used)), \
         mock.patch("v4.zonos3_client.audio_duration_wav",
                    return_value=duration), \
         mock.patch("v4.zonos3_client.zonos3_controls", return_value={}), \
         mock.patch.object(p5_tts, "_zonos3_annotations_for_segment",
                           return_value=[]):
        return p5_tts._synthesize_narrator_zonos3(
            seg=seg,
            fishaudio_text=text,
            mp3_path=Path("/tmp/zone_render_test.mp3"),
            seed=42,
            text_hash="deadbeef",
        )


def test_synthesize_narrator_zonos3_records_none_seed_not_invented():
    """The recorded seed is the X-Seed the runtime reports. When the header is
    absent the result records None -- it does NOT substitute the requested
    seed (acceptance #6: captured, never invented)."""
    result = _render_zonos3(seed_used=None, duration=30.0)
    assert result.seed is None


def test_synthesize_narrator_zonos3_records_reported_seed():
    """When the runtime reports an X-Seed, that exact value is recorded."""
    result = _render_zonos3(seed_used=12345, duration=30.0)
    assert result.seed == 12345


def test_synthesize_narrator_zonos3_raises_on_zero_duration():
    """A 0s render is degenerate and must raise, not pass as 'generated' (the
    old `0 < duration_s < floor_s` guard let a 0s render through)."""
    from v4.p5_tts import NarratorZonos3Unavailable

    try:
        _render_zonos3(seed_used=7, duration=0.0)
    except NarratorZonos3Unavailable:
        return  # success: 0s render rejected
    raise AssertionError("a 0s render was not rejected as degenerate")


def test_synthesize_narrator_zonos3_wav_fallback_path_in_result():
    """When pydub is unavailable the render is written as a .wav; the result
    must point at the .wav actually written, not the .mp3 that was never
    produced."""
    result = _render_zonos3(seed_used=None, duration=30.0, pydub_absent=True)
    # Points at the .wav that was written (same base name), not the .mp3.
    assert Path(result.mp3_path).name == "zone_render_test.wav"


def test_synthesize_narrator_zonos3_wakes_the_service_first():
    """The container is started on demand and a cold pipeline meets it
    stopped.  When the wake fails the seam raises before any render — it
    never falls back to another engine (#15002 acceptance 6)."""
    import v4.p5_tts as p5_tts

    seg = _build_seg(speaker="narrateur", text="Un texte.")
    with mock.patch("v4.zonos3_client.zonos3_ensure_up", return_value=False), \
         mock.patch("v4.zonos3_client.zonos3_tts") as tts:
        try:
            p5_tts._synthesize_narrator_zonos3(
                seg=seg,
                fishaudio_text="Un texte.",
                mp3_path=Path("/tmp/zone_never_written.mp3"),
                seed=42,
                text_hash="deadbeef",
            )
        except p5_tts.NarratorZonos3Unavailable:
            tts.assert_not_called()
            return
    raise AssertionError("a failed wake did not raise")


def test_synthesize_narrator_zonos3_rejects_a_cut_render():
    """The server cuts a render at its frame budget without any signal
    (measured 2026-11-27: 1 991 audio frames = 132.733 s, and a longer
    text lands exactly there).  A render at the ceiling is a cut render:
    it raises instead of shipping a truncated segment."""
    from v4.p5_tts import NarratorZonos3Unavailable
    from v4.zonos3_client import MAX_RENDER_SECONDS

    assert round(MAX_RENDER_SECONDS, 3) == 132.733  # (2000 - 9) / 15
    try:
        _render_zonos3(seed_used=42, duration=MAX_RENDER_SECONDS)
    except NarratorZonos3Unavailable as exc:
        assert "ceiling" in str(exc)
        return
    raise AssertionError("a render at the one-request ceiling was accepted")


def test_synthesize_narrator_zonos3_accepts_a_render_under_the_ceiling():
    """The ceiling guard rejects the cut render only: one frame under the
    ceiling is a complete render."""
    from v4.zonos3_client import FRAME_SECONDS, MAX_RENDER_SECONDS

    result = _render_zonos3(
        seed_used=42, duration=MAX_RENDER_SECONDS - 3 * FRAME_SECONDS
    )
    assert result.status == "generated"


def _drive_zonos3(*, annotations, controls_index, fishaudio_text="Un texte agite."):
    """Run _synthesize_narrator_zonos3 with the service stubbed and the
    request captured. Returns what the seam passed to zonos3_tts (the text
    and its keyword arguments) plus the warning lines it logged."""
    import v4.p5_tts as p5_tts

    seen: dict = {}

    def _capture(text, **kwargs):
        seen["text"] = text
        seen.update(kwargs)
        return b"FAKEWAV", 42

    with mock.patch("v4.zonos3_client.zonos3_ensure_up", return_value=True), \
         mock.patch("v4.zonos3_client.zonos3_tts", side_effect=_capture), \
         mock.patch("v4.zonos3_client.audio_duration_wav", return_value=2.0), \
         mock.patch("v4.zonos3_client.zonos3_controls",
                    return_value=controls_index), \
         mock.patch.object(p5_tts, "_zonos3_annotations_for_segment",
                           return_value=annotations), \
         mock.patch.object(p5_tts, "logger") as log:
        p5_tts._synthesize_narrator_zonos3(
            seg=_build_seg(speaker="narrateur", text="Un texte agite."),
            fishaudio_text=fishaudio_text,
            mp3_path=Path("/tmp/zone_render_test.mp3"),
            seed=42,
            text_hash="deadbeef",
        )
    seen["warnings"] = [
        call.args[0] % tuple(call.args[1:])
        for call in log.warning.call_args_list
    ]
    return seen


def test_synthesize_narrator_zonos3_never_writes_bracket_tags_into_the_text():
    """ZONOS3 reads the request text literally: the FishAudio tags are
    stripped, and an axis that cannot be steered is reported in the log,
    never re-injected as a tag (measured: a bracketed prefix lengthened
    the render by 0.87 s at the same seed)."""
    # dominance is not served by this bundle: its "angry" intent must
    # stay out of the text.
    seen = _drive_zonos3(
        annotations=[_annot("arousal", 0.6), _annot("dominance", 0.6)],
        controls_index=_without(_controls_index(), "mood.dominance"),
        fishaudio_text="[excited] Un texte agite.",
    )
    assert seen["text"] == "Un texte agite."
    assert seen["controls"] == {"mood.arousal": 6.4}
    assert seen["control_spans"] is None
    # The unserved axis is reported, with the tag its intent is left to.
    assert any(
        "dominance" in line and "[angry]" in line for line in seen["warnings"]
    )


def test_synthesize_narrator_zonos3_unreadable_index_still_renders():
    """Without the controls index no axis can be verified as served: the
    render goes on un-steered, and the log says so."""
    seen = _drive_zonos3(annotations=[_annot("arousal", 0.6)], controls_index={})
    assert seen["controls"] is None
    assert seen["control_spans"] is None
    assert any("unreadable" in line for line in seen["warnings"])


def test_narrator_zonos3_default_speaker_is_the_served_french_voice():
    """The default reference is the only French voice the pinned
    checkpoint serves (``GET /v2/speakers``, measured 2026-11-27:
    ``default_517319c805b927e9``), and the cache sentinel names the v2
    request: an MP3 cached under v1 was rendered by a request the server
    refused or steered differently (#19692)."""
    from v4 import p5_tts

    assert p5_tts._ZONOS3_DEFAULT_SPEAKER_ID == "default_517319c805b927e9"
    assert p5_tts._NARRATOR_ENGINE_REFERENCE_IDS["zonos3"].endswith("-v2")


def test_synthesize_narrator_zonos3_sends_the_served_steering():
    """What the resolver produces against the served bundle is what the
    request carries: the tag ``[excited]`` becomes a centred dose on
    ``mood.arousal``, nothing else."""
    from v4 import p5_tts
    from v4.zonos3_steering import annotations_from_tags

    seen = _drive_zonos3(
        annotations=annotations_from_tags(1, ["excited"]),
        controls_index=_controls_index(),
    )
    assert seen["controls"] == {"mood.arousal": 6.4}  # 4.0 + 0.6 * 4.0
    assert seen["control_spans"] is None
    assert seen["reference_id"] == p5_tts._ZONOS3_DEFAULT_SPEAKER_ID


# ---------------------------------------------------------------------------
# Steering resolver (v4/zonos3_steering.py)
# ---------------------------------------------------------------------------

def test_resolve_steering_translates_sidecar_to_controls():
    """A sidecar axis whose direction the bundle serves becomes a
    controls entry at a dose CENTRED ON THE SERVED NEUTRAL (measured
    2026-11-27: mood.arousal and mood.valence are neutral at 4.0, and the
    server never applies that calibration itself)."""
    from v4.zonos3_steering import resolve_steering

    anns = [_annot("arousal", 0.5), _annot("valence", -0.5)]
    res = resolve_steering(anns, _controls_index())
    # dose = neutral 4.0 + ratio * span 4.0 -> 6.0 and 2.0.
    assert res.controls == {"mood.arousal": 6.0, "mood.valence": 2.0}
    assert res.has_steering is True
    assert res.is_degraded is False
    assert res.fallback_tags == []


def test_resolve_steering_follows_the_published_control_windows():
    """Each axis follows the control the studio publishes for it, with
    its own window and its own neutral (``ui.controls`` of the served
    payload): ``pace`` is ``delivery.tempo`` (window [-2, 2], no
    calibration), ``projection`` is one direction per sign, ``emphasis``
    moves two directions at once, ``lively`` is ``expressive.expressive``."""
    from v4.zonos3_steering import resolve_steering

    def _controls(axis, value):
        return resolve_steering([_annot(axis, value)], _controls_index()).controls

    assert _controls("arousal", 1.0) == {"mood.arousal": 8.0}
    assert _controls("arousal", 0.0) == {"mood.arousal": 4.0}  # ratio 0 = neutral
    assert _controls("pace", -0.5) == {"delivery.tempo": -1.0}
    assert _controls("projection", 0.6) == {"delivery.loud": 1.2}
    assert _controls("projection", -0.6) == {"delivery.whisper": 0.9}
    assert _controls("projection", 0.0) == {}  # one-sided: nothing to ask
    assert _controls("clarity", 0.4) == {
        "emphasis_nv_nodur.emphasis": 9.6,
        "mood.arousal": 6.4,
    }
    assert _controls("liveliness", 0.5) == {"expressive.expressive": 4.0}
    assert _controls("dominance", 0.6) == {"mood.dominance": 6.4}


def test_resolve_steering_does_not_invert_a_one_sided_ask():
    """``emphasis`` is a positive-only control: asking for less clarity
    must not be rendered as more of it — the axis degrades to its tag."""
    from v4.zonos3_steering import resolve_steering

    res = resolve_steering([_annot("clarity", -0.4)], _controls_index())
    assert res.controls == {}
    assert res.is_degraded is True
    assert res.fallback_tags == ["emphasis"]
    assert ("clarity", "sens non exprimable par ce bundle") in res.degraded_axes


def test_resolve_steering_degrades_unserved_axis_to_tag():
    """An axis whose direction the bundle does NOT serve degrades to its
    FishAudio fallback tag and is recorded in degraded_axes — never
    silently dropped, never steered on a direction the server lacks."""
    from v4.zonos3_steering import resolve_steering

    # Only mood.dominance is missing from this bundle.
    anns = [_annot("arousal", 0.5), _annot("dominance", 0.6)]
    res = resolve_steering(anns, _without(_controls_index(), "mood.dominance"))
    assert res.controls == {"mood.arousal": 6.0}
    assert res.is_degraded is True
    # degraded_axes records (axis, REASON) — the tag lives in fallback_tags.
    assert any(axis == "dominance" for axis, _reason in res.degraded_axes)
    assert "angry" in res.fallback_tags


def test_resolve_steering_degrades_a_half_served_two_direction_control():
    """A two-direction control is steered only whole: when the bundle
    serves one of its directions and not the other, the axis degrades
    rather than moving half of what the studio defines."""
    from v4.zonos3_steering import resolve_steering

    anns = [_annot("clarity", 0.4)]
    res = resolve_steering(
        anns, _without(_controls_index(), "emphasis_nv_nodur.emphasis")
    )
    assert res.controls == {}
    assert res.is_degraded is True
    assert "emphasis" in res.fallback_tags


def test_resolve_steering_produces_control_spans():
    """A span-scoped annotation (span_start < span_end) on a served axis
    contributes a control_spans entry, in the list shape the server
    reads, and nothing in the whole-segment controls."""
    from v4.zonos3_steering import resolve_steering

    anns = [_annot("pace", -0.5, span=(4, 20))]
    res = resolve_steering(anns, _controls_index())
    assert res.control_spans == [
        {"start": 4, "end": 20, "controls": {"delivery.tempo": -1.0}}
    ]
    # The two channels compose on the server (measured), so a span never
    # also sets the global control of its direction.
    assert res.controls == {}
    assert res.has_steering is True


def test_resolve_steering_merges_axes_annotated_on_the_same_span():
    """Two axes annotated on the same range are carried by one server
    span, not by two overlapping ones."""
    from v4.zonos3_steering import resolve_steering

    anns = [
        _annot("arousal", 0.5, span=(4, 20)),
        _annot("valence", -0.5, span=(4, 20)),
        _annot("pace", -0.5, span=(30, 40)),
    ]
    res = resolve_steering(anns, _controls_index())
    assert res.control_spans == [
        {"start": 4, "end": 20,
         "controls": {"mood.arousal": 6.0, "mood.valence": 2.0}},
        {"start": 30, "end": 40, "controls": {"delivery.tempo": -1.0}},
    ]
    assert res.controls == {}


def test_served_directions_reads_the_directions_object():
    """Discovery reads ``directions``, the object the server fills with
    every direction it serves.  The ``ui`` section names directions too,
    but only in the maps of its 25 studio controls: mined (the previous
    behaviour), it saw 42 names and only 2 of the 7 mapped ones."""
    from v4.zonos3_steering import AXIS_MAPPINGS, served_directions

    index = _controls_index()
    served = served_directions(index)
    assert len(index["directions"]) == 65
    assert len(served) == 65
    mapped = {d.direction for m in AXIS_MAPPINGS for d in m.doses}
    assert len(mapped) == 8
    assert mapped <= served  # 8/8 served by the delivered bundle
    # A payload carrying only the studio's ui section advertises nothing.
    assert served_directions({"ui": index["ui"]}) == set()
    assert served_directions({}) == set()
    assert served_directions(None) == set()


def test_served_neutral_dose_reads_the_calibration():
    """The neutral is the served calibration's default per axis — 4.0 on
    the mood axes, 2.0 on loudness and clarity — and 0.0 for a set the
    bundle does not calibrate (delivery, expressive), or without an
    index."""
    from v4.zonos3_steering import served_neutral_dose

    index = _controls_index()
    assert served_neutral_dose("mood.arousal", index) == 4.0
    assert served_neutral_dose("mood.loudness", index) == 2.0
    assert served_neutral_dose("mood.clarity", index) == 2.0
    assert served_neutral_dose("delivery.tempo", index) == 0.0
    assert served_neutral_dose("expressive.expressive", index) == 0.0
    assert served_neutral_dose("mood.arousal", None) == 0.0


def test_axis_mapping_uses_the_windows_the_studio_publishes():
    """Every declared direction, span and unit is the one the served
    ``ui.controls`` publishes for that control: the table cannot drift
    from the bundle without this test failing."""
    index = _controls_index()
    by_id = {entry["id"]: entry for entry in index["ui"]["controls"]}
    controls = {
        "arousal": "arousal",
        "valence": "valence",
        "pace": "pace",
        "projection": "projection",
        "clarity": "emphasis",
        "liveliness": "lively",
    }
    from v4.zonos3_steering import AXIS_TO_MAPPING

    for axis, control_id in controls.items():
        entry = by_id[control_id]
        safe = entry["safe"]
        for dose in AXIS_TO_MAPPING[axis].doses:
            assert dose.direction in {
                name for branch in entry["map"].values() for name in branch
            }, (axis, dose.direction)
            if dose.sign >= 0:
                assert dose.span == safe[1], (axis, dose.direction)
            if dose.sign <= 0:
                assert dose.span == -safe[0], (axis, dose.direction)
            for branch in entry["map"].values():
                if dose.direction in branch:
                    assert dose.unit == abs(branch[dose.direction]), (
                        axis, dose.direction
                    )


def test_resolve_steering_degrades_all_when_bundle_unreadable():
    """When the controls index is None (bundle unreadable), EVERY axis
    degrades to its fallback tag: the resolver never steers a direction
    it cannot verify as served."""
    from v4.zonos3_steering import resolve_steering

    anns = [_annot("arousal", 0.5), _annot("clarity", 0.4)]
    res = resolve_steering(anns, None)
    assert res.controls == {}
    assert res.has_steering is False
    assert res.is_degraded is True
    assert "excited" in res.fallback_tags
    assert "emphasis" in res.fallback_tags


def test_resolve_steering_unknown_axis_degrades_without_guessing():
    """An axis the mapping table does not know is degraded with an
    explanatory reason — no dose is invented for it."""
    from v4.zonos3_steering import resolve_steering

    # A Zonos3Annotation cannot hold an unknown axis (Literal), so use a
    # plain object exposing the same attribute surface.
    class _Ann:
        axis = "not_an_axis"
        value = 0.5
        span_start = None
        span_end = None

    res = resolve_steering([_Ann()], _controls_index())
    assert res.controls == {}
    assert ("not_an_axis", "axe inconnu du mapping") in res.degraded_axes


def test_parse_axis_value_forms():
    """parse_axis_value coerces the accepted value forms into [-1, 1] and
    returns None (not a guess) for anything unreadable."""
    from v4.zonos3_steering import parse_axis_value

    assert parse_axis_value(0.5) == 0.5
    assert parse_axis_value(-3.0) == -1.0  # clamped
    assert parse_axis_value(2) == 1.0  # int, clamped
    # String forms: "pace-2" -> sign -, magnitude 2, /8 -> -0.25.
    assert parse_axis_value("pace-2") == -0.25
    assert parse_axis_value("+1.5") == 0.1875  # 1.5/8
    # Unreadable forms -> None.
    assert parse_axis_value(True) is None  # bool is not a number
    assert parse_axis_value("") is None
    assert parse_axis_value("lively") is None  # no digits
    assert parse_axis_value(None) is None


def test_fallback_text_renders_bracket_tags_deduped():
    """fallback_text renders the FishAudio tags as a [bracket] prefix and
    drops duplicates (the same axis can degrade on several spans)."""
    from v4.zonos3_steering import fallback_text

    assert fallback_text([]) == ""
    assert fallback_text(["excited", "happy"]) == "[excited] [happy]"
    # Duplicates collapse to one occurrence, order preserved.
    assert fallback_text(["angry", "angry", "sad"]) == "[angry] [sad]"


def test_annotations_from_tags_rule_bridge():
    """annotations_from_tags is the deterministic FishAudio-tag ->
    continuous-axis bridge shared by P4 and P5: each mapped tag becomes
    one rule-sourced annotation carrying the original tag as its
    fallback_tag; unmapped tags are skipped, not invented."""
    from v4.zonos3_steering import annotations_from_tags

    anns = annotations_from_tags(7, ["excited", "whispering", "rustling sound"])
    # "rustling sound" has no continuous counterpart -> skipped.
    assert len(anns) == 2
    by_axis = {a.axis: a for a in anns}
    assert set(by_axis) == {"arousal", "projection"}
    assert by_axis["arousal"].value == 0.6
    assert by_axis["arousal"].source == "rule"
    assert by_axis["arousal"].fallback_tag == "excited"
    assert by_axis["projection"].value == -0.6
    for a in anns:
        assert a.segment_id == 7
        assert a.fallback_tag in ("excited", "whispering")


def test_annotations_from_tags_empty_when_no_mapped_tags():
    from v4.zonos3_steering import annotations_from_tags

    assert annotations_from_tags(3, []) == []
    assert annotations_from_tags(3, ["rustling sound", "gasp"]) == []


# ---------------------------------------------------------------------------
# HTTP client (v4/zonos3_client.py)
# ---------------------------------------------------------------------------

def _fake_response(content=b"FAKEWAV", json_data=None, headers=None):
    """A minimal stand-in for a requests.Response."""
    resp = mock.Mock()
    resp.content = content
    resp.headers = headers or {}
    resp.json.return_value = json_data if json_data is not None else {}
    resp.raise_for_status.return_value = None
    return resp


def test_zonos3_tts_builds_generate_payload():
    """zonos3_tts POSTs to /v2/generate with the wire shape the server
    reads (measured 2026-11-27): a listed language code, a non-streaming
    WAV request, steering controls, control spans as a LIST of
    {start, end, controls}, and the reference clip base64 when given a
    path. requests is mocked: no network, no service."""
    import v4.zonos3_client as client

    with mock.patch.object(client, "requests") as req:
        req.post.return_value = _fake_response(
            content=b"XYZ", headers={"X-Seed": "77", "X-Control-Span-Follow": "rate"}
        )
        audio, seed_used = client.zonos3_tts(
            "Un texte de test.",
            reference_id="emb-1",
            seed=7,
            controls={"mood.arousal": 6.0},
            control_spans=[
                {"start": 0, "end": 5, "controls": {"delivery.tempo": -1.0}}
            ],
        )

    assert audio == b"XYZ"
    assert seed_used == 77
    assert req.post.called
    url = req.post.call_args[0][0]
    kwargs = req.post.call_args[1]
    assert url == f"{client.ZONOS3_URL}/v2/generate"
    payload = kwargs["json"]
    assert payload["text"] == "Un texte de test."
    assert payload["seed"] == 7
    assert payload["controls"] == {"mood.arousal": 6.0}
    assert payload["control_spans"] == [
        {"start": 0, "end": 5, "controls": {"delivery.tempo": -1.0}}
    ]
    # ``fr`` is answered 400 Unsupported language code.
    assert payload["language"] == "fr_fr"
    # format=wav needs stream=false; the server default is stream=true.
    assert payload["format"] == "wav"
    assert payload["stream"] is False
    assert "max_tokens" not in payload  # the server default keeps the ceiling
    # A reference id without a clip is sent as an embedding id.
    assert payload["speaker_embedding_id"] == "emb-1"
    assert "speaker_audio_base64" not in payload


def test_zonos3_tts_logs_the_body_of_a_refusal():
    """A refusal is diagnosed by its body: the server names the clause
    the request broke there (measured: ``400 Unsupported language code:
    'fr'``).  The status alone cannot tell a wrong language code from a
    malformed span."""
    import v4.zonos3_client as client

    resp = _fake_response(content=b"")
    resp.text = '{"detail":"Unsupported language code: \'fr\'."}'
    resp.raise_for_status.side_effect = client.requests.HTTPError(
        "400 Client Error: Bad Request", response=resp
    )
    # Only ``post`` is patched: replacing the whole ``requests`` module
    # would also replace ``requests.RequestException``, which the client's
    # ``except`` clause needs to be a real class.
    with mock.patch.object(client.requests, "post") as post, mock.patch.object(
        client, "logger"
    ) as log:
        post.return_value = resp
        audio, seed_used = client.zonos3_tts("Un texte", language="fr")

    assert audio is None
    assert seed_used is None
    log.error.assert_called_once()
    template, error, detail = log.error.call_args.args
    assert "ZONOS3 TTS error" in template
    assert "400" in str(error)
    assert "Unsupported language code: 'fr'" in detail


def test_zonos3_tts_never_sends_the_dict_span_form():
    """control_spans as a per-direction dict is answered 422 by the server
    (measured): the client refuses that shape locally rather than losing
    the request to it."""
    import v4.zonos3_client as client

    with mock.patch.object(client, "requests") as req:
        req.post.return_value = _fake_response(content=b"X")
        client.zonos3_tts("Un texte", control_spans={"delivery.tempo": [[0, 5]]})
    assert "control_spans" not in req.post.call_args[1]["json"]


def test_zonos3_tts_drops_the_spans_the_server_would_refuse():
    """A span outside the request text is answered 400 for the WHOLE
    request (measured: ``control span [a, b) is outside the text``), so
    one stale sidecar offset would cost the segment.  The client drops
    the offending spans and keeps the valid ones."""
    import v4.zonos3_client as client

    valid = {"start": 0, "end": 5, "controls": {"delivery.tempo": -1.0}}
    with mock.patch.object(client, "requests") as req:
        req.post.return_value = _fake_response(
            content=b"X", headers={"X-Control-Span-Follow": "rate"}
        )
        client.zonos3_tts(
            "court",  # 5 code points
            control_spans=[
                valid,
                # past the end
                {"start": 0, "end": 6, "controls": {"delivery.tempo": -1.0}},
                # reversed
                {"start": 5, "end": 2, "controls": {"delivery.tempo": -1.0}},
                {"start": 0, "end": 5, "controls": {}},  # nothing to apply
                # unreadable dose
                {"start": 0, "end": 5, "controls": {"delivery.tempo": "x"}},
                "not a span",
            ],
        )
    assert req.post.call_args[1]["json"]["control_spans"] == [valid]


def test_zonos3_tts_sends_the_bearer_token_only_when_armed():
    """With ZONOS3_ACCESS_TOKEN armed on the server every route answers
    403 without the header (measured).  The client presents the token
    when one is configured and sends no Authorization header otherwise."""
    import v4.zonos3_client as client

    with mock.patch.object(client, "requests") as req, \
         mock.patch.object(client, "ZONOS3_ACCESS_TOKEN", "placeholder-token"):
        req.post.return_value = _fake_response(content=b"X")
        req.get.return_value = _fake_response(json_data={"directions": {}})
        client.zonos3_tts("t")
        client.zonos3_controls()
        bearer = {"Authorization": "Bearer placeholder-token"}
        assert req.post.call_args[1]["headers"] == bearer
        assert req.get.call_args[1]["headers"] == bearer

    with mock.patch.object(client, "requests") as req, \
         mock.patch.object(client, "ZONOS3_ACCESS_TOKEN", ""):
        req.post.return_value = _fake_response(content=b"X")
        client.zonos3_tts("t")
    assert req.post.call_args[1]["headers"] == {}


def test_zonos3_tts_warns_when_its_spans_were_not_followed():
    """The server answers a request that had spans with
    ``X-Control-Span-Follow``; a 200 without it means no span was
    applied, which must be said rather than taken for a steered render."""
    import v4.zonos3_client as client

    span = [{"start": 0, "end": 5, "controls": {"delivery.tempo": -1.0}}]
    with mock.patch.object(client, "requests") as req, \
         mock.patch.object(client, "logger") as log:
        req.post.return_value = _fake_response(content=b"X", headers={})
        client.zonos3_tts("court", control_spans=span)
    assert any(
        "X-Control-Span-Follow" in call.args[0]
        for call in log.warning.call_args_list
    )

    with mock.patch.object(client, "requests") as req, \
         mock.patch.object(client, "logger") as log:
        req.post.return_value = _fake_response(
            content=b"X", headers={"X-Control-Span-Follow": "rate"}
        )
        client.zonos3_tts("court", control_spans=span)
    assert not any(
        "X-Control-Span-Follow" in call.args[0]
        for call in log.warning.call_args_list
    )


def test_zonos3_tts_forwards_an_explicit_frame_budget():
    """``max_tokens`` is the server's own frame budget: it is forwarded
    when given and capped by the server at MAX_AUDIO_FRAMES."""
    import v4.zonos3_client as client

    with mock.patch.object(client, "requests") as req:
        req.post.return_value = _fake_response(content=b"X")
        client.zonos3_tts("t", max_tokens=1000)
    assert req.post.call_args[1]["json"]["max_tokens"] == 1000


def test_request_ceiling_is_the_measured_cut_value():
    """The ceiling constants encode the measured contract: the budget is
    2 000 frames, the prompt takes a constant 9, one frame is 1/15 s —
    so one request renders at most 1 991 frames = 132.733 s."""
    from v4.zonos3_client import (
        FRAME_SECONDS,
        MAX_AUDIO_FRAMES,
        MAX_RENDER_SECONDS,
        PROMPT_FRAME_OVERHEAD,
    )

    assert (MAX_AUDIO_FRAMES, PROMPT_FRAME_OVERHEAD) == (2000, 9)
    assert round(FRAME_SECONDS, 6) == round(2940 / 44100, 6)
    assert round(MAX_RENDER_SECONDS / FRAME_SECONDS) == 1991
    assert round(MAX_RENDER_SECONDS, 3) == 132.733


def test_zonos3_ensure_up_skips_a_remote_host():
    """Waking is only this machine's container to do: a ZONOS3_URL on
    another host is used, never woken — it returns True without probing
    or starting anything."""
    import v4.zonos3_client as client

    with mock.patch.object(client, "ZONOS3_URL", "http://gpu-node:1919"), \
         mock.patch.object(client, "requests") as req, \
         mock.patch.object(client, "_import_ensure_service_up") as organ:
        assert client.zonos3_ensure_up() is True
    organ.assert_not_called()
    req.get.assert_not_called()


def test_zonos3_ensure_up_goes_through_the_shared_organ_on_loopback():
    """On loopback the wake is the shared organ's (``service_wake
    .ensure_service_up``): this module does not carry a second
    implementation of probe-then-docker-start-then-poll."""
    import v4.zonos3_client as client

    organ = mock.Mock(return_value=True)
    with mock.patch.object(client, "ZONOS3_URL", "http://127.0.0.1:1919"), \
         mock.patch.object(client, "ZONOS3_ACCESS_TOKEN", "placeholder-token"), \
         mock.patch.object(client, "_import_ensure_service_up", return_value=organ):
        assert client.zonos3_ensure_up(timeout=5, poll_interval=1) is True
    organ.assert_called_once_with(
        "tts-zonos3",
        "http://127.0.0.1:1919/v2/health",
        api_key="placeholder-token",
        timeout=5,
        poll_interval=1,
    )


def test_zonos3_ensure_up_reports_a_failure_without_raising():
    """A service that cannot be brought up yields False — the seam raises
    its typed error; the wake itself never raises.  Without the organ
    only an already-running service can answer, and then the plain probe
    decides."""
    import v4.zonos3_client as client

    with mock.patch.object(client, "ZONOS3_URL", "http://127.0.0.1:1919"), \
         mock.patch.object(client, "_import_ensure_service_up",
                           return_value=mock.Mock(return_value=False)):
        assert client.zonos3_ensure_up() is False

    with mock.patch.object(client, "ZONOS3_URL", "http://127.0.0.1:1919"), \
         mock.patch.object(client, "_import_ensure_service_up", return_value=None), \
         mock.patch.object(client, "_probe_health", return_value=False) as probe:
        assert client.zonos3_ensure_up() is False
    probe.assert_called_once_with("http://127.0.0.1:1919/v2/health")


def test_zonos3_tts_reference_clip_base64():
    """When a raw reference clip path is given, it takes precedence over
    the embedding id and is sent base64-encoded."""
    import v4.zonos3_client as client

    with mock.patch.object(client, "requests") as req, \
         mock.patch.object(client, "open", mock.mock_open(read_data=b"RAW")):
        req.post.return_value = _fake_response(content=b"X")
        client.zonos3_tts("t", reference_id="emb-1", reference_audio_path="/ref.wav")

    payload = req.post.call_args[1]["json"]
    import base64
    assert payload["speaker_audio_base64"] == base64.b64encode(b"RAW").decode("ascii")
    assert "speaker_embedding_id" not in payload


def test_zonos3_tts_captures_x_seed_not_invented():
    """The seed returned is the one the runtime reports in X-Seed. When
    the header is absent the returned seed is None — never a substituted
    value (acceptance #6: the seed is captured, never invented)."""
    import v4.zonos3_client as client

    with mock.patch.object(client, "requests") as req:
        req.post.return_value = _fake_response(content=b"X", headers={})
        _audio, seed_used = client.zonos3_tts("t", seed=42)
    assert seed_used is None  # absent header -> None, not 42

    with mock.patch.object(client, "requests") as req:
        req.post.return_value = _fake_response(
            content=b"X", headers={"X-Seed": "12345"}
        )
        _audio, seed_used = client.zonos3_tts("t", seed=42)
    assert seed_used == 12345


def test_zonos3_tts_returns_none_on_failure():
    """A transport failure (4xx/5xx, connection error) yields (None,
    None) — the caller raises the typed narrator-unavailable error. No
    exception leaks out of the client."""
    import requests as _requests
    import v4.zonos3_client as client

    with mock.patch.object(client, "requests") as req:
        # Patching the whole module turns `requests.RequestException` into a
        # Mock; restore the real class so the client's `except` clause works.
        req.RequestException = _requests.RequestException
        req.post.side_effect = _requests.RequestException("boom")
        audio, seed_used = client.zonos3_tts("t")
    assert audio is None
    assert seed_used is None


def test_zonos3_controls_returns_empty_on_failure():
    """/v2/controls is the authority on steerable directions. On failure
    it returns {} so the resolver degrades every axis rather than
    steering a direction it cannot verify."""
    import requests as _requests
    import v4.zonos3_client as client

    with mock.patch.object(client, "requests") as req:
        req.RequestException = _requests.RequestException
        req.get.side_effect = _requests.RequestException("down")
        assert client.zonos3_controls() == {}
    with mock.patch.object(client, "requests") as req:
        req.get.return_value = _fake_response(json_data={"mood": ["mood.valence"]})
        assert client.zonos3_controls() == {"mood": ["mood.valence"]}


# ---------------------------------------------------------------------------
# Sidecar (v4/p4_annotation.py + v4/schemas.py)
# ---------------------------------------------------------------------------

def test_build_zonos3_sidecar_from_tags():
    """build_zonos3_sidecar turns an AnnotatedBatch's per-segment tags
    into the Zonos3AnnotationBatch sidecar via the shared rule bridge.
    A segment with no mappable tags contributes nothing."""
    from v4.p4_annotation import build_zonos3_sidecar
    from v4.schemas import AnnotatedBatch, AnnotatedSegment

    batch = AnnotatedBatch(
        segments=[
            AnnotatedSegment(
                seg_index=0,
                speaker="narrateur",
                type="narration",
                text="Il arriva.",
                annotated_text="[excited] Il arriva.",
            ),
            AnnotatedSegment(
                seg_index=1,
                speaker="loiseau",
                type="dialogue",
                text="Non.",
                annotated_text="[rustling sound] Non.",
            ),
        ]
    )
    sidecar = build_zonos3_sidecar(batch.segments)
    # Only seg 0 has a mappable tag ("excited" -> arousal).
    assert len(sidecar.annotations) == 1
    ann = sidecar.annotations[0]
    assert ann.segment_id == 0
    assert ann.axis == "arousal"
    assert ann.fallback_tag == "excited"
    # for_segment filters correctly.
    assert len(sidecar.for_segment(0)) == 1
    assert sidecar.for_segment(1) == []


def test_zonos3_annotation_batch_roundtrips_json():
    """The sidecar must serialize and deserialize losslessly (it is
    written to disk between P4 and P5)."""
    from v4.schemas import Zonos3Annotation, Zonos3AnnotationBatch
    import json as _json

    batch = Zonos3AnnotationBatch(
        annotations=[
            Zonos3Annotation(
                segment_id=5,
                span_start=2,
                span_end=9,
                axis="pace",
                value=-0.4,
                intent="ralentir",
                source="llm",
                confidence=0.8,
            )
        ]
    )
    restored = Zonos3AnnotationBatch.model_validate_json(
        _json.dumps(batch.model_dump())
    )
    assert restored == batch
