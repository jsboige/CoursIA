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

import io
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


# ---------------------------------------------------------------------------
# Steering resolver (v4/zonos3_steering.py)
# ---------------------------------------------------------------------------

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


def _served(*directions) -> dict:
    """Build a minimal GET /v2/controls payload advertising a direction set."""
    return {"mood": [list(directions)]}


def test_resolve_steering_translates_sidecar_to_controls():
    """A sidecar axis whose direction the bundle serves becomes a
    controls entry at the declared dose (value * dose_scale)."""
    from v4.zonos3_steering import resolve_steering

    anns = [_annot("arousal", 0.5), _annot("valence", -0.5)]
    res = resolve_steering(anns, _served("mood.arousal", "mood.valence"))
    # dose = 0.5 * 3.2 = 1.6 for both mood-bundle axes (scale 3.2).
    assert res.controls == {"mood.arousal": 1.6, "mood.valence": -1.6}
    assert res.has_steering is True
    assert res.is_degraded is False
    assert res.fallback_tags == []


def test_resolve_steering_degrades_unserved_axis_to_tag():
    """An axis whose direction the bundle does NOT serve degrades to its
    FishAudio fallback tag and is recorded in degraded_axes — never
    silently dropped, never steered on a direction the server lacks."""
    from v4.zonos3_steering import resolve_steering

    # Only mood.arousal is served; dominance is not.
    anns = [_annot("arousal", 0.5), _annot("dominance", 0.6)]
    res = resolve_steering(anns, _served("mood.arousal"))
    assert res.controls == {"mood.arousal": 1.6}
    assert res.is_degraded is True
    # degraded_axes records (axis, REASON) — the tag lives in fallback_tags.
    assert any(axis == "dominance" for axis, _reason in res.degraded_axes)
    assert "angry" in res.fallback_tags


def test_resolve_steering_produces_control_spans():
    """A span-scoped annotation (span_start < span_end) on a served axis
    contributes a control_spans entry with the character range."""
    from v4.zonos3_steering import resolve_steering

    anns = [_annot("pace", -0.5, span=(4, 20))]
    res = resolve_steering(anns, _served("mood.tempo"))
    assert res.control_spans == {"mood.tempo": [[4, 20]]}
    # The whole-segment dose is also present (span + whole are independent).
    assert res.controls == {"mood.tempo": -1.0}


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

    res = resolve_steering([_Ann()], _served("mood.arousal"))
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
    """zonos3_tts POSTs to /v2/generate with the steering controls and
    spans in the payload, and the reference clip base64 when given a
    path. requests is mocked: no network, no service."""
    import v4.zonos3_client as client

    with mock.patch.object(client, "requests") as req:
        req.post.return_value = _fake_response(content=b"XYZ", headers={"X-Seed": "77"})
        audio, seed_used = client.zonos3_tts(
            "Un texte de test.",
            reference_id="emb-1",
            seed=7,
            controls={"mood.arousal": 1.6},
            control_spans={"mood.tempo": [[0, 5]]},
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
    assert payload["controls"] == {"mood.arousal": 1.6}
    assert payload["control_spans"] == {"mood.tempo": [[0, 5]]}
    # A reference id without a clip is sent as an embedding id.
    assert payload["speaker_embedding_id"] == "emb-1"
    assert "speaker_audio_base64" not in payload


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
