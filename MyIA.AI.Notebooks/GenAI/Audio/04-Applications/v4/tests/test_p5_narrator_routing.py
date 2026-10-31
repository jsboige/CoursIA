"""F6 narrator routing to Qwen3-TTS VoiceDesign (Issue #15002) — offline tests.

These tests construct AnnotatedSegment instances and verify the routing
decision + bracket-stripping without ever hitting the Qwen3-TTS gateway.
The live gateway is exercised by the run-level smoke in the PR body
(commit hash + byte counts) — these tests guard the dispatch logic.

Run from the v4 directory:
    python -m pytest tests/test_p5_narrator_routing.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

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


def test_routes_narrator_to_qwen_when_flag_on():
    """When NARRATOR_QWEN_ROUTING is forced ON, narrator segments route.
    The default flipped to "0" (FishAudio narrator) in #19454: the Qwen
    narrator degrades literary French to ~0.52 WER while the FishAudio
    clone transcribes at 0.000-0.067 on the same witness segments."""
    from v4 import p5_tts

    original = p5_tts._NARRATOR_QWEN_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = True
        seg = _build_seg(speaker="narrateur")
        assert p5_tts._should_route_narrator_to("qwen_voicedesign", seg) is True
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = original


def test_qwen_off_by_default_fish_narrator():
    """Default post-#19454: no narrator engine flag is on, so the narrator
    falls back to the FishAudio S2-Pro clone (legacy path). The measured
    WER drove the flip: Qwen narrator ~0.52 on literary French, FishAudio
    clone 0.000-0.067 on witness segments 19/38/114 (whisper
    large-v3-turbo fr, methodology of #19453)."""
    from v4 import p5_tts

    assert p5_tts._NARRATOR_QWEN_ROUTING is False
    assert p5_tts._selected_narrator_engine() is None
    seg = _build_seg(speaker="narrateur")
    assert p5_tts._should_route_narrator_to("qwen_voicedesign", seg) is False


def test_does_not_route_non_narrator_speakers():
    """Acceptance #1: routing is limited to narrateur; other speakers stay
    on FishAudio clone even when an engine flag is ON."""
    from v4.p5_tts import _should_route_narrator_to

    for engine in ("qwen_voicedesign", "cosyvoice3"):
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
            assert _should_route_narrator_to(engine, seg) is False, (
                f"non-narrator speaker '{speaker}' must NOT route to {engine}"
            )


def test_routes_off_when_flag_disabled():
    """Env flag NARRATOR_QWEN_ROUTING=0 with no other engine selected
    disables routing (legacy FishAudio path)."""
    from v4 import p5_tts

    original = p5_tts._NARRATOR_QWEN_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = False
        seg = _build_seg(speaker="narrateur")
        assert p5_tts._should_route_narrator_to("qwen_voicedesign", seg) is False
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = original


def test_cosyvoice3_off_by_default():
    """Phase 1 (#19692): CosyVoice3 routing is OFF by default — the default
    narrator engine does not change until the association's listening picks
    the winner (#17586)."""
    from v4 import p5_tts

    assert p5_tts._NARRATOR_COSYVOICE3_ROUTING is False


def test_cosyvoice3_routes_when_selected():
    """With Qwen off and CosyVoice3 on, the narrator routes to CosyVoice3
    and NOT to Qwen — engine selection is exclusive by construction."""
    from v4 import p5_tts

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = False
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = True
        seg = _build_seg(speaker="narrateur")
        assert p5_tts._should_route_narrator_to("cosyvoice3", seg) is True
        assert p5_tts._should_route_narrator_to("qwen_voicedesign", seg) is False
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3


def test_both_engine_flags_active_raises():
    """Two active engine flags are a configuration error, never a silent
    precedence — same no-silent-swap contract as #15002 acceptance 6."""
    from v4 import p5_tts

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = True
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = True
        seg = _build_seg(speaker="narrateur")
        try:
            p5_tts._should_route_narrator_to("cosyvoice3", seg)
        except ValueError:
            pass
        else:
            raise AssertionError("two active engine flags must raise ValueError")
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3


def test_selected_narrator_engine_none_when_all_off():
    """No flag on -> None (legacy FishAudio narrator), not an error."""
    from v4 import p5_tts

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = False
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = False
        assert p5_tts._selected_narrator_engine() is None
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3


def test_strip_brackets_for_qwen_removes_inline_tags():
    """VoiceDesign receives the bare text; brackets would be ignored or,
    worse, vocalized (WER regression #1277/#1485 on FishAudio bracket text).
    The narrator branch must strip them BEFORE sending to Qwen."""
    from v4.p5_tts import _strip_brackets_for_qwen

    stripped = _strip_brackets_for_qwen(
        "[emphasis] Les voyageurs se regardaient [whispering] avec une certaine honte."
    )
    assert stripped == "Les voyageurs se regardaient avec une certaine honte."
    assert "[" not in stripped and "]" not in stripped


def test_strip_brackets_handles_empty_input():
    """Empty or whitespace-only input after stripping must raise the
    narrator-unavailable signal — it indicates upstream P4 produced no
    renderable text and we refuse to fabricate audio."""
    from v4.p5_tts import _strip_brackets_for_qwen

    assert _strip_brackets_for_qwen("") == ""
    assert _strip_brackets_for_qwen("[whispering]") == ""
    assert _strip_brackets_for_qwen("   \n  ") == ""


def test_narrator_reference_id_is_qwen_sentinel():
    """The narrator branch must stamp a distinct reference_id so downstream
    consumers (tts_results.json, p7 WER, p8 listener review) can tell which
    engine produced the audio without re-decoding the MP3."""
    from v4.p5_tts import _QWEN_NARRATOR_REFERENCE_ID

    assert _QWEN_NARRATOR_REFERENCE_ID == "qwen-voicedesign-narrator-fr-literary"
    # And it must NOT collide with any FishAudio voice id (prefixed `v4_`).
    assert not _QWEN_NARRATOR_REFERENCE_ID.startswith("v4_")


def test_narrator_instructions_within_server_cap():
    """VoiceDesign server caps `instructions` at 500 chars (qwen_tts_client
    MAX_INSTRUCTIONS_LEN). The narrator instructions must stay under."""
    from v4.p5_tts import _QWEN_NARRATOR_INSTRUCTIONS
    from v4.prosody_lab.qwen_tts_client import MAX_INSTRUCTIONS_LEN

    assert len(_QWEN_NARRATOR_INSTRUCTIONS) <= MAX_INSTRUCTIONS_LEN, (
        f"instructions length {len(_QWEN_NARRATOR_INSTRUCTIONS)} "
        f"exceeds server cap {MAX_INSTRUCTIONS_LEN}"
    )


def test_narrator_unavailable_is_runtime_error():
    """NarratorQwenUnavailable must be a RuntimeError so callers can catch
    a single class for any Qwen-side failure (gateway 4xx/5xx, render fail,
    WAV->MP3 conversion)."""
    from v4.p5_tts import NarratorQwenUnavailable

    assert issubclass(NarratorQwenUnavailable, RuntimeError)
    # Raising preserves the call chain for diagnosis.
    try:
        raise NarratorQwenUnavailable("test")
    except RuntimeError as exc:
        assert str(exc) == "test"


def test_synthesize_narrator_qwen_raises_on_empty_input():
    """If upstream P4 produces no renderable text, _synthesize_narrator_qwen
    must raise NarratorQwenUnavailable rather than write an empty MP3 or
    silently fall back. The pipeline surfaces this as a hard failure."""
    from v4.p5_tts import (
        NarratorQwenUnavailable,
        _synthesize_narrator_qwen,
    )

    seg = _build_seg(speaker="narrateur", text="")
    try:
        _synthesize_narrator_qwen(
            seg=seg,
            fishaudio_text="   \n  ",  # whitespace-only after strip
            mp3_path=Path("/tmp/should_never_be_written.mp3"),
            seed=42,
            text_hash="deadbeef",
        )
    except NarratorQwenUnavailable:
        return  # success: raised as designed
    raise AssertionError("NarratorQwenUnavailable not raised on empty input")


def test_synthesize_batch_propagates_narrator_hard_failure():
    """A Qwen narrator failure must ABORT the batch, not be absorbed into a
    survivable status="failed" record.

    The gap was measured in review of PR #19453: the typed
    NarratorQwenUnavailable was caught by the generic `except Exception`
    handler, and run()'s final guard only fires when NOTHING was generated.
    A Qwen gateway outage with FishAudio healthy for every other speaker
    therefore finished the pass with the narrator segments silently missing --
    exactly the regression the typed exception exists to surface.
    """
    from v4 import p5_tts
    from v4.schemas import AnnotatedSegment

    text = "Un texte narrateur volontairement non cache."
    seg = AnnotatedSegment(
        seg_index=987654,  # distinctive: no cached mp3 can match it
        speaker="narrateur",
        type="narration",
        text=text,
        annotated_text=text,
    )

    def _boom(_seg, _text):
        raise p5_tts.NarratorQwenUnavailable("gateway :8196 unreachable")

    original_seg, original_thermal = (
        p5_tts._synthesize_segment,
        p5_tts.thermal_wait,
    )
    try:
        p5_tts._synthesize_segment = _boom
        p5_tts.thermal_wait = lambda *a, **k: None
        p5_tts._synthesize_batch([(seg, text)])
    except p5_tts.NarratorQwenUnavailable:
        return  # success: propagated instead of degraded
    finally:
        p5_tts._synthesize_segment = original_seg
        p5_tts.thermal_wait = original_thermal
    raise AssertionError(
        "NarratorQwenUnavailable was absorbed by the generic handler -- the "
        "pass would ship an audiobook with narrator segments missing"
    )


def test_compose_tts_text_keeps_full_text_for_cosyvoice3_narrator():
    """Phase 1 (#19692): the 500-char cap in _compose_tts_text is an S2-Pro
    input limit. A narrator rerouted to CosyVoice3 is bounded per-chunk by
    _chunk_narration instead — truncating here silently drops the tail of
    every long narration (measured: seg 1, 981 chars -> ~440 rendered,
    17.8 s of audio for a 950-char segment = an omission p7's control
    would attribute to the engine). Default (Qwen) and non-narrator
    speakers keep the cap: their engines really do have it."""
    from v4 import p5_tts

    long_text = (
        "Pendant plusieurs jours de suite des lambeaux d'armee en deroute "
        "avaient traverse la ville. " * 8
    ).strip()
    assert len(long_text) > p5_tts._MAX_TTS_CHARS

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    try:
        # CosyVoice3 selected: narrator keeps the full text.
        p5_tts._NARRATOR_QWEN_ROUTING = False
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = True
        narrator = _build_seg(speaker="narrateur", text=long_text)
        composed = p5_tts._compose_tts_text(narrator)
        assert len(composed) > p5_tts._MAX_TTS_CHARS
        assert not composed.endswith("...")
        assert long_text[: p5_tts._MAX_TTS_CHARS] in composed

        # Same flags, non-narrator: S2-Pro path keeps its cap.
        speaker = _build_seg(speaker="loiseau", text=long_text)
        capped = p5_tts._compose_tts_text(speaker)
        assert len(capped) <= p5_tts._MAX_TTS_CHARS
        assert capped.endswith("...")
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3

    # Post-#19454 default (FishAudio narrator): the S2-Pro path keeps the
    # cap for every speaker, narrator included.
    narrator = _build_seg(speaker="narrateur", text=long_text)
    composed = p5_tts._compose_tts_text(narrator)
    assert len(composed) <= p5_tts._MAX_TTS_CHARS
    assert composed.endswith("...")


def test_strip_brackets_never_glues_neighbouring_words():
    """A mid-text tag must become a space, never nothing: the old pattern
    ate the tag plus its trailing whitespace and glued the neighbours
    ("route,[short pause] quand" -> "route,quand"). Measured #19692:
    CosyVoice3 fed such a glued run-on omits everything before the glue
    point (seg 57: audio starts at "quand"), and the gluing also hides
    sentence boundaries from the CV3 chunker."""
    from v4.p5_tts import _strip_brackets_for_qwen

    stripped = _strip_brackets_for_qwen(
        "[breathing]Chacun guettait pour apercevoir un cabaret sur la route,"
        "[short pause] quand la diligence sombra dans un amoncellement "
        "de neige[pause] et il fallut deux heures pour la dégager."
    )
    assert "route, quand la diligence" in stripped
    assert "neige et il fallut" in stripped
    assert "route,quand" not in stripped
    assert "neigeet" not in stripped
    # A tag between two sentences restores the boundary instead of eating it.
    assert _strip_brackets_for_qwen(
        "Ils entrèrent dans la ville.[pause] On voyait des soldats."
    ) == "Ils entrèrent dans la ville. On voyait des soldats."


# ---------------------------------------------------------------------------
# Phase 2 (#17586 acceptance) — Qwen3-TTS CustomVoice narrator routing
# ---------------------------------------------------------------------------

def test_customvoice_off_by_default():
    """Phase 2: CustomVoice routing is OFF by default. The user confirmed
    voice B at 09:10Z on 15/10, but the custom-voice route shape on the
    self-hosted TTS gateway (`tts-api.myia.io/v1`, HTTP 200 on /v1/models
    as of c.1672 2026-10-15) is still TBD by ops. The default narrator
    engine is the FishAudio clone since #19454; CustomVoice activates only
    after ops publishes the route AND the user (or ai-01) flips the flag.
    No silent engine swap (acceptance #6 of #15002)."""
    from v4 import p5_tts

    assert p5_tts._NARRATOR_CUSTOMVOICE_ROUTING is False
    # The CustomVoice branch must not be the selected engine by default.
    seg = _build_seg(speaker="narrateur")
    assert p5_tts._should_route_narrator_to("customvoice", seg) is False


def test_routes_narrator_to_customvoice_when_flag_on():
    """When NARRATOR_CUSTOMVOICE_ROUTING is ON and no other narrator
    engine is selected, narrator segments route to CustomVoice. The flag
    is opt-in: the user confirmed voice B but the activation is reserved
    to the ops-aware launch (after the endpoint is published)."""
    from v4 import p5_tts

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    orig_cv = p5_tts._NARRATOR_CUSTOMVOICE_ROUTING
    try:
        # CustomVoice is exclusive with the other engines (same contract
        # as #15002 acceptance 6): flip Qwen and CV3 OFF before turning
        # CustomVoice ON, otherwise _selected_narrator_engine raises.
        p5_tts._NARRATOR_QWEN_ROUTING = False
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = False
        p5_tts._NARRATOR_CUSTOMVOICE_ROUTING = True
        seg = _build_seg(speaker="narrateur")
        assert p5_tts._should_route_narrator_to("customvoice", seg) is True
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3
        p5_tts._NARRATOR_CUSTOMVOICE_ROUTING = orig_cv


def test_does_not_route_non_narrator_to_customvoice():
    """Acceptance #1 (carries over from #15002): CustomVoice routing is
    limited to the narrateur speaker. Every other speaker stays on
    FishAudio clone even when the CustomVoice flag is ON."""
    from v4 import p5_tts

    original = p5_tts._NARRATOR_CUSTOMVOICE_ROUTING
    try:
        p5_tts._NARRATOR_CUSTOMVOICE_ROUTING = True
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
            assert p5_tts._should_route_narrator_to("customvoice", seg) is False, (
                f"non-narrator speaker '{speaker}' must NOT route to customvoice"
            )
    finally:
        p5_tts._NARRATOR_CUSTOMVOICE_ROUTING = original


def test_customvoice_gateway_failure_raises_typed_error():
    """La route CustomVoice appelle le gateway (client `qwen_tts_customvoice`
    deja livre sur main, meme socket que VoiceDesign). Un gateway
    injoignable doit lever NarratorCustomVoiceUnavailable -- jamais un
    repli silencieux sur FishAudio (acceptance #6 de #15002).

    L'appel est simule : aucun reseau en CI, aucun delai. Le test qui
    precedait (c.1672) attendait un squelette qui leveait sans appeler --
    obsolete depuis le cablage reel de la route.
    """
    from v4 import p5_tts
    from v4.schemas import AnnotatedSegment
    import v4.prosody_lab.qwen_tts_client as client

    text = "Un texte narrateur volontairement non cache pour CustomVoice."
    seg = AnnotatedSegment(
        seg_index=888001,  # distinctive: no cached mp3 can match
        speaker="narrateur",
        type="narration",
        text=text,
        annotated_text=text,
    )

    original = client.qwen_tts_customvoice_chunked
    try:
        # The chunked helper returns None on any gateway failure.
        client.qwen_tts_customvoice_chunked = lambda *a, **k: None
        try:
            p5_tts._synthesize_narrator_customvoice(
                seg=seg,
                fishaudio_text=text,
                mp3_path=Path("/tmp/should_never_be_written_customvoice.mp3"),
                seed=42,
                text_hash="deadbeef",
            )
        except p5_tts.NarratorCustomVoiceUnavailable:
            return  # success: raised as designed
    finally:
        client.qwen_tts_customvoice_chunked = original
    raise AssertionError(
        "NarratorCustomVoiceUnavailable not raised on gateway failure"
    )


def test_synthesize_batch_propagates_customvoice_hard_failure():
    """Une panne du gateway CustomVoice doit ARRETER le batch, pas etre
    absorbee en status="failed".

    Le meme contrat que
    `test_synthesize_batch_propagates_narrator_hard_failure` : la route
    CustomVoice leve sa propre exception typee, et le gestionnaire generique
    `except Exception` de _synthesize_batch l'absorberait sinon -- le pass
    livrerait alors un audiobook dont les segments narrateur manquent en
    silence.
    """
    from v4 import p5_tts
    from v4.schemas import AnnotatedSegment

    text = "Un texte narrateur volontairement non cache."
    seg = AnnotatedSegment(
        seg_index=987655,  # distinctive: no cached mp3 can match it
        speaker="narrateur",
        type="narration",
        text=text,
        annotated_text=text,
    )

    def _boom(_seg, _text):
        raise p5_tts.NarratorCustomVoiceUnavailable("gateway :8196 unreachable")

    original_seg, original_thermal = (
        p5_tts._synthesize_segment,
        p5_tts.thermal_wait,
    )
    try:
        p5_tts._synthesize_segment = _boom
        p5_tts.thermal_wait = lambda *a, **k: None
        p5_tts._synthesize_batch([(seg, text)])
    except p5_tts.NarratorCustomVoiceUnavailable:
        return  # success: propagated instead of degraded
    finally:
        p5_tts._synthesize_segment = original_seg
        p5_tts.thermal_wait = original_thermal
    raise AssertionError(
        "NarratorCustomVoiceUnavailable was absorbed by the generic handler -- "
        "the pass would ship an audiobook with narrator segments missing"
    )


def test_customvoice_cache_sentinel_embeds_the_speaker():
    """La sentinelle de cache encode le speaker : re-pointer
    NARRATOR_CUSTOMVOICE_SPEAKER invalide le cache, donc un MP3 rendu par
    une autre voix n'est jamais resservi."""
    from v4 import p5_tts

    ref_aiden = p5_tts._customvoice_narrator_reference_id("aiden")
    ref_dylan = p5_tts._customvoice_narrator_reference_id("dylan")
    assert "aiden" in ref_aiden
    assert "dylan" in ref_dylan
    assert ref_aiden != ref_dylan
    # La sentinelle effective est bien celle du speaker courant.
    assert p5_tts._CUSTOMVOICE_NARRATOR_REFERENCE_ID == (
        p5_tts._customvoice_narrator_reference_id(
            p5_tts._CUSTOMVOICE_NARRATOR_SPEAKER
        )
    )


def test_customvoice_default_speaker_is_supported():
    """Le speaker par defaut est dans la liste supportee (snake_case).

    Source of truth: ``bakeoff_large/clients/qwen3_tts_customvoice.py:50-62``
    (verified first-hand c.818 16:42Z). Hermes Finding 2 (review sur
    69de2cdf) : importer ce client declenche `import torch` au top du
    module, ce qui fait rougir ce test sur un runner CPU sans torch. On
    duplique la liste de 9 chaines ici -- si la liste source evolue, ce test
    sert de signal d'alerte (constant mismatch).
    """
    from v4 import p5_tts

    # DOIT miroiter bakeoff_large/clients/qwen3_tts_customvoice.py:50-62
    # (get_supported_speakers). Liste verify first-hand c.818, snake_case.
    source_of_truth = (
        "aiden", "dylan", "eric", "ono_anna",
        "ryan", "serena", "sohee", "uncle_fu", "vivian",
    )
    assert p5_tts._CUSTOMVOICE_NARRATOR_SPEAKER in source_of_truth, (
        f"default speaker {p5_tts._CUSTOMVOICE_NARRATOR_SPEAKER!r} not in "
        f"supported list (mirror of bakeoff_large/clients/"
        f"qwen3_tts_customvoice.py:50-62): {source_of_truth}"
    )


def test_narrator_engine_reference_ids_covers_exactly_three_engines():
    """La table engine -> sentinelle couvre les trois moteurs, et rien de
    plus : un alias surnumeraire (une cle que le routeur ne selectionne
    jamais) ferait servir un cache d'un moteur pour un autre."""
    from v4 import p5_tts

    assert set(p5_tts._NARRATOR_ENGINE_REFERENCE_IDS) == {
        "qwen_voicedesign",
        "cosyvoice3",
        "customvoice",
    }
    # La table et le routeur doivent decrire le meme ensemble de moteurs.
    assert set(p5_tts._narrator_engine_flags()) == set(
        p5_tts._NARRATOR_ENGINE_REFERENCE_IDS
    )


def test_customvoice_exclusivity_with_other_engines():
    """Two narrator engines active at once is a configuration error (same
    no-silent-swap contract as #15002 acceptance 6). This test covers
    CustomVoice vs Qwen VoiceDesign and CustomVoice vs CosyVoice3."""
    from v4 import p5_tts

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    orig_cv = p5_tts._NARRATOR_CUSTOMVOICE_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = True
        p5_tts._NARRATOR_CUSTOMVOICE_ROUTING = True
        try:
            p5_tts._selected_narrator_engine()
        except ValueError:
            pass  # success: exclusivity raises
        else:
            raise AssertionError(
                "two active narrator engines (Qwen + CustomVoice) did not raise"
            )

        p5_tts._NARRATOR_QWEN_ROUTING = False
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = True
        p5_tts._NARRATOR_CUSTOMVOICE_ROUTING = True
        try:
            p5_tts._selected_narrator_engine()
        except ValueError:
            pass  # success: exclusivity raises
        else:
            raise AssertionError(
                "two active narrator engines (CV3 + CustomVoice) did not raise"
            )
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3
        p5_tts._NARRATOR_CUSTOMVOICE_ROUTING = orig_cv


def test_customvoice_reference_id_is_engine_specific():
    """The narrator cache is keyed on reference_id (#19692). A CustomVoice
    MP3 must carry its own sentinel, distinct from Qwen VoiceDesign and
    CosyVoice3, so a future engine swap cannot silently re-serve a stale
    MP3 from a previous engine."""
    from v4 import p5_tts

    assert p5_tts._CUSTOMVOICE_NARRATOR_REFERENCE_ID != p5_tts._QWEN_NARRATOR_REFERENCE_ID
    assert p5_tts._CUSTOMVOICE_NARRATOR_REFERENCE_ID != p5_tts._CV3_NARRATOR_REFERENCE_ID
    assert p5_tts._NARRATOR_ENGINE_REFERENCE_IDS["customvoice"] == (
        p5_tts._CUSTOMVOICE_NARRATOR_REFERENCE_ID
    )
