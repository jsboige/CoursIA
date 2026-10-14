"""CosyVoice3 narrator path, phase 1 (#19692) — offline tests.

Covers the sentence chunker (identity, max_chars, clause fallback, no
mid-word cut) and the torch-free failure guards of the CV3 synthesis
branch. The live model is exercised by the measured run in the PR body —
these tests guard the chunking and dispatch logic without torch.

Run from the v4 directory:
    python -m pytest tests/test_p5_cv3_narrator.py -v
"""
from __future__ import annotations

import sys
import types
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


# Extract C of the A0C bench (#17586): real narration long enough to need
# clause fallback and multi-chunk grouping.
_EXTRAIT_C = (
    "Pendant plusieurs jours, des fugitifs discrets arrivaient par tous les "
    "chemins, gens du monde, des femmes, des enfants. Des artilleurs "
    "sombres alignés avec des fantassins divers, sans drapeau, sans "
    "régiment, venaient se ranger sous la croix de guerre. Tous semblaient "
    "accablés, éreintés, incapables de comprendre ou de se décider, prêts à "
    "la fuite puis à la bataille. La maison du notaire était pleine, "
    "jour et nuit."
)


def _build_seg(*, speaker: str, text: str = "x"):
    from v4.schemas import AnnotatedSegment

    return AnnotatedSegment(
        seg_index=1,
        speaker=speaker,
        type="narration" if speaker == "narrateur" else "dialogue",
        text=text,
        annotated_text=text,
    )


def test_chunker_preserves_every_word():
    """Identity: chunks reassemble to the source — the chunker can never be
    the source of a dropped passage (#19692's omission class lives in the
    model, the chunker must not add its own)."""
    from v4.p5_tts import _chunk_narration

    for text in (_EXTRAIT_C, "Une seule phrase.", "Trois mots. Quatre mots ici. Et voilà."):
        chunks = _chunk_narration(text)
        assert " ".join(chunks).replace("  ", " ").strip() == " ".join(text.split())


def test_chunker_respects_max_chars():
    """Every chunk stays <= max_chars — the bound the A0C bench measured
    (#17586 spec: 280)."""
    from v4.p5_tts import _chunk_narration

    chunks = _chunk_narration(_EXTRAIT_C)
    assert chunks, "chunker returned nothing for a long narration"
    assert all(len(c) <= 280 for c in chunks), [len(c) for c in chunks]


def test_chunker_splits_at_sentence_boundaries():
    """Chunks break after . ! ? — never mid-word, never mid-sentence when
    the sentence fits (small max_chars forces one sentence per chunk)."""
    from v4.p5_tts import _chunk_narration

    chunks = _chunk_narration("Phrase un. Phrase deux ! Phrase trois ?", max_chars=14)
    assert chunks == ["Phrase un.", "Phrase deux !", "Phrase trois ?"]
    # With the default 280 the greedy packer merges short sentences into one
    # chunk — whole units only, identity preserved.
    merged = _chunk_narration("Phrase un. Phrase deux ! Phrase trois ?")
    assert merged == ["Phrase un. Phrase deux ! Phrase trois ?"]


def test_chunker_clause_fallback_for_long_sentence():
    """A sentence over max_chars falls back to clause boundaries (, ; :)
    rather than truncating mid-word."""
    from v4.p5_tts import _chunk_narration

    long_sentence = (
        "Une phrase très longue, avec des propositions, des virgules, des "
        "points-virgules ; et encore des mots, beaucoup de mots, toujours "
        "plus de mots pour dépasser largement la limite de deux cent "
        "quatre-vingts caractères, encore quelques mots supplémentaires "
        "ici, puis d'autres encore, et enfin une fin de phrase."
    )
    assert len(long_sentence) > 280
    chunks = _chunk_narration(long_sentence)
    assert all(len(c) <= 280 for c in chunks)
    # Identity still holds through the fallback.
    rejoined = " ".join(chunks)
    assert rejoined == " ".join(long_sentence.split())


def test_chunker_refuses_undivisible_clause():
    """A clause longer than max_chars with no , ; : boundary is a hard
    error: a mid-word cut would corrupt the narration instead of failing
    loudly."""
    from v4.p5_tts import _chunk_narration

    monolith = "mot " * 100  # 400 chars, no punctuation
    try:
        _chunk_narration(monolith.strip())
    except ValueError:
        pass
    else:
        raise AssertionError("undivisible clause must raise ValueError, not truncate")


def test_chunker_empty_input_returns_empty():
    from v4.p5_tts import _chunk_narration

    assert _chunk_narration("") == []
    assert _chunk_narration("   \n  ") == []


def test_cv3_unavailable_is_runtime_error():
    """NarratorCosyVoice3Unavailable shares the NarratorQwenUnavailable
    contract: a single RuntimeError class for any CV3-side failure, hard
    failure, never a silent FishAudio fallback (#15002 acceptance 6)."""
    from v4.p5_tts import NarratorCosyVoice3Unavailable, NarratorQwenUnavailable

    assert issubclass(NarratorCosyVoice3Unavailable, RuntimeError)
    assert NarratorCosyVoice3Unavailable is not NarratorQwenUnavailable


def test_cv3_reference_id_is_distinct_sentinel():
    """The CV3 branch stamps its own reference_id so tts_results.json and p7
    can tell which engine rendered a segment."""
    from v4.p5_tts import _CV3_NARRATOR_REFERENCE_ID, _QWEN_NARRATOR_REFERENCE_ID

    assert _CV3_NARRATOR_REFERENCE_ID != _QWEN_NARRATOR_REFERENCE_ID
    assert not _CV3_NARRATOR_REFERENCE_ID.startswith("v4_")


def test_synthesize_narrator_cv3_raises_on_empty_input():
    """Empty text after bracket stripping raises BEFORE any torch import —
    hermetic: the guard must not require the CosyVoice runtime."""
    from v4.p5_tts import NarratorCosyVoice3Unavailable, _synthesize_narrator_cosyvoice3

    seg = _build_seg(speaker="narrateur", text="")
    try:
        _synthesize_narrator_cosyvoice3(
            seg=seg,
            fishaudio_text="[whispering]",  # empty after strip
            mp3_path=Path("should_never_be_written.mp3"),
            seed=42,
            text_hash="deadbeef",
        )
    except NarratorCosyVoice3Unavailable:
        return  # success: raised as designed
    raise AssertionError("NarratorCosyVoice3Unavailable not raised on empty input")


# Durations measured 2026-10-07 by bisect 2/3 (WAV, not MP3) on a free GPU.
# The same text renders 0.04 s at seed 42 -- one speech token, CosyVoice's
# token_hop_len -- and a plausible duration at other seeds; the degeneracy is
# a function of (text, seed), reproducible bit-for-bit within a process.
_MEASURED_DEGENERATE = [
    ("Oui.", 0.04),
    ("Il marcha.", 0.04),
    ("C'était un Bordelais.", 0.04),
    ("C'était un Bordelais", 0.04),  # trailing period is not the trigger
    ("Il marchait lentement sur le quai désert.", 0.04),
    ("Il marchait lentement sur le quai désert.", 0.20),  # seed 43
    ("Le vieux marin regardait.", 0.16),  # seed 7
]
_MEASURED_LEGITIMATE = [
    ("Oui.", 0.36),
    ("Oui.", 0.64),
    ("Il marcha.", 0.76),
    ("Il marcha.", 1.64),
    ("C'était un Bordelais.", 1.16),
    ("C'était un Bordelais.", 1.88),
    ("Il marchait lentement sur le quai désert.", 2.24),
    ("Le vieux marin regardait.", 1.28),
    ("Le vieux marin regardait.", 2.12),
    ("Le vieux marin regardait la mer sans rien dire.", 2.56),
]


def test_cv3_floor_separates_measured_degenerate_from_legitimate():
    """The floor must accept every measured legitimate render and reject every
    measured degenerate one -- both columns come from the same sweep, so the
    threshold cannot be tuned without contradicting the data."""
    from v4.p5_tts import _cv3_min_expected_s

    for text, dur in _MEASURED_DEGENERATE:
        floor = _cv3_min_expected_s(text)
        assert dur < floor, f"{text!r} at {dur}s must be rejected (floor {floor:.2f}s)"
    for text, dur in _MEASURED_LEGITIMATE:
        floor = _cv3_min_expected_s(text)
        assert dur >= floor, f"{text!r} at {dur}s must be accepted (floor {floor:.2f}s)"


def test_cv3_floor_sits_in_the_measured_empty_band():
    """Corpus-level calibration (#19692), separate from the bisect table above.

    Over the 270-narrator artifact the fastest LEGITIMATE segment runs 38.9
    chars/s and the slowest ASR-confirmed DEFECT runs 43.1 (seg 227: 156
    reference words, 79 transcribed). Nothing in the corpus lies between, so
    the floor is placed in an empty band -- and its two margins are therefore
    thin, which the constant documents rather than hides. Restated as a rate
    on a 100-char chunk: 2.57 s must pass, 2.32 s must not.
    """
    from v4.p5_tts import _cv3_min_expected_s

    text = "x" * 100  # 2.57 s -> 38.9 chars/s; 2.32 s -> 43.1 chars/s
    assert 2.57 >= _cv3_min_expected_s(text), "38.9 chars/s is legitimate"
    assert 2.32 < _cv3_min_expected_s(text), "43.1 chars/s is a defect"


def test_cv3_floor_keeps_an_absolute_term():
    """A ratio alone would let a tiny chunk through on 0.04 s of audio."""
    from v4.p5_tts import _CV3_MIN_ABS_S, _cv3_min_expected_s

    assert _cv3_min_expected_s("Oui.") == _CV3_MIN_ABS_S
    assert _cv3_min_expected_s(".") == _CV3_MIN_ABS_S
    assert _CV3_MIN_ABS_S > 0.04, "the absolute floor must reject one speech token"


class _FakeTensor:
    def __init__(self, n: int):
        self.n = n
        self.shape = (1, n)


class _FakeTorch:
    """Just enough torch for the CV3 branch: the guard, the pause, the concat."""

    def __init__(self):
        self.seeds: list[int] = []

    def manual_seed(self, value: int):
        self.seeds.append(value)

    def cat(self, tensors, dim=-1):
        return _FakeTensor(sum(t.n for t in tensors))

    def zeros(self, *shape):
        return _FakeTensor(shape[-1])


class _FakeModel:
    """Yields a WAV of a scripted duration per call; "CRASH" raises the
    RuntimeError the f0 predictor produces when the mel is too short."""

    sample_rate = 24000

    def __init__(self, script):
        self.script = list(script)
        self.calls: list[str] = []

    def inference_zero_shot(self, text, prompt_text, wav_path, stream=False):
        dur = self.script[len(self.calls)]
        self.calls.append(text)
        if dur == "CRASH":
            raise RuntimeError(
                "Calculated padded input size per channel: (3). Kernel size: (4)."
            )
        yield {"tts_speech": _FakeTensor(int(dur * self.sample_rate))}


def _install_fake_runtime(monkeypatch, model):
    """Wire the fake torch/torchaudio/pydub and the stub client, so the retry
    loop is exercised hermetically -- no GPU, no CosyVoice install."""
    import sys
    import types

    fake_torch = _FakeTorch()
    monkeypatch.setitem(sys.modules, "torch", fake_torch)

    torchaudio = types.ModuleType("torchaudio")
    torchaudio.save = lambda buf, wav, sr, format=None: buf.write(b"WAV")
    monkeypatch.setitem(sys.modules, "torchaudio", torchaudio)

    pydub = types.ModuleType("pydub")

    class _FakeAudio:
        @staticmethod
        def from_file(buf, format=None):
            return _FakeAudio()

        def export(self, buf, format=None, bitrate=None):
            buf.write(b"MP3")

    pydub.AudioSegment = _FakeAudio
    monkeypatch.setitem(sys.modules, "pydub", pydub)

    client = types.SimpleNamespace(
        _bootstrap_paths=lambda: (None, None, "asset.wav"),
        PROMPT_TEXT_ZH="prompt",
        ENDOFPROMPT="<|endofprompt|>",
    )
    monkeypatch.setattr("v4.p5_tts._get_cv3_client", lambda: client)
    monkeypatch.setattr("v4.p5_tts._load_cv3_model", lambda: model)
    monkeypatch.setattr("v4.p5_tts.audio_duration_mp3", lambda b: 1.5)
    return fake_torch


def test_cv3_re_rolls_a_degenerate_render(tmp_path, monkeypatch):
    """A 0.04 s render is retried with a different seed instead of being
    returned as generated -- and the retry is the same text, same engine."""
    from v4.p5_tts import _synthesize_narrator_cosyvoice3

    model = _FakeModel([0.04, 0.04, 1.5])  # two degenerate, then a real one
    fake_torch = _install_fake_runtime(monkeypatch, model)
    seg = _build_seg(speaker="narrateur", text="Il marcha.")
    out = _synthesize_narrator_cosyvoice3(
        seg=seg, fishaudio_text="Il marcha.",
        mp3_path=tmp_path / "seg_0001_narrateur.mp3", seed=42, text_hash="h",
    )
    assert out.status == "generated"
    assert out.attempts == 3, "attempts must report the real re-roll count"
    assert len(model.calls) == 3
    assert len(set(model.calls)) == 1, "a re-roll must not rewrite the text"
    # attempt 0 keeps the pre-guard seed; each retry moves to a fresh one.
    assert fake_torch.seeds == [42, 42 + 104_729, 42 + 2 * 104_729]


def test_cv3_re_rolls_the_crash_face_of_the_same_event(tmp_path, monkeypatch):
    """The conv1d RuntimeError and the silent 0.04 s are one event with two
    faces, so the re-roll answers the crash too instead of failing the run."""
    from v4.p5_tts import _synthesize_narrator_cosyvoice3

    model = _FakeModel(["CRASH", 1.8])
    _install_fake_runtime(monkeypatch, model)
    seg = _build_seg(speaker="narrateur", text="Il marcha.")
    out = _synthesize_narrator_cosyvoice3(
        seg=seg, fishaudio_text="Il marcha.",
        mp3_path=tmp_path / "seg_0001_narrateur.mp3", seed=42, text_hash="h",
    )
    assert out.status == "generated"
    assert out.attempts == 2


def test_cv3_fails_loudly_when_every_attempt_degenerates(tmp_path, monkeypatch):
    """Never a silent short MP3: an unresolvable chunk raises, so the run
    counts it in Failed rather than shipping 0.10 s of nothing."""
    from v4.p5_tts import (
        _CV3_RENDER_ATTEMPTS, NarratorCosyVoice3Unavailable,
        _synthesize_narrator_cosyvoice3,
    )

    model = _FakeModel([0.04] * _CV3_RENDER_ATTEMPTS)
    _install_fake_runtime(monkeypatch, model)
    mp3 = tmp_path / "seg_0001_narrateur.mp3"
    seg = _build_seg(speaker="narrateur", text="Il marcha.")
    try:
        _synthesize_narrator_cosyvoice3(
            seg=seg, fishaudio_text="Il marcha.",
            mp3_path=mp3, seed=42, text_hash="h",
        )
    except NarratorCosyVoice3Unavailable as exc:
        assert "degenerate" in str(exc)
        assert len(model.calls) == _CV3_RENDER_ATTEMPTS
        assert not mp3.exists(), "a failed render must not leave a partial MP3"
        return
    raise AssertionError("an all-degenerate chunk must raise, not return")


class _StubLLM:
    """Minimal stand-in for CosyVoice3LM: records what the sampler hides."""

    def __init__(self, stop_token_ids=(100, 101, 102)):
        self.stop_token_ids = list(stop_token_ids)
        self.calls: list[tuple[list[int], bool]] = []

    def sampling_ids(self, weighted_scores, decoded_tokens, sampling, ignore_eos=True):
        masked = sorted(
            k for k, v in weighted_scores.items() if v == float("-inf")
        )
        self.calls.append((masked, ignore_eos))
        return 0


def _cv3_model(llm):
    """The shape the real loader returns: `AutoModel()` is a factory giving
    `CosyVoice3`, whose `.model` is the `CosyVoice3Model` carrying `.llm`."""
    return types.SimpleNamespace(model=types.SimpleNamespace(llm=llm))


# Upstream's non-vLLM decoder breaks on ANY of three stop ids but masks only
# `speech_token_size` -- which is `stop_token_ids[0]`. The other two walk
# through the min_len floor, and that is the whole degeneracy: a render ends
# after one speech token, 1/25 s = 0.04 s (#19692).
def test_cv3_stop_floor_patch_masks_every_stop_id():
    from v4.p5_tts import _patch_cv3_stop_token_floor

    llm = _StubLLM((100, 101, 102))
    assert _patch_cv3_stop_token_floor(_cv3_model(llm)) == "patched"

    scores = {100: 0.5, 101: 0.5, 102: 0.5, 7: 9.0}
    llm.sampling_ids(scores, [], 25, ignore_eos=True)
    assert scores[100] == float("-inf"), "stop_token_ids[0] was already masked"
    assert scores[101] == float("-inf"), "the leaking id 1 must be masked too"
    assert scores[102] == float("-inf"), "the leaking id 2 must be masked too"
    assert scores[7] == 9.0, "a speech token must stay samplable"
    # The inner call runs with ignore_eos=False: masking twice would make the
    # protected prefix and the free tail indistinguishable.
    assert llm.calls[-1][1] is False


def test_cv3_stop_floor_patch_is_idempotent():
    """Two prompt builds in one process must not stack wrappers -- a wrapper
    over a wrapper would mask on the tail too, and generation would never
    end."""
    from v4.p5_tts import _patch_cv3_stop_token_floor

    llm = _StubLLM()
    model = _cv3_model(llm)
    assert _patch_cv3_stop_token_floor(model) == "patched"
    first = llm.sampling_ids
    assert _patch_cv3_stop_token_floor(model) == "already-patched"
    assert llm.sampling_ids is first
    assert llm.calls == [], "patching alone must not sample"


def test_cv3_stop_floor_leaves_the_tail_able_to_stop():
    """Past min_len the decoder MUST be able to end: with ignore_eos=False
    nothing is masked, so a stop id can win and break the loop."""
    from v4.p5_tts import _patch_cv3_stop_token_floor

    llm = _StubLLM((100, 101, 102))
    _patch_cv3_stop_token_floor(_cv3_model(llm))
    scores = {100: 0.5, 101: -2.0, 102: -3.0}
    llm.sampling_ids(scores, [], 25, ignore_eos=False)
    assert scores == {100: 0.5, 101: -2.0, 102: -3.0}


def test_cv3_stop_floor_patch_fails_loudly_when_the_decoder_moved():
    """A loader that returns another shape must stop the render rather than
    quietly restore the leak -- and must SAY which shape it saw, so localising
    it costs a read instead of a GPU run."""
    from v4.p5_tts import NarratorCosyVoice3Unavailable, _patch_cv3_stop_token_floor

    for model, why in (
        (types.SimpleNamespace(), "no `.model` at all"),
        (types.SimpleNamespace(model=types.SimpleNamespace()), "`.model` with no llm"),
        # The measured wrong path: a first version of the patch addressed
        # `model.llm` and raised on all nine probe segments.
        (types.SimpleNamespace(llm=_StubLLM()), "the decoder at the top level"),
    ):
        try:
            _patch_cv3_stop_token_floor(model)
        except NarratorCosyVoice3Unavailable as exc:
            assert "#19692" in str(exc), why
            assert "model.llm" in str(exc), why
        else:
            raise AssertionError(f"must raise: {why}")


def test_cv3_load_caches_the_refusal_instead_of_reloading_per_segment(monkeypatch):
    """A failing patch must not reload the model for every segment: measured,
    nine probe segments cost six loads (~16 s each) before the run gave up."""
    from v4 import p5_tts
    from v4.p5_tts import NarratorCosyVoice3Unavailable

    loads = []

    def _load():
        loads.append(1)
        return types.SimpleNamespace()  # a shape the patch must reject

    monkeypatch.setattr(
        p5_tts,
        "_get_cv3_client",
        lambda: types.SimpleNamespace(load_model=_load),
    )
    monkeypatch.setattr(p5_tts, "_CV3_MODEL_CACHE", {})

    for _ in range(3):
        try:
            p5_tts._load_cv3_model()
        except NarratorCosyVoice3Unavailable:
            pass
        else:
            raise AssertionError("an unpatched loader must not hand back a model")
    assert len(loads) == 1, f"the refusal must be cached, got {len(loads)} loads"


def test_load_cv3_model_patches_the_decoder_on_the_way_out(monkeypatch):
    """The patch is not optional plumbing: loading the model without it would
    leave every narrator render on the leaky path."""
    from v4 import p5_tts

    llm = _StubLLM()
    model = _cv3_model(llm)
    monkeypatch.setattr(
        p5_tts,
        "_get_cv3_client",
        lambda: types.SimpleNamespace(load_model=lambda: model),
    )
    monkeypatch.setattr(p5_tts, "_CV3_MODEL_CACHE", {})

    assert p5_tts._load_cv3_model() is model
    assert getattr(llm, "_v4_stop_floor_patched", False) is True
    # Second call serves the cached model: the patch is not re-applied.
    assert p5_tts._load_cv3_model() is model
    assert llm.calls == []


def test_narrator_cache_is_engine_aware(tmp_path, monkeypatch):
    """Flipping NARRATOR_COSYVOICE3_ROUTING must not serve the previous
    engine's MP3 from the batch cache: the narrator cache keys on the
    engine sentinel (#19692) — a text hash alone cannot tell which engine
    rendered the file. Dialogue segments stay cached regardless (they never
    change engine)."""
    from v4 import p5_tts
    from v4.schemas import TTSResult

    (tmp_path / "seg_0001_narrateur.mp3").write_bytes(b"fake")
    (tmp_path / "seg_0001_loiseau.mp3").write_bytes(b"fake")
    monkeypatch.setattr(p5_tts, "TTS_DIR", tmp_path)
    monkeypatch.setattr(p5_tts, "audio_duration_mp3", lambda b: 1.0)
    monkeypatch.setattr(p5_tts, "thermal_wait", lambda *a, **k: 0)

    def _stub(seg, text):
        return TTSResult(
            seg_index=seg.seg_index, speaker=seg.speaker, reference_id="stub",
            mp3_path="stub", duration_s=1.0, seed=42, status="generated",
            attempts=1, text_hash="stub",
        )

    monkeypatch.setattr(p5_tts, "_synthesize_segment", _stub)

    narr = _build_seg(speaker="narrateur", text="Il marcha.")
    dlg = _build_seg(speaker="loiseau", text="Bonjour.")
    h_narr = p5_tts._text_hash("Il marcha.")
    h_dlg = p5_tts._text_hash("Bonjour.")

    orig_qwen = p5_tts._NARRATOR_QWEN_ROUTING
    orig_cv3 = p5_tts._NARRATOR_COSYVOICE3_ROUTING
    try:
        p5_tts._NARRATOR_QWEN_ROUTING = False
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = True

        # Cache says Qwen rendered it; CV3 is selected -> regenerate.
        out = p5_tts._synthesize_batch(
            [(narr, "Il marcha.")],
            {1: h_narr},
            {1: p5_tts._QWEN_NARRATOR_REFERENCE_ID},
        )
        assert out[0].status == "generated"

        # Cache says CV3 rendered it; CV3 is selected -> served cached.
        out = p5_tts._synthesize_batch(
            [(narr, "Il marcha.")],
            {1: h_narr},
            {1: p5_tts._CV3_NARRATOR_REFERENCE_ID},
        )
        assert out[0].status == "cached"

        # Dialogue segments never change engine: hash match is enough.
        out = p5_tts._synthesize_batch(
            [(dlg, "Bonjour.")], {1: h_dlg}, {1: "v4_loiseau_voice"}
        )
        assert out[0].status == "cached"
    finally:
        p5_tts._NARRATOR_QWEN_ROUTING = orig_qwen
        p5_tts._NARRATOR_COSYVOICE3_ROUTING = orig_cv3
