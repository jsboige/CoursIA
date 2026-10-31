"""Attack guard wired in the CV3 render loop (#19739, phase 2) — offline tests.

The organ (verdict + re-roll plan) was delivered by #21459 and has its own
suite (test_attack_guard.py); what these tests guard is the WIRING inside
`_synthesize_narrator_cosyvoice3`: a floor-passing render is accepted only
when the ASR hears the chunk's first words, a dropped attack consumes the
same spaced-seed re-roll as a degenerate render, and V4_ATTACK_GUARD=off
restores the pre-guard acceptance for the A/B arm.

Run from the v4 directory:
    python -m pytest tests/test_p5_cv3_attack_guard.py -v
"""
from __future__ import annotations

import sys
import types
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


# Long enough that several words can be lost from the head (the organ's
# threshold is 3 leading words) and that the chunker keeps it whole.
_CHUNK = (
    "Il marcha lentement sur le quai désert en regardant les bateaux "
    "quitter le port une dernière fois."
)
# Same text minus its first four words: the operational onset-drop.
_CHUNK_SANS_ATTAQUE = (
    "sur le quai désert en regardant les bateaux quitter le port une "
    "dernière fois."
)
# Two-sentence text over 280 chars: the chunker (greedy, <= 280) must split
# it in two, so the per-chunk seed indexing is exercised for real.
_S1 = (
    "La vieille dame traversa la place déserte au petit matin en tenant "
    "son parapluie fermé comme une arme oubliée, et personne dans le "
    "village ne se souvenait de l'avoir vue arriver un jour quelconque."
)
_S2 = (
    "Le boulanger lui fit un signe de tête mesuré derrière la vitre "
    "embuée de sa boutique, puis reprit son travail sans un mot de plus "
    "car il savait mieux que quiconque qu'il ne fallait jamais déranger."
)
_TWO_CHUNKS = f"{_S1} {_S2}"


def _build_seg(*, text: str = "x"):
    from v4.schemas import AnnotatedSegment

    return AnnotatedSegment(
        seg_index=1,
        speaker="narrateur",
        type="narration",
        text=text,
        annotated_text=text,
    )


class _FakeTensor:
    def __init__(self, n: int):
        self.n = n
        self.shape = (1, n)


class _FakeTorch:
    def __init__(self):
        self.seeds: list[int] = []

    def manual_seed(self, value: int):
        self.seeds.append(value)

    def cat(self, tensors, dim=-1):
        return _FakeTensor(sum(t.n for t in tensors))

    def zeros(self, *shape):
        return _FakeTensor(shape[-1])


class _FakeModel:
    """Yields a WAV of the scripted duration per call (all above the floor)."""

    sample_rate = 24000

    def __init__(self, script):
        self.script = list(script)
        self.calls: list[str] = []

    def inference_zero_shot(self, text, prompt_text, wav_path, stream=False):
        dur = self.script[len(self.calls)]
        self.calls.append(text)
        yield {"tts_speech": _FakeTensor(int(dur * self.sample_rate))}


class _FakeASR:
    """Returns the scripted transcript per call and records what it served."""

    def __init__(self, transcripts):
        self.script = list(transcripts)
        self.calls: list[str] = []

    def __call__(self, wav_path):
        self.calls.append(str(wav_path))
        idx = min(len(self.calls), len(self.script)) - 1
        return self.script[idx]


def _install_fake_runtime(monkeypatch, model, asr):
    """Fake torch/torchaudio/pydub + stub client + the injected ASR (#19739).

    Same stand-ins as test_p5_cv3_narrator (kept local: test modules are not
    importable organs), with torchaudio.save accepting BOTH the scratch wav
    path the attack verdict writes and the BytesIO the MP3 export uses.
    """
    import sys

    fake_torch = _FakeTorch()
    monkeypatch.setitem(sys.modules, "torch", fake_torch)

    torchaudio = types.ModuleType("torchaudio")

    def _save(dest, wav, sr, format=None):
        if hasattr(dest, "write"):
            dest.write(b"WAV")

    torchaudio.save = _save
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
    # The real resolver builds on attack_guard.asr_http (network); the wiring
    # under test is the loop's use of the callable, so the callable is fake.
    monkeypatch.setattr("v4.p5_tts._resolve_attack_asr", lambda: asr)
    return fake_torch


def _synthesize(tmp_path, monkeypatch, model, asr, text=_CHUNK, guard=None):
    from v4.p5_tts import _synthesize_narrator_cosyvoice3

    if guard is not None:
        monkeypatch.setenv("V4_ATTACK_GUARD", guard)
    else:
        monkeypatch.delenv("V4_ATTACK_GUARD", raising=False)
    fake_torch = _install_fake_runtime(monkeypatch, model, asr)
    out = _synthesize_narrator_cosyvoice3(
        seg=_build_seg(text=text),
        fishaudio_text=text,
        mp3_path=tmp_path / "seg_0001_narrateur.mp3",
        seed=42,
        text_hash="h",
    )
    return out, fake_torch


# Durations scripted above the floor of any chunk used here (~150 chars ->
# floor ~3.9 s at 38.9 chars/s), so the floor never fires in this suite
# except where a test says it does.
_DUR = 6.0


def test_guard_accepts_clean_chunk_on_first_attempt(tmp_path, monkeypatch):
    """Healthy chunk: floor passes, ASR hears the attack -> accepted at
    attempt 0, original seed, exactly one ASR call. A clean chunk must be
    untouched by the guard (the pre-registered protocol's identity arm)."""
    model = _FakeModel([_DUR])
    asr = _FakeASR([_CHUNK])
    out, fake_torch = _synthesize(tmp_path, monkeypatch, model, asr)

    assert out.status == "generated"
    assert out.attempts == 1
    assert fake_torch.seeds == [42], "attempt 0 must keep the pre-guard seed"
    assert len(asr.calls) == 1
    assert len(model.calls) == 1


def test_guard_re_rolls_dropped_attack_with_spaced_seed(tmp_path, monkeypatch):
    """The onset-drop: floor passes but the transcript lost the first words.
    The chunk is re-rolled at the spaced seed -- the same formula the
    degenerate path uses -- and accepted once the attack is heard."""
    model = _FakeModel([_DUR, _DUR])
    asr = _FakeASR([_CHUNK_SANS_ATTAQUE, _CHUNK])
    out, fake_torch = _synthesize(tmp_path, monkeypatch, model, asr)

    assert out.status == "generated"
    assert out.attempts == 2
    assert fake_torch.seeds == [42, 42 + 104_729]
    assert len(asr.calls) == 2
    assert len(set(model.calls)) == 1, "a re-roll must not rewrite the text"


def test_guard_fails_loudly_when_attack_never_recovers(tmp_path, monkeypatch):
    """An attack that never comes back is a hard failure naming the guard,
    never a shipped MP3 whose first words are missing (#19739 is what the
    run counts in Failed -- an unguarded accept would hide the drop)."""
    from v4.p5_tts import _CV3_RENDER_ATTEMPTS, NarratorCosyVoice3Unavailable

    model = _FakeModel([_DUR] * _CV3_RENDER_ATTEMPTS)
    asr = _FakeASR([_CHUNK_SANS_ATTAQUE])
    mp3 = tmp_path / "seg_0001_narrateur.mp3"
    monkeypatch.delenv("V4_ATTACK_GUARD", raising=False)
    fake_torch = _install_fake_runtime(monkeypatch, model, asr)

    from v4.p5_tts import _synthesize_narrator_cosyvoice3

    try:
        _synthesize_narrator_cosyvoice3(
            seg=_build_seg(text=_CHUNK), fishaudio_text=_CHUNK,
            mp3_path=mp3, seed=42, text_hash="h",
        )
    except NarratorCosyVoice3Unavailable as exc:
        assert "attack" in str(exc)
        assert "#19739" in str(exc)
        assert not mp3.exists(), "a failed render must not leave a partial MP3"
        assert len(asr.calls) == _CV3_RENDER_ATTEMPTS
        assert fake_torch.seeds[0] == 42
        assert fake_torch.seeds[-1] == 42 + (_CV3_RENDER_ATTEMPTS - 1) * 104_729
        return
    raise AssertionError("an all-dropped-attack chunk must raise, not return")


def test_guard_off_restores_pre_guard_acceptance(tmp_path, monkeypatch):
    """V4_ATTACK_GUARD=off is the A/B arm of the measured comparison: the
    floor alone decides and the ASR is never called."""
    model = _FakeModel([_DUR])
    asr = _FakeASR([])  # any call would be recorded and fail the assert
    out, fake_torch = _synthesize(
        tmp_path, monkeypatch, model, asr, guard="off"
    )

    assert out.status == "generated"
    assert out.attempts == 1
    assert asr.calls == [], "the guard being off must mean zero ASR calls"
    assert fake_torch.seeds == [42]


def test_asr_runs_only_after_the_floor_passes(tmp_path, monkeypatch):
    """A degenerate render is re-rolled by the floor BEFORE any ASR call --
    transcribing a 0.04 s file would waste the ASR and say nothing."""
    model = _FakeModel([0.04, _DUR])
    asr = _FakeASR([_CHUNK])
    out, _ = _synthesize(tmp_path, monkeypatch, model, asr)

    assert out.status == "generated"
    assert out.attempts == 2
    assert len(asr.calls) == 1, "the degenerate render must not be transcribed"


def test_guard_is_per_chunk_in_a_multi_chunk_segment(tmp_path, monkeypatch):
    """Two chunks; only the second drops its attack on its first attempt.
    The re-roll seed must carry THAT chunk's index (seed + 1 + stride), not
    the segment's -- this is the attack_guard.spaced_seed convention p5
    already uses for degenerate renders."""
    from v4.p5_tts import _chunk_narration

    chunks = _chunk_narration(_TWO_CHUNKS)
    assert len(chunks) == 2, f"fixture must split in two, got {len(chunks)}"

    model = _FakeModel([_DUR, _DUR, _DUR])
    asr = _FakeASR([chunks[0], _headless(chunks[1]), chunks[1]])
    out, fake_torch = _synthesize(
        tmp_path, monkeypatch, model, asr, text=_TWO_CHUNKS
    )

    assert out.status == "generated"
    assert out.attempts == 3
    assert fake_torch.seeds == [42, 43, 43 + 104_729]
    assert len(asr.calls) == 3


def _headless(text: str) -> str:
    """The text minus its first four words -- a buildable onset-drop."""
    words = text.split()
    return " ".join(words[4:])


def test_guard_default_is_on_and_off_values_are_recognized(monkeypatch):
    """The correction ships ON by default; the off-spellings are the A/B
    switch. Anything else (typo, empty) fails safe: the guard stays on."""
    from v4 import p5_tts

    monkeypatch.delenv("V4_ATTACK_GUARD", raising=False)
    assert p5_tts._attack_guard_enabled() is True
    for value in ("0", "off", "no", "false", "OFF", "No"):
        monkeypatch.setenv("V4_ATTACK_GUARD", value)
        assert p5_tts._attack_guard_enabled() is False, value
    for value in ("1", "on", "", "tru"):  # unknown spellings fail safe: ON
        monkeypatch.setenv("V4_ATTACK_GUARD", value)
        assert p5_tts._attack_guard_enabled() is True, value


def test_reference_id_bumped_for_the_attack_guard():
    """The batch cache sentinel must move: a segment the pre-guard run
    shipped with a dropped attack is stale under the guarded acceptance,
    and the sentinel is what forces its re-render (#19692 convention)."""
    from v4.p5_tts import _CV3_NARRATOR_REFERENCE_ID

    assert _CV3_NARRATOR_REFERENCE_ID == "cosyvoice3-zeroshot-narrator-fr-v4"


def test_attack_asr_reuses_the_organ_http_client(monkeypatch):
    """The resolver must build on attack_guard.asr_http -- same endpoint and
    model as p7 -- and honour V4_ASR_BASE_URL, not carry a second client."""
    from v4 import p5_tts
    import v4.attack_guard as ag

    captured = {}

    def _fake_asr_http(chunk, model="large-v3-turbo", base_url="http://localhost:8190", language="fr"):
        captured["base_url"] = base_url
        captured["audio"] = chunk["audio"]
        return "transcrit"

    monkeypatch.setattr(ag, "asr_http", _fake_asr_http)

    monkeypatch.setenv("V4_ASR_BASE_URL", "http://elsewhere:9000")
    asr_fn = p5_tts._resolve_attack_asr()
    assert asr_fn(Path("x.wav")) == "transcrit"
    assert captured["base_url"] == "http://elsewhere:9000"
    assert captured["audio"].endswith("x.wav")

    # The default (no env) points at the p7 endpoint.
    monkeypatch.delenv("V4_ASR_BASE_URL", raising=False)
    asr_default = p5_tts._resolve_attack_asr()
    asr_default(Path("y.wav"))
    assert captured["base_url"] == "http://localhost:8190"
