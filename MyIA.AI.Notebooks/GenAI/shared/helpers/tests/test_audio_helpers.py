#!/usr/bin/env python3
"""Tests unitaires pour audio_helpers.py — 16 fonctions publiques (Phase-2 GenAI Audio).

CI-runnables SANS service re-el : tous les deps audio (librosa / soundfile /
IPython / matplotlib / openai / faster_whisper / dotenv / requests / pydub)
sont late-importees dans chaque fonction -> mockables via injection
`sys.modules[<name>] = stub` avant l'appel (le `import <name>` de la fonction
resout le stub). Charge via `importlib` path-load.

Couvre les sections du module :
- Chargement / sauvegarde / playback (4 fonctions) : 6 tests.
- Visualisation (3 fonctions) : 4 tests.
- STT wrappers (3 fonctions) : 8 tests.
- TTS wrappers (2 fonctions) : 6 tests.
- Utilities (3 fonctions) : 6 tests.
Total : 30 tests CPU-only, ~0.5s.

Quirks pinnes (comportement observe, PAS un fix -- one-subject-per-PR) :
1. transcribe_openai / synthesize_openai : OpenAI() leve si OPENAI_API_KEY
   absent (delegation a la lib openai) -- pas un bug, comportement attendu.
2. transcribe_local : `compute_type="float16"` hardcode meme si
   `device="cpu"` -> float16 incompatible CPU. Comportement observe.
3. transcribe_api : service inconnu -> fallback silencieux vers "WHISPER"
   (intentionnel via `.get(service, "WHISPER")`).
4. play_audio_bytes : `format="pcm"` casse Jupyter sans `rate` argument.
"""

import os
import sys
import types
from pathlib import Path
from unittest import mock

import pytest

# Rendre le package `helpers` importable depuis ce fichier de test (meme
# pattern que test_genai_service.py / test_video_helpers.py).
SHARED = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(SHARED))
sys.path.insert(0, str(SHARED.parent))

from helpers import audio_helpers  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers mock
# ---------------------------------------------------------------------------

def _make_stub_module(name: str, **attrs) -> types.ModuleType:
    """Cree un module stub injectable via sys.modules[<name>] = stub.

    Les attributs specifies deviennent des attributs du module. Les acces
    non specifies leveur AttributeError -- teste ca explicitement si besoin.
    """
    mod = types.ModuleType(name)
    for k, v in attrs.items():
        setattr(mod, k, v)
    return mod


@pytest.fixture
def fake_librosa():
    """Stub librosa : load() retourne (data, sr) configurable."""
    stub = _make_stub_module("librosa")
    stub.load = mock.Mock(return_value=(mock.sentinel.audio_data, 22050))
    sys.modules["librosa"] = stub
    yield stub
    sys.modules.pop("librosa", None)


@pytest.fixture
def fake_soundfile():
    """Stub soundfile : write() et info() mocks."""
    stub = _make_stub_module("soundfile")
    stub.write = mock.Mock()
    stub.info = mock.Mock(return_value=mock.Mock(
        duration=1.5, samplerate=22050, channels=1, frames=33075,
        format="WAV", subtype="PCM_16",
    ))
    sys.modules["soundfile"] = stub
    yield stub
    sys.modules.pop("soundfile", None)


@pytest.fixture
def fake_ipython_display():
    """Stub IPython.display : Audio() et display() captures."""
    stub_display_mod = _make_stub_module("IPython.display")
    stub_display_mod.Audio = mock.Mock()
    stub_display_mod.display = mock.Mock()
    # Le module parent doit aussi exister pour le `from IPython.display import ...`
    stub_ipython = _make_stub_module("IPython")
    stub_ipython.display = stub_display_mod
    sys.modules["IPython"] = stub_ipython
    sys.modules["IPython.display"] = stub_display_mod
    yield stub_display_mod
    sys.modules.pop("IPython", None)
    sys.modules.pop("IPython.display", None)


@pytest.fixture
def fake_matplotlib_pyplot():
    """Stub matplotlib.pyplot : subplots() retourne (fig, ax) factices."""
    stub = _make_stub_module("matplotlib.pyplot")
    fig = mock.Mock()
    ax = mock.Mock()
    stub.subplots = mock.Mock(return_value=(fig, ax))
    stub.show = mock.Mock()
    stub.tight_layout = mock.Mock()
    # colorbar hang off the figure instance, no module-level stub needed
    sys.modules["matplotlib"] = _make_stub_module("matplotlib")
    sys.modules["matplotlib.pyplot"] = stub
    yield stub
    sys.modules.pop("matplotlib", None)
    sys.modules.pop("matplotlib.pyplot", None)


@pytest.fixture
def fake_librosa_display():
    """Stub librosa.display : waveshow(), specshow() mocks."""
    stub = _make_stub_module("librosa.display")
    stub.waveshow = mock.Mock()
    stub.specshow = mock.Mock(return_value=mock.Mock())
    sys.modules["librosa.display"] = stub
    yield stub
    sys.modules.pop("librosa.display", None)


# ---------------------------------------------------------------------------
# load / save / play
# ---------------------------------------------------------------------------

def test_load_audio_returns_tuple_data_sr(fake_librosa):
    """load_audio(path) appelle librosa.load(path, sr=None) et retourne tuple."""
    data, sr = audio_helpers.load_audio("/path/to/audio.wav")
    fake_librosa.load.assert_called_once_with("/path/to/audio.wav", sr=None)
    assert data is mock.sentinel.audio_data
    assert sr == 22050


def test_load_audio_with_sr_override(fake_librosa):
    """load_audio(path, sr=16000) propage le sr cible."""
    audio_helpers.load_audio("/x.wav", sr=16000)
    fake_librosa.load.assert_called_once_with("/x.wav", sr=16000)


def test_save_audio_calls_soundfile_write_with_format(fake_soundfile, tmp_path):
    """save_audio(data, sr, path, format='wav') appelle sf.write(format=format).

    Note: save_audio log via `len(data)/sr`, donc data doit etre len()-able
    -- un numpy array (ou tout sequence) suffit.
    """
    import numpy as np
    out = tmp_path / "out.wav"
    data = np.zeros(16000, dtype=np.float32)  # 1s de zeros a 16kHz
    audio_helpers.save_audio(data, 16000, str(out), format="wav")
    fake_soundfile.write.assert_called_once()
    args, kwargs = fake_soundfile.write.call_args
    assert args[0] == str(out)
    assert args[1] is data
    assert args[2] == 16000
    assert kwargs.get("format") == "wav"


def test_save_audio_creates_parent_directory(fake_soundfile, tmp_path):
    """save_audio cree les repertoires parents manquants (parents=True, exist_ok=True)."""
    import numpy as np
    out = tmp_path / "nested" / "dir" / "out.flac"
    data = np.zeros(22050, dtype=np.float32)
    audio_helpers.save_audio(data, 22050, str(out), format="flac")
    assert out.parent.exists()


def test_play_audio_uses_ipython_display_audio(fake_ipython_display):
    """play_audio(data, sr) construit Audio(data=data, rate=sr) puis display()."""
    audio_helpers.play_audio(mock.sentinel.wave, 16000)
    fake_ipython_display.Audio.assert_called_once_with(data=mock.sentinel.wave, rate=16000)
    fake_ipython_display.display.assert_called_once()


def test_play_audio_file_uses_filename_kwarg(fake_ipython_display):
    """play_audio_file(path) construit Audio(filename=str(path)) puis display()."""
    audio_helpers.play_audio_file("/path/to/clip.mp3")
    fake_ipython_display.Audio.assert_called_once_with(filename="/path/to/clip.mp3")
    fake_ipython_display.display.assert_called_once()


# ---------------------------------------------------------------------------
# Visualisation
# ---------------------------------------------------------------------------

def test_plot_waveform_calls_librosa_display_waveshow(
    fake_matplotlib_pyplot, fake_librosa_display,
):
    """plot_waveform appelle librosa.display.waveshow(data, sr=sr, ax=ax)."""
    audio_helpers.plot_waveform(mock.sentinel.wave, 22050, title="Test")
    fake_librosa_display.waveshow.assert_called_once()
    args, kwargs = fake_librosa_display.waveshow.call_args
    assert args[0] is mock.sentinel.wave
    assert kwargs.get("sr") == 22050


def test_plot_spectrogram_computes_mel_and_specshow(
    fake_matplotlib_pyplot, fake_librosa_display,
):
    """plot_spectrogram utilise librosa.feature.melspectrogram + power_to_db + specshow.

    Note: `import librosa` puis acces `librosa.display.specshow` -- le stub
    `librosa` doit donc pointer son attribut `.display` vers le sous-module
    stub `librosa.display`, sinon AttributeError.
    """
    librosa_stub = _make_stub_module("librosa")
    librosa_stub.feature = _make_stub_module(
        "librosa.feature", melspectrogram=mock.Mock(return_value=mock.sentinel.S),
    )
    librosa_stub.power_to_db = mock.Mock(return_value=mock.sentinel.S_dB)
    librosa_stub.display = fake_librosa_display  # point .display vers le stub
    sys.modules["librosa"] = librosa_stub
    sys.modules["librosa.feature"] = librosa_stub.feature
    try:
        audio_helpers.plot_spectrogram(mock.sentinel.wave, 22050)
        librosa_stub.feature.melspectrogram.assert_called_once()
        librosa_stub.power_to_db.assert_called_once()
        fake_librosa_display.specshow.assert_called_once()
    finally:
        sys.modules.pop("librosa", None)
        sys.modules.pop("librosa.feature", None)


def test_plot_mfcc_uses_n_mfcc_param(
    fake_matplotlib_pyplot, fake_librosa_display,
):
    """plot_mfcc(y=data, sr=sr, n_mfcc=N) propage n_mfcc a librosa.feature.mfcc."""
    librosa_stub = _make_stub_module("librosa")
    librosa_stub.feature = _make_stub_module(
        "librosa.feature", mfcc=mock.Mock(return_value=mock.sentinel.mfccs),
    )
    librosa_stub.display = fake_librosa_display  # .display -> stub
    sys.modules["librosa"] = librosa_stub
    sys.modules["librosa.feature"] = librosa_stub.feature
    try:
        audio_helpers.plot_mfcc(mock.sentinel.wave, 22050, n_mfcc=20)
        args, kwargs = librosa_stub.feature.mfcc.call_args
        assert kwargs.get("n_mfcc") == 20
    finally:
        sys.modules.pop("librosa", None)
        sys.modules.pop("librosa.feature", None)


def test_plot_helpers_call_show(fake_matplotlib_pyplot, fake_librosa_display):
    """Tous les plot_* appellent plt.show() en fin."""
    librosa_stub = _make_stub_module("librosa")
    librosa_stub.feature = _make_stub_module(
        "librosa.feature",
        melspectrogram=mock.Mock(return_value=mock.sentinel.S),
        mfcc=mock.Mock(return_value=mock.sentinel.mfccs),
    )
    librosa_stub.power_to_db = mock.Mock(return_value=mock.sentinel.S_dB)
    librosa_stub.display = fake_librosa_display
    sys.modules["librosa"] = librosa_stub
    sys.modules["librosa.feature"] = librosa_stub.feature
    try:
        audio_helpers.plot_waveform(mock.sentinel.wave, 22050)
        audio_helpers.plot_spectrogram(mock.sentinel.wave, 22050)
        audio_helpers.plot_mfcc(mock.sentinel.wave, 22050)
        assert fake_matplotlib_pyplot.show.call_count == 3
    finally:
        sys.modules.pop("librosa", None)
        sys.modules.pop("librosa.feature", None)


# ---------------------------------------------------------------------------
# STT : transcribe_openai / transcribe_local / transcribe_api
# ---------------------------------------------------------------------------

def test_transcribe_openai_calls_audio_transcriptions_create():
    """transcribe_openai envoie model+file+response_format a audio.transcriptions.create."""
    openai_stub = _make_stub_module("openai")
    transcript = mock.Mock(text="bonjour le monde")
    client_mock = mock.Mock()
    client_mock.audio.transcriptions.create = mock.Mock(return_value=transcript)
    openai_stub.OpenAI = mock.Mock(return_value=client_mock)
    sys.modules["openai"] = openai_stub
    try:
        with mock.patch("builtins.open", mock.mock_open(read_data=b"fake audio bytes")):
            result = audio_helpers.transcribe_openai("/x.wav", language="fr")
        openai_stub.OpenAI.assert_called_once_with()
        client_mock.audio.transcriptions.create.assert_called_once()
        kwargs = client_mock.audio.transcriptions.create.call_args.kwargs
        assert kwargs["model"] == "whisper-1"
        assert kwargs["response_format"] == "json"
        assert kwargs["language"] == "fr"
        assert result["text"] == "bonjour le monde"
    finally:
        sys.modules.pop("openai", None)


def test_transcribe_openai_json_format_returns_dict_with_text_and_raw():
    """response_format='json' (defaut) retourne {'text': ..., 'raw': transcript}."""
    openai_stub = _make_stub_module("openai")
    transcript = mock.Mock(text="hello world")
    client_mock = mock.Mock()
    client_mock.audio.transcriptions.create = mock.Mock(return_value=transcript)
    openai_stub.OpenAI = mock.Mock(return_value=client_mock)
    sys.modules["openai"] = openai_stub
    try:
        with mock.patch("builtins.open", mock.mock_open(read_data=b"bytes")):
            result = audio_helpers.transcribe_openai("/x.wav", response_format="json")
        assert "text" in result
        assert "raw" in result
        assert result["text"] == "hello world"
        assert result["raw"] is transcript
    finally:
        sys.modules.pop("openai", None)


def test_transcribe_openai_verbose_json_format_same_dict():
    """response_format='verbose_json' suit la meme branche que 'json' (return dict)."""
    openai_stub = _make_stub_module("openai")
    transcript = mock.Mock(text="verbose")
    client_mock = mock.Mock()
    client_mock.audio.transcriptions.create = mock.Mock(return_value=transcript)
    openai_stub.OpenAI = mock.Mock(return_value=client_mock)
    sys.modules["openai"] = openai_stub
    try:
        with mock.patch("builtins.open", mock.mock_open(read_data=b"bytes")):
            result = audio_helpers.transcribe_openai("/x.wav", response_format="verbose_json")
        assert result["text"] == "verbose"
        assert "raw" in result
    finally:
        sys.modules.pop("openai", None)


def test_transcribe_openai_text_format_returns_str_text():
    """response_format='text' (non-json) retourne {'text': str(transcript), 'raw': transcript}."""
    openai_stub = _make_stub_module("openai")
    transcript = mock.Mock(text="X", __str__=mock.Mock(return_value="plain text"))
    client_mock = mock.Mock()
    client_mock.audio.transcriptions.create = mock.Mock(return_value=transcript)
    openai_stub.OpenAI = mock.Mock(return_value=client_mock)
    sys.modules["openai"] = openai_stub
    try:
        with mock.patch("builtins.open", mock.mock_open(read_data=b"bytes")):
            result = audio_helpers.transcribe_openai("/x.wav", response_format="text")
        assert result["text"] == "plain text"
    finally:
        sys.modules.pop("openai", None)


def test_transcribe_openai_no_language_kwarg_when_none():
    """Si language=None, le kwarg `language` n'est PAS envoye a l'API."""
    openai_stub = _make_stub_module("openai")
    transcript = mock.Mock(text="hi")
    client_mock = mock.Mock()
    client_mock.audio.transcriptions.create = mock.Mock(return_value=transcript)
    openai_stub.OpenAI = mock.Mock(return_value=client_mock)
    sys.modules["openai"] = openai_stub
    try:
        with mock.patch("builtins.open", mock.mock_open(read_data=b"bytes")):
            audio_helpers.transcribe_openai("/x.wav")  # language=None par defaut
        kwargs = client_mock.audio.transcriptions.create.call_args.kwargs
        assert "language" not in kwargs
    finally:
        sys.modules.pop("openai", None)


def test_transcribe_local_collects_segments_into_dict():
    """transcribe_local itere sur segments, agrege text, expose metadata complete."""
    fw_stub = _make_stub_module("faster_whisper")
    seg1 = mock.Mock(start=0.0, end=2.0, text=" Bonjour ", avg_logprob=-0.3)
    seg2 = mock.Mock(start=2.0, end=5.0, text=" le monde", avg_logprob=-0.4)
    info = mock.Mock(
        language="fr", language_probability=0.99, duration=5.0,
    )
    model_mock = mock.Mock()
    model_mock.transcribe = mock.Mock(return_value=(iter([seg1, seg2]), info))
    fw_stub.WhisperModel = mock.Mock(return_value=model_mock)
    sys.modules["faster_whisper"] = fw_stub
    try:
        result = audio_helpers.transcribe_local("/x.wav", device="cpu")
        fw_stub.WhisperModel.assert_called_once_with(
            "large-v3-turbo", device="cpu", compute_type="float16",
        )
        # Pin : compute_type reste "float16" meme avec device="cpu" (quirk observe).
        assert result["text"] == "Bonjour le monde"
        assert result["language"] == "fr"
        assert result["language_probability"] == 0.99
        assert result["duration"] == 5.0
        assert len(result["segments"]) == 2
        assert result["segments"][0]["start"] == 0.0
        assert result["segments"][1]["confidence"] == -0.4
    finally:
        sys.modules.pop("faster_whisper", None)


def test_transcribe_api_whisper_service_posts_to_localhost_8190(monkeypatch, tmp_path):
    """transcribe_api(service='whisper') POSTe sur http://localhost:8190/v1/audio/transcriptions."""
    dotenv_stub = _make_stub_module("dotenv", load_dotenv=mock.Mock())
    sys.modules["dotenv"] = dotenv_stub
    requests_stub = _make_stub_module("requests")
    response = mock.Mock()
    response.json = mock.Mock(return_value={"text": "salut", "language": "fr", "duration": 1.0})
    response.raise_for_status = mock.Mock()
    requests_stub.post = mock.Mock(return_value=response)
    sys.modules["requests"] = requests_stub
    # Evite la lecture .env reelle
    monkeypatch.delenv("WHISPER_API_URL", raising=False)
    monkeypatch.delenv("WHISPER_API_KEY", raising=False)
    audio_path = tmp_path / "in.wav"
    audio_path.write_bytes(b"FAKE")
    try:
        result = audio_helpers.transcribe_api(str(audio_path), service="whisper")
        requests_stub.post.assert_called_once()
        args, kwargs = requests_stub.post.call_args
        assert args[0] == "http://localhost:8190/v1/audio/transcriptions"
        assert kwargs["timeout"] == 120
        # Pas d'Authorization header sans cle
        assert "Authorization" not in kwargs["headers"]
        assert result["text"] == "salut"
        assert result["service"] == "whisper"
    finally:
        sys.modules.pop("dotenv", None)
        sys.modules.pop("requests", None)


def test_transcribe_api_unknown_service_falls_back_to_whisper(monkeypatch, tmp_path):
    """transcribe_api(service='bogus') -> fallback silencieux vers prefixe WHISPER (URL 8190)."""
    dotenv_stub = _make_stub_module("dotenv", load_dotenv=mock.Mock())
    sys.modules["dotenv"] = dotenv_stub
    requests_stub = _make_stub_module("requests")
    response = mock.Mock()
    response.json = mock.Mock(return_value={"text": ""})
    response.raise_for_status = mock.Mock()
    requests_stub.post = mock.Mock(return_value=response)
    sys.modules["requests"] = requests_stub
    monkeypatch.delenv("WHISPER_API_URL", raising=False)
    monkeypatch.delenv("WHISPER_API_KEY", raising=False)
    audio_path = tmp_path / "in.wav"
    audio_path.write_bytes(b"FAKE")
    try:
        audio_helpers.transcribe_api(str(audio_path), service="bogus")
        args, _ = requests_stub.post.call_args
        assert args[0] == "http://localhost:8190/v1/audio/transcriptions"
    finally:
        sys.modules.pop("dotenv", None)
        sys.modules.pop("requests", None)


def test_transcribe_api_adds_bearer_header_when_key_set(monkeypatch, tmp_path):
    """transcribe_api propage api_key en header Authorization: Bearer <key>."""
    dotenv_stub = _make_stub_module("dotenv", load_dotenv=mock.Mock())
    sys.modules["dotenv"] = dotenv_stub
    requests_stub = _make_stub_module("requests")
    response = mock.Mock()
    response.json = mock.Mock(return_value={"text": "ok"})
    response.raise_for_status = mock.Mock()
    requests_stub.post = mock.Mock(return_value=response)
    sys.modules["requests"] = requests_stub
    audio_path = tmp_path / "in.wav"
    audio_path.write_bytes(b"FAKE")
    try:
        audio_helpers.transcribe_api(
            str(audio_path), api_url="http://api.example.com",
            api_key="secret-key-123", service="whisper", language="fr",
        )
        _, kwargs = requests_stub.post.call_args
        assert kwargs["headers"]["Authorization"] == "Bearer secret-key-123"
        assert kwargs["data"]["language"] == "fr"
    finally:
        sys.modules.pop("dotenv", None)
        sys.modules.pop("requests", None)


# ---------------------------------------------------------------------------
# TTS : synthesize_openai / synthesize_tts_api
# ---------------------------------------------------------------------------

def test_synthesize_openai_returns_bytes_and_calls_create():
    """synthesize_openai(text, voice, model) appelle client.audio.speech.create et retourne .content."""
    openai_stub = _make_stub_module("openai")
    response = mock.Mock(content=b"\x00\x01\x02 FAKE_MP3")
    client_mock = mock.Mock()
    client_mock.audio.speech.create = mock.Mock(return_value=response)
    openai_stub.OpenAI = mock.Mock(return_value=client_mock)
    sys.modules["openai"] = openai_stub
    try:
        audio_bytes = audio_helpers.synthesize_openai("hello world", voice="nova", model="tts-1-hd")
        client_mock.audio.speech.create.assert_called_once_with(
            model="tts-1-hd", voice="nova", input="hello world", response_format="mp3",
        )
        assert audio_bytes == b"\x00\x01\x02 FAKE_MP3"
    finally:
        sys.modules.pop("openai", None)


def test_synthesize_openai_writes_to_output_path_if_provided(tmp_path):
    """Si output_path est fourni, le contenu est aussi ecrit sur disque (parent mkdir)."""
    openai_stub = _make_stub_module("openai")
    response = mock.Mock(content=b"FAKE")
    client_mock = mock.Mock()
    client_mock.audio.speech.create = mock.Mock(return_value=response)
    openai_stub.OpenAI = mock.Mock(return_value=client_mock)
    sys.modules["openai"] = openai_stub
    out = tmp_path / "nested" / "out.mp3"
    try:
        audio_helpers.synthesize_openai("hi", output_path=str(out))
        assert out.exists()
        assert out.read_bytes() == b"FAKE"
    finally:
        sys.modules.pop("openai", None)


def test_synthesize_tts_api_kokoro_uses_default_path(monkeypatch):
    """synthesize_tts_api(model='kokoro', defaut) POSTe sur /v1/audio/speech."""
    dotenv_stub = _make_stub_module("dotenv", load_dotenv=mock.Mock())
    sys.modules["dotenv"] = dotenv_stub
    requests_stub = _make_stub_module("requests")
    response = mock.Mock(content=b"FAKE_KOKORO")
    response.raise_for_status = mock.Mock()
    requests_stub.post = mock.Mock(return_value=response)
    sys.modules["requests"] = requests_stub
    monkeypatch.delenv("TTS_API_URL", raising=False)
    monkeypatch.delenv("TTS_API_KEY", raising=False)
    try:
        audio_bytes = audio_helpers.synthesize_tts_api("bonjour", model="kokoro")
        args, _ = requests_stub.post.call_args
        assert args[0] == "http://localhost:8191/v1/audio/speech"
        assert audio_bytes == b"FAKE_KOKORO"
    finally:
        sys.modules.pop("dotenv", None)
        sys.modules.pop("requests", None)


def test_synthesize_tts_api_qwen3_uses_qwen_path(monkeypatch):
    """synthesize_tts_api(model='qwen3') POSTe sur /qwen/v1/audio/speech (gateway multiplexe)."""
    dotenv_stub = _make_stub_module("dotenv", load_dotenv=mock.Mock())
    sys.modules["dotenv"] = dotenv_stub
    requests_stub = _make_stub_module("requests")
    response = mock.Mock(content=b"FAKE_QWEN3")
    response.raise_for_status = mock.Mock()
    requests_stub.post = mock.Mock(return_value=response)
    sys.modules["requests"] = requests_stub
    monkeypatch.delenv("TTS_API_URL", raising=False)
    try:
        audio_helpers.synthesize_tts_api("salut", model="qwen3")
        args, _ = requests_stub.post.call_args
        assert args[0] == "http://localhost:8191/qwen/v1/audio/speech"
    finally:
        sys.modules.pop("dotenv", None)
        sys.modules.pop("requests", None)


def test_synthesize_tts_api_tada_uses_tada_path(monkeypatch):
    """synthesize_tts_api(model='tada') POSTe sur /tada/v1/audio/speech."""
    dotenv_stub = _make_stub_module("dotenv", load_dotenv=mock.Mock())
    sys.modules["dotenv"] = dotenv_stub
    requests_stub = _make_stub_module("requests")
    response = mock.Mock(content=b"FAKE_TADA")
    response.raise_for_status = mock.Mock()
    requests_stub.post = mock.Mock(return_value=response)
    sys.modules["requests"] = requests_stub
    monkeypatch.delenv("TTS_API_URL", raising=False)
    try:
        audio_helpers.synthesize_tts_api("hi", model="tada", voice="bel")
        args, kwargs = requests_stub.post.call_args
        assert args[0] == "http://localhost:8191/tada/v1/audio/speech"
        assert kwargs["json"]["voice"] == "bel"
    finally:
        sys.modules.pop("dotenv", None)
        sys.modules.pop("requests", None)


def test_synthesize_tts_api_writes_to_output_path(monkeypatch, tmp_path):
    """Si output_path fourni, le contenu est ecrit sur disque en plus d'etre retourne."""
    dotenv_stub = _make_stub_module("dotenv", load_dotenv=mock.Mock())
    sys.modules["dotenv"] = dotenv_stub
    requests_stub = _make_stub_module("requests")
    response = mock.Mock(content=b"BYTES_TTS")
    response.raise_for_status = mock.Mock()
    requests_stub.post = mock.Mock(return_value=response)
    sys.modules["requests"] = requests_stub
    monkeypatch.delenv("TTS_API_URL", raising=False)
    out = tmp_path / "out.mp3"
    try:
        audio_helpers.synthesize_tts_api("hi", output_path=str(out))
        assert out.exists()
        assert out.read_bytes() == b"BYTES_TTS"
    finally:
        sys.modules.pop("dotenv", None)
        sys.modules.pop("requests", None)


# ---------------------------------------------------------------------------
# Utilities : play_audio_bytes / get_audio_info / convert_audio / estimate_audio_duration
# ---------------------------------------------------------------------------

def test_play_audio_bytes_uses_autoplay_false(fake_ipython_display):
    """play_audio_bytes(bytes, format) appelle Audio(data=bytes, autoplay=False)."""
    audio_helpers.play_audio_bytes(b"FAKE", format="mp3")
    fake_ipython_display.Audio.assert_called_once_with(data=b"FAKE", autoplay=False)
    fake_ipython_display.display.assert_called_once()


def test_get_audio_info_returns_metadata_dict(fake_soundfile):
    """get_audio_info(path) appelle sf.info() et retourne dict avec cles canoniques."""
    info = audio_helpers.get_audio_info("/path/to/x.wav")
    fake_soundfile.info.assert_called_once_with("/path/to/x.wav")
    assert info["path"] == "/path/to/x.wav"
    assert info["duration_seconds"] == 1.5
    assert info["sample_rate"] == 22050
    assert info["channels"] == 1
    assert info["frames"] == 33075
    assert info["format"] == "WAV"
    assert info["subtype"] == "PCM_16"


def test_convert_audio_uses_pydub_and_target_sr(tmp_path):
    """convert_audio charge via pydub, applique set_frame_rate(target_sr), export format deduit du suffix."""
    pydub_stub = _make_stub_module("pydub")
    audio_seg = mock.Mock()
    audio_seg.set_frame_rate = mock.Mock(return_value=audio_seg)
    pydub_stub.AudioSegment = mock.Mock()
    pydub_stub.AudioSegment.from_file = mock.Mock(return_value=audio_seg)
    sys.modules["pydub"] = pydub_stub
    inp = tmp_path / "in.mp3"
    out = tmp_path / "out" / "x.wav"
    try:
        audio_helpers.convert_audio(str(inp), str(out), target_sr=16000)
        pydub_stub.AudioSegment.from_file.assert_called_once_with(str(inp))
        audio_seg.set_frame_rate.assert_called_once_with(16000)
        audio_seg.export.assert_called_once_with(str(out), format="wav")
        assert out.parent.exists()
    finally:
        sys.modules.pop("pydub", None)


def test_convert_audio_deduce_format_from_output_suffix(tmp_path):
    """convert_audio: output_format = Path(output).suffix.lstrip('.') -> export(format=X)."""
    pydub_stub = _make_stub_module("pydub")
    audio_seg = mock.Mock()
    audio_seg.set_frame_rate = mock.Mock(return_value=audio_seg)
    pydub_stub.AudioSegment = mock.Mock()
    pydub_stub.AudioSegment.from_file = mock.Mock(return_value=audio_seg)
    sys.modules["pydub"] = pydub_stub
    inp = tmp_path / "in.wav"
    out = tmp_path / "out.flac"
    try:
        audio_helpers.convert_audio(str(inp), str(out))  # target_sr=None
        # set_frame_rate pas appele si target_sr=None
        audio_seg.set_frame_rate.assert_not_called()
        audio_seg.export.assert_called_once_with(str(out), format="flac")
    finally:
        sys.modules.pop("pydub", None)


def test_estimate_audio_duration_pure_no_deps():
    """estimate_audio_duration est pure : words/WPM*60, sans import externe."""
    # "Bonjour le monde" -> 3 mots -> 3/150 * 60 = 1.2 s
    assert audio_helpers.estimate_audio_duration("Bonjour le monde") == 1.2
    # vitesse overridee
    assert audio_helpers.estimate_audio_duration("a b c d", words_per_minute=60) == 4.0
    # string vide -> 0 mots -> 0 secondes
    assert audio_helpers.estimate_audio_duration("") == 0.0


def test_estimate_audio_duration_handles_whitespace_only():
    """estimate_audio_duration("   ") -> split vide -> 0 mots -> 0 secondes (pas d'erreur)."""
    assert audio_helpers.estimate_audio_duration("   \n\t  ") == 0.0


# ---------------------------------------------------------------------------
# Degenerate-input guards (LIVE functions only)
# ---------------------------------------------------------------------------

def test_save_audio_rejects_non_positive_sr(fake_soundfile, tmp_path):
    """save_audio must reject sr<=0 upfront.

    Previously sr=0 was forwarded to soundfile.write (file written!) and then
    crashed in the log line `len(data)/sr` with ZeroDivisionError -- a
    partial-state bug (file on disk + exception raised). save_audio is used in
    20 notebooks.
    """
    import numpy as np
    data = np.zeros(16000, dtype=np.float32)
    for bad in (0, -8000):
        with pytest.raises(ValueError, match="sr must be positive"):
            audio_helpers.save_audio(data, bad, str(tmp_path / "out.wav"))
    # The guard fires BEFORE soundfile.write -> no file written.
    fake_soundfile.write.assert_not_called()


def test_estimate_audio_duration_rejects_non_positive_wpm():
    """estimate_audio_duration must reject words_per_minute<=0 upfront.

    Previously wpm=0 raised an opaque ZeroDivisionError from the division.
    """
    for bad in (0, -60):
        with pytest.raises(ValueError, match="words_per_minute must be positive"):
            audio_helpers.estimate_audio_duration("un deux trois", words_per_minute=bad)
