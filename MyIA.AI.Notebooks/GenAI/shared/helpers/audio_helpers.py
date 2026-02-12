#!/usr/bin/env python3
"""
Audio Helpers - Utilitaires pour les notebooks Audio, Speech & Musique
Fonctionnalites : chargement/playback audio, visualisation, wrappers STT/TTS
"""

import os
import io
import logging
from pathlib import Path
from typing import Optional, Tuple, Dict, Any

import numpy as np

logger = logging.getLogger('genai_coursia.audio')


# ============================================================================
# Chargement et sauvegarde audio
# ============================================================================

def load_audio(path: str, sr: Optional[int] = None) -> Tuple[np.ndarray, int]:
    """Charge un fichier audio et retourne (data, sample_rate).

    Args:
        path: Chemin vers le fichier audio
        sr: Sample rate cible (None = natif)

    Returns:
        Tuple (numpy array, sample rate)
    """
    import librosa
    data, sample_rate = librosa.load(path, sr=sr)
    return data, sample_rate


def save_audio(data: np.ndarray, sr: int, path: str, format: Optional[str] = None):
    """Sauvegarde des donnees audio dans un fichier.

    Args:
        data: Numpy array des echantillons
        sr: Sample rate
        path: Chemin de sortie
        format: Format (wav, mp3, flac, ogg). Auto-detecte depuis l'extension si None.
    """
    import soundfile as sf
    output_path = Path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    sf.write(str(output_path), data, sr, format=format)
    logger.info(f"Audio sauvegarde : {output_path} ({len(data)/sr:.1f}s, {sr}Hz)")


def play_audio(data: np.ndarray, sr: int):
    """Joue un audio dans un notebook Jupyter via IPython.display.Audio.

    Args:
        data: Numpy array des echantillons
        sr: Sample rate
    """
    from IPython.display import Audio, display
    display(Audio(data=data, rate=sr))


def play_audio_file(path: str):
    """Joue un fichier audio dans un notebook Jupyter.

    Args:
        path: Chemin vers le fichier audio
    """
    from IPython.display import Audio, display
    display(Audio(filename=str(path)))


# ============================================================================
# Visualisation audio
# ============================================================================

def plot_waveform(data: np.ndarray, sr: int, title: str = "Forme d'onde",
                  figsize: Tuple[int, int] = (12, 3)):
    """Affiche la forme d'onde d'un signal audio.

    Args:
        data: Numpy array des echantillons
        sr: Sample rate
        title: Titre du graphique
        figsize: Taille de la figure
    """
    import matplotlib.pyplot as plt
    import librosa.display

    fig, ax = plt.subplots(figsize=figsize)
    librosa.display.waveshow(data, sr=sr, ax=ax)
    ax.set_title(title)
    ax.set_xlabel("Temps (s)")
    ax.set_ylabel("Amplitude")
    plt.tight_layout()
    plt.show()


def plot_spectrogram(data: np.ndarray, sr: int, title: str = "Spectrogramme",
                     figsize: Tuple[int, int] = (12, 4)):
    """Affiche le spectrogramme mel d'un signal audio.

    Args:
        data: Numpy array des echantillons
        sr: Sample rate
        title: Titre du graphique
        figsize: Taille de la figure
    """
    import matplotlib.pyplot as plt
    import librosa
    import librosa.display

    fig, ax = plt.subplots(figsize=figsize)
    S = librosa.feature.melspectrogram(y=data, sr=sr, n_mels=128)
    S_dB = librosa.power_to_db(S, ref=np.max)
    img = librosa.display.specshow(S_dB, x_axis='time', y_axis='mel',
                                    sr=sr, ax=ax)
    fig.colorbar(img, ax=ax, format='%+2.0f dB')
    ax.set_title(title)
    plt.tight_layout()
    plt.show()


def plot_mfcc(data: np.ndarray, sr: int, n_mfcc: int = 13,
              title: str = "MFCC", figsize: Tuple[int, int] = (12, 4)):
    """Affiche les coefficients MFCC d'un signal audio.

    Args:
        data: Numpy array des echantillons
        sr: Sample rate
        n_mfcc: Nombre de coefficients MFCC
        title: Titre du graphique
        figsize: Taille de la figure
    """
    import matplotlib.pyplot as plt
    import librosa
    import librosa.display

    fig, ax = plt.subplots(figsize=figsize)
    mfccs = librosa.feature.mfcc(y=data, sr=sr, n_mfcc=n_mfcc)
    img = librosa.display.specshow(mfccs, x_axis='time', ax=ax)
    fig.colorbar(img, ax=ax)
    ax.set_title(title)
    ax.set_ylabel("Coefficient MFCC")
    plt.tight_layout()
    plt.show()


# ============================================================================
# Wrappers STT (Speech-to-Text)
# ============================================================================

def transcribe_openai(audio_path: str, model: str = "whisper-1",
                      language: Optional[str] = None,
                      response_format: str = "json") -> Dict[str, Any]:
    """Transcription audio via l'API OpenAI Whisper.

    Args:
        audio_path: Chemin vers le fichier audio
        model: Modele STT (whisper-1, gpt-4o-transcribe)
        language: Code langue ISO 639-1 (None = auto-detection)
        response_format: Format de reponse (json, text, srt, vtt, verbose_json)

    Returns:
        Dict avec le texte transcrit et les metadonnees
    """
    from openai import OpenAI
    client = OpenAI()

    with open(audio_path, "rb") as audio_file:
        kwargs = {
            "model": model,
            "file": audio_file,
            "response_format": response_format,
        }
        if language:
            kwargs["language"] = language

        transcript = client.audio.transcriptions.create(**kwargs)

    if response_format == "json" or response_format == "verbose_json":
        return {"text": transcript.text, "raw": transcript}
    return {"text": str(transcript), "raw": transcript}


def transcribe_local(audio_path: str, model_size: str = "large-v3-turbo",
                     language: Optional[str] = None,
                     device: str = "cuda") -> Dict[str, Any]:
    """Transcription audio avec Whisper local (faster-whisper).

    Args:
        audio_path: Chemin vers le fichier audio
        model_size: Taille du modele Whisper
        language: Code langue (None = auto-detection)
        device: Device (cuda, cpu)

    Returns:
        Dict avec le texte, les segments et les metadonnees
    """
    from faster_whisper import WhisperModel
    model = WhisperModel(model_size, device=device, compute_type="float16")

    segments, info = model.transcribe(audio_path, language=language)
    segments_list = list(segments)

    text = " ".join([s.text.strip() for s in segments_list])
    return {
        "text": text,
        "language": info.language,
        "language_probability": info.language_probability,
        "duration": info.duration,
        "segments": [
            {
                "start": s.start,
                "end": s.end,
                "text": s.text.strip(),
                "confidence": s.avg_logprob,
            }
            for s in segments_list
        ],
    }


# ============================================================================
# Wrappers TTS (Text-to-Speech)
# ============================================================================

def synthesize_openai(text: str, voice: str = "alloy", model: str = "tts-1",
                      output_path: Optional[str] = None,
                      response_format: str = "mp3") -> bytes:
    """Synthese vocale via l'API OpenAI TTS.

    Args:
        text: Texte a synthetiser
        voice: Voix (alloy, echo, fable, onyx, nova, shimmer)
        model: Modele TTS (tts-1, tts-1-hd)
        output_path: Chemin de sauvegarde (optionnel)
        response_format: Format (mp3, opus, aac, flac, wav, pcm)

    Returns:
        Bytes du fichier audio genere
    """
    from openai import OpenAI
    client = OpenAI()

    response = client.audio.speech.create(
        model=model,
        voice=voice,
        input=text,
        response_format=response_format,
    )

    audio_bytes = response.content

    if output_path:
        Path(output_path).parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, "wb") as f:
            f.write(audio_bytes)
        logger.info(f"Audio TTS sauvegarde : {output_path}")

    return audio_bytes


def play_audio_bytes(audio_bytes: bytes, format: str = "mp3"):
    """Joue des bytes audio dans un notebook Jupyter.

    Args:
        audio_bytes: Donnees audio brutes
        format: Format audio (mp3, wav, etc.)
    """
    from IPython.display import Audio, display
    display(Audio(data=audio_bytes, autoplay=False))


# ============================================================================
# Utilitaires
# ============================================================================

def get_audio_info(path: str) -> Dict[str, Any]:
    """Retourne les metadonnees d'un fichier audio.

    Args:
        path: Chemin vers le fichier audio

    Returns:
        Dict avec duree, sample_rate, channels, format, etc.
    """
    import soundfile as sf
    info = sf.info(str(path))
    return {
        "path": str(path),
        "duration_seconds": info.duration,
        "sample_rate": info.samplerate,
        "channels": info.channels,
        "frames": info.frames,
        "format": info.format,
        "subtype": info.subtype,
    }


def convert_audio(input_path: str, output_path: str,
                  target_sr: Optional[int] = None):
    """Convertit un fichier audio vers un autre format.

    Args:
        input_path: Chemin source
        output_path: Chemin destination (le format est deduit de l'extension)
        target_sr: Sample rate cible (None = conserve l'original)
    """
    from pydub import AudioSegment

    audio = AudioSegment.from_file(input_path)
    if target_sr:
        audio = audio.set_frame_rate(target_sr)

    output_format = Path(output_path).suffix.lstrip('.')
    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    audio.export(output_path, format=output_format)
    logger.info(f"Audio converti : {input_path} -> {output_path}")


def estimate_audio_duration(text: str, words_per_minute: int = 150) -> float:
    """Estime la duree d'un texte parle en secondes.

    Args:
        text: Texte a estimer
        words_per_minute: Vitesse de parole estimee

    Returns:
        Duree estimee en secondes
    """
    word_count = len(text.split())
    return (word_count / words_per_minute) * 60
