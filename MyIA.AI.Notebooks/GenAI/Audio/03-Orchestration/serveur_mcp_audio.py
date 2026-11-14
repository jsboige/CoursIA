"""Serveur MCP audio : transcription, synthese vocale et analyse de fichiers audio.

Ce serveur expose trois capacites audio reelles de la serie Audio comme
outils du Model Context Protocol (FastMCP, SDK officiel). Il est lance en
**stdio** par le carnet `03-5-MCP-Audio.ipynb`, qui l'interroge avec un
client MCP reel, puis qui fait choisir les outils par un modele.

Chaque outil appelle un moteur reel de la serie, jamais une fonction
factice :

- `transcrire_audio`   : faster-whisper (`small`, CPU int8) ;
- `synthetiser_voix`   : Kokoro (backend ONNX) ;
- `analyser_audio`     : soundfile + numpy (duree, niveau, silences).

Contraintes de ce serveur :

- **stdout est la voie du protocole** : rien ne doit y etre ecrit. Les
  journaux partent sur stderr (le client MCP les recoit via `errlog`).
- Les modeles sont charges **paresseusement**, au premier appel : le
  serveur demarre instantanement, et la latence de chargement est mesuree
  separement du temps de traitement.

Variables d'environnement lues :

- `KOKORO_MODEL_DIR`   : repertoire des fichiers ONNX Kokoro ;
- `KOKORO_VOICES_FILE` : fichier des voix (defaut : `<KOKORO_MODEL_DIR>/voices-v1.0.bin`) ;
- `AUDIO_WORK_DIR`     : repertoire de travail des fichiers WAV produits ;
- `WHISPER_MODEL`      : modele faster-whisper (defaut : `small`) ;
- `WHISPER_COMPUTE`    : type de calcul ctranslate2 (defaut : `int8`).
"""

from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path
from typing import Any, Dict, Optional

import numpy as np
import soundfile as sf

from mcp.server.fastmcp import FastMCP

# --- Journalisation sur stderr uniquement (stdout appartient au protocole) ---

def journal(message: str) -> None:
    """Ecrit une ligne de journal sur stderr."""
    sys.stderr.write(f"[serveur-mcp-audio] {message}\n")
    sys.stderr.flush()


# --- Chargement paresseux des moteurs ---

_ETAT: Dict[str, Any] = {
    "whisper": None,
    "kokoro": None,
    "charges": {},
}


def _dossier_modeles_kokoro() -> Path:
    """Repertoire des fichiers ONNX Kokoro, resolu par variable d'environnement."""
    brut = os.environ.get("KOKORO_MODEL_DIR", "")
    if brut:
        return Path(brut)
    # Repli : le cache partage de la serie GenAI.
    racine = Path(__file__).resolve().parents[2]
    return racine / ".cache" / "kokoro-onnx"


def _fichier_voix() -> Path:
    """Fichier des voix Kokoro."""
    brut = os.environ.get("KOKORO_VOICES_FILE", "")
    if brut:
        return Path(brut)
    return _dossier_modeles_kokoro() / "voices-v1.0.bin"


def _dossier_travail() -> Path:
    """Repertoire de travail des WAV produits par la synthese."""
    brut = os.environ.get("AUDIO_WORK_DIR", "")
    dossier = Path(brut) if brut else Path.cwd() / "outputs" / "audio" / "mcp"
    dossier.mkdir(parents=True, exist_ok=True)
    return dossier


def moteur_whisper():
    """Charge faster-whisper au premier appel et rend le modele."""
    if _ETAT["whisper"] is None:
        from faster_whisper import WhisperModel

        nom = os.environ.get("WHISPER_MODEL", "small")
        calcul = os.environ.get("WHISPER_COMPUTE", "int8")
        debut = time.perf_counter()
        _ETAT["whisper"] = WhisperModel(nom, device="cpu", compute_type=calcul)
        _ETAT["charges"]["whisper_s"] = round(time.perf_counter() - debut, 2)
        journal(f"faster-whisper '{nom}' ({calcul}, CPU) charge en "
                f"{_ETAT['charges']['whisper_s']} s")
    return _ETAT["whisper"]


def moteur_kokoro():
    """Charge Kokoro (ONNX) au premier appel et rend le modele."""
    if _ETAT["kokoro"] is None:
        from kokoro_onnx import Kokoro

        modele = _dossier_modeles_kokoro() / "kokoro-v1.0.onnx"
        voix = _fichier_voix()
        if not modele.exists() or not voix.exists():
            raise FileNotFoundError(
                f"fichiers Kokoro absents ({modele}, {voix}) : "
                "telechargez-les dans KOKORO_MODEL_DIR"
            )
        debut = time.perf_counter()
        _ETAT["kokoro"] = Kokoro(str(modele), str(voix))
        _ETAT["charges"]["kokoro_s"] = round(time.perf_counter() - debut, 2)
        journal(f"Kokoro ONNX charge en {_ETAT['charges']['kokoro_s']} s")
    return _ETAT["kokoro"]


# --- Outils MCP ---

mcp = FastMCP("serveur-mcp-audio")


@mcp.tool()
def transcrire_audio(chemin: str, langue: Optional[str] = None) -> Dict[str, Any]:
    """Transcrit un fichier audio WAV en texte (faster-whisper, CPU).

   :param chemin: chemin absolu du fichier audio a transcrire ;
    :param langue: code ISO de la langue ('fr', 'en', ...) ; None = detection.
    :return: le texte transcrit, la langue detectee, la duree audio et le
        temps de traitement mesure.
    """
    debut = time.perf_counter()
    fichier = Path(chemin)
    if not fichier.exists():
        raise FileNotFoundError(f"fichier audio absent : {fichier}")
    modele = moteur_whisper()
    segments, info = modele.transcribe(str(fichier), language=langue, beam_size=5)
    texte = " ".join(segment.text.strip() for segment in segments).strip()
    duree = time.perf_counter() - debut
    journal(f"transcrire_audio({fichier.name}) -> {len(texte)} caracteres en {duree:.2f} s")
    return {
        "texte": texte,
        "langue": info.language,
        "probabilite_langue": round(float(info.language_probability), 4),
        "duree_audio_s": round(float(info.duration), 3),
        "temps_s": round(duree, 3),
        "moteur": "faster-whisper",
    }


@mcp.tool()
def synthetiser_voix(texte: str, voix: str = "af_heart",
                     langue: str = "en-us", vitesse: float = 1.0,
                     nom_fichier: str = "synthese") -> Dict[str, Any]:
    """Synthetise un texte en voix (Kokoro ONNX) et ecrit un fichier WAV.

    :param texte: le texte a synthetiser ;
    :param voix: identifiant de voix Kokoro ('af_heart', 'ff_siwis', ...) ;
    :param langue: 'en-us' ou 'fr-fr' ;
    :param vitesse: vitesse de diction, 1.0 = normale ;
    :param nom_fichier: nom du WAV produit (sans extension).
    :return: le chemin du WAV, sa duree, sa frequence et le temps mesure.
    """
    debut = time.perf_counter()
    modele = moteur_kokoro()
    samples, frequence = modele.create(texte, voice=voix, lang=langue, speed=float(vitesse))
    dossier = _dossier_travail()
    cible = dossier / f"{nom_fichier}.wav"
    sf.write(str(cible), samples, frequence)
    duree_audio = len(samples) / float(frequence)
    duree = time.perf_counter() - debut
    journal(f"synthetiser_voix({voix}) -> {cible.name} "
            f"({duree_audio:.1f} s d'audio en {duree:.2f} s)")
    return {
        "chemin": str(cible),
        "duree_audio_s": round(duree_audio, 3),
        "frequence": int(frequence),
        "temps_s": round(duree, 3),
        "voix": voix,
        "moteur": "kokoro-onnx",
    }


@mcp.tool()
def analyser_audio(chemin: str) -> Dict[str, Any]:
    """Mesure un fichier audio : duree, niveau, crête et plus long silence.

    :param chemin: chemin absolu du fichier audio ;
    :return: duree, frequence, RMS en dBFS, crête en dBFS, plus long silence
        en millisecondes et le rapport de temps parle.
    """
    debut = time.perf_counter()
    fichier = Path(chemin)
    if not fichier.exists():
        raise FileNotFoundError(f"fichier audio absent : {fichier}")
    samples, frequence = sf.read(str(fichier), dtype="float32", always_2d=False)
    if samples.ndim > 1:
        samples = samples.mean(axis=1)
    total = len(samples) / float(frequence)
    rms = float(np.sqrt(np.mean(samples ** 2))) if len(samples) else 0.0
    crete = float(np.max(np.abs(samples))) if len(samples) else 0.0

    # Plus long silence : fenetres de 10 ms sous -40 dBFS.
    fenetre = max(1, int(frequence * 0.01))
    blocs = len(samples) // fenetre
    silence_ms = 0
    if blocs:
        rms_blocs = np.sqrt((samples[:blocs * fenetre].reshape(blocs, fenetre) ** 2).mean(axis=1))
        bruyant = np.where(rms_blocs >= 10 ** (-40 / 20))[0]
        if len(bruyant):
            courant = 0
            for valeur in rms_blocs[bruyant[0]:bruyant[-1] + 1] < 10 ** (-40 / 20):
                courant = courant + 1 if valeur else 0
                silence_ms = max(silence_ms, courant * 10)
    rapport = float(np.mean(np.abs(samples) >= 10 ** (-40 / 20))) if len(samples) else 0.0
    duree = time.perf_counter() - debut
    journal(f"analyser_audio({fichier.name}) -> {total:.2f} s, "
            f"silence max {silence_ms} ms en {duree:.3f} s")
    return {
        "duree_s": round(total, 3),
        "frequence": int(frequence),
        "rms_dbfs": round(20 * float(np.log10(rms)) if rms > 0 else -120.0, 2),
        "crete_dbfs": round(20 * float(np.log10(crete)) if crete > 0 else -120.0, 2),
        "silence_max_ms": int(silence_ms),
        "taux_parole": round(rapport, 4),
        "temps_s": round(duree, 3),
        "moteur": "soundfile+numpy",
    }


if __name__ == "__main__":
    # Les erreurs de protocole restent lisibles cote client.
    try:
        mcp.run(transport="stdio")
    except Exception as exc:  # pragma: no cover - trace de diagnostic
        journal(f"arret du serveur : {type(exc).__name__}: {exc}")
        print(json.dumps({"erreur": str(exc)}), file=sys.stderr, flush=True)
        raise
