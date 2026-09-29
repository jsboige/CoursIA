"""bakeoff_small — Phase A0 banc TTS modeles tenant sur 8 GB (RTX 4060).

Driver distinct de bench.py (matrix lourde FishAudio/Qwen/Higgs/Kokoro/OpenAI)
pour les modeles Open Weights legers ouverts : Chatterbox Multilingual V3
(Resemble AI, 0.5B), Kyutai tts-1.6b-en_fr (1.6B CC-BY-4.0), pocket-tts
(kyutai-labs, 100M), Fun-CosyVoice 3.0 (FunAudioLLM, 0.5B).

G-VAR-1 strict : grain DEEP/notebook-python (livrable mesurable + non
rejouable par scan). Mesures via prosody_metrics + syllable_pitch (memes
instruments que bench.py pour permettre la comparaison cross-bench).
Outputs : 1 WAV + 1 JSON prosody + 1 WER vs Whisper-tiny par modele,
ranges dans G:\\Mon Drive\\MyIA\\Projets\\BibliothequesSonores\\
run-20260924-093628\\A0-bakeoff\\<modele>\\ (cf issue #17586 Phase A0).

Limites :
  - VRAM 8 GB => un seul modele charge a la fois (del/load entre cellules)
  - Pas de GPU partage avec les clients v4 (Qwen, FishAudio) pendant la
    session -- a prevoir hors session lourde.
  - Whisper-tiny charge une seule fois au debut (73 MB VRAM FP16).
"""
from __future__ import annotations
