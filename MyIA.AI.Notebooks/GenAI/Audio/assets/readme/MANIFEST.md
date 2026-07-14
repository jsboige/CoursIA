# Manifeste des figures — GenAI/Audio

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).
**Audit G.1 c.481 (2026-07-14, doctrine #5780)** : swap audio3↔audio5 corrige le mismatch de contenu (les PNG assignés à ces deux slots ne correspondaient pas à leurs alt-texts respectifs). Le PNG « comparaison multi-modèles » (2 barplots kokoro/openai-tts-1) est désormais sous `audio5-multimodel.png` ; le PNG « caractéristiques audio extraites » (4 courbes librosa) est désormais sous `audio3-stt-tts.png`.

## audio1-waveform.png

- **Source** : notebook `01-Foundation/01-3-Basic-Audio-Operations.ipynb` (cellule 12, output 1)
- **Alt-text (FR)** : Forme d'onde : échantillonnage d'un signal audio continu et visualisation temporelle.
- **Poids** : 36.4 KB (natif)
- **G.1 firsthand (2026-07-10)** : VRAI — matplotlib "Forme d'onde - Echantillon de test", amplitude ±0.4, 12 s, signal parole avec silences.

## audio2-spectrogram.png

- **Source** : notebook `01-Foundation/01-3-Basic-Audio-Operations.ipynb` (cellule 20, output 3)
- **Alt-text (FR)** : Spectrogramme et MFCC : décomposition temps-fréquence du signal pour la reconnaissance vocale.
- **Poids** : 75.8 KB (natif)
- **G.1 firsthand (2026-07-14, c.481)** : **VRAI** (correction c.481) — 3 heatmaps MFCC authentiques (MFCC + Delta vitesse + Delta-Delta accélération), échelle −400 à +200, axe temps 0–10 s. Le DÉCLASSÉ catalogué en 2026-07-10 était une erreur d'audit : le contenu décrit alors (« 2 barplots Latence/Taille kokoro vs openai/tts-1 ») correspond en fait au PNG actuel de `audio5-multimodel.png` (après swap c.481).

## audio3-stt-tts.png

- **Source** : notebook `01-Foundation/01-3-Basic-Audio-Operations.ipynb` (cellule 28, output 2)
- **Alt-text (FR)** : Reconnaissance (STT) et synthèse (TTS) : transcription et génération vocale appliquées au même flux.
- **Poids** : 92.1 KB (natif) — *avant c.481 : 163.8 KB ; après swap audio3↔audio5, le PNG 92.1 KB « Caractéristiques audio extraites » est désormais sous ce nom.*
- **G.1 firsthand (2026-07-14, c.481)** : **DÉCLASSÉ** (contenu ≠ intitulé, le titre « STT/TTS » est trompeur) — 4 courbes librosa d'analyse spectrale d'un seul échantillon audio : Spectral Centroid (Hz 0–8000), Spectral Bandwidth (Hz 1000–3500), RMS Energy (Amplitude 0–0.15), Zero-Crossing Rate (Rate 0–0.6), axe temps 0–12 s. L'audit 2026-07-10 avait correctement catalogué le contenu, mais sous le mauvais slot (`audio5-multimodel` à l'époque).

## audio4-demucs.png

- **Source** : notebook `02-Advanced/02-4-Demucs-Source-Separation.ipynb` (cellule 23, output 2)
- **Alt-text (FR)** : Séparation de sources : Demucs isole voix, batterie, basse et autre à partir d'un mix stéréo.
- **Poids** : 171.0 KB (downscale max-dim 700, source 1398×1490 / 277.4 KB)
- **G.1 firsthand (2026-07-10)** : VRAI — Demucs SOTA séparation source, 5 panneaux matplotlib Mix original + DRUMS (RMS 0.0307) + BASS (0.1626) + OTHER (0.1524) + VOCALS (0.0117).

## audio5-multimodel.png

- **Source** : notebook `03-Orchestration/03-1-Multi-Model-Audio-Comparison.ipynb` (cellule 29, output 1)
- **Alt-text (FR)** : Comparaison de modèles audio : plusieurs voies STT/TTS évaluées côte à côte dans un pipeline.
- **Poids** : 163.8 KB (natif) — *avant c.481 : 92.1 KB ; après swap audio3↔audio5, le PNG 163.8 KB « barplots Latence + Taille » est désormais sous ce nom.*
- **G.1 firsthand (2026-07-14, c.481)** : **VRAI TTS-only** (correction c.481) — 2 barplots matplotlib authentiques, axe log-latence ms 3·10³–4·10³, axe taille KB 0–350, légende Type (dialogue/monologue/narration), modèles kokoro vs openai/tts-1. Le scope est TTS-côté-serveur uniquement (pas de volet STT dans la même figure, contrairement au titre « STT/TTS multi-voies »).

## audio6-tts-benchmark.png

- **Source** : notebook `04-Applications/04-7-TTS-Voice-Benchmark.ipynb` (cellule 31, output 0)
- **Alt-text (FR)** : Benchmark de voix TTS : qualité, naturel et latence comparés en vue d'un déploiement en production.
- **Poids** : 48.8 KB (downscale max-dim 1200, source 1389×490)
- **G.1 firsthand (2026-07-10)** : VRAI — 3 heatmaps MFCC (coefficients cepstraux) + Delta + Delta-Delta matplotlib, échelle −400 à +200, axe temps 0–10 s. Représentation feature-space d'un échantillon benchmark, structurellement un output de comparaison TTS post-extraction MFCC.
