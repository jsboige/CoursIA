# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

## audio1-waveform.png

- **Source** : notebook `01-Foundation/01-3-Basic-Audio-Operations.ipynb` (cellule 12, output 1)
- **Alt-text (FR)** : Forme d'onde : échantillonnage d'un signal audio continu et visualisation temporelle.
- **Poids** : 36.4 KB (natif)
- **G.1 firsthand (2026-07-10)** : VRAI — matplotlib "Forme d'onde - Echantillon de test", amplitude ±0.4, 12 s, signal parole avec silences.

## audio2-spectrogram.png

- **Source** : notebook `01-Foundation/01-3-Basic-Audio-Operations.ipynb` (cellule 20, output 3)
- **Alt-text (FR)** : Spectrogramme et MFCC : décomposition temps-fréquence du signal pour la reconnaissance vocale.
- **Poids** : 75.8 KB (natif)
- **G.1 firsthand (2026-07-10)** : DÉCLASSÉ (#5780) — l'image montre 2 barplots "Latence/Taille audio par modèle et type de texte" (kokoro vs openai/tts-1, type dialogue/monologue/narration), pas un spectrogramme. Contenu ≠ intitulé. Voir README "Aperçu" pour la figure de remplacement.

## audio3-stt-tts.png

- **Source** : notebook `01-Foundation/01-3-Basic-Audio-Operations.ipynb` (cellule 28, output 2)
- **Alt-text (FR)** : Reconnaissance (STT) et synthèse (TTS) : transcription et génération vocale appliquées au même flux.
- **Poids** : 163.8 KB (natif)
- **G.1 firsthand (2026-07-10)** : PARTIEL — grille 2×2 matplotlib avec barplot STT (large-v3-turbo, latence 0.47 s) côté supérieur gauche ; les 3 autres sous-figures portent la mention "Pas de resultats TTS" (TTS échoué en environnement de test). Seul STT est validé. Voir README "Aperçu" pour la mention honnête.

## audio4-demucs.png

- **Source** : notebook `02-Advanced/02-4-Demucs-Source-Separation.ipynb` (cellule 23, output 2)
- **Alt-text (FR)** : Séparation de sources : Demucs isole voix, batterie, basse et autre à partir d'un mix stéréo.
- **Poids** : 171.0 KB (downscale max-dim 700, source 1398×1490 / 277.4 KB)
- **G.1 firsthand (2026-07-10)** : VRAI — Demucs SOTA séparation source, 5 panneaux matplotlib Mix original + DRUMS (RMS 0.0307) + BASS (0.1626) + OTHER (0.1524) + VOCALS (0.0117).

## audio5-multimodel.png

- **Source** : notebook `03-Orchestration/03-1-Multi-Model-Audio-Comparison.ipynb` (cellule 29, output 1)
- **Alt-text (FR)** : Comparaison de modèles audio : plusieurs voies STT/TTS évaluées côte à côte dans un pipeline.
- **Poids** : 92.1 KB (downscale max-dim 1200, source 1379×855)
- **G.1 firsthand (2026-07-10)** : DÉCLASSÉ (#5780) — l'image montre 4 courbes librosa sur un seul échantillon audio (Spectral Centroid, Bandwidth, RMS Energy, Zero-Crossing Rate), pas une comparaison multi-modèles. Contenu ≠ intitulé. Voir README "Aperçu" pour la figure de remplacement.

## audio6-tts-benchmark.png

- **Source** : notebook `04-Applications/04-7-TTS-Voice-Benchmark.ipynb` (cellule 31, output 0)
- **Alt-text (FR)** : Benchmark de voix TTS : qualité, naturel et latence comparés en vue d'un déploiement en production.
- **Poids** : 48.8 KB (downscale max-dim 1200, source 1389×490)
- **G.1 firsthand (2026-07-10)** : VRAI — 3 heatmaps MFCC (coefficients cepstraux) + Delta + Delta-Delta matplotlib, échelle −400 à +200, axe temps 0–10 s. Représentation feature-space d'un échantillon benchmark, structurellement un output de comparaison TTS post-extraction MFCC.
