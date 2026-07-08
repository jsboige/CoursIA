# Galerie README — Audio 01-Foundation (bases speech & audio)

Provenance de chaque figure (convention `extract_readme_figures.py` L132 : index ALL-CELLS).
Toutes les figures sont extraites des **outputs déjà committés** des notebooks (C.3 — aucune re-exécution).
Bornes EPIC #5654 P1 respectées : ≤200 KB/fichier, ≤1200 px max-dim.

**Note de diversité** : les 5 figures proviennent du notebook fondationnel `01-3-Basic-Audio-Operations.ipynb` (seul du module à produire des visualisations PNG). Elles couvrent le **pipeline audio complet** : forme d'onde → spectrogramme → MFCC → extraction de caractéristiques. Les 4 autres notebooks du module (TTS, STT, etc.) ne produisent pas de sorties image extractibles.

| Figure | Notebook source | Cellule | Output | Format | Dimensions | Poids | Alt-text FR |
|--------|-----------------|---------|--------|--------|------------|-------|-------------|
| `aud1-waveform.png` | `01-3-Basic-Audio-Operations.ipynb` | 12 | 1 | PNG | 1189×290 | 36,4 KB | Forme d'onde (waveform) du signal audio |
| `aud1-spectrogram.webp` | `01-3-Basic-Audio-Operations.ipynb` | 15 | 1 | WebP | 800×713 | 81,7 KB | Spectrogramme — décomposition temps-fréquence |
| `aud1-mfcc.png` | `01-3-Basic-Audio-Operations.ipynb` | 20 | 1 | PNG | 1080×390 | 32,1 KB | MFCC — coefficients cepstraux mel |
| `aud1-mfcc2.png` | `01-3-Basic-Audio-Operations.ipynb` | 20 | 3 | PNG | 1072×790 | 75,8 KB | MFCC — carte de chaleur des coefficients |
| `aud1-features.png` | `01-3-Basic-Audio-Operations.ipynb` | 28 | 2 | PNG | 1189×985 | 163,8 KB | Extraction de caractéristiques audio |

**Diversité couverte** : 5 visualisations du pipeline audio (waveform, spectrogramme, MFCC ×2, features). Total : 5 figures, 389,8 KB, max 163,8 KB/fichier. WebP fallback (P2) pour le spectrogramme (source dense 438 KB). 5 figures plutôt que 6 : seules 5 visualisations distinctes existent dans le module (pas de padding).
