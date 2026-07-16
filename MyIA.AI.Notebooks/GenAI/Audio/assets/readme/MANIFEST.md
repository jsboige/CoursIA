# Manifeste des figures — GenAI/Audio

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks via `extract_readme_figures.py`).

**Résolution d'audit c.529 (2026-07-16, #5780) — vérification vision firsthand + traçage nbformat.** Les notes d'audit c.481 et c.490 concluaient à tort que 5/6 PNG étaient « invérifiables / probablement externes ». Cette conclusion reposait sur une **double erreur de méthode** :

1. **Inversion de lecture audio2↔audio4** : le c.490 a lu le contenu de `audio2` (3 heatmaps MFCC) comme du « Demucs », et celui de `audio4` (5 panneaux Demucs) comme une « grille STT/TTS ». Les deux attributions de cellule source du MANIFEST c.481 étaient en fait **correctes** (audio2 ← MFCC, audio4 ← Demucs).
2. **Fausse prémisse « MD5 ≠ donc externe »** : `extract_readme_figures.py` **optimise chaque figure au moment de l'extraction** (downscale à ≤ 1200 px de large + recompression PIL). Le MD5 et la taille du PNG disque **diffèrent donc nécessairement** de la sortie de cellule brute — ce n'est pas la signature d'une source externe, mais le comportement normal de l'outil. Le « ratio systématique 0,55–2,36 » invoqué par le c.490 provenait de comparaisons contre les **mauvaises cellules attendues** (le corps du c.490 identifiait pourtant les bonnes sources pour audio5/audio6, en contradiction avec sa propre table).

**Constat c.529 : les 6 figures sont de vraies sorties de notebook.** Cinq sont tracées à une cellule committée par contenu + ratio de taille cohérent avec l'optimisation PIL (ratio 0,62–0,97, toujours ≤ 1,0). La sixième (`audio3`) est une figure de benchmark STT/TTS réelle dont le volet TTS vide est **honnêtement signalé** dans l'alt-text in-situ (disclosure, cf doctrine C522) ; sa cellule source exacte n'est pas committée dans les 3 notebooks référencés. **Aucun swap de fichier n'est nécessaire** ; les légendes inline du README sont corrigées pour être fidèles au contenu réel.

## audio1-waveform.png

- **Source** : `01-Foundation/01-3-Basic-Audio-Operations.ipynb` cell[12] out[1] (`# Visualisation de la forme d'onde`).
- **Contenu (vision firsthand c.529)** : courbe matplotlib unique « Forme d'onde », amplitude ±0,4, axe temps 0–12 s.
- **Traçage** : cellule brute 39 273 B (md5 `3ace572f`) → disque 37 273 B (md5 `09e55bfb`), ratio **0,95**.
- **Alt-text (FR)** : Forme d'onde : échantillonnage d'un signal audio continu et visualisation temporelle.
- **Verdict** : **SOTA-OK** — vraie sortie de notebook, légende fidèle. Inliné (README §01-Foundation).

## audio2-spectrogram.png

- **Source** : `01-Foundation/01-3-Basic-Audio-Operations.ipynb` cell[20] out[3] (`# MFCC (Mel-Frequency Cepstral Coefficients)`).
- **Contenu (vision firsthand c.529)** : **3 heatmaps MFCC** empilées (MFCC, delta, delta-delta), échelle de couleur, axe temps horizontal, coefficients en ordonnée. **Ce ne sont pas des panneaux Demucs** (erreur de lecture c.490).
- **Traçage** : cellule brute 84 031 B (md5 `238e0bd6`) → disque 77 625 B (md5 `b9792e33`), ratio **0,92**.
- **Alt-text (FR)** : Spectrogramme et MFCC : décomposition temps-fréquence du signal pour la reconnaissance vocale.
- **Verdict** : **SOTA-OK** — vraie sortie MFCC du 01-3. Asset orphelin (non inliné dans le README ; disponible pour réutilisation).

## audio3-stt-tts.png

- **Source** : figure de benchmark STT/TTS réelle. **Cellule source non committée** dans les 3 notebooks 01-3 / 02-4 / 03-1 (aucun n'émet la chaîne « Pas de resultats TTS » en output committé). Candidat probable : une exécution de comparaison STT/TTS où les services TTS étaient indisponibles.
- **Contenu (vision firsthand c.529)** : grille 4 panneaux — (1) barplot « Latence STT par modele » (large-v3-turbo = 0,47 s), (2) panneau vide « Pas de resultats TTS », (3) « Analyse des couts (USD/heure) » (Gratuit), (4) radar « Pas de resultats TTS ».
- **Poids disque** : 94 346 B (md5 `b047ef65`).
- **Alt-text in-situ (README ligne 89)** : Reconnaissance vocale (STT) validée par Whisper large-v3-turbo ; volet TTS non abouti dans l'environnement de test (sous-figures vides). — **fidèle au contenu**.
- **Verdict** : **INTRINSIC (disclosure honnête, C522)** — le volet TTS vide est explicitement signalé dans l'alt-text et le caption ; c'est une divulgation honnête d'un état d'environnement de test, pas un placebo consacré. Inliné (README §01-Foundation). Provenance de cellule à confirmer si les notebooks STT/TTS sont un jour re-exécutés avec services TTS actifs.

## audio4-demucs.png

- **Source** : `02-Advanced/02-4-Demucs-Source-Separation.ipynb` cell[23] out[2] (`# Visualisation et remixage des stems`).
- **Contenu (vision firsthand c.529)** : **5 panneaux Demucs** — Mix original + DRUMS (RMS 0,0307) + BASS (RMS 0,1626) + OTHER (RMS 0,1524) + VOCALS (RMS 0,0117), axe temps 0–9 s. **C'est bien du Demucs** (erreur de lecture c.490 qui y voyait une grille STT/TTS).
- **Traçage** : cellule brute 284 044 B (md5 `b5cc7ba0`) → disque 175 056 B (md5 `ab63e644`), ratio **0,62** (figure large 1398 px ramenée sous le plafond 1200 px).
- **Alt-text (FR, corrigé c.529)** : Séparation de sources Demucs : un mix stéréo décomposé en quatre stems (batterie, basse, autre, voix), chacun avec son énergie RMS annotée.
- **Verdict** : **SOTA-OK** — vraie sortie Demucs du 02-4, légende corrigée (l'ancienne, héritée du misread c.490, décrivait une grille STT/TTS). Inliné (README §02-Advanced).

## audio5-multimodel.png

- **Source** : `01-Foundation/01-3-Basic-Audio-Operations.ipynb` cell[28] out[2] (`# Extraction de caracteristiques`).
- **Contenu (vision firsthand c.529)** : **4 courbes de features librosa** empilées — Spectral Centroid, Spectral Bandwidth, RMS Energy, Zero-Crossing Rate, axe temps 0–12 s.
- **Traçage** : cellule brute 172 278 B (md5 `890f2d8a`) → disque 167 756 B (md5 `03e86f25`), ratio **0,97**.
- **Alt-text (FR)** : Comparaison de modèles audio : plusieurs voies STT/TTS évaluées côte à côte dans un pipeline. — *le nom de slot et l'alt-text historique évoquent une comparaison multi-modèles ; le contenu réel est un panneau de features librosa. Asset orphelin (non inliné), conservé pour traçabilité ; à renommer si un jour réutilisé.*
- **Verdict** : **SOTA-OK** (contenu réel = features librosa du 01-3). Le c.490 avait correctement identifié la cellule source (cell[28]) tout en la classant à tort « déclassée ».

## audio6-tts-benchmark.png

- **Source** : `03-Orchestration/03-1-Multi-Model-Audio-Comparison.ipynb` cell[29] out[1] (`# Visualisation des resultats`).
- **Contenu (vision firsthand c.529)** : **2 barplots** « Latence par modele et type de texte » + « Taille audio par modele et type de texte », kokoro vs openai/tts-1, légende dialogue/monologue/narration.
- **Traçage** : cellule brute 71 205 B (md5 `18fd4304`) → disque 49 946 B (md5 `25b1a862`), ratio **0,70**.
- **Alt-text (FR)** : Benchmark multi-modèles TTS : latence (ms) et taille audio (KB) de kokoro vs openai/tts-1 par type de texte (dialogue, monologue, narration).
- **Verdict** : **SOTA-OK** — vraie sortie du 03-1, légende fidèle. Inliné (README §03-Orchestration). Le c.490 avait correctement identifié la cellule source (03-1 cell[29]) tout en la classant à tort « déclassée ».

---

## Vérification — traçage nbformat c.529 (2026-07-16, worktree fresh origin/main)

Scan `nbformat` des outputs image committés des 3 notebooks sources, croisé avec le MD5/taille des PNG disque :

| Fichier | Cellule source | Brut (nbformat) | Disque | Ratio | Inliné | Verdict |
|---|---|---|---|---|---|---|
| `audio1-waveform.png` | 01-3 cell[12] out[1] | 39 273 B / `3ace572f` | 37 273 B / `09e55bfb` | 0,95 | oui | SOTA-OK |
| `audio2-spectrogram.png` | 01-3 cell[20] out[3] | 84 031 B / `238e0bd6` | 77 625 B / `b9792e33` | 0,92 | non (orphelin) | SOTA-OK (MFCC) |
| `audio3-stt-tts.png` | non committée (3 nb réf.) | — | 94 346 B / `b047ef65` | — | oui | INTRINSIC (TTS vide signalé) |
| `audio4-demucs.png` | 02-4 cell[23] out[2] | 284 044 B / `b5cc7ba0` | 175 056 B / `ab63e644` | 0,62 | oui | SOTA-OK (Demucs) |
| `audio5-multimodel.png` | 01-3 cell[28] out[2] | 172 278 B / `890f2d8a` | 167 756 B / `03e86f25` | 0,97 | non (orphelin) | SOTA-OK (features) |
| `audio6-tts-benchmark.png` | 03-1 cell[29] out[1] | 71 205 B / `18fd4304` | 49 946 B / `25b1a862` | 0,70 | oui | SOTA-OK (barplots TTS) |

**Lecture des ratios** : tous ≤ 1,0 — cohérent avec l'optimisation PIL de `extract_readme_figures.py` (recompression + downscale ≤ 1200 px, qui ne peut que réduire la taille). Le ratio 0,62 d'`audio4` correspond au downscale d'une figure large (1398 px) sous le plafond 1200 px. Aucun ratio n'exige une « source externe ».

**Bilan c.529** : 5/6 tracés à une cellule committée (SOTA-OK), 1/6 (`audio3`) = benchmark STT/TTS réel à volet TTS honnêtement vide (INTRINSIC/C522). 0 figure DROP, 0 swap, 0 régénération nécessaire. La remédiation #5780 sur cette tranche = correction de **texte d'audit faux** (README + MANIFEST), pas de rendu de figure.

## Historique d'audit (superséré — conservé pour traçabilité)

- **c.481 (2026-07-14)** : swap `audio3`↔`audio5` au niveau des blobs disque. Attributions de cellule d'audio2 (MFCC) et audio4 (Demucs) **correctes** ; celles d'audio5 (donné 03-1 au lieu de 01-3) et audio6 (donné 04-7 au lieu de 03-1) **erronées**.
- **c.490 (2026-07-14)** : a **inversé la lecture visuelle d'audio2 et audio4** (MFCC lu « Demucs », Demucs lu « STT/TTS »), et conclu à tort « 5/6 externes » sur la fausse prémisse MD5≠brut (ignorant l'optimisation PIL). A néanmoins corrigé les sources d'audio5 (01-3 cell[28]) et audio6 (03-1 cell[29]).
- **c.529 (2026-07-16)** : réconciliation firsthand (vision + git par-blob + nbformat) → les 6 figures sont de vraies sorties de notebook ; attributions ci-dessus définitives.

**Voir aussi** : issue [#5780](../../../issues/5780) ; EPIC [#5654](../../../issues/5654) ; [GenAI/Image MANIFEST](../../../Image/assets/readme/MANIFEST.md) et [GenAI/Video MANIFEST](../../../Video/assets/readme/MANIFEST.md) (patterns frères de traçabilité de figures).
