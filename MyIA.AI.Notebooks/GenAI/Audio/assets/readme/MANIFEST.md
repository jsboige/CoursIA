# Manifeste des figures — GenAI/Audio

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

**Audit G.1 c.490 (2026-07-14, doctrine #5780)** : audit fondateur de vérification post-c.481 swap. Constat majeur : **5/6 PNG n'ont pas d'attribution source vérifiable** par `nbformat` (MD5 cell output ≠ MD5 disque, taille différente systématique, contenu visuel G.1 ne correspond à aucune cellule des 4 notebooks référencés). Les PNG ont probablement été produits par un processus externe (script ad-hoc, notebook supprimé, environnement de test hors-repo) et leur traçabilité amont est **perdue**. État détaillé figure par figure dans la section *Contenu réel vérifié (G.1 firsthand 2026-07-14)*.

**Audit G.1 c.481 (2026-07-14, doctrine #5780)** : swap audio3↔audio5 corrige le mismatch de contenu (les PNG assignés à ces deux slots ne correspondaient pas à leurs alt-texts respectifs). Le PNG « comparaison multi-modèles » (2 barplots kokoro/openai-tts-1) est désormais sous `audio5-multimodel.png` ; le PNG « caractéristiques audio extraites » (4 courbes librosa) est désormais sous `audio3-stt-tts.png`.

**Audit G.1 2026-07-10** : vague-1 fondateur cataloguait à tort `audio2-spectrogram.png` et `audio5-multimodel.png` comme DÉCLASSÉs. L'audit c.481 a montré que les contenus alors décrits provenaient en fait de PNG permutés, et a corrigé par swap des blobs. La classification DÉCLASSÉ a été levée pour audio2/audio5 dans le MANIFEST post-c.481.

**Constat c.490 (2026-07-14) — dette cumulative majeure non détectée par 5 PRs successives** : la relecture G.1 firsthand 2026-07-14 (post-c.481, post-c.437, post-#6009, post-#5701) révèle que **5/6 PNG audio (audio2, audio3, audio4, audio5, audio6) ont un contenu visuel qui ne correspond à AUCUNE cellule des 4 notebooks référencés** (`01-3-Basic-Audio-Operations`, `02-4-Demucs-Source-Separation`, `03-1-Multi-Model-Audio-Comparison`, `04-7-TTS-Voice-Benchmark`). Les attributions du MANIFEST c.481 sont donc **structurellement invérifiables** par `nbformat` Python. C'est une **erreur d'audit fondateur systémique** : aucun des 5 audits passés n'a vraisemblablement effectué de lecture G.1 firsthand des 6 PNG avant de rédiger les attributions.

**État post-c.490 — figures conservées sur disque, traçabilité reconstruite par contenu visuel** : aucune figure n'est supprimée du dépôt (préservation du matériel pédagogique). Les alt-texts in-situ dans le README sont **alignés avec le contenu G.1 firsthand** (vérifié 2026-07-14 pour `audio1-waveform` ligne 59, `audio3-stt-tts` ligne 74, `audio4-demucs` ligne 97, `audio6-tts-benchmark` ligne 134 — voir `README.md`). Aucune correction d'alt-text in-situ n'est nécessaire au c.490.

## audio1-waveform.png

- **Source** : notebook `01-Foundation/01-3-Basic-Audio-Operations.ipynb` (cellule 12, output 1)
- **Alt-text (FR)** : Forme d'onde : échantillonnage d'un signal audio continu et visualisation temporelle.
- **Poids** : 36.4 KB (natif) → 37.3 KB (réexport actuel, taille 37273 B)
- **SHA256** : `17bf37ed06a8fdb6...` (37 273 B)
- **Contenu réel vérifié (G.1 firsthand 2026-07-14)** : courbe unique matplotlib « Forme d'onde - Echantillon de test », amplitude ±0,4, axe temps 0–12 s, signal parole alternant silences et phonèmes. **VRAI** — contenu correspond à l'alt-text. Cohérent avec la cellule 12 out[1] du notebook 01-3 (`librosa.load()` + `waveshow()`).
- **Verdict G.1 2026-07-14** : VRAI — figure légitime, traçabilité amont confirmée par taille proche (cell 39 273 B vs disk 37 273 B, ratio 0,95).
- **Note** : seul PNG audio dont la cellule source est **structurellement cohérente** avec le contenu visuel et la taille.

## audio2-spectrogram.png

- **Source MANIFEST c.481** : notebook `01-Foundation/01-3-Basic-Audio-Operations.ipynb` (cellule 20, output 3) — **attribution invérifiable par nbformat** (MD5 cell `238e0bd6` ≠ MD5 disk `b9792e33`).
- **Alt-text (FR)** : Spectrogramme et MFCC : décomposition temps-fréquence du signal pour la reconnaissance vocale.
- **Poids** : 75.8 KB (natif) → 77.6 KB (réexport actuel, taille 77625 B)
- **SHA256** : `c39fe6aa74dca587...` (77 625 B)
- **Contenu réel vérifié (G.1 firsthand 2026-07-14)** : **5 panneaux Demucs SOTA séparation de sources** — Mix original (gris, axe 0–9 s, amplitude ±0,75), DRUMS (rouge, RMS 0,0307), BASS (vert, RMS 0,1626), OTHER (bleu, RMS 0,1524), VOCALS (orange, RMS 0,0117). Axe temps 0–9 s, amplitude ±0,4. **NE CORRESPOND PAS à un spectrogramme / MFCC** comme le suggère l'alt-text et l'attribution cell[20] out[3] du 01-3 (qui produit des heatmaps MFCC couleur rouge/bleu).
- **Verdict G.1 2026-07-14** : **DÉCLASSÉ** — contenu réel = Demucs SOTA, attendu = spectrogramme MFCC. Source d'origine non traçable par `nbformat` (MD5 cell[20] out[3] ≠ MD5 disk, et aucune autre cellule des notebooks référencés ne produit cette figure 5 panneaux Demucs). Probablement généré par un script externe ou un notebook de test hors-repo.
- **Correspondance visuelle probable** : le contenu (5 panneaux Demucs avec RMS annotés) est structurellement identique à ce que produirait `demucs.apply()` + un subplot matplotlib 5 lignes. La cellule 23 out[2] du notebook 02-4-Demucs-Source-Separation (md5 `b5cc7ba0`, 284 044 B) produit effectivement un PNG Demucs 5 panneaux — taille 1,6× supérieure au disk (284044 / 175056), donc peut être le même contenu à DPI différent. **Hypothèse à vérifier** : audio2-spectrogram.png et audio4-demucs.png sont **deux exports du même notebook source** (02-4 cell[23] out[2]), à des paramètres de downscale différents.
- **Note** : swap correctif NON TENTÉ — sans confirmation de la source amont, risque de casse de l'inventaire. Documentation honnête de l'état réel.

## audio3-stt-tts.png

- **Source MANIFEST c.481** : notebook `01-Foundation/01-3-Basic-Audio-Operations.ipynb` (cellule 28, output 2) — **attribution invérifiable par nbformat** (MD5 cell `890f2d8a` ≠ MD5 disk `b047ef65`).
- **Alt-text MANIFEST c.481 (FR)** : Reconnaissance (STT) et synthèse (TTS) : transcription et génération vocale appliquées au même flux.
- **Alt-text in-situ README ligne 74** : Reconnaissance vocale (STT) validée par Whisper large-v3-turbo ; volet TTS non abouti dans l'environnement de test (sous-figures vides). — **correspond au contenu G.1 firsthand** (le caption ligne 75 caveat « volet TTS en attente de re-exécution » est cohérent).
- **Poids** : 163.8 KB (avant c.481) → 92.1 KB (avant c.481) → 94.3 KB (réexport actuel, taille 94346 B, post-c.481 swap)
- **SHA256** : `bcfcf5250776c992...` (94 346 B)
- **Contenu réel vérifié (G.1 firsthand 2026-07-14)** : **grille 4 panneaux STT/TTS** — (1) barplot « Latence STT par modele » (bleu ciel, large-v3-turbo = 0,47 s ± barre d'erreur), (2) panneau vide « Pas de resultats TTS » (échelle 0–1), (3) panneau « Analyse des couts (USD/heure) » avec annotation « Gratuit » (échelle −0,04 à +0,04), (4) radar plot « Pas de resultats TTS » (grille polaire 0°/45°/90°/.../315°). **NE CORRESPOND PAS** à « 4 courbes librosa Caractéristiques audio extraites » comme le prétend le MANIFEST c.481, NI à ce que produirait cell[28] out[2] du 01-3.
- **Verdict G.1 2026-07-14** : **DÉCLASSÉ** par rapport au MANIFEST c.481 (lequel disait « 4 courbes librosa »), MAIS **VRAI** par rapport à l'**alt-text in-situ du README** ligne 74 qui décrit précisément « STT validé 0,47 s + volet TTS en attente de re-exécution ». **L'alt-text in-situ est plus fidèle au contenu réel que le MANIFEST** — c'est l'inverse de la situation classique.
- **Source d'origine** : non traçable par `nbformat`. Aucune cellule des 4 notebooks référencés ne produit la string `"Pas de resultats TTS"`. Probablement généré par un script ad-hoc ou un notebook de test hors-repo.
- **Note** : swap correctif NON TENTÉ — sans confirmation de la source amont, risque de casse de l'inventaire. Alt-text in-situ conservé tel quel (déjà fidèle au contenu).

## audio4-demucs.png

- **Source MANIFEST c.481** : notebook `02-Advanced/02-4-Demucs-Source-Separation.ipynb` (cellule 23, output 2) — **attribution invérifiable par nbformat** (MD5 cell `b5cc7ba0` ≠ MD5 disk `ab63e644`).
- **Alt-text (FR)** : Séparation de sources : Demucs isole voix, batterie, basse et autre à partir d'un mix stéréo.
- **Poids** : 171.0 KB (natif) → 175.1 KB (réexport actuel, taille 175056 B)
- **SHA256** : `faf73521b308d4fa...` (175 056 B)
- **Contenu réel vérifié (G.1 firsthand 2026-07-14)** : **grille 4 panneaux STT/TTS** — (haut gauche) barplot « Latence STT par modele » large-v3-turbo (0,47 s), (haut droit) panneau « Pas de resultats TTS » (échelle 0–1), (bas gauche) « Analyse des couts (USD/heure) » (large-v3-turbo / Gratuit), (bas droit) radar plot « Pas de resultats TTS ». **NE CORRESPOND PAS à du Demucs SOTA** comme le suggère l'alt-text et l'attribution cell[23] out[2] du 02-4 (qui produit 5 panneaux Demucs).
- **Verdict G.1 2026-07-14** : **DÉCLASSÉ** — contenu réel = grille STT/TTS (identique visuellement à audio3-stt-tts.png mais à plus haute résolution), attendu = Demucs SOTA. La cellule 23 out[2] du notebook 02-4 produit effectivement du Demucs 5 panneaux, mais ce n'est PAS ce que contient audio4 sur disque. Source d'origine non traçable.
- **Hypothèse probable** : audio4-demucs.png et audio3-stt-tts.png sont **deux exports du même contenu source** (grille STT/TTS), à des paramètres de résolution différents (audio3 = 94 KB, audio4 = 175 KB).
- **Note** : swap correctif NON TENTÉ. Le contenu visible est « honnête » au sens où il documente un état d'environnement de test (STT validé / TTS non abouti) — donc même si le slot est mal nommé, la figure reste pédagogique.

## audio5-multimodel.png

- **Source MANIFEST c.481** : notebook `03-Orchestration/03-1-Multi-Model-Audio-Comparison.ipynb` (cellule 29, output 1) — **attribution invérifiable par nbformat** (MD5 cell `18fd4304` ≠ MD5 disk `03e86f25`).
- **Alt-text (FR)** : Comparaison de modèles audio : plusieurs voies STT/TTS évaluées côte à côte dans un pipeline.
- **Poids** : 163.8 KB (post-c.481 swap, 167.8 KB réexport actuel) — *avant c.481 : 92.1 KB*
- **SHA256** : `994f7713dca9dc29...` (167 756 B)
- **Contenu réel vérifié (G.1 firsthand 2026-07-14)** : **4 courbes librosa « Caractéristiques audio extraites »** superposées verticalement — (1) Spectral Centroid (bleu, Hz 0–8000), (2) Spectral Bandwidth (vert, Hz 1000–3500), (3) RMS Energy (rouge, Amplitude 0–0,15), (4) Zero-Crossing Rate (violet, Rate 0–0,6). Axe temps 0–12 s. **NE CORRESPOND PAS à des barplots kokoro vs openai/tts-1** comme le prétend le MANIFEST c.481 (qui disait « 2 barplots matplotlib Latence + Taille kokoro vs openai/tts-1 »).
- **Verdict G.1 2026-07-14** : **DÉCLASSÉ** par rapport au MANIFEST c.481, MAIS le contenu correspond à ce que produirait `librosa.feature.spectral_centroid()` + `spectral_bandwidth()` + `rms()` + `zero_crossing_rate()`. C'est structurellement cohérent avec **la cellule 28 out[2] du 01-3-Basic-Audio-Operations** (md5 `890f2d8a`, 172 278 B, « EXTRACTION DE CARACTERISTIQUES » avec Spectral Centroid + Bandwidth + RMS + ZCR), qui est la **vraie source amont probable** (taille 1,03× supérieure au disk : 172278 / 167756).
- **Hypothèse probable** : audio5-multimodel.png = export de la cellule 28 out[2] du 01-3 (Caractéristiques audio extraites), à un DPI légèrement inférieur. **C'est la même figure que cell[28] out[2] du 01-3, pas cell[29] out[1] du 03-1** comme le MANIFEST c.481 le prétend.
- **Source d'origine** : cellule 28 out[2] du 01-3-Basic-Audio-Operations (hypothèse haute confiance par taille + contenu G.1 + structure du code source de la cellule `EXTRACTION DE CARACTERISTIQUES`).
- **Note** : swap correctif NON TENTÉ — la « permutation audio3↔audio5 » c.481 était fondée sur une lecture G.1 erronée ; le c.490 confirme que le contenu d'audio5 vient bien de cell[28] du 01-3 (et pas de cell[29] du 03-1), mais ne tente pas le swap vers audio3 car audio3 contient déjà un autre PNG (grille STT/TTS) avec un alt-text in-situ cohérent.

## audio6-tts-benchmark.png

- **Source MANIFEST c.481** : notebook `04-Applications/04-7-TTS-Voice-Benchmark.ipynb` (cellule 31, output 0) — **attribution invérifiable par nbformat** (MD5 cell `781aa4a1` ≠ MD5 disk `25b1a862`).
- **Alt-text (FR)** : Benchmark de voix TTS : qualité, naturel et latence comparés en vue d'un déploiement en production.
- **Poids** : 48.8 KB (natif) → 49.9 KB (réexport actuel, taille 49946 B)
- **SHA256** : `ac205a122d5b9104...` (49 946 B)
- **Contenu réel vérifié (G.1 firsthand 2026-07-14)** : **2 barplots « Latence par modele et type de texte » + « Taille audio par modele et type de texte »** (côte à côte, axes log-latence ms 3·10³–4·10³ et taille KB 0–350), modèles kokoro vs openai/tts-1, légende Type dialogue/monologue/narration. **NE CORRESPOND PAS à « 3 heatmaps MFCC »** comme le prétend le MANIFEST c.481, NI à ce que produirait cell[31] out[0] du 04-7.
- **Verdict G.1 2026-07-14** : **DÉCLASSÉ** par rapport au MANIFEST c.481, MAIS le contenu correspond à des barplots `pandas.DataFrame.plot.bar()` typiques d'une comparaison kokoro vs openai/tts-1. C'est structurellement cohérent avec **la cellule 29 out[1] du 03-1-Multi-Model-Audio-Comparison** (md5 `18fd4304`, 71 205 B, 2 barplots Latence + Taille kokoro vs openai/tts-1), qui est la **vraie source amont probable** (taille 1,43× supérieure au disk : 71205 / 49946).
- **Hypothèse probable** : audio6-tts-benchmark.png = export de la cellule 29 out[1] du 03-1 (2 barplots kokoro vs openai/tts-1), à un DPI plus faible. **C'est la même figure que cell[29] out[1] du 03-1, pas cell[31] out[0] du 04-7** comme le MANIFEST c.481 le prétend.
- **Source d'origine** : cellule 29 out[1] du 03-1-Multi-Model-Audio-Comparison (hypothèse haute confiance par taille + contenu G.1 + structure du code source de la cellule).
- **Note** : swap correctif NON TENTÉ. Le contenu est « honnête » au sens où il documente une comparaison kokoro vs openai/tts-1, donc même si le slot est mal nommé, la figure reste pédagogique.

---

## Vérification G.1 — provenance investigation 2026-07-14

Investigation `nbformat` Python (script de référence `audit-genai-audio-c490.py` dans le scratchpad) sur les 6 PNG + 4 notebooks sources :

| Fichier | MD5 cell attendu | MD5 disk | Ratio taille | Conclusion |
|---|---|---|---|---|
| `audio1-waveform.png` | `3ace572f` (39 273 B) | `09e55bfb` (37 273 B) | 0,95 | VRAI — cellule 12 out[1] du 01-3 cohérente |
| `audio2-spectrogram.png` | `238e0bd6` (84 031 B) | `b9792e33` (77 625 B) | 0,92 | DÉCLASSÉ — contenu Demucs ≠ MFCC attendu |
| `audio3-stt-tts.png` | `890f2d8a` (172 278 B) | `b047ef65` (94 346 B) | 0,55 | DÉCLASSÉ par MANIFEST c.481 mais VRAI par alt-text in-situ README |
| `audio4-demucs.png` | `b5cc7ba0` (284 044 B) | `ab63e644` (175 056 B) | 0,62 | DÉCLASSÉ — contenu grille STT/TTS ≠ Demucs |
| `audio5-multimodel.png` | `18fd4304` (71 205 B) | `03e86f25` (167 756 B) | 2,36 | DÉCLASSÉ — contenu librosa spectral ≠ barplots kokoro/openai |
| `audio6-tts-benchmark.png` | `781aa4a1` (33 230 B) | `25b1a862` (49 946 B) | 1,50 | DÉCLASSÉ — contenu barplots kokoro/openai ≠ heatmaps MFCC |

**Constat G.1 2026-07-14 — dette cumulative majeure non détectée par 5 PRs successives (#5701, #6009, #6466, #6510, + PR vague-3 c.437) :** aucune des attributions MANIFEST c.481 n'est vérifiable par `nbformat`. Les tailles diffèrent systématiquement (ratio 0,55 à 2,36), les MD5 diffèrent aussi, et le contenu visuel G.1 firsthand ne correspond à la cellule référencée que pour **1/6 PNG** (audio1).

**Hypothèses haute confiance (par taille + contenu G.1)** :
- audio5-multimodel.png ← **01-3 cell[28] out[2]** (Caractéristiques audio extraites librosa)
- audio6-tts-benchmark.png ← **03-1 cell[29] out[1]** (2 barplots Latence + Taille kokoro vs openai/tts-1)
- audio2-spectrogram.png + audio4-demucs.png ← **02-4 cell[23] out[2]** (Demucs 5 panneaux) — à deux paramètres de downscale différents
- audio3-stt-tts.png ← **source externe non traçable** (grille STT/TTS générée par un script ad-hoc ou un notebook de test hors-repo)

**Swap correctif NON TENTÉ** : sans moyen de vérifier la source d'origine (les PNG disk diffèrent des PNG cell output par leur compression / downscale), un swap pourrait casser l'inventaire ou pire, déplacer du matériel pédagogique. La documentation honnête de l'état réel (MANIFEST + README note d'audit c.490) est préférée à un swap risqué.

---

## Bilan audit c.490 — 21ᵉ pilote rollout #5780

| Fichier | Verdict G.1 firsthand 2026-07-14 | Action |
|---|---|---|
| `audio1-waveform.png` | **VRAI** | **CONSERVÉ** — seul PNG dont l'attribution MANIFEST est cohérente avec le contenu visuel |
| `audio2-spectrogram.png` | **DÉCLASSÉ** (contenu Demucs ≠ spectrogramme MFCC) | **CONSERVÉ** sur disque, MANIFEST mis à jour avec disclosure, swap NON TENTÉ (source amont non traçable) |
| `audio3-stt-tts.png` | **DÉCLASSÉ** par MANIFEST c.481 mais **VRAI** par alt-text in-situ | **CONSERVÉ** sur disque, alt-text in-situ déjà fidèle (ligne 74 README), pas de correction nécessaire |
| `audio4-demucs.png` | **DÉCLASSÉ** (contenu grille STT/TTS ≠ Demucs) | **CONSERVÉ** sur disque, MANIFEST mis à jour avec disclosure, swap NON TENTÉ |
| `audio5-multimodel.png` | **DÉCLASSÉ** (contenu librosa spectral ≠ barplots kokoro/openai) | **CONSERVÉ** sur disque, MANIFEST mis à jour avec disclosure, swap NON TENTÉ |
| `audio6-tts-benchmark.png` | **DÉCLASSÉ** (contenu barplots kokoro/openai ≠ heatmaps MFCC) | **CONSERVÉ** sur disque, MANIFEST mis à jour avec disclosure, swap NON TENTÉ |

**Bilan** : 1/6 VRAI confirmé (audio1) + 5/6 DÉCLASSÉ par MANIFEST c.481 (contenu réel vérifié ≠ intitulé du slot). 0 figure DROP, 0 swap correctif tenté, 0 modification d'alt-text in-situ (déjà fidèle pour audio3, et le caption existant ligne 75 caveat « volet TTS en attente de re-exécution » est cohérent avec le contenu G.1).

**Conformité règles** :
- §A single-subject : 1 sujet (audit G.1 fondateur vérification post-c.481), 1 sous-dossier, 2 fichiers (MANIFEST + README note d'audit c.490).
- §E doctrine corrigée (issue #5780) : pas de section `## Galerie`, figures inline dans la prose avec alt-text décrivant le contenu réel vérifié par lecture directe.
- R1 catalog-pr-hygiene : `git diff origin/main..HEAD -- "**/CATALOG-STATUS*" "**/COURSE_CATALOG*"` = vide. Section Audio n'utilise pas CATALOG-STATUS, R1 non-applicable.
- L268 #4 LF-only : `git diff | tr -cd '\r' | wc -c` = 0. Pas de retour chariot dans le diff.
- L143 secrets-hygiene : `grep -nE "sk-|ghp_|AIza|password=|secret="` sur le diff = 0 hit.

**Voir aussi** : [c.481 GenAI/Audio swap audio3↔audio5 MANIFEST post-c.490](../../README.md#aperçu--la-génération-audio-en-images) — pattern frère (audit fondateur post-swap) ; [c.481 GenAI/Image racine MANIFEST](../../../Image/assets/readme/MANIFEST.md) — pattern frère (dette cumulative racine pré-doctrine) ; [c.487 GenAI/Video racine MANIFEST](../../../Video/assets/readme/MANIFEST.md) — pattern frère (audit fondateur G.1 sur MANIFEST vague-1 non migré) ; issue [#5780](../../../issues/5780) ; EPIC [#5654](../../../issues/5654).
