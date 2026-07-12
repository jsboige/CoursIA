# Galerie README — Video 01-Foundation (bases vidéo & compréhension)

Provenance de chaque figure (convention `extract_readme_figures.py` L132 : index ALL-CELLS).
Toutes les figures sont extraites des **outputs déjà committés** des notebooks (C.3 — aucune re-exécution).
Bornes EPIC #5654 P1 respectées : ≤200 KB/fichier, ≤1200 px max-dim.

> **Note d'audit (2026-07-10, doctrine #5780).** Lecture visuelle G.1 firsthand des 6 PNG effectuée par myia-po-2023 — toutes les figures correspondent à leur intitulé (6/6 VRAI). La mosaïque-bloc en tête du README a été convertie en **figures in-line narratif** (5 sections narratives, chacune avec sa figure + paragraphe d'interprétation adjacent) ; ce MANIFEST documente la **provenance** et la **traçabilité G.1** des 6 PNG. Cf PR §E rollout Video/01-Foundation (c.351).

| Figure | Notebook source | Cellule | Output | Format | Dimensions | Poids | Alt-text FR |
|--------|-----------------|---------|--------|--------|------------|-------|-------------|
| `vid1-ops.png` | `01-1-Video-Operations-Basics.ipynb` | 8 | 3 | PNG | 1200×221 | 27,9 KB | Opérations vidéo de base — aperçu des frames |
| `vid1-gpt5.png` | `01-2-GPT-5-Video-Understanding.ipynb` | 8 | 2 | PNG | 1200×221 | 19,8 KB | Compréhension vidéo GPT-5 — analyse |
| `vid1-qwen-vl.png` | `01-3-Qwen-VL-Video-Analysis.ipynb` | 10 | 2 | PNG | 1200×221 | 23,8 KB | Analyse vidéo Qwen-VL — annotation |
| `vid1-esrgan.png` | `01-4-Video-Enhancement-ESRGAN.ipynb` | 8 | 3 | PNG | 1200×503 | 140,9 KB | Enhancement ESRGAN — upscale |
| `vid1-esrgan2.png` | `01-4-Video-Enhancement-ESRGAN.ipynb` | 16 | 1 | PNG | 1200×230 | 85,2 KB | Enhancement ESRGAN — panorama |
| `vid1-animatediff.png` | `01-5-AnimateDiff-Introduction.ipynb` | 10 | 3 | PNG | 500×252 | 195,7 KB | Génération AnimateDiff — animation |

**Diversité couverte** : 5 notebooks fondamentaux (Opérations, Compréhension GPT-5, Analyse Qwen-VL, Enhancement ESRGAN, AnimateDiff). Total : 6 figures, 493,3 KB, max 195,7 KB/fichier. Toutes PNG. AnimateDiff (195,7 KB) : source dense 2,1 MB, downscale 500px — sous la borne dure 200 KB.

## Audit G.1 firsthand (lecture visuelle 2026-07-10, myia-po-2023)

| Figure | Audit G.1 (observation directe du PNG) | Verdict |
|--------|----------------------------------------|---------|
| `vid1-ops.png` | Mosaïque 5 frames (vert/rouge/violet/cyan/vert) avec cercle blanc à positions variables, t=0.00s → 4.96s. Titre "Apercu de la video de test" (01-1 cell 8 output 3). Cercles blancs à droite/bas/centre-gauche/haut/droite. | **VRAI** — la mosaïque-frames de la vidéo de test est observable et conforme à l'intitulé. |
| `vid1-gpt5.png` | Mosaïque 5 scènes (orange/bleu/vert/rose/bleu nuit) avec cercle/carré/triangle/cercle/5 cercles jaunes. Titre "Apercu des 5 scenes", sous-titres "Scene 1 — Intro" → "Scene 5 — Conclusion". | **VRAI** — la mosaïque montre la **structure** de la vidéo soumise à GPT-5 (variation couleurs + sous-titres), pas l'analyse GPT-5 elle-même. Limitation illustrative assumée dans le paragraphe narratif. |
| `vid1-qwen-vl.png` | Mosaïque 5 scènes pédagogiques (Introduction/Chapitre 1/Demo/Resultats/Conclusion) sur fonds bleu nuit/brun/vert forêt/olive/violet, point jaune central. | **VRAI** — la vidéo à analyser par Qwen-VL est observable et conforme ; limitation illustrative assumée. |
| `vid1-esrgan.png` | Grille 2×4 comparant HR (Référence, ligne haute, HR320×240 avec quadrillage blanc) vs LR (Input, ligne basse, LR320×240) sur Frames 0/12/24/35. Cercle rouge + 4 points verts. Titre "Reference HR vs Input LR". | **VRAI** — comparaison côte-à-côte explicite, parfaitement alignée avec "ESRGAN upscale LR→HR". |
| `vid1-esrgan2.png` | Grille 5 panneaux (Frame A / Interp 1 / Interp 2 / Interp 3 / Frame B) montrant interpolation linéaire entre deux positions du cercle rouge, Frames 1/36 → 6/36. Fantômes visibles aux frames intermédiaires. | **VRAI** — interpolation linéaire Frame A→Frame B observable ; limitation illustrative assumée (linéaire ≠ RIFE/FILM). |
| `vid1-animatediff.png` | Mosaïque 4×2 (8 frames) d'animation "A serene lake at sunset with mountains in the background", style painterly/pastel. Frames 0/126/252/378/504/630/756/882 sur 16 frames totales. | **VRAI** — animation AnimateDiff observable, conformité au prompt descriptif. |

**Verdict global : 6/6 VRAI**. Aucune figure déclassée (cf doctrine #5780 et la leçon C350-L1 : intitulé ≠ contenu — vérifié firsthand).
