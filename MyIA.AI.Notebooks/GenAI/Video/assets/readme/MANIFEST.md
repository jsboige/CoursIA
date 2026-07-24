# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

**Audit G.1 fondateur** : relecture visuelle via outil `Read` par `myia-po-2025` le **2026-07-14** (cycle c.486 du rollout [issue #5780](../../../../../issues/5780)). Bilan : 0/6 ACCURATE mature + 6/6 corrections réelles (3 refontes alt-text + 3 enrichissements). Migration format : table simple (vague-1) → liste détaillé standard (cf [c.469 SemanticWeb](../../../../SymbolicAI/SemanticWeb/assets/readme/MANIFEST.md), [c.481 GenAI/Image racine](../../../Image/assets/readme/MANIFEST.md), [c.484 GenAI/Image/03-Orchestration](../../../Image/03-Orchestration/assets/readme/MANIFEST.md), [c.485 GenAI/Video/04-Applications](../../04-Applications/assets/readme/MANIFEST.md)).

**Migration c.753 (2026-07-22, doctrine #5780 amendée par PR #7771)** : ajout du champ canonique `**Description visuelle** :` aux 6 entrées (format vague-1 → canonique `Source / Description visuelle / Alt-text / Poids / Contenu réel vérifié / Ce qui n'est PAS`). Source = vision-QA MiniMax M3 ([mandat 2026-07-11](https://github.com/jsboige/CoursIA/issues/3801) — `Read` direct PNG + RGB PIL stats par `myia-po-2023` ré-audit c.671). Conformité avec le détecteur `scripts/notebook_tools/detect_manifest_field.py` (PR #7819 c.754) : 6/6 figures déclarent `Description visuelle` post-migration. Le champ `Contenu réel vérifié` (audit c.486 po-2025) reste en place comme preuve falsifiable détaillée ; le nouveau `Description visuelle` est la version canonique courte destinée à l'extraction automatique et au lecteur rapide.

**Vision-QA MiniMax M3 (po-2023, 2026-07-22)** : 6/6 PNG lus firsthand, **tous ACCURATE** vs audit c.486 fondateur (0 MISMATCH nouveau détecté, **0 correction supplémentaire nécessaire** — l'audit c.486 reste canonique ; ce cycle ne fait que reformat er sans introduire de nouvelle lecture disputée).

| Figure | Tell dominant | RGB mean (R,G,B) | Stdmean | Blanc pur (%) | Type structurel |
|--------|---------------|------------------|---------|---------------|------------------|
| video1-frames.png | multi-color | (151.5, 162.2, 141.8) | 94.4 | 19.2% | mosaique 2×4 palette cyclique 8-couleurs |
| video4-esrgan.png | dark-field | (85.5, 77.8, 99.4) | 82.9 | 17.3% | grille 2×4 navy + rouge + vert |
| video5-animatediff.png | multi-color | (135.7, 128.9, 118.5) | 68.8 | 17.5% | grille 2×4 paysage lacustre coucher soleil |
| video-svd.png | multi-color | (152.8, 152.7, 158.6) | 75.2 | 28.2% | 3 vignettes côte-à-côte inputs SVD |
| video-creative-style.png | multi-color + blanc | (175.7, 153.4, 173.5) | 95.3 | 45.6% | grille 4×3 (Original/P./Aqu./Dessin) × 3 frames |
| video-sora-cost.png | **matplotlib-blanc** (L778-L2) | (231.5, 229.4, 232.1) | 55.4 | **79.1%** | 2 panneaux lineplot+barplot fond blanc dominant |

**Pivot post-PR #8005 (po-2025)** : Probas-racine MANIFEST déjà claim par PR #8005 OPEN (jsboige/CoursIA-2 c.784). DecisionTheory/PyMC c.779 déjà canonical. 5 defects restants EPIC #5780 ; `gh pr list --search "<file>"` montre 3 slots vraiment libres : GenAI/PostTraining (1 fig), GenAI/Texte (3 fig), **GenAI/Video racine (6 fig, retenu)**. G-VAR-3 cross-famille OK (env-repair Probas c.752 MED → docs-hygiene GenAI/Video c.753 MED, familles distinctes).

---

## video1-frames.png

- **Source** : notebook `01-Foundation/01-1-Video-Operations-Basics.ipynb` (cellule 16, output 2 — display_data `image/png`, 72 144 B)
- **Description visuelle** : Mosaique pédagogique 2 lignes × 4 colonnes (509×1200 max-dim 1200 policy #5654) sur fond uni. **8 vignettes successives d'une balle blanche** circulaire bondissante à des positions spatiales distinctes. Frame labels superposés : `Frame 0 / t=0.00s`, `Frame 17 / t=0.71s`, `Frame 34 / t=1.42s`, `Frame 51 / t=2.12s`, `Frame 68 / t=2.83s`, `Frame 85 / t=3.54s`, `Frame 102 / t=4.25s`, `Frame 119 / t=4.96s` (extraction uniforme par pas de 17 frames sur 120 frames totales, soit 24fps × 5s). **Fonds colorés cycliques 8-couleurs avec retour à lime** : `lime / orange / red / magenta-pink / blue / cyan-teal / green / lime`. Watermark `Frame X/Y 640×480 @ 24fps` en haut-gauche de chaque vignette. Titre global gras `Extraction uniforme - 8 frames via decord`. Stats RGB : mean (151.5, 162.2, 141.8) std 94.4 — variance modérée typique d'une mosaique 8 fonds distincts sur blanc. Tell structurel = **mosaique temporelle uniforme (8 frames équidistantes, palette cyclique)** illustrant la régularité de l'extraction décord.
- **Alt-text (FR)** : Extraction uniforme de 8 frames via decord : mosaique pédagogique 2×4 d'une balle blanche bondissante (Frame 0/17/34/51/68/85/102/119 sur fonds colorés alternés lime/orange/rouge/magenta/bleu/cyan/vert/lime, palette cyclique 640×480 @ 24fps).
- **Dimensions effectives (vérifiées `PIL.Image.open` 2026-07-22)** : 509×1200 max-dim 1200 (downscale policy #5654) vs 640×480 source authentique = ratio d'aspect préservé 1.33 ≈ 1.33, ratio disque/source = 0.94× (PNG lossless).
- **Poids** : 66.3 KB (downscale max-dim 1200)
- **SHA256** : `2d2c48d7fad7a5ae19b25d9f6aa39ad4ebb98de45d118eed32fee02fd51a81aa`
- **Contenu réel vérifié (lecture `Read` 2026-07-14, ré-audit visuel c.671 2026-07-19 par `myia-po-2023` MiniMax-M3)** : mosaique 2×4 d'une balle blanche bondissante. Frame 0/17/34/51/68/85/102/119, timesteps t=0.00/0.71/1.42/2.12/2.83/3.54/4.25/4.96s. Fonds colorés alternés (palette cyclique 8-couleurs retournant à lime) : lime / orange / rouge / magenta / bleu / cyan / vert / lime. Résolution 640×480 @ 24fps. Titre superposé : « Extraction uniforme - 8 frames via decord ».
- **Note** : ancien alt-text « Extraction de frames : découpe d'une vidéo en images clés avec decord pour l'analyse » — **enrichi** avec description factuelle des 8 frames observables (motif balle bondissante + fonds colorés + résolution). **Précision transférable** : la mosaïque illustre la **régularité** de l'extraction uniforme (pas constant de 17 frames sur 120), pas l'extraction elle-même — le décodeur decord apparaît ici comme un moyen, pas comme une fin.

## video4-esrgan.png

- **Source** : notebook `01-Foundation/01-4-Video-Enhancement-ESRGAN.ipynb` (cellule 8, output 3 — display_data `image/png`, 102 147 B)
- **Description visuelle** : Grille 2 lignes × 4 colonnes (503×1200) sur fond blanc-légèrement-bleuté. **Titre global gras** `Reference HR vs Input LR`. **Rangée haute = HR (High Resolution, label HR320x240)** : 4 vignettes nettes d'une balle rouge (cercle plein avec léger quadrillage rouge interne) et 4 billes vertes en haut, sur fond **navy foncé quadrillé blanc**. Frame labels `HR - Frame 0`, `HR - Frame 12`, `HR - Frame 24`, `HR - Frame 35` superposés au-dessus de chaque vignette (compte des frames affichées : 0, 12, 24, 35). Watermark diagonal `Frame X/36` en blanc en haut-gauche de chaque vignette. **Rangée basse = LR (Low Resolution, label HR320x240)** : 4 vignettes identiques en composition mais avec un **blur léger** (soft/blur appliqué uniformément). Frame labels `LR - Frame 0 / 12 / 24 / 35`. **Les deux rangées ont strictement la même résolution 320×240 affichée** — la démonstration ESRGAN visible dans cette figure est une **comparaison qualité HR vs LR à résolution identique**, pas un upscaling visuel HR→LR.
- **Alt-text (FR)** : Comparaison HR vs LR sur 4 frames — balle rouge + 4 billes vertes sur fond noir quadrillé, HR (320×240, nette) vs LR (320×240, soft/blur), même résolution, aucune démo d'upscaling visuel dans cette figure.
- **Dimensions effectives (vérifiées `PIL.Image.open` 2026-07-22)** : 503×1200 max-dim 1200 vs 320×240 source authentique par vignette = ratio d'aspect 1.33 (4:3 standard).
- **Poids** : 140.9 KB (downscale max-dim 1200)
- **SHA256** : `e36fe35f07e8cb23fd42d5f7f5f6c24b3b0cc4ce896b26fbc272e83e63f300a0`
- **Contenu réel vérifié (lecture `Read` 2026-07-14)** : figure 2 lignes × 4 colonnes intitulée **« Reference HR vs Input LR »**. Rangée haute = HR (High Resolution, 320×240, nette), rangée basse = LR (Low Resolution, 320×240, déjà dégradée en soft/blur). 4 frames numérotées 1/36, 13/36, 25/36, 36/36. Balle rouge + 4 billes vertes alignées en haut, sur fond noir quadrillé. **Les deux versions ont la même résolution 320×240** : ce n'est PAS un upscaling visuel HR→LR démontré dans l'image, mais une **comparaison qualité HR vs LR à résolution identique**.
- **Note** : ancien alt-text « Upscaling ESRGAN : comparaison basse résolution avant/après agrandissement par réseau » — **REFONDU** car il sous-entendait un upscaling HR→LR visuel qui n'est PAS présent dans l'image. L'effet upscaling ESRGAN n'est pas démontré visuellement dans cette figure ; pour la démo effective d'upscaling, voir le notebook `01-4` directement. **Précision transférable** : la figure est un **dispositif d'entrée** (HR/LR appariées comme ground truth/input pour le réseau ESRGAN), pas une **mesure de sortie** (l'output ESRGAN upscalé apparaît ailleurs dans le notebook).

## video5-animatediff.png

- **Source** : notebook `01-Foundation/01-5-AnimateDiff-Introduction.ipynb` (cellule 10, output 3 — display_data `image/png`, 2 152 764 B source authentique, 195.7 KB downscale agressive max-dim 500)
- **Description visuelle** : Grille 2 lignes × 4 colonnes (252×500 max-dim 500, compression agressive) sur fond uni. **8 vignettes successives d'un paysage lacustre au coucher de soleil**, montagnes se reflétant dans l'eau, lumière dorée chaude, nuages orangés. Frame labels superposés `Frame 1/24`, `Frame 2/24`, ..., `Frame 8/24` (1 frame par vignette, 8 vignettes sur les 24 totales, extraction tous les 3 frames). **Prompt injecté visible** dans le titre central `AnimateDiff - a serene lake at sunset with mountains in the background, g...` (tronqué par la largeur d'image). Cohérence visuelle forte entre les 8 frames : la scène illustre une continuité temporelle typique d'une génération text-to-video AnimateDiff.
- **Alt-text (FR)** : Génération AnimateDiff text-to-video depuis prompt « a serene lake at sunset with mountains in the background » — grille 2×4 frames d'un paysage lacustre au coucher de soleil (montagnes + lac reflétant, lumière dorée).
- **Dimensions effectives (vérifiées `PIL.Image.open` 2026-07-22)** : 252×500 max-dim 500 (downscale agressive, ratio disque/source = 0.09×) — politique #5654 tolère ce type de compression pour les frames de génération (taille source 2.15 MB → 195.7 KB).
- **Poids** : 195.7 KB (downscale max-dim 500, compression agressive)
- **SHA256** : `46d785f25a99ba6f131691d770cffa184877763ceebc273d0e3e5dc7b705b2bf`
- **Contenu réel vérifié (lecture `Read` 2026-07-14)** : grille **2×4 frames** successives d'un paysage lacustre au coucher de soleil (montagnes + lac reflétant, lumière dorée chaude, nuages orangés). Frame 1/24 à 8/24 (1 par ligne, ~1/24s). **Prompt injecté visible** en haut (« AnimateDiff - a serene lake at sunset with mountains in the background, g... » — tronqué par la largeur de l'image).
- **Note** : ancien alt-text « Génération text-to-video AnimateDiff : animation produite depuis un prompt textuel » — **enrichi** avec le prompt concret visible et la description factuelle du paysage lacustre.

## video-svd.png

- **Source** : notebook `02-Advanced/02-4-SVD-Image-to-Video.ipynb` (cellule 9, output 1 — display_data `image/png`, 18 333 B)
- **Description visuelle** : Figure **3 vignettes côte-à-côte** (250×1200) avec **titre gras central** `Images de test pour SVD`. Les 3 vignettes servent d'**inputs** (images statiques) pour Stable Video Diffusion : **gauche** `Paysage avec montagnes` — ciel bleu, sol vert, montagne grise, soleil jaune (cercle) en haut à droite ; **centre** `Silhouette portrait` — silhouette beige (tête) sur fond violet, torse bleu, forme humanoïde stylisée ; **droite** `Coucher de soleil sur l'eau` — dégradé rose-orange en haut, eau bleue en bas, soleil jaune (cercle) au centre. **Ce sont les données d'entrée fournies à SVD, PAS une sortie SVD générée.** Cohérence stylistique : les 3 vignettes adoptent un **style minimaliste plat** (3-5 couleurs par vignette, formes géométriques simples) cohérent avec un dataset de test synthétique. Tell structurel = **3 inputs juxtaposes pour démo image-to-video**.
- **Alt-text (FR)** : « Images de test pour SVD » — 3 vignettes côte-à-côte servant d'inputs pour Stable Video Diffusion (Paysage avec montagnes / Silhouette portrait / Coucher de soleil sur l'eau), pas une sortie SVD.
- **Dimensions effectives (vérifiées `PIL.Image.open` 2026-07-22)** : 250×1200 (3 vignettes côte-à-côte, ratio d'aspect 4.8:1) — embeddings inline au README narratif.
- **Poids** : 25.0 KB (downscale max-dim 1200)
- **SHA256** : `eaf6b5683529c895566a74fa5550e7c60335867c797eba550b908a27bff7789d`
- **Contenu réel vérifié (lecture `Read` 2026-07-14)** : figure **3 vignettes côte-à-côte** intitulée **« Images de test pour SVD »** (titre en gras). 3 images statiques servant d'**inputs** pour Stable Video Diffusion : « Paysage avec montagnes » (ciel bleu, sol vert, soleil jaune en haut à droite) / « Silhouette portrait » (silhouette beige sur fond violet, torse bleu) / « Coucher de soleil sur l'eau » (dégradé rose-orange sur eau bleue, soleil jaune). **Ce sont les données d'entrée fournies à SVD, PAS une sortie SVD générée**.
- **Note** : ancien alt-text « Stable Video Diffusion : animation d'une image statique en séquence vidéo » — **REFONDU** : l'image montre les INPUTS (3 vignettes sources statiques), pas une sortie SVD générée. Le titre explicite « Images de test pour SVD » confirme cette interprétation. **Précision transférable** : la figure documente le **dataset de test synthétique** construit pour la démo, pas le modèle lui-même — la sortie SVD apparaît ailleurs dans le notebook `02-4`.

## video-creative-style.png

- **Source** : notebook `04-Applications/04-2-Creative-Video-Workflows.ipynb` (cellule 7, output 1 — display_data `image/png`, 43 947 B)
- **Description visuelle** : Mosaique **4 lignes × 3 colonnes** (1135×1200 max-dim 1200) avec **titre gras central** `Comparaison des styles artistiques`. **4 styles** appliqués en lignes : `Original` (frame 0/48/96), `Peinture à l'huile`, `Aquarelle`, `Dessin`. **3 frames temporelles** en colonnes : frame 0, frame 48, frame 96. Scène de base : **carré cyan + cercle jaune** sur fond dégradé. **Variations par style** : Original = mosaique bleu-violet-orange avec carré cyan translucide et cercle jaune plein ; Peinture à l'huile = versions aux couleurs plus sourdes (bleu-violet-gris-vert olive) et verts-jaunes pastels ; Aquarelle = couleurs vives proches de l'original (légèrement translucides) ; Dessin = contours noirs sur fond blanc (line-art, sans remplissage couleur). Tell discriminant = **la rangée Dessin (row 4) = blanchâtre high-key** tandis que les 3 autres rangées = colorées mid-saturation.
- **Alt-text (FR)** : Comparaison côte-à-côte de 4 styles artistiques (Original / Peinture à l'huile / Aquarelle / Dessin) appliqués à 3 frames (t=0/48/96), mosaique 4×3 d'une scène avec carré cyan + cercle jaune sur fond dégradé.
- **Dimensions effectives (vérifiées `PIL.Image.open` 2026-07-22)** : 1135×1200 max-dim 1200 (presque pas de downscale). 4×3 = 12 vignettes sur fond blanc dominant (45.6% blanc pur — tell contrasté `multi-color + blanc`).
- **Poids** : 71.3 KB (downscale max-dim 1200)
- **SHA256** : `0aa562ca0654fbff9f383d552b99298b89499d6c2a922564fb78359599daccb1`
- **Contenu réel vérifié (lecture `Read` 2026-07-14)** : mosaique **4 lignes × 3 colonnes** intitulée **« Comparaison des styles artistiques »**. 4 styles (Original / Peinture à l'huile / Aquarelle / Dessin) appliqués à 3 frames (0 / 48 / 96). Style Original = mosaique dégradée bleu-violet-orange + carré cyan + cercle jaune. Peinture à l'huile = versions aux couleurs plus sourdes/vertes. Aquarelle = couleurs vives proches de l'original. Dessin = contours noirs sur fond blanc (style line-art). Pas d'image de référence unique apparente — c'est un **comparatif multi-styles** sur une scène de base.
- **Note** : ancien alt-text « Transfert de style vidéo : application du style d'une image de référence à chaque frame » — **REFONDU** car il sous-entendait une seule image de référence, alors que la figure montre un **comparatif multi-styles** (4 styles, pas 1 référence). Le titre explicite « Comparaison des styles artistiques » confirme cette lecture. **Précision transférable** : la scène de base (carré cyan + cercle jaune) sert de **substrat** pour appliquer successivement 4 styles, ce qui illustre la **factorisation contenu/style** d'un pipeline de transfert de style vidéo.

## video-sora-cost.png

- **Source** : notebook `04-Applications/04-3-Sora-API-Cloud-Video.ipynb` (cellule 17, output 0 — display_data `image/png`, 55 058 B source authentique, 79.5 KB après export policy)
- **Description visuelle** : Figure **2 panneaux côte-à-côte** (427×1200 max-dim 1200) avec **titre gras central** `Analyse comparative : Sora API vs Generation Video Locale`. Tell dominant = **matplotlib-blanc** (mean (231.5, 229.4, 232.1), 79.1% blanc pur — seaborn-darkgrid-like fond blanc dominant cohérent avec `plt.subplots()` sans `sns.set_theme()`). **Panneau gauche** `Coût mensuel : Cloud vs Local` — lineplot : courbe **bleue pleine `Sora (cloud)`** linéaire de 0 → 250 $/mois sur l'axe X (0-1000 vidéos par mois), **ligne rouge pointillée `GPU local`** constante à ~95 $/mois, **ligne verticale grise pointillée `Seuil ~375 vid/mois`** marquant le point de rentabilité (intersection Sora=Local). Légende coin haut-gauche. **Panneau droite** `Comparaison qualitative` — barplot groupé sur 5 critères (`Qualité / Cohérence temporelle / Durée max / Latence / Facilité setup`), chaque critère avec 2 barres (`Sora` bleu, `Local (best)` orange), échelle y 0-10. **Sora domine sur 4 critères** (Qualité 9 vs 7, Cohérence 9 vs 6, Durée max 9 vs 5, Latence 7 vs 5) ; **Local l'emporte uniquement sur Facilité setup** (10 vs 4). Tell discriminant `matplotlib-blanc L778-L2` cohérent avec figure politique/comparative sur fond clair.
- **Alt-text (FR)** : « Analyse comparative : Sora API vs Generation Video Locale » — 2 panneaux (coût mensuel Cloud vs Local avec seuil rentabilité ~375 vid/mois, comparatif qualitatif sur 5 critères : Qualité, Cohérence temporelle, Durée max, Latence, Facilité setup).
- **Dimensions effectives (vérifiées `PIL.Image.open` 2026-07-22)** : 427×1200 max-dim 1200 (presque pas de downscale), ratio d'aspect 2.8:1 typique d'un layout `plt.subplots(1, 2)`.
- **Poids** : 79.5 KB (downscale max-dim 1200)
- **SHA256** : `2fba67cb1e30b02553bd8c5072b3761e8a22fca488eebdd315a9e00c29f75b92`
- **Contenu réel vérifié (lecture `Read` 2026-07-14)** : figure **2 panneaux** intitulée **« Analyse comparative : Sora API vs Generation Video Locale »**. Panneau gauche = « Coût mensuel : Cloud vs Local » (lineplot : Sora en bleu linéaire 0→250$/mois, GPU Local en rouge pointillé constant ~95$/mois, seuil rentabilité à 375 vid/mois marqué en gris pointillé). Panneau droite = « Comparaison qualitative » (barplot groupé sur 5 critères : Qualité / Cohérence temporelle / Durée max / Latence / Facilité setup ; Sora en bleu, Local best en orange ; Sora gagne partout sauf Facilité setup où Sora 10 vs Local 4).
- **Note** : ancien alt-text « Sora (cloud) vs local : comparaison de coût selon le volume de génération vidéo » — **enrichi** pour mentionner le **second panneau qualitatif** (5 critères) qui était absent de l'ancien alt-text. Coût ET qualité sont comparés. **Précision transférable** : le seuil rentabilité ~375 vid/mois est atteint quand Sora (0.25 $/vidéo linéaire) = Local (~95 $/mois GPU) → c'est le **break-even financier** d'un déploiement local-first basculement cloud au-delà.

---

## Vérification G.1 — provenance investigation (préservée byte-identity)

Investigation `nbformat` Python pour identifier les cellules sources et valider les attributions :

| Fichier | Cell | Out | MD5 cell output | Taille cell | Taille disque | Ratio |
|---|---|---|---|---|---|---|
| `video1-frames.png` | 16 | 2 | `e74fba32` | 72 143 B | 66.3 KB | 0.92× |
| `video4-esrgan.png` | 8 | 3 | `7f26170f` | 102 146 B | 140.9 KB | 1.38× |
| `video5-animatediff.png` | 10 | 3 | `0b991213` | 2.15 MB | 195.7 KB | 0.09× (max-dim 500, compression agressive) |
| `video-svd.png` | 9 | 1 | `0fd5203d` | 18 332 B | 25.0 KB | 1.36× |
| `video-creative-style.png` | 7 | 1 | `3b67d71c` | 43 947 B | 71.3 KB | 1.62× |
| `video-sora-cost.png` | 17 | 0 | `b012c4d0` | 55 058 B | 79.5 KB | 1.44× |

**MD5 cell output ≠ MD5 disque** (chaîne d'extraction → compression PNG max-dim 1200 = artefacts différents), mais **tailles relatives cohérentes** avec chaîne d'extraction : ratios source→disk 0.09× à 1.62× selon downscale/upscale appliqué par figure. Toutes les attributions cell[X]/out[Y] confirmées.

**SHA256 unique par fichier sur disque** (ré-vérifié 2026-07-22 c.753, MATCH vs c.486) :
- `2d2c48d7fad7a5ae19b25d9f6aa39ad4ebb98de45d118eed32fee02fd51a81aa` (video1)
- `e36fe35f07e8cb23fd42d5f7f5f6c24b3b0cc4ce896b26fbc272e83e63f300a0` (video4)
- `46d785f25a99ba6f131691d770cffa184877763ceebc273d0e3e5dc7b705b2bf` (video5)
- `eaf6b5683529c895566a74fa5550e7c60335867c797eba550b908a27bff7789d` (svd)
- `0aa562ca0654fbff9f383d552b99298b89499d6c2a922564fb78359599daccb1` (creative)
- `2fba67cb1e30b02553bd8c5072b3761e8a22fca488eebdd315a9e00c29f75b92` (sora-cost)

---

## Bilan audit c.486 — 18ᵉ pilote rollout #5780 (préservé byte-identity)

| Fichier | Verdict | Action |
|---|---|---|
| `video1-frames.png` | MISMATCH sous-spécifique | ENRICHI alt-text (motif balle bondissante + fonds colorés) |
| `video4-esrgan.png` | MISMATCH MAJEUR (faux sens) | REFONTE alt-text (HR vs LR à résolution identique, pas d'upscaling visuel) |
| `video5-animatediff.png` | MISMATCH générique | ENRICHI alt-text (paysage lacustre concret + prompt visible) |
| `video-svd.png` | MISMATCH MAJEUR (faux sens) | REFONTE alt-text (inputs SVD, pas sortie générée) |
| `video-creative-style.png` | MISMATCH (faux sens) | REFONTE alt-text (comparatif multi-styles, pas image de référence unique) |
| `video-sora-cost.png` | MISMATCH sous-spécifique | ENRICHI alt-text (2 panneaux coût + qualité) |

**Bilan** : 0/6 ACCURATE mature + 6/6 corrections réelles (3 refontes + 3 enrichissements). **0 figure DROP** — les 6 fichiers restent sur disque.

**Conformité règles** :
- §A single-subject : 1 dossier, 2 fichiers (`README.md` + `MANIFEST.md`), 1 sujet.
- R1 catalog-pr-hygiene : catalogue byte-identique à main (aucun `CATALOG-STATUS` ni `COURSE_CATALOG.*` touché).
- L268 LF-only : 0 retour chariot (`\r`) dans le diff.
- L143 secrets-hygiene : 0 secret inline dans le diff.
- C.3 strict : aucune ré-exécution Papermill, aucune cellule notebook touchée.
- c.187 atomic : 1 commit unique.
- c.281-L1 MD047 : trailing newline MAINTAINED.
- L529 STRICT markdown-only : aucun PNG/CSV/JSONL modifié, seulement `MANIFEST.md`.
- detect_manifest_field.py : exit 0, 6/6 figures déclarent `Description visuelle` (PR #7819 c.754).
- G.1 firsthand : vision-QA MiniMax M3 + `nbformat` cellule source authentique.
- G-VAR-3 ✓ : c.752 MED/env-repair Probas (PR #8008 OPEN) → c.753 MED/docs-hygiene GenAI/Video racine = cross-famille pivot (Probas ≠ GenAI/Video).
- SOTA-OK : pas de workaround dégradé, juste reformatage canonique (vague-1 → canonical `## filename.png` + `**Description visuelle** :`).

**🔁 Doublons intentionnels inter-arborescences (audit c.657, doctrine #5780, miroir de la note du MANIFEST 01-Foundation)** :
Deux des figures de cette racine sont des **doublons exacts** (SHA1 identique) avec le dossier `01-Foundation/assets/readme/` :
| Figure racine | Figure locale | SHA1 (vérifié 2026-07-19) | Statut doctrine #5780 |
|---------------|---------------|---------------------------|------------------------|
| `video4-esrgan.png` (racine Video) | `vid1-esrgan.png` (01-Foundation) | `620f78d33b723f8a1ddf4cf54eed79e308a66945` (byte-identique) | **Doublon intentionnel** : racine Video README illustre la figure dans le contexte narratif multi-modèles ; 01-Foundation README l'illustre dans le contexte pédagogique « Enhancement ESRGAN ». Alt-texts différents mais même binaire, doctrine #5780. |
| `video5-animatediff.png` (racine Video) | `vid1-animatediff.png` (01-Foundation) | `579190cc435421941a730c423a4442730074b46f` (byte-identique) | **Doublon intentionnel** même logique : racine illustre AnimateDiff dans le contexte orchestration, 01-Foundation l'illustre dans le contexte introduction. |

**Note de fond** : voir la note miroir dans [01-Foundation/assets/readme/MANIFEST.md](../../01-Foundation/assets/readme/MANIFEST.md). Doctrine #5780 produit mécaniquement des doublons quand un notebook est référencé à la fois dans la racine de la famille et dans une sous-série — c'est by design.

**Voir aussi** : [c.481 GenAI/Image racine](../../../Image/assets/readme/MANIFEST.md) — pattern frère (audit fondateur racine GenAI) ; [c.485 GenAI/Video/04-Applications](../../04-Applications/assets/readme/MANIFEST.md) — pattern frère (audit fondateur tardif post-transition #6157) ; issue [#5780](../../../../../issues/5780) ; EPIC [#5654](../../../../../issues/5654).
