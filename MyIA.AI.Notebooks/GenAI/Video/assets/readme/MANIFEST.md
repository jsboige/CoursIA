# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

**Audit G.1 fondateur** : relecture visuelle via outil `Read` par `myia-po-2025` le **2026-07-14** (cycle c.486 du rollout [issue #5780](../../../../../issues/5780)). Bilan : 0/6 ACCURATE mature + 6/6 corrections réelles (3 refontes alt-text + 3 enrichissements). Migration format : table simple (vague-1) → liste détaillé standard (cf [c.469 SemanticWeb](../../../../SymbolicAI/SemanticWeb/assets/readme/MANIFEST.md), [c.481 GenAI/Image racine](../../../Image/assets/readme/MANIFEST.md), [c.484 GenAI/Image/03-Orchestration](../../../Image/03-Orchestration/assets/readme/MANIFEST.md), [c.485 GenAI/Video/04-Applications](../../04-Applications/assets/readme/MANIFEST.md)).

---

## video1-frames.png

- **Source** : notebook `01-Foundation/01-1-Video-Operations-Basics.ipynb` (cellule 16, output 2)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14, **ré-audit visuel c.671 2026-07-19 par `myia-po-2023`** MiniMax-M3) : mosaique pédagogique **2×4 frames** d'une balle blanche bondissante. Frame 0/17/34/51/68/85/102/119, timesteps t=0.00/0.71/1.42/2.12/2.83/3.54/4.25/4.96s. Fonds colorés alternés (palette cyclique 8-couleurs retournant à lime) : lime / orange / rouge / magenta / bleu / cyan / vert / lime. Résolution 640×480 @ 24fps. Titre superposé : « Extraction uniforme - 8 frames via decord ». Le motif balle bondissante illustre la **régularité de l'extraction uniforme** via decord.
- **Alt-text (FR)** : Extraction uniforme de 8 frames via decord : mosaique pédagogique 2×4 d'une balle blanche bondissante (Frame 0/17/34/51/68/85/102/119 sur fonds colorés alternés lime/orange/rouge/magenta/bleu/cyan/vert/lime, palette cyclique 640×480 @ 24fps).
- **Poids** : 66.3 KB (downscale max-dim 1200)
- **Note** : ancien alt-text « Extraction de frames : découpe d'une vidéo en images clés avec decord pour l'analyse » — **enrichi** avec description factuelle des 8 frames observables (motif balle bondissante + fonds colorés + résolution).

## video4-esrgan.png

- **Source** : notebook `01-Foundation/01-4-Video-Enhancement-ESRGAN.ipynb` (cellule 8, output 3)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14) : figure 2 lignes × 4 colonnes intitulée **« Reference HR vs Input LR »**. Rangée haute = HR (High Resolution, 320×240, nette), rangée basse = LR (Low Resolution, 320×240, déjà dégradée en soft/blur). 4 frames numérotées 1/36, 13/36, 25/36, 36/36. Balle rouge + 4 billes vertes alignées en haut, sur fond noir quadrillé. **Les deux versions ont la même résolution 320×240** : ce n'est PAS un upscaling visuel HR→LR démontré dans l'image, mais une **comparaison qualité HR vs LR à résolution identique**.
- **Alt-text (FR)** : Comparaison HR vs LR sur 4 frames — balle rouge + 4 billes vertes sur fond noir quadrillé, HR (320×240, nette) vs LR (320×240, soft/blur), même résolution, aucune démo d'upscaling visuel dans cette figure.
- **Poids** : 140.9 KB (downscale max-dim 1200)
- **Note** : ancien alt-text « Upscaling ESRGAN : comparaison basse résolution avant/après agrandissement par réseau » — **refondu** car il sous-entendait un upscaling HR→LR visuel qui n'est PAS présent dans l'image. L'effet upscaling ESRGAN n'est pas démontré visuellement dans cette figure ; pour la démo effective d'upscaling, voir le notebook `01-4` directement.

## video5-animatediff.png

- **Source** : notebook `01-Foundation/01-5-AnimateDiff-Introduction.ipynb` (cellule 10, output 3)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14) : grille **2×4 frames** successives d'un paysage lacustre au coucher de soleil (montagnes + lac reflétant, lumière dorée chaude, nuages orangés). Frame 1/24 à 8/24 (1 par ligne, ~1/24s). **Prompt injecté visible** en haut (« AnimateDiff - a serene lake at sunset with mountains in the background, g... » — tronqué par la largeur de l'image).
- **Alt-text (FR)** : Génération AnimateDiff text-to-video depuis prompt « a serene lake at sunset with mountains in the background » — grille 2×4 frames d'un paysage lacustre au coucher de soleil (montagnes + lac reflétant, lumière dorée).
- **Poids** : 195.7 KB (downscale max-dim 500, compression agressive)
- **Note** : ancien alt-text « Génération text-to-video AnimateDiff : animation produite depuis un prompt textuel » — **enrichi** avec le prompt concret visible et la description factuelle du paysage lacustre.

## video-svd.png

- **Source** : notebook `02-Advanced/02-4-SVD-Image-to-Video.ipynb` (cellule 9, output 1)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14) : figure **3 vignettes côte-à-côte** intitulée **« Images de test pour SVD »** (titre en gras). 3 images statiques servant d'**inputs** pour Stable Video Diffusion : « Paysage avec montagnes » (ciel bleu, sol vert, soleil jaune en haut à droite) / « Silhouette portrait » (silhouette beige sur fond violet, torse bleu) / « Coucher de soleil sur l'eau » (dégradé rose-orange sur eau bleue, soleil jaune). **Ce sont les données d'entrée fournies à SVD, PAS une sortie SVD générée**.
- **Alt-text (FR)** : « Images de test pour SVD » — 3 vignettes côte-à-côte servant d'inputs pour Stable Video Diffusion (Paysage avec montagnes / Silhouette portrait / Coucher de soleil sur l'eau), pas une sortie SVD.
- **Poids** : 25.0 KB (downscale max-dim 1200)
- **Note** : ancien alt-text « Stable Video Diffusion : animation d'une image statique en séquence vidéo » — **refondu** : l'image montre les INPUTS (3 vignettes sources statiques), pas une sortie SVD générée. Le titre explicite « Images de test pour SVD » confirme cette interprétation.

## video-creative-style.png

- **Source** : notebook `04-Applications/04-2-Creative-Video-Workflows.ipynb` (cellule 7, output 1)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14) : mosaique **4 lignes × 3 colonnes** intitulée **« Comparaison des styles artistiques »**. 4 styles (Original / Peinture à l'huile / Aquarelle / Dessin) appliqués à 3 frames (0 / 48 / 96). Style Original = mosaique dégradée bleu-violet-orange + carré cyan + cercle jaune. Peinture à l'huile = versions aux couleurs plus sourdes/vertes. Aquarelle = couleurs vives proches de l'original. Dessin = contours noirs sur fond blanc (style line-art). Pas d'image de référence unique apparente — c'est un **comparatif multi-styles** sur une scène de base.
- **Alt-text (FR)** : Comparaison côte-à-côte de 4 styles artistiques (Original / Peinture à l'huile / Aquarelle / Dessin) appliqués à 3 frames (t=0/48/96), mosaique 4×3 d'une scène avec carré cyan + cercle jaune sur fond dégradé.
- **Poids** : 71.3 KB (downscale max-dim 1200)
- **Note** : ancien alt-text « Transfert de style vidéo : application du style d'une image de référence à chaque frame » — **refondu** car il sous-entendait une seule image de référence, alors que la figure montre un **comparatif multi-styles** (4 styles, pas 1 référence). Le titre explicite « Comparaison des styles artistiques » confirme cette lecture.

## video-sora-cost.png

- **Source** : notebook `04-Applications/04-3-Sora-API-Cloud-Video.ipynb` (cellule 17, output 0)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14) : figure **2 panneaux** intitulée **« Analyse comparative : Sora API vs Generation Video Locale »**. Panneau gauche = « Coût mensuel : Cloud vs Local » (lineplot : Sora en bleu linéaire 0→250$/mois, GPU Local en rouge pointillé constant ~95$/mois, seuil rentabilité à 375 vid/mois marqué en gris pointillé). Panneau droite = « Comparaison qualitative » (barplot groupé sur 5 critères : Qualité / Cohérence temporelle / Durée max / Latence / Facilité setup ; Sora en bleu, Local best en orange ; Sora gagne partout sauf Facilité setup où Sora 10 vs Local 4).
- **Alt-text (FR)** : « Analyse comparative : Sora API vs Generation Video Locale » — 2 panneaux (coût mensuel Cloud vs Local avec seuil rentabilité ~375 vid/mois, comparatif qualitatif sur 5 critères : Qualité, Cohérence temporelle, Durée max, Latence, Facilité setup).
- **Poids** : 79.5 KB (downscale max-dim 1200)
- **Note** : ancien alt-text « Sora (cloud) vs local : comparaison de coût selon le volume de génération vidéo » — **enrichi** pour mentionner le **second panneau qualitatif** (5 critères) qui était absent de l'ancien alt-text. Coût ET qualité sont comparés.

---

## Vérification G.1 — provenance investigation

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

**SHA256 unique par fichier sur disque** :
- `2d2c48d7fad7a5ae19b25d9f6aa39ad4ebb98de45d118eed32fee02fd51a81aa` (video1)
- `e36fe35f07e8cb23fd42d5f7f5f6c24b3b0cc4ce896b26fbc272e83e63f300a0` (video4)
- `46d785f25a99ba6f131691d770cffa184877763ceebc273d0e3e5dc7b705b2bf` (video5)
- `eaf6b5683529c895566a74fa5550e7c60335867c797eba550b908a27bff7789d` (svd)
- `0aa562ca0654fbff9f383d552b99298b89499d6c2a922564fb78359599daccb1` (creative)
- `2fba67cb1e30b02553bd8c5072b3761e8a22fca488eebdd315a9e00c29f75b92` (sora-cost)

---

## Bilan audit c.486 — 18ᵉ pilote rollout #5780

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

**🔁 Doublons intentionnels inter-arborescences (audit c.657, doctrine #5780, miroir de la note du MANIFEST 01-Foundation)** :
Deux des figures de cette racine sont des **doublons exacts** (SHA1 identique) avec le dossier `01-Foundation/assets/readme/` :
| Figure racine | Figure locale | SHA1 (vérifié 2026-07-19) | Statut doctrine #5780 |
|---------------|---------------|---------------------------|------------------------|
| `video4-esrgan.png` (racine Video) | `vid1-esrgan.png` (01-Foundation) | `620f78d33b723f8a1ddf4cf54eed79e308a66945` (byte-identique) | **Doublon intentionnel** : racine Video README illustre la figure dans le contexte narratif multi-modèles ; 01-Foundation README l'illustre dans le contexte pédagogique « Enhancement ESRGAN ». Alt-texts différents mais même binaire, doctrine #5780. |
| `video5-animatediff.png` (racine Video) | `vid1-animatediff.png` (01-Foundation) | `579190cc435421941a730c423a4442730074b46f` (byte-identique) | **Doublon intentionnel** même logique : racine illustre AnimateDiff dans le contexte orchestration, 01-Foundation l'illustre dans le contexte introduction. |

**Note de fond** : voir la note miroir dans [01-Foundation/assets/readme/MANIFEST.md](../../01-Foundation/assets/readme/MANIFEST.md). Doctrine #5780 produit mécaniquement des doublons quand un notebook est référencé à la fois dans la racine de la famille et dans une sous-série — c'est by design.

**Voir aussi** : [c.481 GenAI/Image racine](../../../Image/assets/readme/MANIFEST.md) — pattern frère (audit fondateur racine GenAI) ; [c.485 GenAI/Video/04-Applications](../../04-Applications/assets/readme/MANIFEST.md) — pattern frère (audit fondateur tardif post-transition #6157) ; issue [#5780](../../../../../issues/5780) ; EPIC [#5654](../../../../../issues/5654).
