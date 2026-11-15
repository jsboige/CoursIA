# Manifeste des figures — GenAI/Video/04-Applications (cas d'usage production)

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks). Les indices de cellule et de sortie commencent à 0 et comptent toutes les cellules.

> **Audit vision po-2025 c.485 (2026-07-14, doctrine #5780)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` et leur contenu réel confronté à leur description existante. **Bilan G.1 firsthand : 6/6 alt-texts sur-vendeurs / faux sens majeur — 0 figure ACCURATE mature**. Le dossier GenAI/Video/04-Applications **n'avait pas reçu d'audit G.1 préalable** (contrairement à GenAI/Video/01-Foundation c.351 po-2023) — c'est donc un audit fondateur tardif pour ce sous-dossier. **Migration format vague-1 → liste détaillé standard** (sections Contenu réel vérifié / Alt-text (FR) / Poids / Note) appliquée pour aligner avec le standard rollout #5780. **6/6 corrections réelles** :
> 1. `vid4-educational.png` : alt-text sur-vendeur (« aperçu des frames ») → refait pour préciser le **contenu visible** = panorama des 4 premiers slides « Introduction au Machine Learning » (Slide 1: « Introduction au Machine Learning — Concepts fondamentaux et applications » ; Slide 2: « Qu'est-ce que le Machine Learning ? — Apprentissage à partir de données, Amélioration avec l'expérience, Généralisation à de nouveaux cas, Alternative à la programmation explicite » ; Slide 3: « Types d'apprentissage — Supervisé (données étiquetées: classification, régression), Non supervisé (découverte de structures), Par renforcement (apprentissage par essai-erreur) » ; Slide 4: « Pipeline typique ML — Collecte et préparation, Sélection et entraînement du modèle, Évaluation des performances, Déploiement et monitoring »). **Ce sont des SLIDES de présentation pédagogique, pas des frames vidéo.**
> 2. `vid4-creative.png` : alt-text sur-vendeur (« séquence créative ») → refait = grille 2×3 « Effets synchronisés sur beats (120 BPM) » avec 3 battements (Original beat 1/2/3 × frame 0/12/24 en haut ; Avec effet en bas), comparant un carré cyan + cercle orange en mouvement sur fond dégradé bleu/violet → rose. **C'est une synchro audio-reactive pédagogique, pas une vidéo créative libre.**
> 3. `vid4-creative2.png` : alt-text sous-spécifique (« variante de composition ») → refait = collage vidéo 2×2 « Original / Aquarelle / Dessin / Teal & Orange » à 3 timestamps t=0/3/6s — comparaison de **4 styles visuels** appliqués au même contenu sur 3 instants.
> 4. `vid4-sora.png` : alt-text partiellement correct mais ambigu → précisez le contenu réel = grille 2×4 « Generation Text → Video (Sora API) » sur deux thèmes Nature/Urbain à 4 timesteps t=0.0/1.6/3.3/5.0s, avec soleil stylisé jaune + horizon herbe vert dégradé, filigrane « Sora API - Simulation » en bas (sphère-monde + Simulation) **et** prompt injecté en gras en haut de chaque frame (« Prompt: A realistic mountain lake at sunset, reflecting sky » / « Prompt: A busy Tokyo street at night, neon signs reflecting »).
> 5. `vid4-sora2.png` : alt-text cite « Sora » mais le contenu réel = **« Image → Video (effet Ken Burns) »** = 5 frames t=0/1.6/3.3/5.0s avec zoom progressif sur image source (soleil + collines + horizon). C'est **un effet Ken Burns, pas une simulation Sora** — correction MISMATCH.
> 6. `vid4-pipeline.png` : alt-text sur-vendeur (« Pipeline production — orchestration ») → refait = « Images des scènes du pipeline » = 5 scènes « Introduction / Origines historiques / Fonctionnement / Applications / Perspectives », chacune avec fond coloré distinct (bleu/marron/vert/violet/bleu nuit) et constellation de bulles + constellation filaire. C'est **un storytelling slide par slide, pas une orchestration production**.

Toutes les attributions cell[X]/out[Y] sont **validées par ratio** (downscaling 1589→1200 ≈ 1.32, sauf fig creative.png 1240→1200 ≈ 1.03 car source déjà rès-petite).

> **Migration canonical c.763 (2026-07-22, jsboige:CoursIA-2)** : ajout du champ **`Description visuelle`** (gist compact de ce qui est *visible* en un coup d'œil, distinct du `Contenu réel vérifié` détaillé et du `Alt-text (FR)` accessibilité). Format aligné sur c.751 (GenAI/Audio) + modèle rollout #5780. 6/6 figures migrées, audit vision MiniMax M3 firsthand + PIL RGB mean+std à 80×80 (cf. PR body). **Audit fondateur c.485 préservé verbatim** ci-dessus ; cette migration est purement additive (pas de suppression de contenu).

> **Ré-alignement #24395 (2026-11-07, myia-po-2023:CoursIA)** : doctrine — une figure README n'existe qu'avec une **provenance committée** (extraction d'outputs de notebooks, EPIC #5654 source 1). Deux gestes :
> - **Remplacement** de `vid4-creative.png` : l'ancienne version (grille « 120 BPM », cellule 9 d'époque) ne correspondait plus à la sortie committée courante du notebook 04-2, qui détecte le **vrai tempo** du morceau. Nouvelle source (pérenne, ancrée par titre de sortie) : « Effets synchronises sur les beats DETECTES (vrai tempo 96 BPM) » — cellule 11 à l'extraction du 07/11 ; texte compagnon committé : « Periode vraie 0.625 s (96 BPM) vs 0.500 s (temoin 120) ». PNG 1200×576 (downscalé depuis 1235×593), 55 Ko.
> - **Retrait** de `vid4-sora.png`, `vid4-sora2.png` (notebook 04-3) et `vid4-pipeline.png` (notebook 04-4) : aucune sortie committée de ces notebooks ne correspond plus à ces figures. L'issue #24395 autorise explicitement le retrait pour les figures sans provenance committée ; tombstones ci-dessous, historique descriptif complet dans git.
>
> L'audit fondateur c.485 et la migration c.763 ci-dessus restent valables **pour les figures d'époque** (historique git) ; les sections ci-dessous décrivent l'état courant.

## vid4-educational.png

- **Source** : notebook `04-1-Educational-Video-Generation.ipynb` (cellule 11, output 2) — génération automatique de slides pédagogiques à partir d'un script textuel
- **Description visuelle** : Quatre rectangles bleu nuit côte-à-côte sous le titre noir gras « Apercu des premiers slides ». Slide 1 met en valeur son titre « Introduction au Machine Learning » dans un bandeau bleu plus clair (le seul slide avec emphase visuelle). Slides 2/3/4 portent respectivement 4/3/4 puces textuelles alignées à gauche sur fond uniforme. Palette dominante bleu nuit (RGB 80×80 mean ≈ 117/124/150, variance modérée), texte blanc. Densité d'information textuelle croissante gauche→droite (slide 1 = quasi-vierge avec titre/sous-titre uniquement, slide 4 = 4 étapes pipeline remplies).
- **Contenu réel vérifié** : PNG 1200×252, panorama horizontal de **4 slides successifs** sous le titre « Apercu des premiers slides » :
  - **Slide 1** : fond bleu nuit, titre « Introduction au Machine Learning », sous-titre « Concepts fondamentaux et applications ».
  - **Slide 2** : fond bleu nuit, titre « Qu'est-ce que le Machine Learning ? », 4 bullet points (Apprentissage à partir de données, Amélioration avec l'expérience, Généralisation à de nouveaux cas, Alternative à la programmation explicite).
  - **Slide 3** : fond bleu nuit, titre « Types d'apprentissage », 3 bullet points sur Supervisé / Non supervisé / Par renforcement.
  - **Slide 4** : fond bleu nuit, titre « Pipeline typique ML », 4 étapes (Collecte et préparation, Sélection et entraînement, Évaluation, Déploiement et monitoring).
- **Alt-text (FR)** : Panorama des 4 premiers slides d'un deck pédagogique « Introduction au Machine Learning » — Slide 1 (titre/sous-titre), Slide 2 (définition + 4 bullets), Slide 3 (3 types d'apprentissage supervisé/non-supervisé/renforcement), Slide 4 (pipeline typique ML en 4 étapes).
- **Poids** : 47 Ko (PNG max-dim 1200 px depuis source 1589×335, RGBA → RGB)
- **Note** : alt-text antérieur « aperçu des frames vidéo » = sur-vendeur ; ce sont des slides de présentation, illustrant le **contenu pédagogique** produit par la chaîne script → slides → vidéo.

## vid4-creative.png

- **Source** : notebook `04-2-Creative-Video-Workflows.ipynb` — sortie titrée « Effets synchronises sur les beats DETECTES (vrai tempo 96 BPM) » (cellule 11 à l'extraction du 07/11) — effets audio-réactifs synchronisés sur les beats détectés du morceau témoin
- **Description visuelle** : Six vignettes en grille 2×3 sous le suptitre « Effets synchronises sur les beats DETECTES (vrai tempo 96 BPM) ». Chaque panneau porte un fond en dégradé (violet/magenta, rouge/olive, rose/gris selon le panneau) avec deux formes géométriques — un petit carré bleu clair et un cercle jaune/orange. Rangée du haut = panneaux « Original » aux beats 1/2/3 (frames 13/27/42) ; rangée du bas = « Avec effet » sur les mêmes beats — flash, zoom puis flash. La comparaison haut/bas montre l'effet audio-réactif appliqué aux instants exacts des beats détectés.
- **Contenu réel vérifié** (structurel à la source committée + audit #20603 + QA vision 07/11) : PNG 1200×576, grille 2×3 :
  - Suptitre intégré « Effets synchronises sur les beats DETECTES (vrai tempo 96 BPM) » ; texte stream compagnon : « Periode vraie 0.625 s (96 BPM) vs 0.500 s (temoin 120) ».
  - Rangée du haut = « Original (beat 1, frame 13, t=0.53s) » / « Original (beat 2, frame 27, t=1.14s) » / « Original (beat 3, frame 42, t=1.76s) ».
  - Rangée du bas = « Avec effet (flash) » / « Avec effet (zoom) » / « Avec effet (flash) ».
  - Le point pédagogique : le tempo **détecté** (96 BPM) diffère du témoin (120 BPM) — la synchronisation suit les beats réels du morceau, pas un métronome supposé.
- **Alt-text (FR)** : Grille 2×3 « Effets synchronisés sur les beats détectés (vrai tempo 96 BPM) » — rangée du haut : frames originales aux beats 1/2/3 (frames 13/27/42) ; rangée du bas : mêmes frames avec effet audio-réactif (flash/zoom) appliqué à chaque beat détecté.
- **Poids** : 55 Ko (PNG max-dim 1200 px depuis source committée 1235×593)
- **Note** : remplacement #24395 — l'ancienne version (grille « 120 BPM », cf audit c.485 + migration c.763 dans l'historique git) datait d'une exécution dont la sortie n'est plus committée.

## vid4-creative2.png

- **Source** : notebook `04-2-Creative-Video-Workflows.ipynb` (cellule 18, output 2) — collage 4 styles visuels sur même séquence vidéo
- **Description visuelle** : Douze vignettes en grille 3 colonnes × 2 lignes (3 timestamps × 4 styles) sous le titre gras « Collage video 2x2 : Original / Aquarelle / Dessin / Teal & Orange ». Chaque colonne correspond à un timestamp t=0.0/3.0/6.0s ; chaque ligne montre 2 vignettes de styles différents (Original/Aquarelle sur la première moitié verticale, Dessin/Teal & Orange en bas). Le carré cyan + cercle orange réapparaissent dans toutes les vignettes, mais changent **radicalement de palette selon la colonne** : bleu/violet à t=0s, vert olive/rouge brique à t=3s (effet aquarelle), retour bleu/violet décalé à t=6s. Variance colorimétrique élevée (RGB 80×80 std ≈ 80/92/91 — la figure la plus *multi-palette* des 6).
- **Contenu réel vérifié** : PNG 1200×313, sous-titre « Collage video 2x2 : Original / Aquarelle / Dessin / Teal & Orange », 3 colonnes × 2 lignes :
  - **t=0.0s** : 4 vignettes carrées sur fond bleu/violet en haut, 4 vignettes sur fond blanc/bleu en bas (style Teal & Orange).
  - **t=3.0s** : variante avec fond vert/olive/rouge brique (style Aquarelle en bas à droite, dessin simplifié au centre).
  - **t=6.0s** : retour au rendu proche de t=0.0s avec décalages de palette.
- **Alt-text (FR)** : Collage vidéo 2×2 « Original / Aquarelle / Dessin / Teal & Orange » à 3 timestamps t=0/3/6s — comparaison de 4 styles visuels appliqués au même clip : Original (rendu fidèle sur fond bleu/violet), Aquarelle (rendu vert/olive pastel), Dessin (rendu simplifié sur fond clair), Teal & Orange (grade cinématique sur fond bleu/orange).
- **Poids** : 37 Ko (PNG max-dim 1200 px depuis source 1519×397)
- **Note** : alt-text antérieur « variante de composition » = sous-spécifique ; le contenu réel = **mosaïque 4 styles visuels** (Original / Aquarelle / Dessin / Teal & Orange), pas une simple variation de cadrage.

## vid4-sora.png — RETIRÉE

- **Statut** : **RETIRÉE le 2026-11-07 (#24395)**. Aucune sortie committée du notebook `04-3-Sora-API-Cloud-Video.ipynb` à main ne correspond à cette figure ; sans provenance committée, une figure README ne se maintient pas (doctrine #24395). La description complète (audit c.485 + migration c.763 : grille 2×4 « Generation Text -> Video (Sora API) », filigrane « Sora API - Simulation ») reste dans l'historique git de ce MANIFEST. Le notebook 04-3 conserve sa disclose « simulation disciplinée » dans le README de série.

## vid4-sora2.png — RETIRÉE

- **Statut** : **RETIRÉE le 2026-11-07 (#24395)**, même motif : aucune sortie committée du notebook 04-3 ne correspond à cette figure. La description complète (séquence « Image -> Video (effet Ken Burns) », zoom progressif sur image fixe) reste dans l'historique git de ce MANIFEST.

## vid4-pipeline.png — RETIRÉE

- **Statut** : **RETIRÉE le 2026-11-07 (#24395)** : aucune sortie committée du notebook `04-4-Production-Video-Pipeline.ipynb` ne correspond à cette figure. La description complète (5 scènes titrées « Introduction / Origines historiques / Fonctionnement / Applications / Perspectives », storytelling slide-par-slide) reste dans l'historique git de ce MANIFEST. Le notebook 04-4 reste la référence visuelle de son pipeline.

---

**Total** : 3 figures, 138 Ko (après retraits #24395 : educational 47 Ko, creative 55 Ko, creative2 37 Ko). **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Toutes PNG ; pas de fallback WebP nécessaire (compresseur PNG downscalé → fichiers 37-55 Ko, sous les 200 Ko sans effort).

**⚠️ Limitations de ce MANIFEST** :
- Aucune figure restante ne montre de limitation manifeste du pipeline (toutes ont produit du contenu visible et illustratif).
- 3 figures retirées le 2026-11-07 (#24395) faute de provenance committée : `vid4-sora.png`, `vid4-sora2.png` (notebook 04-3), `vid4-pipeline.png` (notebook 04-4) — tombstones ci-dessus ; les notebooks reprennent la fonction d'illustration.
- `vid4-creative.png` est la sortie committée courante du notebook 04-2 (tempo détecté 96 BPM) ; l'ancienne version à 120 BPM n'est plus committée.
- Les sources sont **downscalées** (≤1200 px) — c'est la compression PNG max-dim 1200 standard, pas une modification du contenu.
- Les retraits #24395 sont documentés en tombstones, jamais silencieux ; les figures conservées demeurent sur disque.
