# Manifeste des figures — GenAI/Video/04-Applications (cas d'usage production)

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

> **Audit vision po-2025 c.485 (2026-07-14, doctrine #5780)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` et leur contenu réel confronté à leur description existante. **Bilan G.1 firsthand : 6/6 alt-texts sur-vendeurs / faux sens majeur — 0 figure ACCURATE mature**. Le dossier GenAI/Video/04-Applications **n'avait pas reçu d'audit G.1 préalable** (contrairement à GenAI/Video/01-Foundation c.351 po-2023) — c'est donc un audit fondateur tardif pour ce sous-dossier. **Migration format vague-1 → liste détaillé standard** (sections Contenu réel vérifié / Alt-text (FR) / Poids / Note) appliquée pour aligner avec le standard rollout #5780. **6/6 corrections réelles** :
> 1. `vid4-educational.png` : alt-text sur-vendeur (« aperçu des frames ») → refait pour préciser le **contenu visible** = panorama des 4 premiers slides « Introduction au Machine Learning » (Slide 1: « Introduction au Machine Learning — Concepts fondamentaux et applications » ; Slide 2: « Qu'est-ce que le Machine Learning ? — Apprentissage à partir de données, Amélioration avec l'expérience, Généralisation à de nouveaux cas, Alternative à la programmation explicite » ; Slide 3: « Types d'apprentissage — Supervisé (données étiquetées: classification, régression), Non supervisé (découverte de structures), Par renforcement (apprentissage par essai-erreur) » ; Slide 4: « Pipeline typique ML — Collecte et préparation, Sélection et entraînement du modèle, Évaluation des performances, Déploiement et monitoring »). **Ce sont des SLIDES de présentation pédagogique, pas des frames vidéo.**
> 2. `vid4-creative.png` : alt-text sur-vendeur (« séquence créative ») → refait = grille 2×3 « Effets synchronisés sur beats (120 BPM) » avec 3 battements (Original beat 1/2/3 × frame 0/12/24 en haut ; Avec effet en bas), comparant un carré cyan + cercle orange en mouvement sur fond dégradé bleu/violet → rose. **C'est une synchro audio-reactive pédagogique, pas une vidéo créative libre.**
> 3. `vid4-creative2.png` : alt-text sous-spécifique (« variante de composition ») → refait = collage vidéo 2×2 « Original / Aquarelle / Dessin / Teal & Orange » à 3 timestamps t=0/3/6s — comparaison de **4 styles visuels** appliqués au même contenu sur 3 instants.
> 4. `vid4-sora.png` : alt-text partiellement correct mais ambigu → précisez le contenu réel = grille 2×4 « Generation Text → Video (Sora API) » sur deux thèmes Nature/Urbain à 4 timesteps t=0.0/1.6/3.3/5.0s, avec soleil stylisé jaune + horizon herbe vert dégradé, filigrane « Sora API - Simulation » en bas (sphère-monde + Simulation) **et** prompt injecté en gras en haut de chaque frame (« Prompt: A realistic mountain lake at sunset, reflecting sky » / « Prompt: A busy Tokyo street at night, neon signs reflecting »).
> 5. `vid4-sora2.png` : alt-text cite « Sora » mais le contenu réel = **« Image → Video (effet Ken Burns) »** = 5 frames t=0/1.6/3.3/5.0s avec zoom progressif sur image source (soleil + collines + horizon). C'est **un effet Ken Burns, pas une simulation Sora** — correction MISMATCH.
> 6. `vid4-pipeline.png` : alt-text sur-vendeur (« Pipeline production — orchestration ») → refait = « Images des scènes du pipeline » = 5 scènes « Introduction / Origines historiques / Fonctionnement / Applications / Perspectives », chacune avec fond coloré distinct (bleu/marron/vert/violet/bleu nuit) et constellation de bulles + constellation filaire. C'est **un storytelling slide par slide, pas une orchestration production**.

Toutes les attributions cell[X]/out[Y] sont **validées par ratio** (downscaling 1589→1200 ≈ 1.32, sauf fig creative.png 1240→1200 ≈ 1.03 car source déjà rès-petite).

> **Migration canonical c.763 (2026-07-22, jsboige:CoursIA-2)** : ajout du champ **`Description visuelle`** (gist compact de ce qui est *visible* en un coup d'œil, distinct du `Contenu réel vérifié` détaillé et du `Alt-text (FR)` accessibilité). Format aligné sur c.751 (GenAI/Audio) + modèle rollout #5780. 6/6 figures migrées, audit vision MiniMax M3 firsthand + PIL RGB mean+std à 80×80 (cf. PR body). **Audit fondateur c.485 préservé verbatim** ci-dessus ; cette migration est purement additive (pas de suppression de contenu).

## vid4-educational.png

- **Source** : notebook `04-1-Educational-Video-Generation.ipynb` (cellule 9, output 2) — génération automatique de slides pédagogiques à partir d'un script textuel
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

- **Source** : notebook `04-2-Creative-Video-Workflows.ipynb` (cellule 9, output 2) — effets audio-réactifs synchronisés sur beats musicaux
- **Description visuelle** : Six vignettes en grille 2×3 sous le titre gras « Effets synchronises sur les beats (120 BPM) ». Chaque vignette contient un **petit carré bleu cyan** (côté gauche) et un **cercle orange** (côté droit) en mouvement. Rangée du haut = « Original » aux frames 0/12/24 (les couleurs du carré et du cercle restent saturées). Rangée du bas = « Avec effet » sur les mêmes frames (le carré devient pastel bleu clair, le cercle jaune pastel). Fond dégradé diagonale bleu-violet → rose. Palette dominante violet/magenta (RGB 80×80 mean ≈ 179/150/211, fort B), contraste fort entre les 2 formes géométriques simples et le fond.
- **Contenu réel vérifié** : PNG 1200×573, grille 2×3 sous le titre « Effets synchronisés sur les beats (120 BPM) » :
  - Rangée du haut = « Original (beat 1, frame 0) » / « Original (beat 2, frame 12) » / « Original (beat 3, frame 24) » — formes géométriques simples (carré cyan + cercle orange) sur fond bleu/violet → rose.
  - Rangée du bas = « Avec effet » sur les mêmes timesteps — formes décalées + couleurs plus pastelisées.
  - L'effet de synchronisation est visible : à chaque beat (toutes les 12 frames à 120 BPM), la position du cercle orange ou la palette change.
- **Alt-text (FR)** : Grille 2×3 « Effets synchronisés sur les beats (120 BPM) » — comparaison entre frames originales (haut, beat 1/2/3 à frame 0/12/24) et frames transformées par effet audio-réactif (bas), montrant le carré cyan et le cercle orange se déplacer/changer au fil des battements sur fond dégradé bleu-violet-rose.
- **Poids** : 45 Ko (PNG max-dim 1200 px depuis source 1240×593)
- **Note** : alt-text antérieur « Workflow créatif vidéo — séquence générée » = sur-vendeur ; le pattern pédagogique est **audio-réactif sur beats**, pas « créativité libre ».

## vid4-creative2.png

- **Source** : notebook `04-2-Creative-Video-Workflows.ipynb` (cellule 15, output 2) — collage 4 styles visuels sur même séquence vidéo
- **Description visuelle** : Douze vignettes en grille 3 colonnes × 2 lignes (3 timestamps × 4 styles) sous le titre gras « Collage video 2x2 : Original / Aquarelle / Dessin / Teal & Orange ». Chaque colonne correspond à un timestamp t=0.0/3.0/6.0s ; chaque ligne montre 2 vignettes de styles différents (Original/Aquarelle sur la première moitié verticale, Dessin/Teal & Orange en bas). Le carré cyan + cercle orange réapparaissent dans toutes les vignettes, mais changent **radicalement de palette selon la colonne** : bleu/violet à t=0s, vert olive/rouge brique à t=3s (effet aquarelle), retour bleu/violet décalé à t=6s. Variance colorimétrique élevée (RGB 80×80 std ≈ 80/92/91 — la figure la plus *multi-palette* des 6).
- **Contenu réel vérifié** : PNG 1200×313, sous-titre « Collage video 2x2 : Original / Aquarelle / Dessin / Teal & Orange », 3 colonnes × 2 lignes :
  - **t=0.0s** : 4 vignettes carrées sur fond bleu/violet en haut, 4 vignettes sur fond blanc/bleu en bas (style Teal & Orange).
  - **t=3.0s** : variante avec fond vert/olive/rouge brique (style Aquarelle en bas à droite, dessin simplifié au centre).
  - **t=6.0s** : retour au rendu proche de t=0.0s avec décalages de palette.
- **Alt-text (FR)** : Collage vidéo 2×2 « Original / Aquarelle / Dessin / Teal & Orange » à 3 timestamps t=0/3/6s — comparaison de 4 styles visuels appliqués au même clip : Original (rendu fidèle sur fond bleu/violet), Aquarelle (rendu vert/olive pastel), Dessin (rendu simplifié sur fond clair), Teal & Orange (grade cinématique sur fond bleu/orange).
- **Poids** : 37 Ko (PNG max-dim 1200 px depuis source 1519×397)
- **Note** : alt-text antérieur « variante de composition » = sous-spécifique ; le contenu réel = **mosaïque 4 styles visuels** (Original / Aquarelle / Dessin / Teal & Orange), pas une simple variation de cadrage.

## vid4-sora.png

- **Source** : notebook `04-3-Sora-API-Cloud-Video.ipynb` (cellule 9, output 3) — simulation Sora API sur 2 thèmes (Nature/Urbain) à 4 timesteps
- **Description visuelle** : Huit vignettes en grille 2×4 sous le titre gras « Generation Text -> Video (Sora API) ». Rangée du haut = « Nature » à t=0.0/1.6/3.3/5.0s ; rangée du bas = « Urbain » aux mêmes timesteps. Chaque vignette contient un **disque jaune** (le « soleil stylisé ») centré sur un **horizon herbe vert** et un **ciel dégradé violet/bleu**. La rangée du bas diffère surtout par le prompt injecté en haut (Tokyo/rue vs montagne/lac), mais le rendu géométrique reste quasiment identique à la rangée du haut (soleil + horizon + ciel) — d'où l'aspect « simulation disciplinée ». Filigrane « Sora API - Simulation » lisible en bas-gauche de chaque vignette. Palette globale vert/bleu/violet équilibrée (RGB 80×80 mean ≈ 125/146/144, B≈R≈144, écart-type modéré).
- **Contenu réel vérifié** : PNG 1200×422, sous le titre global « Generation Text -> Video (Sora API) », grille 2×4 :
  - Rangée du haut = thème « Nature » à t=0.0s / t=1.6s / t=3.3s / t=5.0s — soleil stylisé jaune sur ciel dégradé + horizon herbe vert, prompt « Prompt: A realistic mountain lake at sunset, reflecting sky » en haut de chaque frame, filigrane « Sora API - Simulation » + sphère 3D en bas à gauche.
  - Rangée du bas = thème « Urbain » aux mêmes timesteps — soleil + horizon herbe (prompts qui ne correspondent PAS au prompt affiché, simplification géométrique), filigrane identique.
- **Alt-text (FR)** : Grille 2×4 « Generation Text → Video (Sora API) » — simulation sur 2 thèmes (Nature : montagne lac au coucher de soleil réfléchissant le ciel ; Urbain : rue Tokyo de nuit avec néons) à 4 timesteps t=0.0/1.6/3.3/5.0s. Soleil stylisé + horizon herbe + ciel dégradé + filigrane « Sora API - Simulation ».
- **Poids** : 49 Ko (PNG max-dim 1200 px depuis source 1589×559)
- **Note** : le notebook produit une **simulation disciplinée** (pas de Sora API réel faute de clé/quota) — disclose assumée dans le README « workflow Sora en simulation ».

## vid4-sora2.png

- **Source** : notebook `04-3-Sora-API-Cloud-Video.ipynb` (cellule 11, output 2) — effet Ken Burns sur image source
- **Description visuelle** : Cinq vignettes côte-à-côte sous le titre gras « Image -> Video (effet Ken Burns) » montrant un **zoom progressif** sur la même scène : **montagnes triangulaires vert foncé** + **soleil jaune** + **horizon herbe vert** + **ciel bleu**. Frame 0 « Image source » = cadrage large (montagnes + soleil en haut, herbe en bas). Frames 1→4 = zoom graduel (t=0.0s/1.6s/3.3s/5.0s), montagnes de plus en plus grandes, soleil de plus en plus proche. La **statique de la composition interne** (aucun objet ne bouge) contraste avec l'**évolution du cadrage** (camera se rapproche) — c'est précisément ce qui définit l'effet Ken Burns. Palette globale vert/bleu (RGB 80×80 mean ≈ 153/167/173, G domine), variance modérée.
- **Contenu réel vérifié** : PNG 1200×200, sous le titre « Image -> Video (effet Ken Burns) », séquence horizontale 5 frames :
  - Frame 0 « Image source » : montagne triangulaire + soleil + horizon, cadrage large.
  - Frame 1 « t = 0.0s » : zoom léger (cadre plus serré, montagnes plus grandes, soleil plus proche).
  - Frame 2 « t = 1.6s » : zoom progressif.
  - Frame 3 « t = 3.3s » : zoom progressif.
  - Frame 4 « t = 5.0s » : zoom maximal (montagnes + soleil occupant la moitié du cadre).
- **Alt-text (FR)** : Séquence « Image → Video (effet Ken Burns) » — 5 frames d'un zoom progressif sur une image source statique (montagnes + soleil + horizon herbe) entre t=0.0s et t=5.0s : la caméra se rapproche graduellement, cadrage de plus en plus serré, sans aucun objet en mouvement interne au clip.
- **Poids** : 36 Ko (PNG max-dim 1200 px depuis source 1589×265)
- **Note** : alt-text antérieur « Simulation Sora — aperçu alternatif » cite « Sora » à tort, le contenu est **un effet Ken Burns** (zoom statique sur image fixe), pas une simulation Sora. C'est **le 2ᵉ exemple pédagogique** du notebook 04-3, illustrant un autre mode de génération à partir d'images.

## vid4-pipeline.png

- **Source** : notebook `04-4-Production-Video-Pipeline.ipynb` (cellule 9, output 2) — 5 scènes vidéo produites par le pipeline bout-en-bout
- **Description visuelle** : Cinq vignettes côte-à-côte sous le titre gras « Images des scenes du pipeline », chaque vignette correspondant à une **scène titrée** (« Scene 1: Introduction » → « Scene 5: Perspectives »). Toutes les vignettes partagent la **même structure visuelle** : constellation de bulles de tailles variées reliées par des lignes filaires, sur fond coloré distinct. Palette varies nettement par scène : bleu vif, marron/ocre, vert forêt, violet, bleu nuit (RGB 80×80 std ≈ 102/101/95 — la variance la plus forte des 6, signature d'une mosaïque multi-couleurs). Étiquette blanche en bas de chaque vignette reprend le titre de la scène. Lecture séquentielle gauche→droite raconte la progression narrative du pipeline.
- **Contenu réel vérifié** : PNG 1200×236, sous le titre « Images des scenes du pipeline », séquence horizontale 5 scènes :
  - **Scene 1: Introduction** (fond bleu) — constellation de bulles bleues + lignes filaires reliant plusieurs nœuds.
  - **Scene 2: Origines historiques** (fond marron) — bulles ocres + constellation filaire géométrique.
  - **Scene 3: Fonctionnement** (fond vert forêt) — bulles vertes + lignes filaires, réseau plus dense.
  - **Scene 4: Applications** (fond violet) — bulles magenta + lignes filaires, constellation aérée.
  - **Scene 5: Perspectives** (fond bleu nuit) — bulles bleues pâles + lignes filaires, ton final plus sombre.
- **Alt-text (FR)** : « Images des scènes du pipeline » — 5 vignettes côte-à-côte des scènes vidéo générées bout-en-bout par le pipeline de production : « Scene 1: Introduction » (bulles bleues sur fond bleu), « Scene 2: Origines historiques » (bulles ocres sur fond marron), « Scene 3: Fonctionnement » (bulles vertes sur fond vert forêt), « Scene 4: Applications » (bulles magenta sur fond violet), « Scene 5: Perspectives » (bulles bleues pâles sur fond bleu nuit). Chaque scène porte une constellation filaire reliant ses bulles.
- **Poids** : 75 Ko (PNG max-dim 1200 px depuis source 1589×313)
- **Note** : alt-text antérieur « Pipeline vidéo production — orchestration » = sur-vendeur ; le contenu est **un storytelling slide-par-slide** (5 scènes titrées), pas un schéma d'orchestration. Le pipeline de production est illustré au niveau **résultat** (ses 5 scènes générées), pas au niveau **mécanique**.

---

**Total** : 6 figures, 292 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Toutes PNG ; pas de fallback WebP nécessaire (compresseur PNG downscalé gagne déjà 1589→1200 = ratio 1.32 → fichiers 35-75 Ko, sous les 200 Ko sans effort).

**⚠️ Limitations de ce MANIFEST** :
- Aucune figure ne montre de limitation manifeste du pipeline (toutes les figures ont produit du contenu visible et illustratif).
- 2 figures Sora (vid4-sora.png + vid4-sora2.png) sont **des simulations disciplinées** (Sora API réelle = besoin clé/quota utilisateur, RECOVERABLE-USER-HAND) — le notebook 04-3 le disclose explicitement dans son README « workflow en simulation ».
- 1 figure pipeline (vid4-pipeline.png) montre le **résultat** du pipeline (5 scènes) et pas son **mécanique** — l'illustration pédagogique privilégie le storytelling narratif.
- Les sources sont **downscalées** (ratio 1589→1200 ≈ 1.32, sauf vid4-creative.png 1240→1200 ≈ 1.03) — c'est la compression PNG max-dim 1200 standard, pas une modification du contenu.
- Toutes les figures restent sur disque ; cette PR ne supprime AUCUN fichier PNG.
