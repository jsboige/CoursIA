# Manifeste des figures — GenAI/Image/02-Advanced (modèles avancés)

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

> **Audit vision po-2025 c.483 (2026-07-14, doctrine #5780)** : les 6 PNG/WebP ci-dessous ont été ouverts un par un via l'outil `Read` et leur contenu réel confronté à leur description existante. **Verdict par figure dans le champ *Contenu réel vérifié***. **1/6 ACCURATE sans correction** (img2-bonsai-ternary.png, l'audit fondateur c.347 avait déjà produit le format standard). **5/6 corrections réelles** : (1) img2-qwen-edit.png alt-text ENRICHI pour décrire le triptyque original/masque/édition (l'ancien alt-text « panorama avant/après » était imprécis — c'est un triptyche 3 panneaux) ; (2) img2-qwen-edit2.webp alt-text REFONTAISONNÉ — c'est une **mosaïque 4 variations thématiques** (cityscape/temple/underwater/library), pas une « variante de prompt » isolée ; (3) img2-flux-gen.webp alt-text ENRICHI pour mentionner les éléments visuels clés (jardin zen japonais, cerisier en fleurs, sable ratissé au coucher de soleil) ; (4) img2-flux-gen2.png alt-text REFONTAISONNÉ — c'est un **comparatif de ratios d'aspect** 4 cellules (1:1/16:9/9:16/4:3), pas une « composition alternative » ; (5) img2-zimage-lumina.webp alt-text ENRICHI (samouraï robotique en armure dans ruelle cyberpunk néon rose/magenta). **0 figure DROP** — les 6 fichiers restent sur disque. **0 notebook ré-exécuté** (C.3 strict respecté). Migration **format table vague-1 → format liste détaillé standard** (sections *Contenu réel vérifié* par figure + *Ce qui n'est PAS dans la figure* + alt-text refait ou confirmé). **C'est l'audit fondateur c.347 (2026-07-11) qui avait flagué 5/6 bugs sur ce dossier** — re-audit cross-cycles 2026-07-14 confirme que les alt-texts étaient toujours imprécis, pas migrés au format standard.

## img2-qwen-edit.png

- **Source** : notebook `02-1-Qwen-Image-Edit-2509.ipynb` (cellule 17, output 1)
- **Contenu réel vérifié** : PNG 900×242, triptyque côte-à-côte avec titres « **Image Originale** » (gauche, intérieur de café chaleureux avec table en bois, tasse de café, plantes, lampadaire pendant), « **Masque (blanc = zone à modifier)** » (centre, masque blanc flou rectangulaire sur fond noir), « **Zone d'édition (rouge)** » (droite, même intérieur de café avec une zone rouge sur la table du fond indiquant la zone éditée). Palette = brun/chaud/orange, ambiance restaurant cosy.
- **Alt-text (FR)** : Triptyque d'édition Qwen Image Edit — image originale d'un intérieur de café (gauche), masque blanc flou (centre), zone d'édition marquée en rouge (droite) — workflow image-to-image avec masque d'inpainting.
- **Poids** : 170,5 KB (natif PNG)
- **Note** : enrichissement de l'ancien alt-text « panorama avant/après » imprécis — c'est bien un triptyque original/masque/édition, pas un simple panorama.

## img2-qwen-edit2.webp

- **Source** : notebook `02-1-Qwen-Image-Edit-2509.ipynb` (cellule 24, output 5)
- **Contenu réel vérifié** : WebP 780×800, mosaïque 2×2 sous le titre « **Batch Generation - Variations Thématiques** » avec 4 prompts thématiques : « A futuristic cityscape at sunset » (haut-gauche, cyberpunk violet/magenta avec voiture volante), « An ancient Japanese temple in autumn » (haut-droite, pagode dans érables rouges), « An underwater coral reef » (bas-gauche, récif corallien avec poissons tropicaux et rayons lumineux), « A cozy library interior » (bas-droite, bibliothèque avec chat sur fauteuil près d'une fenêtre). 4 images de domaines thématiques très différents générées en batch.
- **Alt-text (FR)** : Batch generation Qwen Image Edit — mosaïque 4 variations thématiques (cityscape futuriste au coucher de soleil / temple japonais en automne / récif corallien sous-marin / bibliothèque cosy avec chat).
- **Poids** : 66,8 KB (WebP fallback max-dim 800)
- **Note** : refonte de l'ancien alt-text « Édition Qwen — variante de prompt » très sous-spécifique — ce sont **4 variations thématiques distinctes en batch**, pas une seule variante.

## img2-flux-gen.webp

- **Source** : notebook `02-2-FLUX-1-Advanced-Generation.ipynb` (cellule 9, output 9)
- **Contenu réel vérifié** : WebP 781×800, titre intégré « **FLUX.1-schnell (4 steps)** ». **Jardin zen japonais** au coucher de soleil : cerisier en fleurs (sakura rose pâle) couvrant toute la partie supérieure, bâtiment traditionnel japonais (toit sombre, véranda en bois) au centre-droit, **sable ratissé en motifs concentriques** au premier plan avec mousses vert-vif et pierres plates disposées symétriquement. Palette = rose pâle/vert mousse/ocre/orange coucher de soleil, ambiance sereine et contemplative.
- **Alt-text (FR)** : Jardin zen japonais au coucher de soleil (cerisier en fleurs sakura, sable ratissé en motifs concentriques, mousses vert-vif, pierres plates) — génération FLUX.1-schnell en 4 steps.
- **Poids** : 195,0 KB (WebP fallback max-dim 800)
- **Note** : enrichissement de l'ancien alt-text « Génération FLUX-1 — image photoréaliste » — ajout des éléments visuels distinctifs (sakura, sable ratissé, jardin zen, coucher de soleil).

## img2-flux-gen2.png

- **Source** : notebook `02-2-FLUX-1-Advanced-Generation.ipynb` (cellule 15, output 9)
- **Contenu réel vérifié** : PNG 500×329, mosaïque 4 cellules sous le titre « **Comparaison des Ratios d'Aspect** » avec 4 ratios : « 1:1 (Carré) » (haut-gauche, coucher de soleil sur palmiers en format carré), « 16:9 (Paysage) » (haut-droite, coucher de soleil sur palmiers en format paysage panoramique avec ciel rouge dominant), « 9:16 (Portrait) » (bas-gauche, coucher de soleil sur palmiers en format vertical), « 4:3 (Standard) » (bas-droite, coucher de soleil sur palmiers en format 4:3). **Même scène** (coucher de soleil tropical sur palmiers avec ciel rouge/orange/violet) générée dans 4 ratios d'aspect différents.
- **Alt-text (FR)** : Comparatif de ratios d'aspect FLUX-1 — même coucher de soleil sur palmiers rendu en 4 ratios (1:1 carré, 16:9 paysage, 9:16 portrait, 4:3 standard).
- **Poids** : 154,1 KB (natif PNG)
- **Note** : refonte de l'ancien alt-text « Génération FLUX-1 — composition alternative » imprécis — ce n'est PAS une composition différente, c'est une **même scène testée à différents ratios d'aspect**.

## img2-zimage-lumina.webp

- **Source** : notebook `02-4-Z-Image-Lumina2.ipynb` (cellule 11, output 3)
- **Contenu réel vérifié** : WebP 784×800, titre intégré « **Z-Image: Cinematic photography of a samurai robot in a neon...** ». **Samouraï robotique en armure** traditionnelle japonaise (kabuto à cornes) debout de dos dans une ruelle cyberpunk nocturne ruisselante de pluie, entourée d'enseignes lumineuses verticales au néon rose/magenta (kanji japonais partiellement lisibles) et de buildings aux fenêtres bleutées. Palette = rose/magenta/violet/bleu profond, ambiance Blade Runner / Ghost in the Shell.
- **Alt-text (FR)** : Samouraï robotique en armure traditionnelle japonaise (kabuto à cornes) debout dans une ruelle cyberpunk nocturne ruisselante de pluie, enseignes néon rose/magenta — rendu cinématographique Z-Image.
- **Poids** : 61,1 KB (WebP fallback max-dim 800)
- **Note** : enrichissement de l'ancien alt-text « Génération Z-Image/Lumina2 — prototypage rapide » — ajout des éléments visuels distinctifs (samouraï robotique, kabuto à cornes, ambiance Blade Runner, pluie, enseignes néon).

## img2-bonsai-ternary.png

- **Source** : notebook `02-5-Bonsai-Image-Ternary.ipynb` (cellule 6, output 0)
- **Contenu réel vérifié** : PNG 885×590, scatter plot matplotlib sous le titre « **Quantization : trade-off taille vs qualité (transformer 4B)** / **Bonsai-Image vise le coin haut-gauche** ». Axes = X = « Taille modèle on-disk (GB, échelle log) » / Y = « Qualité relative (% vs FP16) ». 6 points de quantization marqués : **FP16** (haut-droite, ~32GB, 100%), **INT8 (LLM.int8)** (~16GB, 95%), **Ternaire 1.58-bit** (~4GB, 92%), **NF4 / INT4** (~7GB, 90%), **INT3** (~3GB, 82%), **INT2 naïf** (~2GB, 55%). Ligne horizontale en pointillés à 92% = cible Bonsai. Légende : « Bonsai-Image vise le coin haut-gauche ».
- **Alt-text (FR)** : Scatter plot matplotlib du trade-off taille vs qualité pour un transformer 4B — 6 niveaux de quantization (FP16/INT8/INT4/NF4/INT3/INT2/Bonsai 1.58-bit) positionnés sur la cible « coin haut-gauche » (petit + bonne qualité).
- **Poids** : 34,1 KB (natif PNG)
- **Note** : alt-text déjà correct dans la version pré-c.347 (« Bonsai ternaire 1,58-bit — génération efficace ») — mais amélioration de la précision descriptive (« scatter plot trade-off » vs « génération efficace ») pour mieux refléter le contenu (c'est un **plot de positionnement comparatif**, pas une image générée par Bonsai).

---

**Total** : 6 figures, ~682 KB. **Politique** (#5654) : ≤200 KB/fichier, downscale ≤1200 px max. 3 WebP (img2-qwen-edit2, img2-flux-gen, img2-zimage-lumina — fallback PNG >200KB) + 3 PNG natifs (img2-qwen-edit, img2-flux-gen2, img2-bonsai-ternary). Arc pédagogique dans le README : édition ciblée (02-1 Qwen triptyque + batch variations) → génération photoréaliste (02-2 FLUX jardin zen + comparatif ratios) → prototypage rapide (02-4 Z-Image samouraï) → quantification extrême (02-5 Bonsai scatter plot). Chaque figure est placée **dans la section du README où le notebook correspondant est discuté** (et non dans une section Galerie isolée), conformément à la doctrine figures amendée 2026-07-09.

**⚠️ Limitations de ce MANIFEST** :
- Aucune figure ne montre de limitation manifeste du pipeline (contrairement à img1-qwen-edit2.png de 01-Foundation qui montrait des blocs bleus plats dus à une cellule sans image source). Tous les outputs de 02-Advanced ont produit du contenu visible et utilisable.
- Les figures sont conservées **telles quelles** sur disque ; cette PR ne supprime AUCUN fichier PNG/WebP (seuls les alt-texts et notes du MANIFEST/README sont corrigés).
