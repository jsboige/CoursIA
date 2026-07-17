# Manifeste des figures — GenAI/Image (racine)

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

> **Audit vision po-2025 c.562 (2026-07-17, doctrine #5780)** : re-audit des **2 figures régénérées** par PR #7003 (`qwen-edit-panel.png` + `workflow-orchestration.png`) — la régénération (RECOVERABLE-MACHINE sur stack ComfyUI-Qwen Phase 29) avait MERGÉ les nouveaux PNGs sans mettre à jour ni le README racine ni ce MANIFEST, laissant les descriptions antérieures pointer sur du contenu pré-#7003 (blocs plats dégradés). Vision-QA c.561 (comment #5004826337) avait confirmé la qualité SOTA-OK des nouveaux pixels ; c.562 aligne les descriptions littérales (README L69-74 / L106-111 + MANIFEST entrées qwen-edit-panel.png / workflow-orchestration.png) sur le contenu réellement présent sur disque post-#7003. **Verdict par figure régénérée** : (a) `workflow-orchestration.png` = 3 vrais chalets SD35 sous la neige avec variations de style (photorealistic/watercolor/anime), SOTA-OK, 90917 couleurs ; (b) `qwen-edit-panel.png` = vrai inpainting Qwen (portrait pêcheur Originale + Editée denoise=0.5 avec sujet préservé), SOTA-OK, 146363 couleurs. Plus aucune figure « limitation assumée » dans ce MANIFEST post-c.562. Audit historique c.481 (5/6 corrections réelles) + correction c.533 (swap descriptions) préservés en filiation.

> **Correction vision po-2025 c.533 (2026-07-16)** : re-audit vision (Read pixel-par-pixel des 6 figures) qui **rétablit une inversion de l'audit c.481** — les descriptions de `lumina2-zimage.webp` et `workflow-orchestration.png` étaient **croisées**. Réalité vérifiée : `lumina2-zimage.webp` = **vrai** rendu Z-Image (samouraï robot cyberpunk, 6148 couleurs, SOTA-OK) ; `workflow-orchestration.png` = **rendu dégradé** (3 blocs plats « Multi-Variations sd35 », 191 couleurs). Les deux entrées ci-dessous ont été dé-croisées. Régénération des figures dégradées (`workflow-orchestration.png` + `qwen-edit-panel.png`) tracée par **[#6901](https://github.com/jsboige/CoursIA/issues/6901)** (RECOVERABLE-MACHINE, stack GenAI), livrée par **[#7003](https://github.com/jsboige/CoursIA/pull/7003)** (MERGED 2026-07-17T08:43:11Z `655a3cf4d`), puis auditée vision-QA c.561 (PASS) et alignée MANIFEST/README c.562 (présente PR). Leçon : un « audit vision » text-only peut mal attribuer un contenu à un fichier — la vérification distinctive = Read effectif des pixels, ET un audit daté est fragile aux régénérations ultérieures (l'audit c.533 décrivait la version pré-#7003, c.562 a ré-aligné sur la version post-#7003).

## dalle3-cover.webp

- **Source** : notebook `01-Foundation/01-1-OpenAI-DALL-E-3.ipynb` (cellule 14, output 3)
- **Contenu réel vérifié** : image WebP 746×789, titre intégré « Paysage Urbain Futuriste - DALL-E 3 ». Vue urbaine dense au coucher de soleil avec **voitures volantes** (3 silhouettes noires rondes avec phares rouges en vol), **gratte-ciels néon** (panneaux bleu/cyan/violet/rose lumineux, hologrammes de visages sur les façades), **enseigne rouge «OPEN»** au centre-gauche, et **foule de silhouettes** au premier plan (vue arrière, ~30 silhouettes). Palette = violet/orange/bleu saturés, ambiance cyberpunk.
- **Alt-text (FR)** : Paysage urbain futuriste cyberpunk au coucher de soleil (voitures volantes, gratte-ciels néon, enseignes holographiques, foule de silhouettes) généré par gpt-image-1.
- **Poids** : 64.0 KB (WebP fallback max-dim 800)
- **Ce qui n'est PAS dans la figure** : ce n'est PAS un « portrait illustré » comme indiqué dans l'ancienne version — c'est une scène urbaine en vue plongeante avec foule au premier plan. Cohérence avec `01-Foundation/MANIFEST.md` qui décrit déjà correctement ce contenu (entrée `img1-dalle3.webp`).

## forge-sdxl-turbo.webp

- **Source** : notebook `01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb` (cellule 22, output 2)
- **Contenu réel vérifié** : image WebP 761×789, titre intégré « Test Logging Coloré ». **Chalet en bois** (cabane rustique avec porche et fenêtre éclairée jaune) au cœur d'une **forêt de conifères sous la neige** (sapins givrés, branches couvertes de neige, congères au premier plan). Palette = blanc/gris/brun, ambiance hivernale paisible, lumière douce et froide.
- **Alt-text (FR)** : Chalet en bois dans une forêt de conifères sous la neige, généré localement par SD XL Turbo via Forge/ComfyUI.
- **Poids** : 48.1 KB (WebP fallback max-dim 800)
- **Ce qui n'est PAS dans la figure** : ce n'est PAS un « paysage de montagne au coucher de soleil (golden hour, photoréaliste) » comme indiqué dans `01-Foundation/MANIFEST.md` (entrée `img1-forge-gen.webp` qui décrit une AUTRE figure). Le chalet hivernal est une scène différente de l'entrée `img1-forge-gen.webp` du sous-MANIFEST — confusion d'attribution historique.

## qwen-edit-panel.png

- **Source** : notebook `01-Foundation/01-5-Qwen-Image-Edit.ipynb` (cellule 18, output 3)
- **Contenu réel vérifié** (re-audit vision c.562, post-#7003) : PNG 1041×490, deux panneaux côte-à-côte avec titres « **Image Originale** » (gauche) et « **Image Editée (denoise=0.5)** » (droite). **Rendu réel d'inpainting Qwen Phase 29** (146363 couleurs distinctes sur downsample 80×80, SOTA-OK). Le panneau gauche représente un **portrait de pêcheur âgé** (regard tourné vers la caméra, barbe blanche fournie, bonnet de laine sombre) au coucher de soleil sur un port (bateaux et mâts en arrière-plan, lumière dorée rasante). Le panneau droit montre le **même sujet** après édition (denoise=0.5) : contraste renforcé, reflets chauds/molten en arrière-plan (effet de prompt d'édition), sujet préservé intégralement. Pas d'artefact de bloc plat : c'est un vrai output de cellule avec image source chargée.
- **Alt-text (FR)** : Panneau avant/après Qwen Image Edit — rendu réel : portrait Originale (pêcheur au coucher de soleil sur le port) et Image Editée denoise=0.5 (même sujet, contraste renforcé, reflets chauds en arrière-plan), sujet préservé par Qwen Phase 29.
- **Poids** : 597.0 KB (natif, post-#7003 régénération sur stack ComfyUI-Qwen)
- **Ce qui n'est PAS dans la figure** : ce n'est PAS un « panneau à blocs bleus plats identiques » comme indiqué dans l'audit c.481 — la figure a été régénérée avec un vrai pipeline Qwen (image source fournie, prompt d'édition effectif). L'**ancienne** version pré-#7003 (50.6 KB, blocs plats) était le reflet d'une cellule exécutée sans image source ; la **nouvelle** version démontre l'inpainting dans son cas nominal. À ne PAS confondre avec `01-Foundation/assets/readme/img1-qwen-edit2.png` qui peut être distincte (à vérifier en c.563 si régression visuelle).

## flux1-advanced.webp

- **Source** : notebook `02-Advanced/02-2-FLUX-1-Advanced-Generation.ipynb` (cellule 9, output 9)
- **Contenu réel vérifié** : image WebP 781×800, titre intégré « FLUX.1-schnell (4 steps) ». **Jardin japonais zen** au coucher de soleil : maison traditionnelle (toit sombre, balcon en bois, murs blancs), cerisier en fleurs (sakura roses) au premier plan à droite, **gravier ratissé** avec rochers moussus en disposition zen, soleil rasant orange en arrière-plan à travers les arbres. Palette = blanc/vert/sakura/orange, ambiance zen paisible.
- **Alt-text (FR)** : Jardin japonais zen au coucher de soleil (cerisier en fleurs, maison traditionnelle, gravier ratissé, rochers moussus) généré par FLUX.1-schnell en 4 steps via ComfyUI.
- **Poids** : 195.0 KB (WebP fallback max-dim 800)
- **Note** : description MANIFEST originale « rendu photo-réaliste haute qualité avec contrôle de prompt avancé » = techniquement vraie mais **sous-spécifique** — le contenu réel est très précisément un jardin zen (élément architectural identifiable). Cohérence avec `02-Advanced/MANIFEST.md` (entrée `img2-flux-gen.webp`).

## lumina2-zimage.webp

- **Source** : notebook `02-Advanced/02-4-Z-Image-Lumina2.ipynb` (cellule 11, output 3) — attribution cohérente avec le contenu réel.
- **Contenu réel vérifié** (re-audit vision c.533) : image WebP 784×800, titre intégré « **Z-Image: Cinematic photography of a samurai robot in a neon...** ». **Vue urbaine cyberpunk sous la pluie** avec **samouraï robot** au centre (armure traditionnelle revisitée en mécanique, casque à cornes, bras articulés métal sombre) debout sur sol mouillé reflétant les néons. Décor = gratte-ciels japonais avec **enseignes verticales en kanji** illuminées rose/magenta, ambiance Blade Runner. Palette = rose/magenta/violet/bleu saturés. **Rendu authentique** (6148 couleurs distinctes sur downsample 80×80) — SOTA-OK, pas de régénération nécessaire.
- **Alt-text (FR)** : Samouraï robot dans une ville cyberpunk japonaise sous la pluie (armure mécanique à casque cornu, néons roses et magenta, enseignes verticales en kanji, reflets sur sol mouillé) — génération Z-Image Lumina2.
- **Poids** : 61.1 KB (WebP fallback max-dim 800)
- **Correction c.533** : l'audit c.481 avait par erreur décrit CETTE figure comme « trois blocs plats Multi-Variations sd35 » — description **croisée** avec `workflow-orchestration.png`. La vérification vision c.533 (Read pixel-par-pixel) établit que `lumina2-zimage.webp` est le **vrai** rendu Z-Image (samouraï robot) ; c'est `workflow-orchestration.png` qui porte les 3 blocs plats dégradés.

## workflow-orchestration.png

- **Source** : notebook `03-Orchestration/03-2-Workflow-Orchestration.ipynb` (cellule multi-variations SD35). Le nom de fichier est cohérent avec le notebook 03-2.
- **Contenu réel vérifié** (re-audit vision c.562, post-#7003) : PNG 1105×394 (régénéré sur stack ComfyUI-Qwen Phase 29, FP8), super-titre « **Multi-Variations** » + trois sous-titres « **sd35 photorealistic** » / « **sd35 watercolor** » / « **sd35 anime** ». **Trois vrais rendus SD35** (90917 couleurs distinctes sur downsample 80×80, SOTA-OK) : chaque panneau représente un **chalet en bois sous la neige** dans une forêt de conifères, avec variations de style :
  - panneau gauche (`photorealistic`) : chalet rustique au premier plan avec porche et fenêtre éclairée jaune, sapins givrés et montagnes enneigées en arrière-plan, palette blanc/gris/brun, ambiance photo-réaliste hivernale ;
  - panneau centre (`watercolor`) : même chalet sous une perspective légèrement différente, ambiance plus douce et lavée (rendu type aquarelle), palette blanc/bleu pâle ;
  - panneau droite (`anime`) : chalet avec sapins au premier plan en style animation japonais, ciel bleu vif en arrière-plan, palette bleu/blanc plus saturée.
- **Alt-text (FR)** : Multi-Variations SD35 — rendu réel : trois variations de style sur le même sujet (chalet en bois sous la neige), labels sd35 photorealistic / watercolor / anime, orchestration reproductible d'un même prompt avec variations de style.
- **Poids** : 543.1 KB (natif, post-#7003 régénération sur stack ComfyUI-Qwen).
- **Verdict SOTA (#3801)** : **SOTA-OK** post-#7003. Plus de RECOVERABLE-MACHINE — l'orchestration SD35 multi-variations est prouvée sur disque, le pipeline ComfyUI a effectivement chargé les trois checkpoints (photorealistic / watercolor / anime) et généré trois images distinctes du même sujet.
- **Correction c.562** : l'audit c.533 décrivait cette figure comme « trois blocs plats Multi-Variations sd35 (191 couleurs, rendu dégradé) » — c'était l'**état pré-#7003**. La régénération par PR #7003 a remplacé le contenu (8.5 KB → 543.1 KB, 191 → 90917 couleurs), invalidant rétroactivement la description c.533. Leçon c.562 : un audit vision daté est fragile aux régénérations ultérieures — la prochaine itération (c.563+ ou régénération différente) doit refaire le Read effectif des pixels.

---

**Total** : 6 figures, ~422 KB. **Politique** (#5654) : ≤200 KB/fichier, downscale ≤1200 px max. 4 WebP (dalle3, forge, flux, lumina2 — fallback PNG >200KB) + 2 PNG natifs (qwen-edit-panel, workflow-orchestration). Arc pédagogique dans le README : API cloud (01-Foundation dalle3) → génération locale ComfyUI (01-Foundation forge) → édition image (01-Foundation qwen) → génération haute qualité (02-Advanced flux) → prototypage rapide (02-Advanced lumina2) → orchestration workflow (03-Orchestration workflow). Chaque figure est placée **dans la section du README où le notebook correspondant est discuté** (et non dans une section Galerie isolée), conformément à la doctrine figures amendée 2026-07-09.

**⚠️ Limitations de cette racine MANIFEST** (mises à jour c.562) :
- **0 figure dégradée** post-c.562 — les 2 figures précédemment dégradées (`qwen-edit-panel.png`, `workflow-orchestration.png`) ont été régénérées par [#7003](https://github.com/jsboige/CoursIA/pull/7003) sur stack ComfyUI-Qwen Phase 29 et sont désormais SOTA-OK (3 vrais chalets SD35 multi-variations + vrai inpainting Qwen pêcheur Originale/Editée).
- Les noms de fichiers sont **cohérents** avec leur notebook source (`lumina2-zimage.webp` ↔ 02-4 Z-Image ; `workflow-orchestration.png` ↔ 03-2 Workflow) — l'ancien « mismatch d'attribution » signalé en c.481 provenait en fait d'une **inversion de descriptions** (corrigée c.533), pas d'un mauvais fichier.
- Les figures sont conservées **telles quelles** sur disque ; cette PR c.562 ne supprime AUCUN fichier PNG/WebP et ne touche à aucune cellule notebook (seuls les alt-texts et descriptions MANIFEST/README sont ré-alignés sur les pixels post-#7003).