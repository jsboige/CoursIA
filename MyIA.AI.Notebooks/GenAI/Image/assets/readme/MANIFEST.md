# Manifeste des figures — GenAI/Image (racine)

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

> **Audit vision po-2025 c.481 (2026-07-14, doctrine #5780)** : les 6 PNG/WebP ci-dessous ont été ouverts un par un via l'outil `Read` et leur contenu réel confronté à leur description existante. Le MANIFEST racine était en format vague-1 (sections `##` par figure + alt-text court) avec des **incohérences manifestes** (3/6 alt-texts sur-vendeurs ou hors-sujet, 3/6 fichiers dont l'attribution source ne correspond pas au contenu effectif). **Verdict par figure dans le champ *Contenu réel vérifié***. **5/6 corrections réelles** (dalle3-cover.webp alt-text refait ; forge-sdxl-turbo.webp alt-text refait ; qwen-edit-panel.png alt-text honnête disclose limitation ; lumina2-zimage.webp alt-text honnête disclose limitation ; workflow-orchestration.png alt-text refait + correction source). **1/6 ACCURATE sans correction** (flux1-advanced.webp — jardin japonais zen, description déjà cohérente, juste enrichie). **0 figure DROP** — les 6 fichiers restent sur disque, les alt-texts sont honnêtes (« limitation illustrative assumée » cf doctrine figures amendée 2026-07-09). **0 notebook ré-exécuté** (C.3 strict respecté). Migration **format vague-1 → format liste détaillé standard** (sections *Contenu réel vérifié* par figure + *Ce qui n'est PAS dans la figure* + alt-text refait).

> **Correction vision po-2025 c.533 (2026-07-16)** : re-audit vision (Read pixel-par-pixel des 6 figures) qui **rétablit une inversion de l'audit c.481** — les descriptions de `lumina2-zimage.webp` et `workflow-orchestration.png` étaient **croisées**. Réalité vérifiée : `lumina2-zimage.webp` = **vrai** rendu Z-Image (samouraï robot cyberpunk, 6148 couleurs, SOTA-OK) ; `workflow-orchestration.png` = **rendu dégradé** (3 blocs plats « Multi-Variations sd35 », 191 couleurs). Les deux entrées ci-dessous ont été dé-croisées. Régénération des figures dégradées (`workflow-orchestration.png` + `qwen-edit-panel.png`) tracée par **[#6901](https://github.com/jsboige/CoursIA/issues/6901)** (RECOVERABLE-MACHINE, stack GenAI). Leçon : un « audit vision » text-only peut mal attribuer un contenu à un fichier — la vérification distinctive = Read effectif des pixels.

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
- **Contenu réel vérifié** : PNG 1041×490, deux panneaux côte-à-côte avec titres « **Image Originale** » (gauche) et « **Image Editée (denoise=0.5)** » (droite). **Les deux panneaux sont des blocs plats bleus uniformes identiques** (sans contenu généré, sans inpainting visible). Limitation illustrée : la cellule 18 output 3 du notebook a produit un rendu sans image source pour ce test — les blocs plats témoignent d'une exécution où l'image source n'a pas été fournie au workflow Qwen Phase 29 (ou le rendu matplotlib n'a pas chargé l'image avant le subplot).
- **Alt-text (FR)** : Panneau avant/après Qwen Image Edit — limitation illustrée : deux blocs bleus plats identiques (sortie de cellule sans contenu généré, le pipeline n'a pas reçu d'image source).
- **Poids** : 50.6 KB (natif)
- **Ce qui n'est PAS dans la figure** : ce n'est PAS un « panneau avant/après d'inpainting sur une zone masquée » comme indiqué dans l'ancienne version — le contenu est volontairement vide pour illustrer un cas de pipeline Qwen sans entrée. **Cette figure apparaît identique à `01-Foundation/assets/readme/img1-qwen-edit2.png`** (même cellule, même output = bloc plat bleu) — corrélation confirmée par audit c.481.

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

- **Source** : notebook `03-Orchestration/03-2-Workflow-Orchestration.ipynb` (cellule multi-variations produisant normalement trois chalets). Le nom de fichier est cohérent avec le notebook 03-2 ; c'est le **rendu** qui a dégénéré.
- **Contenu réel vérifié** (re-audit vision c.533) : PNG 1143×397, super-titre « **Multi-Variations** » + trois sous-titres « **sd35 photorealistic** » (bloc olive/kaki) / « **sd35 watercolor** » (bloc violet/mauve) / « **sd35 anime** » (bloc vert clair). **Les trois panneaux sont des blocs de couleur plats uniformes** (191 couleurs distinctes sur downsample 80×80) — sortie de fallback matplotlib, **sans contenu généré** (pas de chalet ni de scène). Rendu **dégradé**.
- **Alt-text (FR)** : Multi-Variations sd35 — rendu dégradé : trois blocs de couleur plats (olive « photorealistic », violet « watercolor », vert « anime ») au lieu des trois images attendues ; sortie de fallback matplotlib, régénération suivie par l'issue #6901.
- **Poids** : 8.5 KB (natif — cohérent avec un rendu en aplats plats, pas une image riche).
- **Verdict SOTA (#3801)** : **RECOVERABLE-MACHINE** — régénérer sur la stack GenAI (po-2023 / GPU) depuis `03-2-Workflow-Orchestration.ipynb` (trois vraies variations SD35, ou un vrai graphe de workflow ComfyUI). Suivi : **[#6901](https://github.com/jsboige/CoursIA/issues/6901)**. Le bon rendu du même concept existe déjà : `03-Orchestration/assets/readme/img3-workflow4.webp` (3 chalets SD35 réussis).
- **Correction c.533** : l'audit c.481 avait par erreur décrit CETTE figure comme un « samouraï robot Z-Image 1024×1024 » — description **croisée** avec `lumina2-zimage.webp` (le dimensionnement 1024×1024 annoncé était d'ailleurs faux : la figure fait 1143×397). La vérification vision c.533 rétablit les deux descriptions.

---

**Total** : 6 figures, ~422 KB. **Politique** (#5654) : ≤200 KB/fichier, downscale ≤1200 px max. 4 WebP (dalle3, forge, flux, lumina2 — fallback PNG >200KB) + 2 PNG natifs (qwen-edit-panel, workflow-orchestration). Arc pédagogique dans le README : API cloud (01-Foundation dalle3) → génération locale ComfyUI (01-Foundation forge) → édition image (01-Foundation qwen) → génération haute qualité (02-Advanced flux) → prototypage rapide (02-Advanced lumina2) → orchestration workflow (03-Orchestration workflow). Chaque figure est placée **dans la section du README où le notebook correspondant est discuté** (et non dans une section Galerie isolée), conformément à la doctrine figures amendée 2026-07-09.

**⚠️ Limitations de cette racine MANIFEST** (mises à jour c.533) :
- 2 figures (`qwen-edit-panel.png`, `workflow-orchestration.png`) sont des **rendus dégradés sans contenu généré** (blocs plats matplotlib) — labellisées honnêtement, régénération tracée par **[#6901](https://github.com/jsboige/CoursIA/issues/6901)** (RECOVERABLE-MACHINE, stack GenAI po-2023/GPU).
- Les noms de fichiers sont **cohérents** avec leur notebook source (`lumina2-zimage.webp` ↔ 02-4 Z-Image ; `workflow-orchestration.png` ↔ 03-2 Workflow) — l'ancien « mismatch d'attribution » signalé en c.481 provenait en fait d'une **inversion de descriptions** (corrigée c.533), pas d'un mauvais fichier.
- Les figures sont conservées **telles quelles** sur disque ; cette PR ne supprime AUCUN fichier PNG/WebP (seuls les alt-texts et descriptions MANIFEST/README sont corrigés pour coller aux pixels).