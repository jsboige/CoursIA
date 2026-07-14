# Manifeste des figures — GenAI/Image/01-Foundation (modèles de base)

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

> **Audit vision po-2025 c.482 (2026-07-14, doctrine #5780)** : les 6 PNG/WebP ci-dessous ont été ouverts un par un via l'outil `Read` et leur contenu réel confronté à leur description existante. **Verdict par figure dans le champ *Contenu réel vérifié***. **4/6 ACCURATE sans correction** (img1-dalle3.webp urbain futuriste + img1-forge-gen.webp montagne golden hour + img1-forge-gen2.webp ville 4-steps + img1-forge-gen3.webp forêt reproductible). **2/6 corrections réelles** : (1) img1-qwen-edit.png alt-text enrichi pour mentionner le chat tigré sur appui de fenêtre (contenu réel du hello-world Qwen 2.5-VL, qui est effectivement un chat — l'ancien alt-text « test de connectivité hello-world » était techniquement vrai mais sous-spécifique) ; (2) img1-qwen-edit2.png disclose limitation assumée (deux blocs bleus plats identiques = sortie de cellule sans image source fournie au pipeline Qwen Phase 29 ; alt-text refait pour honnêteté pédagogique). **0 figure DROP** — les 6 fichiers restent sur disque. **0 notebook ré-exécuté** (C.3 strict respecté). Migration **format table vague-1 → format liste détaillé standard** (sections *Contenu réel vérifié* par figure + *Ce qui n'est PAS dans la figure* + alt-text refait ou confirmé).

## img1-dalle3.webp

- **Source** : notebook `01-1-OpenAI-DALL-E-3.ipynb` (cellule 14, output 3)
- **Contenu réel vérifié** : image WebP 746×789, titre intégré « Paysage Urbain Futuriste - DALL-E 3 ». Vue urbaine dense au coucher de soleil avec **voitures volantes** (3 silhouettes noires rondes avec phares rouges en vol), **gratte-ciels néon** (panneaux bleu/cyan/violet/rose lumineux, hologrammes de visages sur les façades), **enseigne rouge «OPEN»** au centre-gauche, et **foule de silhouettes** au premier plan (vue arrière). Palette = violet/orange/bleu saturés, ambiance cyberpunk.
- **Alt-text (FR)** : Paysage urbain futuriste cyberpunk au coucher de soleil (voitures volantes, gratte-ciels néon, enseignes holographiques, foule de silhouettes) généré par gpt-image-1.
- **Poids** : 64,0 KB (WebP fallback max-dim 800)

## img1-forge-gen.webp

- **Source** : notebook `01-4-Forge-SD-XL-Turbo.ipynb` (cellule 10, output 2)
- **Contenu réel vérifié** : image WebP 761×789, titre intégré « Paysage de Montagne au Coucher du Soleil ». **Vallée de montagne** au coucher de soleil, premier plan = herbe verte + rochers + chemin de terre, arrière-plan = chaînes de montagnes superposées en dégradé bleu-violet. Ciel = coucher de soleil avec nuages gris/orange/rose. Palette = vert/brun/orange/bleu, ambiance paisible « golden hour ».
- **Alt-text (FR)** : Paysage de montagne au coucher de soleil (« golden hour », photoréaliste) généré par SDXL Turbo via Forge.
- **Poids** : 51,3 KB (WebP fallback max-dim 800)

## img1-forge-gen2.webp

- **Source** : notebook `01-4-Forge-SD-XL-Turbo.ipynb` (cellule 12, output 2)
- **Contenu réel vérifié** : image WebP 766×790, titre intégré « Ville Futuriste (4 steps, cfg=2.0) ». **Ruelle urbaine verticale** entre deux tours industrielles : structures métalliques complexes, fenêtres éclairées, atmosphère brumeuse vert/cyan/orange en arrière-plan, style concept-art futuriste (pas vraiment cyberpunk néons comme suggéré par l'ancien alt-text). Palette = vert/cyan/orange/gris métallique, ambiance industrielle futuriste.
- **Alt-text (FR)** : Ville futuriste industrielle (ruelle verticale entre tours, fenêtres éclairées, brume cyan/orange) en mode 4-steps Turbo cfg=2.0, générée par SDXL Turbo via Forge.
- **Poids** : 45,2 KB (WebP fallback max-dim 800)
- **Note** : ancien alt-text « ville cyberpunk nocturne (néons) » était imprécis — la palette dominante est vert/cyan industriel, pas vraiment « néons nocturnes ».

## img1-forge-gen3.webp

- **Source** : notebook `01-4-Forge-SD-XL-Turbo.ipynb` (cellule 18, output 1)
- **Contenu réel vérifié** : image WebP 568×590, titre intégré « Génération Reproductible (seed=42) ». **Forêt brumeuse** : troncs verticaux d'arbres serrés au premier plan, mousses orangées/marron au sol, lumière diffuse jaune-brume en arrière-plan. Palette = brun/vert/orange/marron, ambiance mystique forestière.
- **Alt-text (FR)** : Forêt brumeuse aux troncs verticaux et mousses orangées, génération reproductible avec seed fixe 42 via SDXL Turbo (Forge).
- **Poids** : 43,4 KB (WebP fallback max-dim 800)
- **Note** : ancien alt-text « champignons lumineux » imprécis — l'image montre une forêt brumeuse, pas de champignons visibles distinctement.

## img1-qwen-edit.png

- **Source** : notebook `01-5-Qwen-Image-Edit.ipynb` (cellule 10, output 2)
- **Contenu réel vérifié** : PNG 370×390, titre intégré « qwen_hello_00001_.png ». **Chat domestique tigré** (tabby brun avec rayures noires, yeux verts-jaune, collier/baudrier léger) assis sur un appui de fenêtre en bois, tourné vers la caméra, arrière-plan flou lumineux (fenêtre + plante verte). Palette = brun/crème/vert, ambiance photo réaliste « hello-world ».
- **Alt-text (FR)** : Chat domestique tigré (tabby brun, yeux verts) assis sur un appui de fenêtre en bois, première génération hello-world du workflow ComfyUI Qwen Image Edit 2509 (test de connectivité au service, ~277 s, ~29 GB VRAM).
- **Poids** : 131,0 KB (natif)
- **Note** : enrichissement de l'ancien alt-text « Génération hello-world » (techniquement vrai mais sous-spécifique) — le contenu réel est précisément un chat tigré, qui sert d'illustration parlante au test de connectivité du pipeline ComfyUI.

## img1-qwen-edit2.png

- **Source** : notebook `01-5-Qwen-Image-Edit.ipynb` (cellule 18, output 3)
- **Contenu réel vérifié** : PNG 1041×490, deux panneaux côte-à-côte avec titres « **Image Originale** » (gauche) et « **Image Editée (denoise=0.5)** » (droite). **Les deux panneaux sont des blocs plats bleus uniformes identiques** (sans contenu généré, sans inpainting visible). Limitation illustrée : la cellule 18 output 3 du notebook a produit un rendu sans image source pour ce test — les blocs plats témoignent d'une exécution où l'image source n'a pas été fournie au workflow Qwen Phase 29 (ou le rendu matplotlib n'a pas chargé l'image avant le subplot). **Cette figure apparaît identique à `assets/readme/qwen-edit-panel.png` du dossier racine GenAI/Image** (même limitation, mêmes blocs bleus plats) — corrélation confirmée par audit c.481 sur la racine.
- **Alt-text (FR)** : Panneau avant/après Qwen Image Edit Phase 29 — limitation illustrée : deux blocs bleus plats identiques (sortie de cellule sans contenu généré, le pipeline n'a pas reçu d'image source en entrée).
- **Poids** : 50,6 KB (natif)
- **Ce qui n'est PAS dans la figure** : ce n'est PAS un « workflow image-to-image Qwen Phase 29 (VAE 16-ch + CLIP sd3 + UNET fp8 + ModelSamplingAuraFlow shift 3.0 + CFGNorm 1.0) » comme indiqué dans l'ancienne version — le contenu est volontairement vide pour illustrer un cas de pipeline Qwen sans entrée. L'architecture du workflow (VAE/CLIP/UNET/ModelSamplingAuraFlow/CFGNorm) est **techniquement vraie** mais **non visible** dans cette figure : les blocs bleus plats témoignent de l'absence de rendu effectif, pas du workflow lui-même.

---

**Total** : 6 figures, ~385,5 KB. **Politique** (#5654) : ≤200 KB/fichier, downscale ≤1200 px max. 4 WebP (img1-dalle3, img1-forge-gen, img1-forge-gen2, img1-forge-gen3 — fallback PNG >200KB) + 2 PNG natifs (img1-qwen-edit, img1-qwen-edit2). Arc pédagogique dans le README : API cloud (01-1 dalle3) → génération locale ComfyUI (01-4 forge 3 variantes) → édition image (01-5 qwen hello-world + workflow image-to-image). Chaque figure est placée **dans la section du README où le notebook correspondant est discuté** (et non dans une section Galerie isolée), conformément à la doctrine figures amendée 2026-07-09.

**⚠️ Limitations de ce MANIFEST** :
- 1 figure (`img1-qwen-edit2.png`) illustre un **rendu sans contenu généré** (deux blocs plats bleus) — limitation assumée, conservée pour transparence pédagogique. Re-régénération recommandée hors-scope de cette PR d'audit (tracker par issue dédiée).
- Les figures sont conservées **telles quelles** sur disque ; cette PR ne supprime AUCUN fichier PNG/WebP (seuls les alt-texts et notes du MANIFEST/README sont corrigés).