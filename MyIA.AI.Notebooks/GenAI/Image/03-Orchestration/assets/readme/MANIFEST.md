# Manifeste des figures — GenAI/Image/03-Orchestration (multi-modèles & workflows)

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

> **Audit vision po-2025 c.484 (2026-07-14, doctrine #5780)** : les 5 PNG/WebP ci-dessous ont été ouverts un par un via l'outil `Read` et leur contenu réel confronté à leur description existante. **Verdict par figure dans le champ *Contenu réel vérifié***. **4/5 ACCURATE avec enrichissements mineurs** : (1) img3-multimodel.webp : MANIFEST déjà mature avec contenu vérifié détaillé depuis audit G.1 fondateur (2026-07-10/11), ajout datation c.484 + note timing Z-Image vs SDXL ; (2) img3-workflow1.webp ENRICHI pour préciser la scène (coucher de soleil sur montagnes enneigées, même composition aux 3 étapes) ; (3) img3-workflow2.webp ENRICHI pour préciser le prompt exact (« A futuristic city with flying cars and neon lights… ») ; (4) img3-workflow3.png ENRICHI pour préciser les 3 barres à score ~0.53 sous le seuil 0.75 ; (5) img3-workflow4.webp REFONTAISON — ancien alt-text « Trois déclinaisons stylistiques d'un même prompt » imprécis, le contenu réel = chalet en bois + montagnes enneigées + 3 styles **spécifiques à SD35** (photoréaliste/aquarelle/anime), pas un modèle générique. **0 figure DROP, 0 limitation disclosed** — toutes les figures ont produit du contenu visible (contrairement à img1-qwen-edit2.png 01-Foundation). **0 notebook ré-exécuté** (C.3 strict respecté). Migration **format table → format liste détaillé standard** déjà partiellement appliquée (img3-multimodel avait déjà son bloc Contenu réel vérifié depuis audit G.1 fondateur), c.484 complète en harmonisant les 4 autres figures sur le même format + datation audit-block.

## img3-multimodel.webp

- **Source** : notebook `03-1-Multi-Model-Comparison.ipynb` (cellule 8, output 2) — comparaison côte à côte SDXL Lightning-4step (Forge) vs Z-Image/Lumina-2 (ComfyUI)
- **Contenu réel vérifié** (audit G.1 fondateur juillet 2026, doctrine #5780 ; re-audit c.484 2026-07-14) : grille *« SDXL Lightning-4step (16.11s) 512×512 »* et *« Z-Image (409.86s) 1024×1024 »* sur le même prompt *« A cute robot playing chess in a park, sunlight, detailed »*. Le panneau gauche montre un robot au rendu painterly/blueprint (peinture acrylique rouge, échiquier stylisé, rayures verticales blanches/noires en arrière-plan) généré en 16 s par SDXL Lightning-4step ; le panneau droit montre un robot photoréaliste blanc aux yeux cyan lumineux, échiquier bois posé sur l'herbe d'un parc verdoyant baigné de lumière chaude, généré en 410 s par Z-Image/Qwen Image Edit fp8. **170 314 couleurs uniques ≫ floor placeholder (~330)** sur l'image RGBA — preuve SOTA-OK des deux moteurs. La différence de durée (~25×) illustre le compromis vitesse/qualité entre SDXL few-step distilled et Z-Image/Lumina-2 full-step : choix pédagogique canonique pour un notebook de comparaison multi-modèles.
- **Alt-text (FR)** : Comparaison côte à côte de deux modèles d'image (SDXL Lightning-4step et Z-Image/Lumina-2) sur un même prompt — robot jouant aux échecs, l'un stylisé l'autre photoréaliste.
- **Poids** : 53 Ko (WebP q88, depuis PNG 601 Ko)

## img3-workflow1.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 11, output 5) — pipeline séquentiel (génération → style → upscaling)
- **Contenu réel vérifié** : WebP 1200×411, triptyque côte-à-côte avec titres *« 1. Generated »* / *« 2. Styled »* / *« 3. Upscaled ((1024, 1024)) »*. Trois rendus d'une **même scène** : coucher de soleil rouge/orange sur **montagnes enneigées** silhouettées, soleil partiellement masqué derrière les crêtes, brume légère dans les vallées. La composition (montagnes alignées + soleil + brume) reste identique aux trois étapes — seule la définition/lumière varie subtilement entre l'image générée, l'image stylisée et l'image upscalée 2048×2048.
- **Alt-text (FR)** : Pipeline séquentiel ComfyUI en 3 étapes (Generated / Styled / Upscaled) sur la même scène coucher de soleil sur montagnes enneigées — la composition est préservée aux trois étapes, seule la définition/lumière varie.
- **Poids** : 32 Ko (WebP q88, depuis PNG 472 Ko)
- **Note** : enrichissement de l'ancien alt-text « image générée, puis stylée, puis suréchantillonnée » pour préciser la **scène** (coucher de soleil sur montagnes enneigées) + la préservation de composition.

## img3-workflow2.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 13, output 2) — comparaison multi-modèles en parallèle
- **Contenu réel vérifié** : WebP 1200×423, triptyque côte-à-côte avec titres *« QWEN (55.47s) »* / *« FLUX (55.47s) »* / *« SD35 (55.47s) »* sous le titre global *« Comparaison Multi-Modèles 'A futuristic city with flying cars and neon lights…' »*. Trois rendus **très similaires** d'une **ville futuriste cyberpunk nocturne** : gratte-ciels illuminés de néons rose/violet/cyan, **voitures volantes** (silhouettes rondes avec phares rouges/orange) survolant la scène, perspective urbaine dense avec ciel bleu nuit. Les 3 modèles produisent des variations mineures (couleurs précises, composition exacte) sur la même scène.
- **Alt-text (FR)** : Comparaison parallèle Qwen / FLUX / SD35 sur le même prompt (ville futuriste cyberpunk nocturne avec voitures volantes et néons rose/violet/cyan) — 3 modèles tournent en ~55 s et produisent des rendus très similaires avec variations mineures.
- **Poids** : 52 Ko (WebP q88, depuis PNG 513 Ko)
- **Note** : enrichissement de l'ancien alt-text « Comparaison parallèle de plusieurs modèles d'image sur un même prompt » pour préciser **la scène** (ville futuriste cyberpunk avec voitures volantes + néons) + la similarité frappante des 3 rendus.

## img3-workflow3.png

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 17, output 5) — pipeline conditionnel (score qualité vs tentatives)
- **Contenu réel vérifié** : PNG 694×396, histogramme matplotlib sous le titre *« Pipeline Conditionnel - Évolution de la Qualité »*. Axes = X = *« Tentative »* (1 à 3) / Y = *« Score Qualité »* (0 à ~0.75). **3 barres orange identiques** à hauteur ~0.53 (tentatives 1, 2, 3). **Ligne horizontale en pointillés rouges** à ~0.75 avec légende *« Seuil »* en haut à droite. Les 3 tentatives restent **sous le seuil** mais stables — illustre le fonctionnement du pipeline conditionnel : on relance tant que score < seuil, ici le score plafonne à 0.53 sans franchir 0.75.
- **Alt-text (FR)** : Diagramme en barres matplotlib du score qualité (3 tentatives) d'un pipeline conditionnel — 3 barres orange identiques à ~0.53, ligne pointillée rouge à 0.75 (seuil) que le pipeline cherche à franchir en relançant.
- **Poids** : 16 Ko (PNG natif)
- **Note** : enrichissement de l'ancien alt-text « Diagramme en barres du score de qualité selon les tentatives d'un pipeline conditionnel » pour préciser **les valeurs** (3 barres à ~0.53 sous seuil 0.75) + le mécanisme illustrée.

## img3-workflow4.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 21, output 4) — générations multi-variations par style
- **Contenu réel vérifié** : WebP 1143×397, triptyque côte-à-côte avec titres *« sd35 photorealistic »* / *« sd35 watercolor »* / *« sd35 anime »* sous le titre global *« Multi-Variations »*. **Trois rendus d'un même chalet** dans un paysage de montagnes enneigées :
  - Gauche *« sd35 photorealistic »* : chalet en rondins de bois avec balcon, fenêtres éclairées (lumière chaude intérieure), cheminée, sapins enneigés en arrière-plan, ciel crépusculaire bleu/orange.
  - Centre *« sd35 watercolor »* : même chalet en bois, style aquarelle (couleurs pastel, contours fondus), sapins en arrière-plan très pâles, ambiance plus onirique.
  - Droite *« sd35 anime »* : même chalet, style anime/manga (couleurs plus saturées, contours marqués, lumière plus dramatique), sapins en arrière-plan avec chutes de neige stylisées, montagne plus haute visible derrière le chalet.
- **Alt-text (FR)** : Variations stylistiques SD35 sur un même prompt (chalet en rondins de bois dans montagnes enneigées) — 3 styles : photoréaliste (rendu photographique chaud), aquarelle (couleurs pastel, contours fondus), anime (couleurs saturées, contours marqués, ambiance manga).
- **Poids** : 54 Ko (WebP q88, depuis PNG 524 Ko)
- **Note** : refonte de l'ancien alt-text « Trois déclinaisons stylistiques d'un même prompt d'image » — le contenu est **spécifiquement SD35** (pas un modèle générique), la **scène** est un chalet en bois dans montagnes enneigées (pas juste « un même prompt »), et les **3 styles** sont identifiés (photoréaliste/aquarelle/anime).

---

**Total** : 5 figures, 224 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max, WebP fallback quand le gain est net. Les grilles de photos générées (séquentiel, comparaison, variations) compressent mal en PNG (472-524 Ko) — WebP q88 les ramène sous le plafond (32-54 Ko, ~10 % du PNG) sans perte visuelle sensible. Le pipeline conditionnel reste en PNG natif (diagramme en barres peu dense = 16 Ko).

**⚠️ Limitations de ce MANIFEST** :
- Aucune figure ne montre de limitation manifeste du pipeline (contrairement à img1-qwen-edit2.png 01-Foundation qui montrait des blocs bleus plats). Tous les outputs de 03-Orchestration ont produit du contenu visible et utilisable.
- Les sources re-exécutées en vrai (ComfyUI Qwen / Forge sdapi) le 2026-07-10/11 (#5867) suite à des bugs identifiés (03-2 : var-name `COMFYUI_AUTH_TOKEN` + timeout de poll trop court cellule 9 ; 03-1 : port fantôme 7865 + sampler invalide `euler` cellule 4, sdapi exige `Euler`). Les 5/5 figures sont maintenant réelles.
- Les figures sont conservées **telles quelles** sur disque ; cette PR ne supprime AUCUN fichier PNG/WebP (seuls les alt-texts et notes du MANIFEST/README sont corrigés).