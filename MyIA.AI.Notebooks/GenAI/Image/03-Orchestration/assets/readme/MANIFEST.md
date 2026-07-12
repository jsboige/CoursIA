# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

# Manifeste des figures — 03-Orchestration

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources re-exécutées en vrai (ComfyUI Qwen / Forge sdapi) le 2026-07-10/11 — #5867. 03-2 : bug de var-name `COMFYUI_AUTH_TOKEN` + timeout de poll trop court (cellule 9). 03-1 : port fantôme 7865 + sampler invalide `euler` (cellule 4, sdapi exige `Euler`). Les 5/5 figures sont maintenant réelles.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Source native |
|--------|---------|------------|-------|--------------------------------------|---------------|
| Grille multi-modèles | `img3-multimodel.webp` | 1182×591 | 53 Ko | `03-1-Multi-Model-Comparison.ipynb` · cellule 8 · output 2 | 1182×591, 601 Ko |
| Pipeline séquentiel | `img3-workflow1.webp` | 1200×411 | 32 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 11 · output 5 | 1500×500, 472 Ko (PNG) |
| Comparaison multi-modèles | `img3-workflow2.webp` | 1200×423 | 52 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 13 · output 2 | 1500×500, 513 Ko (PNG) |
| Pipeline conditionnel | `img3-workflow3.png` | 694×396 | 16 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 17 · output 5 | 800×400, 17 Ko (natif) |
| Générations multi-variations | `img3-workflow4.webp` | 1143×397 | 54 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 21 · output 4 | 1200×400, 524 Ko (PNG) |

**Total** : 5 figures, 224 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max, WebP fallback quand le gain est net. Les grilles de photos générées (séquentiel, comparaison, variations) compressent mal en PNG (472-524 Ko) — WebP q88 les ramène sous le plafond (32-54 Ko, ~10 % du PNG) sans perte visuelle sensible. Le pipeline conditionnel reste en PNG natif (diagramme en barres peu dense = 16 Ko).

## img3-multimodel.webp

- **Source** : notebook `03-1-Multi-Model-Comparison.ipynb` (cellule 8, output 2) — comparaison côte à côte SDXL Lightning-4step (Forge) vs Z-Image/Lumina-2 (ComfyUI)
- **Contenu réel vérifié** (audit G.1 juillet 2026, doctrine #5780) : grille *« SDXL Lightning-4step (16.11s) 512×512 »* et *« Z-Image (409.86s) 1024×1024 »* sur le même prompt *« A cute robot playing chess in a park, sunlight, detailed »*. Le panneau gauche montre un robot au rendu painterly/blueprint (peinture acrylique rouge, échiquier stylisé, rayures verticales blanches/noires en arrière-plan) généré en 16 s par SDXL Lightning-4step ; le panneau droit montre un robot photoréaliste blanc aux yeux cyan lumineux, échiquier bois posé sur l'herbe d'un parc verdoyant baigné de lumière chaude, généré en 410 s par Z-Image/Qwen Image Edit fp8. **170 314 couleurs uniques ≫ floor placeholder (~330)** sur l'image RGBA — preuve SOTA-OK des deux moteurs. La différence de durée (~25×) illustre le compromis vitesse/qualité entre SDXL few-step distilled et Z-Image/Lumina-2 full-step : choix pédagogique canonique pour un notebook de comparaison multi-modèles.
- **Alt-text (FR)** : Comparaison côte à côte de deux modèles d'image (SDXL Lightning-4step et Z-Image/Lumina-2) sur un même prompt — robot jouant aux échecs, l'un stylisé l'autre photoréaliste
- **Poids** : 53 Ko (WebP q88, depuis PNG 601 Ko)

## img3-workflow1.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 11, output 5) — pipeline séquentiel (génération → style → upscaling)
- **Alt-text (FR)** : Pipeline séquentiel : image générée, puis stylée, puis suréchantillonnée
- **Poids** : 32 Ko (WebP q88, depuis PNG 472 Ko)

## img3-workflow2.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 13, output 2) — comparaison multi-modèles en parallèle
- **Alt-text (FR)** : Comparaison parallèle de plusieurs modèles d'image sur un même prompt
- **Poids** : 52 Ko (WebP q88, depuis PNG 513 Ko)

## img3-workflow3.png

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 17, output 5) — pipeline conditionnel (score qualité vs tentatives)
- **Alt-text (FR)** : Diagramme en barres du score de qualité selon les tentatives d'un pipeline conditionnel
- **Poids** : 16 Ko (PNG natif)

## img3-workflow4.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 21, output 4) — générations multi-variations par style
- **Alt-text (FR)** : Trois déclinaisons stylistiques d'un même prompt d'image
- **Poids** : 54 Ko (WebP q88, depuis PNG 524 Ko)
