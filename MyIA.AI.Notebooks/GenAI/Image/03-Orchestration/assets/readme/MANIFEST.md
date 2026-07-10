# MANIFEST des figures README — 03-Orchestration

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks). Convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule. Sources re-exécutées en vrai (ComfyUI Qwen) le 2026-07-10 — #5867 (racine causale : bug de var-name `COMFYUI_AUTH_TOKEN` + timeout de poll trop court dans la cellule 9, corrigés).

**Audit G.1 juillet 2026 — doctrine #5780 appliquée** : la figure `img3-multimodel.webp` a été **retirée** (cf `git rm`). Au moment de l'audit visuel par lecture directe des PNG/WebP commités, la figure ne montrait qu'une seule image *« Z-Image (214.73s), 1024×1024, Forge Offline »* — pas la grille multi-modèles annoncée par sa légende. Cause = à l'exécution de référence, seul le moteur Z-Image (via Forge) avait produit une sortie ; les autres moteurs (DALL-E 3, FLUX, Qwen via OpenAI API, etc.) étaient listés comme planifiés mais sans image rendue. Plutôt que conserver une légende misleading, doctrine « pas de Galerie, légende = ce que l'image MONTRE, choisir figure distinctive ou renoncer » s'applique : **renoncer**. Le comparatif multi-modèles reste un livrable à part dans le notebook `03-1` — sa version « vraie grille multi-modèles » (toutes cases renseignées) est tracker comme **RECOVERABLE-MACHINE/USER-HAND** dans le commentaire de review de c.342 (#5928) et sera livrée en PR séparée. Les 4 figures de `03-2-Workflow-Orchestration` sont vérifiées comme **vrais outputs** (séquentiel/parallèle/conditionnel/variations) et **conservées**, intégrées narrativement dans la section *Concepts clés / Workflow Orchestration* du README.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Source native |
|--------|---------|------------|-------|--------------------------------------|---------------|
| ~~Grille multi-modèles~~ | ~~`img3-multimodel.webp`~~ *(retirée — faux, doctrine #5780)* | 1182×596 | 67 Ko | `03-1-Multi-Model-Comparison.ipynb` · cellule 8 · output 2 | 1182×596, 542 Ko |
| Pipeline séquentiel | `img3-workflow1.webp` | 1200×411 | 32 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 11 · output 5 | 1500×500, 472 Ko (PNG) |
| Comparaison multi-modèles | `img3-workflow2.webp` | 1200×423 | 52 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 13 · output 2 | 1500×500, 513 Ko (PNG) |
| Pipeline conditionnel | `img3-workflow3.png` | 694×396 | 16 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 17 · output 5 | 800×400, 17 Ko (natif) |
| Générations multi-variations | `img3-workflow4.webp` | 1143×397 | 54 Ko | `03-2-Workflow-Orchestration.ipynb` · cellule 21 · output 4 | 1200×400, 524 Ko (PNG) |

**Total survivant** : 4 figures, 154 Ko (au lieu de 5 / 224 Ko). **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max, WebP fallback quand le gain est net. Les grilles de photos générées (séquentiel, comparaison, variations) compressent mal en PNG (472-524 Ko) — WebP q88 les ramène sous le plafond (32-54 Ko, ~10 % du PNG) sans perte visuelle sensible. Le pipeline conditionnel reste en PNG natif (diagramme en barres peu dense = 16 Ko).

## img3-workflow1.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 11, output 5) — pipeline séquentiel (génération → style → upscaling)
- **Contenu réel vérifié** (audit G.1 juillet 2026, doctrine #5780) : triptyque *« Pipeline Séquentiel : 1.Generated / 2.Styled / 3.Upscaled ((1024, 1024)) »* — coucher de soleil sur crêtes de montagnes, bois de conifères en premier plan, gradient rouge-orangé identique aux trois étapes. Les trois panneaux montrent l'effet d'un pipeline séquentiel : image initiale 1024×1024, puis stylée (même composition, rendu painterly), puis upscalée (2048×2048 avec détails affinés).
- **Alt-text (FR)** : Trois étapes d'un pipeline séquentiel : image Qwen générée, puis stylée, puis upscalée à 2048×2048
- **Poids** : 32 Ko (WebP q88, depuis PNG 472 Ko)

## img3-workflow2.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 13, output 2) — comparaison multi-modèles en parallèle
- **Contenu réel vérifié** (audit G.1 juillet 2026, doctrine #5780) : triptyque *« Comparaison Multi-Modèles : "A futuristic city with flying cars and neon lights…" »* — QWEN (55.47s), FLUX (55.47s), SD35 (55.47s). Trois panneaux côte-à-côte d'une cité futuriste avec voitures volantes et néons magenta/cyan. Chaque moteur a produit la même scène mais avec une esthétique différente : QWEN plus saturé néon, FLUX plus détaillé en arrière-plan, SD35 plus diffus. Les trois temps de génération identiques (55.47 s) confirment qu'ils ont tourné en parallèle.
- **Alt-text (FR)** : Grille de comparaison : Qwen, FLUX et SD35 produisent le même prompt en parallèle (~55 s chacun)
- **Poids** : 52 Ko (WebP q88, depuis PNG 513 Ko)

## img3-workflow3.png

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 17, output 5) — pipeline conditionnel (score qualité vs tentatives)
- **Contenu réel vérifié** (audit G.1 juillet 2026, doctrine #5780) : histogramme matplotlib *« Pipeline Conditionnel - Évolution de la Qualité »*, axe X = *Tentative* (1 à 3), axe Y = *Score Qualité* (0 à ~0.75). Trois barres orange uniformes à ≈0.53. Ligne rouge pointillée horizontale à 0.75 marquée « Seuil ». Montre la stabilisation du score sous le seuil — le pipeline re-tente mais ne franchit pas le seuil en 3 essais.
- **Alt-text (FR)** : Histogramme du score qualité par tentative d'un pipeline conditionnel, seuil rouge pointillé à 0.75
- **Poids** : 16 Ko (PNG natif)

## img3-workflow4.webp

- **Source** : notebook `03-2-Workflow-Orchestration.ipynb` (cellule 21, output 4) — générations multi-variations par style
- **Contenu réel vérifié** (audit G.1 juillet 2026, doctrine #5780) : triptyque *« Multi-Variations »* — *sd35 photorealistic* / *sd35 watercolor* / *sd35 anime*. Trois chalets de montagne sous la neige avec des traitements stylistiques distincts : photoréaliste avec fenêtres illuminées warm, aquarelle avec contours estompés, anime avec contours marqués et couleurs saturées. Géométrie (chalet + sapins + montagne enneigée) conservée, seule l'apparence change.
- **Alt-text (FR)** : Trois variations stylistiques sur un même prompt : photoréaliste, aquarelle, anime
- **Poids** : 54 Ko (WebP q88, depuis PNG 524 Ko)
