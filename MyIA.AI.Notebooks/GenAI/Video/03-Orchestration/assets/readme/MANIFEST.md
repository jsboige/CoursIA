# Manifeste des figures — Video 03-Orchestration

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

> **Audit vision po-2025 c.476 (2026-07-14, doctrine #5780)** : les 5 WebP ci-dessous ont été ouvertes un par un via l'outil `Read` et confrontées à leur description de MANIFEST. Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = **1/5 exacte + 1/5 partielle + 3/5 mismatch** — **3 corrections d'alt-text appliquées**. Constat pédagogique majeur : plusieurs figures (vid3-frame2 batch multi-prompts, vid3-comfyui "lac au couchant") illustrent **la dérive qualité** des modèles vidéo GenAI (LTX-Video, AnimateDiff) sur des prompts concrets — utile pédagogiquement (montre la capacité ET la limite des moteurs), mais le MANIFEST les légendait comme si les outputs étaient pleinement réussis, créant un **sous-vente de la dérive**. Migration du format vague-1 (table sans Alt-text explicite) vers le format liste détaillé standard, avec ajout du champ *Contenu réel vérifié* par figure + section *Détail vérifié figure par figure (audit vision c.476)* post-tableau.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Source native |
|--------|---------|------------|-------|--------------------------------------|---------------|
| Image source SDXL (pipeline text→image→vidéo) | `vid3-workflow1.webp` | 819×490 | 6 Ko | `03-2-Video-Workflow-Orchestration.ipynb` · cellule 8 · output 3 | 819×490, 10 Ko |
| Pipeline text→image→vidéo — planche-contact (source + frames 1-25) | `vid3-workflow2.webp` | 1200×201 | 8 Ko | `03-2-Video-Workflow-Orchestration.ipynb` · cellule 8 · output 10 | 1790×300, 113 Ko |
| Comparatif brut vs upscale + interpolation (LTX-Video, marguerite) | `vid3-frame1.webp` | 1200×531 | 40 Ko | `03-2-Video-Workflow-Orchestration.ipynb` · cellule 10 · output 9 | 1589×704, 984 Ko |
| Batch multi-prompts LTX-Video (océan / torche / montagnes, 3×4 frames) | `vid3-frame2.webp` | 1200×723 | 46 Ko | `03-2-Video-Workflow-Orchestration.ipynb` · cellule 12 · output 14 | 1389×837, 913 Ko |
| ComfyUI AnimateDiff — frames 1-8/16 (lac au couchant) | `vid3-comfyui.webp` | 1200×606 | 82 Ko | `03-3-ComfyUI-Video-Workflows.ipynb` · cellule 9 · output 4 | 1560×788, 1697 Ko |

**Total** : 5 figures, 185 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Les frames vidéo GenAI sont des images photographiques denses (sources 913–1697 Ko) : WebP q82 à 1200 px bat massivement le PNG (ex. frame 1 : 984 Ko → WebP 1200 px 40 Ko vs PNG 600 px 162 Ko — 2× la résolution pour 4× moins de poids). C'est la recommandation WebP P2 « quand le gain est net ».

---

## Détail vérifié figure par figure (audit vision c.476)

### vid3-workflow1.webp

- **Description (MANIFEST original)** : Image source SDXL (pipeline text→image→vidéo).
- **Description (corrigée c.476)** : Image source SDXL abstraite — **rectangle noir fin vertical avec ovale jaune pâle sommital**, sur fond dégradé mauve→orange. L'aspect évoque une **allumette / pilule stylisée géométrique abstraite**, pas une image concrète (pas de personnage / objet identifiable).
- **Contenu réel vérifié** : Image 819×490, titre intégré en haut « Image source (sdxl) generee en 8.1s ». **Constat** : SDXL a généré une **image abstraite géométrique simple** plutôt qu'une scène d'illustration concrète. Le titre intégré est factuellement correct ("sdxl, 8.1s") mais **sur-vend la fonction pédagogique** : présenté comme "image source" d'un pipeline alors que c'est juste un output stylisé SDXL. **Dérive qualitative attendue d'un modèle SDXL appelé avec un prompt vague** — utile pédagogiquement pour montrer les limites de SDXL sur ce type de brief, mais le MANIFEST n'en faisait pas mention.
- **Type pédagogique** : exemple de **sortie SDXL abstraite / non-illustrative** — utile pour ouvrir une discussion sur la qualité des prompts vs la qualité du rendu.

### vid3-workflow2.webp

- **Description** : Pipeline text→image→vidéo — planche-contact (source + frames 1-25).
- **Contenu réel vérifié** : Planche-contact horizontale, format 1200×201 (très compact). Titre intégré « Pipeline Text → Image -> Video ». **5 frames étiquetées** : « Source (sdxl) » (la même allumette abstraite de vid3-workflow1) → « Frame 1 » (allumette dégradée floue) → « Frame 9 » (ovale jaune seul détaché, fond mauve) → « Frame 17 » (forme composite : visage abstrait + ovale jaune mêlés) → « Frame 25 » (silhouette mauve verticale + ovale à droite). **Constat** : le pipeline est réel et illustre bien une **propagation temporelle**, mais **les frames divergent fortement de la source** — la dérive qualitative est manifeste (allumette → ovale seul → forme composite → silhouette). La planche-contact illustre donc **une dérive pipeline visible**, plus qu'une transformation fidèle. **Alt-text et figure cohérents** sur l'intention (montrer le pipeline), mais la dérive visible n'était pas disclosed dans le MANIFEST original.
- **Type pédagogique** : exemple de **dérive pipeline text→image→vidéo** — utile pour ouvrir une discussion sur la propagation des artefacts d'un étage à l'autre.

### vid3-frame1.webp

- **Description** : Comparatif brut vs upscale + interpolation (LTX-Video, marguerite).
- **Contenu réel vérifié** : Comparatif 2×4 frames, format 1200×531. Titre intégré « Pipeline : Brut vs Upscale + Interpolation ». **Ligne du haut "Brut"** : 4 frames (1, 9, 17, 25) d'une même marguerite blanche (fleurs à pétales fins jaunes au centre, tige verte sur fond flou verdâtre) — focus doux, qualité photo relativement basse. **Ligne du bas "Final"** : 4 frames (1, 17, 33, 49) de la même marguerite — focus plus net, pétales mieux définis, bruit réduit. **Constat** : marguerite clairement identifiable, **comparatif brut vs final réussi** : upscale + interpolation lisse effectivement la marguerite (pétales mieux définis, arrière-plan moins bruité). **Alt-text et figure cohérents** sur le contenu ET sur l'effet pédagogique (montrer la valeur ajoutée de l'upscale + interpolation).
- **Type pédagogique** : exemple de **comparatif réussi avant/après** — utile pour démontrer l'apport qualité de l'upscale + interpolation LTX-Video.

### vid3-frame2.webp

- **Description (MANIFEST original)** : Batch multi-prompts LTX-Video (océan / torche / montagnes, 3×4 frames).
- **Description (corrigée c.476)** : Batch multi-prompts LTX-Video (3 lignes × 4 frames) **avec dérive qualitative visible** : la ligne «océan» dérive vers des reflets crépusculaires sans étendue océan identifiable ; la ligne «torche» génère une forme floue orangée type bougie/lumignon plutôt qu'une torche vive ; la ligne «montagnes» produit un paysage crépusculaire avec strates montagneuses visibles mais secondaires. Le contenu sémantique exact est suggéré plus que rendu.
- **Contenu réel vérifié** : Batch 3×4 frames, format 1200×723. Titre intégré « Generation Batch - LTX-Video ». **Ligne 1 «océan»** : 4 frames d'un ciel crépusculaire mauve-rose se reflétant sur eau — vagues/ondulations mais **pas clairement un océan profond identifiable** (ressemble à un plan d'eau calme au crépuscule). **Ligne 2 «torche»** : 4 frames d'une forme floue lumineuse centrale orangée avec halo diffus — **pas une torche reconnaissable** (plutôt bougie allumée, lumignon, ou flamme abstraite). **Ligne 3 «montagnes»** : 4 frames d'un coucher de soleil orange-rougeoyant sur couches montagneuses en arrière-plan — **paysage crépusculaire avec strates montagnardes visibles mais secondaires**, l'attention du modèle a été accaparée par le ciel crépusculaire. **Constat** : **chaque prompt produit une interprétation approximative**. Le **format batch multi-prompts** est respecté (3 prompts, 4 frames chacun) mais le **contenu sémantique exact dérive**. **Pédagogiquement utile** pour montrer les limites de LTX-Video sur des prompts concrets : océan↔eau crépusculaire, torche↔lumignon, montagnes↔ciel.
- **Type pédagogique** : exemple de **dérive qualitative sur batch multi-prompts** — utile pour discuter de la sensibilité du modèle au prompt engineering.

### vid3-comfyui.webp

- **Description (MANIFEST original)** : ComfyUI AnimateDiff — frames 1-8/16 (lac au couchant).
- **Description (corrigée c.476)** : ComfyUI AnimateDiff — frames 1-8/16 générant **une palette coucher de soleil spectaculaire (or/orange sur bleu profond)** sous forme de **bandes horizontales ondulées type reflets sur eau**, mais **sans contenu sémantique identifiable de lac** (pas de ligne d'horizon nette, pas de rive, pas d'étendue d'eau continue). AnimateDiff a généré une **palette + ambiance** cohérente avec le prompt "serene lake at sunset" mais sans la **structure spatiale** attendue.
- **Contenu réel vérifié** : Batch 2×4 frames, format 1200×606. Titre intégré « ComfyUI AnimateDiff : a serene lake at sunset, soft ripples on water, go... » (prompt tronqué, longueur cellule). **8 frames** : alternance de bandes horizontales ondulées jaune-or fluo sur bleu profond, puis jaune-or sur bleu plus sombre — **style impressionniste abstrait** type Monet (Nymphéas / soleil couchant). Aucune ligne d'horizon, aucune rive, aucun élément figuratif identifiable. **Constat** : la **palette coucher de soleil est présente et spectaculaire** (or / orange fluo sur bleu), l'animation ondulation est visible entre frames, mais le **sujet "lac"** (étendue d'eau identifiable, reflet net, ligne d'horizon) est **absent**. AnimateDiff a généré une **texture/ambiance** sans le **sujet concret**. **Dérive qualitative significative** vs l'attente du prompt.
- **Type pédagogique** : exemple de **lacuna structurale AnimateDiff** — utile pour montrer la capacité à générer palette/ambiance sans structure spatiale identifiable. **Alternative possible** : régénérer avec un prompt plus structurant (ex. "wide shot, horizontal line dividing sky from lake surface, distant mountains") pour voir si AnimateDiff peut produire un vrai lac — à discuter en classe.

## Constat méthodologique — dérive qualitative vs succès

| Figure | Type attendu (prompt) | Type observé | Niveau de succès |
|--------|----------------------|--------------|------------------|
| vid3-workflow1 | image source concrète | rectangle abstrait | Très partiel |
| vid3-workflow2 | propagation temporelle | propagation + dérive qualitative | Partiel — montre la dérive |
| vid3-frame1 | comparatif marguerite focus | comparatif marguerite réussi | Réussi |
| vid3-frame2 | batch océan/torche/montagnes | batch eau/lumignon/paysage crépusculaire | Très partiel |
| vid3-comfyui | lac au couchant | palette coucher de soleil sans lac | Très partiel |

**Bilan** : **1/5 figure illustre pleinement son concept** (vid3-frame1 — comparatif marguerite). Les 4 autres illustrent **la dérive qualitative** des modèles vidéo GenAI sur des prompts concrets. **Utile pédagogiquement** (montre les limites), mais **le MANIFEST les présentait comme des succès**, créant un **sous-vente de la dérive**.

## Conformité règles

- **§A single-subject** : 1 sujet (audit figures GenAI/Video/03), 1 domaine (GenAI Video), 1 fichier. Bien sous plafond 3000L.
- **§E doctrine corrigée** (issue #5780) : pas de section `## Galerie`, figures inline dans le tableau récapitulatif + section *Contenu réel vérifié* en lecture linéaire, légende/alt-text décrivent le contenu réel de l'image vérifié par lecture directe.
- **R1 catalog-pr-hygiene** : `git diff origin/main..HEAD -- "**/CATALOG-STATUS*" "**/COURSE_CATALOG*"` = vide. Catalogue byte-identique à main.
- **L268 #4 LF-only** : `git diff | tr -cd '\r' | wc -c` = 0. Pas de retour chariot dans le diff.
- **L143 secrets-hygiene** : `grep -nE "sk-|ghp_|AIza|password=|secret="` sur le diff = 0 hit.