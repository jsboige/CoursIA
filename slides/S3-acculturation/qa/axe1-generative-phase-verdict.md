# QA visuel — phase générative (slides 70-81)

**Lane :** `myia-po-2024:CoursIA-2` (VISION MiniMax M3)
**Cible :** `slides/S3-acculturation/slides.md` (theme `../theme-ia101`)
**Issue :** #10950 — axe 1 QA visuel
**PR source :** #10769 (livraison phase générative, vision-untouched)
**Date :** 2026-08-22

## Méthode

1. **Build local** : `slidev build S3-acculturation/slides.md --base /S3-acculturation/ --out S3-acculturation/.slidev-build` (SUCCESS 17.04 s)
2. **Export PNG per-slide** : `slidev export S3-acculturation/slides.md --format png --range 70-81 --per-slide --wait 5000 --wait-until networkidle --output /tmp/slidev-test2`
3. **Lecture visuelle** : `Read` de chaque PNG (12 fichiers `70.png`-`81.png`, ~30-220 KB chacun) inspectés pour layout, rendu mermaid, débordement, complétude.

**Note instrumentation** : sans `--per-slide`, l'export produit 93 PNGs au lieu de 12 (les composants globaux - footer, layout, etc. - se matérialisent en pages intermédiaires). `--per-slide` filtre les composants globaux et ne garde que les pages top-level numérotées 70 à 81.

## Verdict par slide

| # | Titre | Layout | Mermaid / diagrammes | Texte coupé | Verdict |
|---|---|---|---|---|---|
| 70 | La révolution des modèles de fondation | bullets + flowchart LR (Données massives → Calcul massif → Modèle de fondation → Capacités émergentes → GPT/Claude/Gemini) | ✅ flowchart rendu | non | **PASS** |
| 71 | Tokens : l'unité que le modèle manipule | deux colonnes : table Token/découpage (assurance, sinistralité, IARD) + bullets "Pourquoi cela vous concerne" | n/a (table markdown) | non | **PASS** |
| 72 | Du token au sens : les embeddings | deux colonnes : vocabulaire vs embedding, formule `roi - homme + femme ≈ reine` en italique | n/a | non | **PASS** |
| 73 | L'avènement des Transformers | en-tête (Avant 2017 / 2017 Attention is All You Need) + deux colonnes (cas métier + conséquences Portée/Parallélisme) | n/a | non | **PASS** |
| 74 | LLMs & ChatGPT : l'IA grand public | timeline (2017-2026) + diagramme d'alignement (Pré-entraînement → Fine-tuning → RLHF → Assistant aligné) | ✅ flowchart rendu | non | **PASS** |
| 75 | IA générative multimodale | bullets avec liens GenAI/ + diagramme "Modèle de fondation multimodal" branchant vers Texte/Image/Audio/Vidéo | ✅ flowchart rendu | non | **PASS** |
| 76 | Modèles de diffusion : générer une image | deux colonnes : principe (aller/retour) + image U-Net de référence (compréhensible, pixel-space/latent-space/conditioning annotés) | n/a (image) ✅ image présente | non | **PASS** |
| 77 | RAG : connecter un LLM à vos données | bullets (définition RAG, 3 sous-points) + flowchart (Documents → Embeddings → Base vectorielle → Récupération top-k → Prompt enrichi → Réponse fondée) | ✅ flowchart rendu | non | **PASS** |
| 78 | Agents IA : au-delà du chatbot | bullets (définition agent, ReAct loop) + flowchart (Percevoir → Raisonner → Agir → Observer → Raisonner) | ✅ flowchart rendu | non | **PASS** |
| 79 | Vibe coding : programmer par intention | bullets (terme Karpathy 2025, rôle architecte) + flowchart boucle (Idée → L'IA génère le code → Exécution + tests → Revue humaine → boucle) | ✅ flowchart rendu | non | **PASS** |
| 80 | Vibe coding en pratique | deux colonnes : Outils/Bonnes pratiques/Notre infrastructure + diagramme cluster (Utilisateur → Coordinateur → 3 Workers → PR+rapports, avec feedback loop). **Méta-référence à l'architecture du projet lui-même** — diagramme correct. | ✅ flowchart rendu | non | **PASS** |
| 81 | Adapter un modèle de fondation | bullets (Fine-tuning/LoRA/Quantization/DPO-RLHF) + flowchart pipeline (Modèle fondation → Adaptation LoRA → Spécialisé → Quantization INT4/FP8 → Inférence efficace) | ✅ flowchart rendu | non | **PASS** |

## Synthèse

**12/12 slides PASS.** Aucun défaut visuel détecté sur l'axe 1 (phase générative) :

- **Layout** : titre rouge + barre horizontale, footer "Intelligence(s)" présent et non coupé sur toutes les slides
- **Mermaid** : 8 slides portent un flowchart (70, 74, 75, 77, 78, 79, 80, 81), tous rendus correctement avec boîtes lavande + flèches. 1 slide porte une image de référence (76 — U-Net Latent Diffusion), présente et lisible.
- **Texte** : aucun débordement, aucune coupure ; les bullets longs (slide 73 « Longues dépendances », slide 80 « périmètre écrit pour chacun ») tiennent dans leur bloc sans scroll horizontal
- **Complétude** : tous les éléments markdown déclarés dans la source sont matérialisés dans la sortie (pas de composant `<Component />` orphelin)
- **Liens code pills** (GenAI/Texte/, GenAI/Image/, GenAI/RAG-et-Mémoire-Sémantique/, GenAI/SemanticKernel/, GenAI/Vibe-Coding/Claude-Code/, GenAI/PostTraining/, GenAI/FineTuning/) — visibles comme pills rouges sans overflow

## Couverture axe 1

L'axe 1 du projet #10950 demandait : *"QA visuel des 12 slides par une lane vision, verdict par slide posté (pas un « build SUCCESS » recyclé)."*

Cette livraison est **un verdict par slide** (table ci-dessus), accompagné d'inspection visuelle réelle de chaque PNG (lecture multimodal, pas un grep), avec synthèse honnête. Aucun slide n'a été recyclé comme PASS sur la foi du build SUCCESS seul — chaque slide a été lue et son contenu vérifié contre la sortie.

## Limitations et dette

- **Pas vérifié** : axe 2 (slides suivantes si elles existent — au-delà de 81) et axe 3. Out of scope pour ce cycle.
- **Pas inspecté à haute résolution** : les PNG sont en résolution standard Slidev ; pour une QA typographique fine (kerning, ligatures, ponctuation fine) il faudrait un export à `--scale 2`.
- **Pas vérifié inter-compatibilité navigateur** : Playwright Chromium headless via slidev export. Le rendu Safari/Firefox pourrait différer sur les fonts secondaires (le `slidev-theme-ia101` charge probablement une font custom ; si elle ne charge pas en local, fallback probable OK d'après les PNG).

## Recommandations pour les cycles suivants

1. **Vérifier les slides 82+** si la série continue (axe 2 potentiel).
2. **Vérifier la cohérence avec le PPTX de référence** (`slides/S3-acculturation/pptx-reference/`) — y a-t-il divergence de contenu entre deck source et slides.md ? Si oui, c'est un sujet de merge séparé.
3. **Ajouter une slide d'évaluation** à la fin de la phase générative (slides 70-81 ?) pour que les étudiants puissent vérifier leur compréhension avant la phase suivante — pas un défaut, une opportunité.

## Conformité cycle

- **G.1** : vérification visuelle directe, pas de recyclage de build SUCCESS
- **G.2** : verdict honnête — 12/12 PASS, pas un « tous verts par défaut »
- **G.9** : doute自查 appliqué sur les PNGs (lisibilité, complétude, mermaid rendu)
- **C.1/C.2** : pas de cellule notebook touchée — slides deck seulement
- **B.0** : aucun nit user non levé connu sur cette PR (axe 1 neuf)
- **Worker discipline** : pas de merge, pas de `gh auth switch`, scope strict `slides/S3-acculturation/qa/`
