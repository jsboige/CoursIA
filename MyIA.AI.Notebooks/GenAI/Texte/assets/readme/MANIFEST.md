# Manifeste des figures — GenAI Texte

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

> **Audit vision po-2025 c.479 (2026-07-14, doctrine #5780)** : les 3 PNG ci-dessous ont été ouvertes un par un via l'outil `Read` et confrontées à leur description. Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = **3/3 exacte** — toutes les figures sont des **sorties matplotlib authentiques** (line-art, axes annotés, légendes explicites) qui correspondent **fidèlement** à leur description pédagogique (scaling pass@k, frontière compute-optimal BoN/Réflexion, comparaison cost-normalisée Snell). **0 correction d'alt-text nécessaire** ; le seul changement est la **migration du format table vague-1 vers le format liste détaillé standard** (pattern c.469-c.478), avec ajout du champ *Contenu réel vérifié* par figure + un audit-block en tête pour la traçabilité G.1.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Sujet |
|--------|---------|------------|-------|--------------------------------------|-------|
| Scaling pass@k | `texte-scaling-passk.png` | 715×462 | 33 Ko | `16_Scaling_Test_Time_Compute.ipynb` · cellule 8 · output 0 | Courbes de scaling pass@k par bucket de difficulté (Snell 2024) |
| BoN vs Réflexion | `texte-bon-vs-reflex.png` | 715×462 | 24 Ko | `16_Scaling_Test_Time_Compute.ipynb` · cellule 11 · output 0 | Best-of-N parallèle vs Réflexion séquentielle — frontière compute-optimal |
| Raisonnement vs Scaling | `texte-reason-vs-scale.png` | 770×505 | 50 Ko | `17_Native_Reasoning_vs_Scaling.ipynb` · cellule 11 · output 0 | Raisonnement natif vs scaling hand-rolled, comparaison cost-normalisée |

**Total** : 3 figures, 105 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Ces sorties sont des **courbes matplotlib** (line-art + étiquettes de texte) : **PNG lossless natif** préféré à WebP pour préserver la netteté du texte (plots déjà petits, 23–50 Ko natifs). 3 figures = toutes les sorties PNG du module (pas de padding). Arc narratif : (1) scaling du test-time compute — combien d'échantillons pour quelle difficulté ; (2) compute-optimal — parallèle vs séquentiel à budget égal ; (3) cost-normalisé Snell — le raisonnement natif d'un gros modèle vaut-il un scaling hand-rolled ?

---

## Détail vérifié figure par figure (audit vision c.479)

### texte-scaling-passk.png

- **Description** : Scaling du test-time compute (BoN) par difficulté — courbes pass@k vs budget d'échantillons pour 3 niveaux (facile / moyen / difficile).
- **Contenu réel vérifié** : Figure 715×462, titre centré en haut « Scaling du test-time compute (BoN) par difficulte ». **Axes annotés explicitement** : axe X = « Budget d'echantillons k (test-time compute) » avec valeurs discrètes 1, 2, 4, 6 ; axe Y = « pass@k (taux de succes estime) » de 0.0 à 1.0. **3 courbes de marqueurs** (lignes simples avec cercles) :
  - **Facile (vert)** : plateau à 1.0 sur tout le budget k=1→6 (le modèle résout déjà dès k=1)
  - **Moyen (bleu)** : plateau à 1.0 sur tout le budget k=1→6 (résolu tôt aussi)
  - **Difficile (rouge)** : montée monotone de ~0.38 (k=1) → ~0.54 (k=2) → ~0.67 (k=4) → ~0.75 (k=6)

  Légende en bas-gauche « difficulte » avec les 3 codes couleur. **Alt-text et figure cohérents** : illustre le principe du scaling BoN — les problèmes faciles saturent rapidement, les difficiles bénéficient marginalement du budget supplémentaire mais sans converger vers 1.0 dans la plage observée.
- **Note** : référence implicite à Snell 2024 (scaling laws for test-time compute) — choix pédagogique pertinent pour ouvrir sur la discussion compute-optimal.

### texte-bon-vs-reflex.png

- **Description** : Compute-optimal — BoN parallèle vs Réflexion séquentielle — taux de succès par bucket pour les 2 stratégies à budget égal (K=4).
- **Contenu réel vérifié** : Figure 715×462, titre centré en haut « Compute-optimal : strategie gagnante selon la difficulte ». **Axe Y** = « Taux de succes » de 0.0 à 1.0 ; **axe X** = 3 buckets discrets (facile / moyen / difficile) sans label d'axe explicite. **6 barres groupées par 2** (BoN orange + Réflexion violet) :
  - **Facile** : BoN = 1.00, Réflexion = 1.00 → **egal**
  - **Moyen** : BoN = 1.00, Réflexion = 1.00 → **egal**
  - **Difficile** : BoN = ~0.67, Réflexion = ~0.50 → **BoN gagne**

  Légende en haut-droite : « BoN parallele (pass@4) » orange × « Reflexion sequentielle (K=4) » violet. **Alt-text et figure cohérents** : illustre le résultat pédagogique clé — pour les problèmes difficiles, le **parallélisme BoN** est plus compute-efficace que la **réflexion séquentielle** (à budget tokens égal). Note : pour les problèmes faciles/moyens, les deux stratégies atteignent le plafond donc sont équivalentes — la discrimination est sur le bucket difficile.
- **Note** : comparaison côte-à-côte (grouped bars) = choix lisible ; le verdict « BoN gagne » est implicite (hauteur de barre) sans annotation texte additionnelle.

### texte-reason-vs-scale.png

- **Description** : Raisonnement natif (deepseek-r1) vs scaling hand-rolled (BoN llama-3.3-70b-instruct), comparaison cost-normalisée (axe X = tokens dépensés).
- **Contenu réel vérifié** : Figure 770×505, titre centré en haut « Raisonnement natif vs scaling hand-rolled (cost-normalise) ». **Axes annotés explicitement** : axe X = « Tokens depenses (cout test-time compute) » de 0 à 700 ; axe Y = « Taux de succes (pass@k / single-shot) » de 0.0 à 1.0. **6 séries** (3 buckets × 2 stratégies), toutes à pass-rate = 1.0 sauf la courbe rouge :
  - **BoN facile (vert cercles)** : plateau 1.0 de x≈40 à x≈300
  - **r1 facile (vert croix)** : 1 point isolé à x≈300, y=1.0 (single-shot)
  - **BoN moyen (bleu cercles)** : plateau 1.0 de x≈40 à x≈300
  - **r1 moyen (bleu croix)** : 1 point isolé à x≈575, y=1.0
  - **BoN difficile (rouge cercles)** : montée monotone de ~0.16 (x=40) → ~0.29 (x=110) → ~0.43 (x=210) → ~0.49 (x=300)
  - **r1 difficile (rouge croix)** : 1 point isolé à x≈735, y=1.0

  Légende en bas-droite listant les 6 séries. **Alt-text et figure cohérents** : illustre la question Snell 2024 — pour les problèmes difficiles, le **modèle à raisonnement natif** (deepseek-r1) atteint **100% en single-shot** alors qu'il faut ~300 tokens de BoN llama-3.3-70b-instruct pour atteindre 49%. **Le point r1 difficile se situe au-dessus de la courbe BoN difficile extrapolée** → raisonnement natif gagne au coût-égal pour le bucket difficile. Pour facile/moyen, BoN sature rapidement donc les deux stratégies sont équivalentes au plafond.
- **Note** : les marqueurs différents (cercle pour BoN, X pour r1 single-shot) permettent de distinguer visuellement « courbe d'effort » vs « point d'arrivée » — choix pédagogique très clair.

## Note méthodologique — figures pédagogiques matplotlib authentiques

Cette série est **4ᵉ dans le rollout** à présenter exclusivement des **figures matplotlib authentiques** (après #6446 c.475 GenAI/Image/examples qui montrait 6/6 GenAI riches, #6451 c.476 GenAI/Video/03 1/5 réussie, #6453 c.478 SocialChoice 6/6 ACCURATE, et maintenant #c.479 GenAI/Texte 3/3 ACCURATE). Les 3 figures GenAI/Texte sont des **diagrammes académiques** (résultats d'expérience, pas des œuvres artistiques), avec exigence de **rigueur quantitative** :

- **Axes annotés explicitement** (noms de variables, unités, échelles)
- **Légendes identifiant les séries** (BoN/Réflexion, llama/deepseek, bucket difficulté)
- **Couleurs sémantiques** (vert facile / bleu moyen / rouge difficile)
- **Titres explicites** en français (« Scaling du test-time compute... », « Compute-optimal : strategie gagnante selon la difficulte », « Raisonnement natif vs scaling hand-rolled (cost-normalise) »)

**Pattern transférable** : pour les familles à dominante matplotlib (Texte, SocialChoice, GameTheory, Search/*, ML, Probas), la rigueur des **annotations** (variables, légendes, unités) est presque toujours au rendez-vous. Le travail d'audit consiste principalement à vérifier la **fidélité des annotations au contenu effectif**, pas à corriger des sur-ventes majeures. **0 bug détecté sur les 3 figures** : la table c.479 MANIFEST est **plus proche du standard** que les vagues 1-2 (SymbolicLearning/Image), ce qui réduit le travail de migration à un simple changement de format.

**Contraste avec c.476 GenAI/Video/03** : c.476 = 1/5 ACCURATE (modèles vidéo GenAI à dimension temporelle = dérive fréquente sur prompts concrets) ; **c.479 GenAI/Texte = 3/3 ACCURATE** (sorties matplotlib de notebook = annotations fidèles par construction). Les deux PRs traitent **deux états différents du même déploiement pédagogique**.

## Conformité règles

- **§A single-subject** : 1 sujet (audit figures GenAI/Texte), 1 domaine (GenAI Texte), 1 fichier. Bien sous plafond 3000L.
- **§E doctrine corrigée** (issue #5780) : pas de section `## Galerie`, figures inline dans le tableau récapitulatif + section *Contenu réel vérifié* en lecture linéaire, légende/alt-text décrivent le contenu réel de l'image vérifié par lecture directe.
- **R1 catalog-pr-hygiene** : `git diff origin/main..HEAD -- "**/CATALOG-STATUS*" "**/COURSE_CATALOG*"` = vide. Catalogue byte-identique à main.
- **L268 #4 LF-only** : `git diff | tr -cd '\r' | wc -c` = 0. Pas de retour chariot dans le diff.
- **L143 secrets-hygiene** : `grep -nE "sk-|ghp_|AIza|password=|secret="` sur le diff = 0 hit (l'unique hit est la règle elle-même dans la section *Conformité règles*).