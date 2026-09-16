# Manifeste des figures — GenAI Texte

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

> **Audit vision po-2025 c.479 (2026-07-14, doctrine #5780)** : les 3 PNG ci-dessous ont été ouvertes un par un via l'outil `Read` et confrontées à leur description. Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = **3/3 exacte** — toutes les figures sont des **sorties matplotlib authentiques** (line-art, axes annotés, légendes explicites) qui correspondent **fidèlement** à leur description pédagogique (scaling pass@k, frontière compute-optimal BoN/Réflexion, comparaison cost-normalisée Snell). **0 correction d'alt-text nécessaire** ; le seul changement est la **migration du format table vague-1 vers le format liste détaillé standard** (pattern c.469-c.478), avec ajout du champ *Contenu réel vérifié* par figure + un audit-block en tête pour la traçabilité G.1.

> **Migration canonical c.767 (2026-07-22, jsboige:CoursIA-2)** : ajout du champ **`Description visuelle`** (gist compact de ce qui est *visible* en un coup d'œil, distinct du `Contenu réel vérifié` détaillé) sur les 3 figures txt-*. Format aligné sur c.751 (GenAI/Audio racine, PR #7995) + c.763 (GenAI/Video/04-Applications, PR #8000) + c.764 (GenAI/Image/02-Advanced, PR #8002) + c.765 (GenAI/Video/03-Orchestration, PR #8007) + c.766 (GenAI/Open-WebUI/00-Tour-Plateforme, PR #8012) + modèle rollout #5780. 3/3 figures migrées, audit vision MiniMax M3 firsthand + PIL RGB mean+std à 80×80 (cf PR body). **Audit fondateur c.479 préservé verbatim** ci-dessus ; cette migration est purement additive (pas de suppression de contenu). **Pivot cross-famille strict** vs c.766 (Open-WebUI = nouveau sous-genre #5780, captures Playwright self-hosted) → Texte = sous-genre **matplotlib authentiques** (figures académiques Snell 2024). G-VAR-3 pivot obligatoire après 5 cycles MED/docs-figures-audit consécutifs sur sous-genres GenAI : c.751 (Audio racine) → c.763 (Video/04-Apps) → c.764 (Image/02-Advanced) → c.765 (Video/03) → c.766 (Open-WebUI/00) → c.767 (Texte/00) — famille distincte Open-WebUI → Texte, sous-genre distinct captures Playwright → matplotlib académique.

> **Re-extraction #16275 (2026-09-15, myia-po-2026:CoursIA)** : les 3 PNG étaient **périmés**. Ils avaient été exportés le 2026-07-08 depuis un run antérieur, alors que les notebooks 16 et 17 ont été **re-exécutés depuis** — leurs sorties committées sur `main` portent un autre run (`difficile` : 0.38/0.54/0.67/0.75 → **0.25/0.40/0.50/0.50**). Mesure, en pixels et non à l'œil : la figure committée de la cellule 8 différait du PNG sur disque de **13 146 px** (cellule 11 : **4 161 px** ; notebook 17 cellule 11 : **24 654 px**) — après re-extraction, **0 px** d'écart sur les trois. Les notebooks eux-mêmes étaient **cohérents** (table committée et figure committée du même run) : rien à re-exécuter, seul l'export avait dérivé. Champs *Description visuelle* / *Contenu réel vérifié* / *Alt-text* / *Poids* réalignés sur **le run committé** ; blocs d'audit c.479 et c.767 **préservés verbatim** (ce bloc est purement additif).

**Geste de régénération** — à rejouer après toute ré-exécution des notebooks 16/17 :

```bash
SR=MyIA.AI.Notebooks/GenAI/Texte
python scripts/notebook_tools/notebook_tools.py figures-extract "GenAI/Texte/16_Scaling_Test_Time_Compute.ipynb" \
  --cell 8 --output "$SR/assets/readme/texte-scaling-passk.png" \
  --alt "<alt-text FR>" --description-visuelle "<ce que la figure montre>" \
  --serie-root "$SR" --no-manifest
# idem --cell 11 sur 16_Scaling... et --cell 11 sur 17_Native_Reasoning_vs_Scaling.ipynb
```

**`--no-manifest` est obligatoire sur cette série** : les sections ci-dessous sont en `## <fichier>.png` (canonical c.767) et l'append par défaut de l'outil **remplace le bloc de même nom** — il détruirait les champs mesurés `Description visuelle` / `Contenu réel vérifié` et leurs blocs d'audit datés. Mesuré : sans le drapeau, `Contenu réel vérifié` passe de 6 à 5 occurrences sur ce fichier (l'option a été ajoutée par cette PR, avec un test de contrôle positif qui épingle ce comportement). **Aucun organe ne détecte aujourd'hui la dérive PNG ↔ sortie de cellule** — c'est le résidu de #16275, hors de ce correctif.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Sujet |
|--------|---------|------------|-------|--------------------------------------|-------|
| Scaling pass@k | `texte-scaling-passk.png` | 715×462 | 30,4 Ko | `16_Scaling_Test_Time_Compute.ipynb` · cellule 8 · output 0 | Courbes de scaling pass@k par bucket de difficulté (Snell 2024) |
| BoN vs Réflexion | `texte-bon-vs-reflex.png` | 715×462 | 23,1 Ko | `16_Scaling_Test_Time_Compute.ipynb` · cellule 11 · output 0 | Best-of-N parallèle vs Réflexion séquentielle — frontière compute-optimal |
| Raisonnement vs Scaling | `texte-reason-vs-scale.png` | 770×505 | 47,0 Ko | `17_Native_Reasoning_vs_Scaling.ipynb` · cellule 11 · output 0 | Raisonnement natif vs scaling hand-rolled, comparaison cost-normalisée |

**Total** : 3 figures, 100,5 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Ces sorties sont des **courbes matplotlib** (line-art + étiquettes de texte) : **PNG lossless natif** préféré à WebP pour préserver la netteté du texte (plots déjà petits, 23–47 Ko natifs). 3 figures = toutes les sorties PNG du module (pas de padding). Arc narratif : (1) scaling du test-time compute — combien d'échantillons pour quelle difficulté ; (2) compute-optimal — parallèle vs séquentiel à budget égal ; (3) cost-normalisé Snell — le raisonnement natif d'un gros modèle vaut-il un scaling hand-rolled ?

---

## Détail vérifié figure par figure (audit vision c.479 + canonical migration c.767)

## texte-scaling-passk.png

- **Source** : notebook `16_Scaling_Test_Time_Compute.ipynb` (cellule 8, output 0)
- **Description visuelle** : Line plot matplotlib 715×462 sur fond majoritairement **blanc cassé** (RGB 80×80 mean R247/G246/B246 std 21/21/21 — variance très basse, signature canonique d'un plot blanc avec peu de pixels colorés : les courbes + axes + grille occupent une fraction minoritaire de la surface), titre intégré en haut « Scaling du test-time compute (BoN) par difficulte ». **3 courbes de marqueurs cercles** : une **verte** (facile) et une **bleue** (moyen) qui forment un plateau horizontal à y=1.0 de x=1 à x=6 (ces deux courbes se superposent quasi exactement) ; une **rouge** (difficile) en montée de y=0.25 (x=1) → y=0.40 (x=2) → y=0.50 (x=4) → y=0.50 (x=6), plateau atteint dès x=4. **Grille pâle horizontale** (lignes pointillées à 0.2/0.4/0.6/0.8/1.0). **Légende en bas-gauche** listant les 3 codes couleur. Lecture pédagogique = le scaling BoN **sature rapidement** sur les buckets faciles/moyens (dès k=1) et **bénéficie marginalement** du budget supplémentaire sur le bucket difficile sans converger vers 1.0 dans la plage observée.
- **Contenu réel vérifié** : Figure 715×462, titre centré en haut « Scaling du test-time compute (BoN) par difficulte ». **Axes annotés explicitement** : axe X = « Budget d'echantillons k (test-time compute) » avec valeurs discrètes 1, 2, 4, 6 ; axe Y = « pass@k (taux de succes estime) » de 0.0 à 1.0. **3 courbes de marqueurs** (lignes simples avec cercles) :
  - **Facile (vert)** : plateau à 1.0 sur tout le budget k=1→6 (le modèle résout déjà dès k=1)
  - **Moyen (bleu)** : plateau à 1.0 sur tout le budget k=1→6 (résolu tôt aussi)
  - **Difficile (rouge)** : montée de 0.25 (k=1) → 0.40 (k=2) → 0.50 (k=4) → 0.50 (k=6), puis **plateau** (le budget supplémentaire ne gagne plus rien au-delà de k=4)

  Légende en bas-gauche « difficulte » avec les 3 codes couleur. **Alt-text et figure cohérents** : illustre le principe du scaling BoN — les problèmes faciles saturent rapidement, les difficiles bénéficient marginalement du budget supplémentaire mais sans converger vers 1.0 dans la plage observée.
- **Alt-text (FR)** : Scaling pass@k vs budget d'échantillons (BoN) par bucket de difficulté — courbe rouge « difficile » en montée 0.25→0.40→0.50→0.50 sur k=1→6 (plateau dès k=4), courbes verte « facile » et bleue « moyen » en plateau à 1.0 sur tout le budget (Snell 2024, scaling laws for test-time compute).
- **Poids** : 30,4 Ko (natif PNG 715×462)
- **Note** : référence implicite à Snell 2024 (scaling laws for test-time compute) — choix pédagogique pertinent pour ouvrir sur la discussion compute-optimal.

## texte-bon-vs-reflex.png

- **Source** : notebook `16_Scaling_Test_Time_Compute.ipynb` (cellule 11, output 0)
- **Description visuelle** : Bar plot matplotlib 715×462 (grouped bars) sur fond blanc cassé avec la palette **la plus saturée** des 3 figures (RGB 80×80 mean R229/G196/B190 std 41/65/88 — B plus étalé que R/G car le violet Réflexion tire B vers le haut, std B=90 le plus élevé des 3 figures), titre intégré « Compute-optimal : strategie gagnante selon la difficulte ». **6 barres groupées par 2** sur 3 clusters de l'axe X (facile / moyen / difficile) : **orange vif** = BoN parallèle (pass@4), **violet-mauve** = Réflexion séquentielle (K=4). Lecture des hauteurs : **facile** = BoN 1.00 ≈ Réflexion 1.00 (barres jumelles au plafond, indiscernables) ; **moyen** = BoN 1.00 ≈ Réflexion 1.00 (idem) ; **difficile** = BoN 0.50 ≈ Réflexion 0.50 (barres jumelles, **aucune discrimination** sur ce run). **Légende en haut-droite** avec carré orange × carré violet. Axes sans label explicite sur X (catégoriel), Y = 0.0 à 1.0. Lecture pédagogique = sur ce run, **aucun bucket ne discrimine** les deux stratégies (le notebook l'assume en section 4, limites honnêtes G.2) ; la discrimination que Snell prédit sur le bucket difficile demande un n et un modèle plus grands. **Précision de mesure** : ce verdict décrit un tirage, pas une propriété — le bucket décisif ne compte que **2 problèmes** et le décodage est échantillonné, sans graine ; rejouer la comparaison au même n donne tantôt l'égalité, tantôt l'avantage à l'une des deux stratégies. Ce document décrit le tirage committé ; il ne tranche pas la frontière compute-optimale.
- **Contenu réel vérifié** : Figure 715×462, titre centré en haut « Compute-optimal : strategie gagnante selon la difficulte ». **Axe Y** = « Taux de succes » de 0.0 à 1.0 ; **axe X** = 3 buckets discrets (facile / moyen / difficile) sans label d'axe explicite. **6 barres groupées par 2** (BoN orange + Réflexion violet) :
  - **Facile** : BoN = 1.00, Réflexion = 1.00 → **egal**
  - **Moyen** : BoN = 1.00, Réflexion = 1.00 → **egal**
  - **Difficile** : BoN = 0.50, Réflexion = 0.50 → **egal**

  Légende en haut-droite : « BoN parallele (pass@4) » orange × « Reflexion sequentielle (K=4) » violet. **Alt-text et figure cohérents** : sur ce run les deux stratégies rendent **le même taux sur les trois buckets** — la figure documente donc un **résultat négatif** (la discrimination compute-optimale de Snell n'est pas atteignable à n=6 / K=4 sur ce modèle), ce que le notebook énonce lui-même en section 4 (limites honnêtes G.2).
- **Alt-text (FR)** : Bar plot compute-optimal — 3 buckets (facile/moyen/difficile), 2 stratégies à budget égal K=4 (BoN orange vs Réflexion violet). Facile et moyen : 1.0 pour les deux (équivalentes). Difficile : BoN 0.50 et Réflexion 0.50 — égalité, aucune stratégie ne domine sur ce run.
- **Poids** : 23,1 Ko (natif PNG 715×462)
- **Note** : comparaison côte-à-côte (grouped bars) = choix lisible ; le verdict est **implicite** par la hauteur des barres (ici : égalité, donc pas de verdict à lire) sans annotation texte additionnelle.

## texte-reason-vs-scale.png

- **Source** : notebook `17_Native_Reasoning_vs_Scaling.ipynb` (cellule 11, output 0)
- **Description visuelle** : Line plot + scatter matplotlib 770×505 sur fond blanc cassé (RGB 80×80 mean R245/G245/B245 std 23/22/23 — variance basse, même signature que scaling-passk.png car line-art éparse sur fond blanc), titre intégré « Raisonnement natif vs scaling hand-rolled (cost-normalise) ». **6 séries** distinguées par couleur (vert facile / bleu moyen / rouge difficile) ET par marqueur (cercle pour BoN, X pour r1 single-shot), organisées en 2 strates : **3 courbes BoN** (vert/bleu/rouge cercles, lignes simples) qui montrent la montée du pass@k vs tokens dépensés — les courbes verte/bleue s'écrasent à 1.0 dès x=30-386 (plateau), la courbe rouge monte de y=0.25 (x=73) → y=0.40 (x=146) → y=0.50 (x=292) → y=0.50 (x=438) puis plafonne ; **3 points isolés r1** (croix) à y=1.0 single-shot : vert facile à x=232, bleu moyen à x=553, rouge difficile à x=1213. **Légende en bas-droite** listant les 6 séries. Lecture pédagogique = le point **rouge r1 difficile** (x=1213, y=1.0) se situe **au-dessus** de l'extrapolation de la courbe BoN difficile (qui plafonne à 0.50) → le raisonnement natif (deepseek-r1) **gagne au coût-égal** sur le bucket difficile, là où BoN llama-3.3-70b-instruct investit 438 tokens pour 50%.
- **Contenu réel vérifié** : Figure 770×505, titre centré en haut « Raisonnement natif vs scaling hand-rolled (cost-normalise) ». **Axes annotés explicitement** : axe X = « Tokens depenses (cout test-time compute) » de 0 à ~1250 (ticks jusqu'à 1200) ; axe Y = « Taux de succes (pass@k / single-shot) » de 0.0 à 1.0. **6 séries** (3 buckets × 2 stratégies), toutes à pass-rate = 1.0 sauf la courbe rouge :
  - **BoN facile (vert cercles)** : plateau 1.0 de x=30 à x=281
  - **r1 facile (vert croix)** : 1 point isolé à x=232, y=1.0 (single-shot)
  - **BoN moyen (bleu cercles)** : plateau 1.0 de x=71 à x=386
  - **r1 moyen (bleu croix)** : 1 point isolé à x=553, y=1.0
  - **BoN difficile (rouge cercles)** : montée de 0.25 (x=73) → 0.40 (x=146) → 0.50 (x=292) → 0.50 (x=438), plateau dès x=292
  - **r1 difficile (rouge croix)** : 1 point isolé à x=1213, y=1.0

  Légende en bas-droite listant les 6 séries. **Alt-text et figure cohérents** : illustre la question Snell 2024 — pour les problèmes difficiles, le **modèle à raisonnement natif** (deepseek-r1) atteint **100% en single-shot** alors qu'il faut 438 tokens de BoN llama-3.3-70b-instruct pour atteindre 50%. **Le point r1 difficile se situe au-dessus de la courbe BoN difficile extrapolée** → raisonnement natif gagne au coût-égal pour le bucket difficile. Pour facile/moyen, BoN sature rapidement donc les deux stratégies sont équivalentes au plafond.
- **Alt-text (FR)** : Raisonnement natif deepseek-r1 (X) vs scaling hand-rolled BoN llama-3.3-70b-instruct (cercles), cost-normalisé (axe X = tokens). Sur le bucket difficile : r1 single-shot à x=1213 atteint 100%, BoN plafonne à 50% dès x=438 → raisonnement natif gagne au coût-égal. Facile/moyen : les deux stratégies s'équivalent au plafond 1.0 (Snell 2024 cost-normalisé).
- **Poids** : 47,0 Ko (natif PNG 770×505)
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
- **§E doctrine corrigée** (issue #5780) : pas de section `## Galerie`, figures inline dans le tableau récapitulatif + section *Contenu réel vérifié* en lecture linéaire, légende/alt-text décrivent le contenu réel de l'image vérifié par lecture directe. Canonical c.767 : chaque figure a son propre `## <filename>.png` H2 (vs ancien `### filename.png` H3) + champ `**Description visuelle**` distinct du `Contenu réel vérifié` détaillé, aligné sur c.751 Audio + c.763 Video/04 + c.764 Image/02 + c.765 Video/03 + c.766 Open-WebUI/00.
- **R1 catalog-pr-hygiene** : `git diff origin/main..HEAD -- "**/CATALOG-STATUS*" "**/COURSE_CATALOG*"` = vide. Catalogue byte-identique à main.
- **R3 atomic** : 1 fichier (`MANIFEST.md` du dossier `assets/readme/`), pas de churn ailleurs. Migration purement additive (audit fondateur c.479 préservé verbatim byte-identity, nouveau champ `Description visuelle` ajouté par figure + bloc de migration c.767 en tête de section).
- **L268 #4 LF-only** : `git diff | tr -cd '\r' | wc -c` = 0. Pas de retour chariot dans le diff.
- **L143 secrets-hygiene** : `grep -nE "sk-|ghp_|AIza|password=|secret="` sur le diff = 0 hit (l'unique hit est la règle elle-même dans la section *Conformité règles*).
- **C.3 strict respecté (c.767)** : 0 notebook ré-exécuté (cellules sources inchangées), 0 PNG régénéré (3 figures conservées telles quelles sur disque, lecture directe via `Read` sans modification binaire). *Constat de la PR c.767 — voir la ligne #16275 ci-dessous pour l'état courant.*
- **C.3 / #16275** : **0 notebook ré-exécuté** (aucune cellule source modifiée — les sorties committées étaient déjà cohérentes avec leurs figures) ; **3 PNG régénérés** par le chemin outillé de l'EPIC #5654 (`figures-extract --no-manifest`), avec égalité pixel à pixel vérifiée contre la sortie de cellule déclarée (0 px d'écart). Périmètre : 3 PNG + `README.md` + ce MANIFEST + `extract_readme_figures.py` / `notebook_tools.py` et leurs tests — **1 sujet** (régénération des figures README), **1 domaine** (GenAI/Texte).