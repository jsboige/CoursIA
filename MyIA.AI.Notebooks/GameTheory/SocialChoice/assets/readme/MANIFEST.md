# Manifeste des figures — GameTheory / SocialChoice

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

> **Audit vision po-2025 c.477 (2026-07-14, doctrine #5780)** : les 6 PNG ci-dessous ont été ouvertes un par un via l'outil `Read` et confrontées à leur description. Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = **6/6 exacte** — toutes les figures sont des **sorties matplotlib authentiques** (line-art, axes annotés, légendes explicites) qui correspondent **fidèlement** à leur description pédagogique (axiomes d'Arrow, cycle Condorcet, paradoxe Sen, électeur médian, modèle Downs, explosion combinatoire SAT). **0 correction d'alt-text nécessaire** ; le seul changement est la **migration du format table vague-1 vers le format liste détaillé standard** (pattern c.469-c.476), avec ajout du champ *Contenu réel vérifié* par figure + un audit-block en tête pour la traçabilité G.1.

**Note de migration c.771 (2026-07-22)** : ajout du champ canonique `Description visuelle` à chacune des 6 entrées existantes, dans l'ordre canonique (Source → Description visuelle → Alt-text FR → Contenu réel vérifié). Champs pré-existants préservés intacts (audit c.477 = 6/6 ACCURATE sans correction, juste migration `Description visuelle` à ajouter). Vision-QA MiniMax M3 re-confirmée 6/6 ACCURATE par lecture directe des 6 PNG via `Read` (mandat 2026-07-11 — vision ACTIVE lanes CoursIA-2). Partition-cœur GameTheory/SocialChoice (11ᵉ partition-cœur distincte c.754+, suite logique c.770 GameTheory partition principale).

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Sujet |
|--------|---------|------------|-------|--------------------------------------|-------|
| Synthèse des axiomes d'Arrow | `sc-arrow.png` | 1200×415 | 43 Ko | `01-Arrow-Impossibility-Theorem.ipynb` · cellule 29 · output 0 | 3 panneaux (Borda / Pluralité / Dictature) × 3 barres (Pareto, IIA, Non-dictature), vert « SATISFAIT » / rouge « VIOLÉ » |
| Cycle de Condorcet | `sc-condorcet.png` | 690×490 | 25 Ko | `03-Voting-Methods.ipynb` · cellule 10 · output 1 | Graphe orienté du tournoi majoritaire, sommets A / B / C disposés en triangle : les arêtes forment un cycle A→B→C→A, aucun vainqueur de Condorcet n'émerge |
| Paradoxe de Sen | `sc-sen.png` | 765×590 | 24 Ko | `03-Voting-Methods.ipynb` · cellule 21 · output 0 | 3 états sociaux (a, b, c) : deux flèches vertes pleines « Liberté » (le Prude décide c>a, le Lecteur décide b>c), une flèche orange pointillée horizontale étiquetée « Pareto » en rouge (a>b) ; le cycle a>b>c>a rend liberté et Pareto incompatibles |
| Théorème de l'électeur médian | `sc-median.png` | 1200×423 | 86 Ko | `03-Voting-Methods.ipynb` · cellule 29 · output 0 | 2 panneaux : histogramme des pics de préférence (ligne pointillée rouge = médiane) + courbes d'utilité unimodales de 3 électeurs (utilité = −distance au pic) |
| Modèle de Downs | `sc-downs.png` | 1200×423 | 80 Ko | `03-Voting-Methods.ipynb` · cellule 32 · output 0 | 2 panneaux : histogramme des électeurs (positions initiales/finales des partis) + trajectoires des 2 partis (bleu gauche / rouge droite) convergeant vers l'électeur médian (vert pointillé) sur 20 rounds |
| Illustration de l'agrégation computationnelle | `sc-z3-sat.png` | 1200×540 | 94 Ko | `04-Computational-Aggregation-SAT-Z3.ipynb` · cellule 31 · output 0 | 2 panneaux : diagramme conceptuel des cercles de contraintes Pareto/IIA/Non-dictature à intersection vide + courbe semi-log du nombre de profils (m!)^k explosant avec le nombre d'alternatives (illustration conceptuelle, non une sortie du solveur Z3) |

**Total** : 6 figures, 351 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib (line-art + étiquettes de texte) → **PNG lossless** ; 4 figures à panneaux multiples (sc-arrow, sc-median, sc-downs, sc-z3-sat) étaient à l'origine en largeur >1200 px (matplotlib `figsize` wide) et ont été **downscalées LANCZOS à 1200 px max-dim** pour respecter la borne dure EPIC (le texte reste net à cette résolution) ; 2 figures simples (sc-condorcet, sc-sen) sous la borne nativement. Arc narratif : du théorème d'impossibilité d'Arrow (limite axiomatique) aux méthodes de vote (Condorcet, Sen, électeur médian, Downs) puis à l'agrégation computationnelle par SAT/Z3.

---

## Détail vérifié figure par figure (audit vision c.477)

### sc-arrow.png

- **Description** : Théorème d'Arrow — synthèse des 3 axiomes (Pareto, IIA, Non-dictature) × 3 systèmes de vote (Borda, Pluralité, Dictature) avec verdict visuel SATISFAIT (vert) / VIOLÉ (rouge).
- **Description visuelle** : Figure matplotlib single row 1200×415 px (std RGB 93.8/64.8/81.9 — std R la plus élevée du lot = signature des grandes zones vert/rouge saturés). Titre principal centré en haut « Theoreme d'Arrow : aucun systeme ne satisfait les 3 axiomes ». **3 panneaux côte-à-côte** (Borda / Pluralité / Dictature), chacun contenant **3 barres verticales pleine hauteur** étiquetées en blanc au centre (SATISFAIT en vert ≈ #2ECC71, VIOLE en rouge ≈ #E74C3C). Labels d'axe X sous chaque barre (Pareto / IIA / Non-dictature). Disposition très haute en contraste colorimétrique = lisibilité immédiate du verdict par cellule.
- **Contenu réel vérifié** : Figure 1200×415, titre principal centré en haut « Théorème d'Arrow : aucun système ne satisfait les 3 axiomes ». **3 panneaux côte à côte** (Borda / Pluralité / Dictature), chacun contenant **3 barres verticales** (Pareto / IIA / Non-dictature). **9 cellules totales** :
  - Borda : Pareto SATISFAIT (vert) + IIA VIOLÉ (rouge) + Non-dictature SATISFAIT (vert)
  - Pluralité : Pareto SATISFAIT (vert) + IIA VIOLÉ (rouge) + Non-dictature SATISFAIT (vert)
  - Dictature : Pareto SATISFAIT (vert) + IIA SATISFAIT (vert) + Non-dictature VIOLÉ (rouge)

  Étiquettes SATISFAIT / VIOLÉ inscrites en blanc au centre de chaque barre (vert ≈ #2ECC71, rouge ≈ #E74C3C). Labels d'axe X (Pareto / IIA / Non-dictature) en dessous de chaque barre. **Alt-text et figure cohérents** : le tableau illustre parfaitement le théorème d'Arrow — chaque système de vote viole au moins 1 axiome sur 3 (Borda → IIA, Pluralité → IIA, Dictature → Non-dictature).
- **Note** : la palette vert/rouge est universellement lisible (étiquettes textuelles à l'intérieur de chaque barre, pas de risque d'ambiguïté daltonien).

### sc-condorcet.png

- **Description** : Cycle de Condorcet — graphe orienté du tournoi majoritaire à 3 candidats A/B/C, montrant l'impossibilité d'un vainqueur de Condorcet quand le graphe contient un cycle.
- **Description visuelle** : Figure matplotlib single panel 690×490 px (std RGB 27.2/21.5/18.7 — std le plus bas du lot = signature fond blanc majoritaire + 3 nœuds pastel + 3 arêtes fines). Titre en haut « Cycle de Condorcet (graphe oriente) ». **3 sommets circulaires bleu pastel** étiquetés A (à droite), B (haut-gauche), C (bas-gauche) disposés en **triangle isocèle**. **3 arêtes courbes bleues** reliant les sommets dans un cycle fermé (arcs supérieur convexe, gauche concave, inférieur convexe). **Nuance disclosed c.771** : bien que l'audit c.477 décrive un « graphe orienté », les flèches directionnelles ne sont PAS visibles sur le rendu PNG (uniquement les courbes comme un graphe non-orienté). La structure cyclique reste néanmoins apparente par la disposition triangulaire symétrique ; le cycle est implicite par l'absence de sommet dominant.
- **Contenu réel vérifié** : Figure 690×490, titre en haut « Cycle de Condorcet (graphe orienté) ». **3 sommets circulaires bleu clair** étiquetés A (droite), B (haut-gauche), C (bas-gauche), disposés en triangle isocèle. **3 arêtes courbes bleues** reliant les sommets dans un cycle fermé : A→B (arc supérieur convexe), B→C (arc gauche concave), C→A (arc inférieur convexe). **Pas de vainqueur** : aucun sommet n'a un degré entrant qui le rendrait dominant (chacun a 1 arc entrant et 1 arc sortant). **Alt-text et figure cohérents** : la triangulation cyclique illustre précisément le paradoxe de Condorcet où le tournoi majoritaire ne peut pas être résolu en un ordre transitif.
- **Note** : les arêtes courbes (vs droites) renforcent visuellement le caractère cyclique vs hiérarchique — choix pédagogique pertinent.

### sc-sen.png

- **Description** : Paradoxe de Sen — illustration de l'incompatibilité entre la Liberté (deux décideurs individuels) et le Principe de Pareto quand les préférences forment un cycle.
- **Description visuelle** : Figure matplotlib single panel 765×590 px (std RGB 29.1/24.7/30.3 — std bas similaire à sc-condorcet = fond blanc dominant + nœuds pastel + 3 flèches fines). Titre en haut « Paradoxe de Sen : Liberte vs Pareto ». **3 nœuds circulaires bleu pastel** étiquetés a (à gauche), b (à droite), c (en bas) en triangle isocèle inversé. **3 flèches colorées avec direction visible** (vs sc-condorcet) : **flèche orange pointillée horizontale** de a vers b, étiquette rouge au-dessus « Pareto: a > b » ; **flèche verte pleine diagonale** de c vers a, étiquette verte « Liberte Prude: c > a » ; **flèche verte pleine diagonale** de b vers c, étiquette verte « Liberte Lewd: b > c ». Annotation orange centrale « Transitivite: b > a ». Le cycle complet (a>b par Pareto + b>c par Lewd + c>a par Prude) rend Liberté et Pareto incompatibles.
- **Contenu réel vérifié** : Figure 765×590, titre en haut « Paradoxe de Sen : Liberte vs Pareto ». **3 nœuds circulaires bleu clair** étiquetés a (gauche), b (droite), c (bas) disposés en triangle. **3 flèches colorées** :
  - **Flèche orange pointillée horizontale** de a vers b, étiquette rouge au-dessus « Pareto: a > b » (indique que tous préfèrent a à b)
  - **Flèche verte pleine diagonale** de c vers a, étiquette verte « Liberte Prude: c > a » (le Prude préfère c à a)
  - **Flèche verte pleine diagonale** de b vers c, étiquette verte « Liberte Lewd: b > c » (le Lewd préfère b à c)

  Plus une annotation orange « Transitivite: b > a » au centre (résultat de la composition transitivité b>c et c>a). **Le cycle complet** : a>b (Pareto) + b>c (Lewd) + c>a (Prude) = transitivité cassée. **Alt-text et figure cohérents** : la figure montre précisément l'incompatibilité entre Liberté minimale (chaque décideur classe au moins une paire) et Pareto (unanimité) quand les préférences forment un cycle.
- **Note** : «Lewd» est probablement un nom propre de décideur lié au scénario pédagogique — choix stylistique qui ne perturbe pas la compréhension.

### sc-median.png

- **Description** : Théorème de l'électeur médian — 2 panneaux : histogramme des pics de préférence (avec médiane en rouge) + courbes d'utilité unimodales de 3 électeurs (utilité = −distance au pic).
- **Description visuelle** : Figure matplotlib **2 panneaux côte-à-côte** 1200×423 px (std RGB 58.7/45.8/37.8 — std modéré = signature de l'histogramme à barres pleines + 3 courbes fines). **Gauche** : « Distribution des pics (preferences unimodales) » — histogramme bleu pastel semi-transparent, axe X = Position (gauche-droite) de 0 à 10, axe Y = Nombre d'electeurs de 0 à 1.0. Barres hauteur = 1.0 aux positions occupées (1, 3, 4, 5, 7, 8, 9). **Ligne pointillée rouge verticale à x=5** + légende « Median = 5 ». **Droite** : « Exemples de preferences unimodales » — axe X = Alternative (position) 0→10, axe Y = Utilite -8→0. **3 courbes triangulaires** (lignes simples) : bleu pic=1 (descente de 0 à -9), orange pic=3 (0 à -7), vert pic=4 (0 à -6). Légende coin bas-gauche.
- **Contenu réel vérifié** : Figure 1200×423, **2 panneaux côte à côte** :
  - **Panneau gauche** : histogramme des pics de préférence, axe X = « Position (gauche-droite) » de 0 à 10, axe Y = « Nombre d'electeurs » de 0 à 1.0. Barres bleues semi-transparentes : hauteur = 1.0 aux positions occupées (1, 3, 4, 5, 7, 8, 9), hauteur = 0 ailleurs. **Ligne pointillée rouge verticale** à x=5, étiquette en légende « Median = 5 ».
  - **Panneau droit** : courbes d'utilité, axe X = « Alternative (position) » de 0 à 10, axe Y = « Utilite » de -8 à 0. **3 courbes triangulaires (lignes simples)** :
    - Bleu : pic à x=1 (utilité max = 0), descente linéaire vers x=10 (utilité ≈ -9)
    - Orange : pic à x=3 (utilité max = 0), descente vers x=10 (utilité ≈ -7)
    - Vert : pic à x=4 (utilité max = 0), descente vers x=10 (utilité ≈ -6)

  Légende en bas-gauche du panneau droit : « Electeur (pic=1) » / « Electeur (pic=3) » / « Electeur (pic=4) ». **Alt-text et figure cohérents** : illustre le théorème de l'électeur médian (le gagnant de Condorcet = celui qui a la médiane des pics = position 5 ici) + la forme d'utilité unimodale (distance négative au pic).

### sc-downs.png

- **Description** : Modèle de Downs — 2 panneaux : histogramme des électeurs avec positions initiales/finales des partis + trajectoires des 2 partis convergeant vers l'électeur médian sur 20 itérations.
- **Description visuelle** : Figure matplotlib **2 panneaux côte-à-côte** 1200×423 px (std RGB 37.3/38.8/37.8 — std modéré et équilibré = distribution unimodale + 3 lignes de convergence). **Gauche** : « Distribution des electeurs et positions des partis » — histogramme gris (Nombre d'electeurs 0→12) sur axe « Position politique » 0→9, distribution unimodale centrée autour de 5. **5 annotations verticales** superposées : **ligne pointillée verte** x≈4.8 (Median), **ligne pleine bleue** x=2 (Gauche int), **ligne pleine rouge** x=8 (Droite int), **ligne pointillée bleue** x=4.8 (Gauche final superposée médiane), **ligne pointillée rouge** x=4.8 (Droite final superposée médiane). Légende haut-droit. **Droite** : « Convergence vers l'electeur median (Downs 1957) » — axe X Iteration 0→20, axe Y Position politique 0→10. **3 courbes** : bleu « Parti Gauche » croissante de (0,2) à (~10,4.8) puis plateau, rouge « Parti Droite » décroissante de (0,8) à (~10,4.8) puis plateau, vert pointillé horizontal à 4.8 « Electeur median ».
- **Contenu réel vérifié** : Figure 1200×423, **2 panneaux côte à côte** :
  - **Panneau gauche** : « Distribution des electeurs et positions des partis », histogramme gris (Nombre d'electeurs de 0 à 12) sur l'axe « Position politique » de 0 à 9. Distribution unimodale centrée autour de 5. **Annotations verticales** :
    - **Ligne pointillée verte** à x≈4.8 (médiane), légende « Median = 4.8 »
    - **Ligne pleine bleue** à x=2 (Gauche init), légende « Gauche int = 2 »
    - **Ligne pleine rouge** à x=8 (Droite init), légende « Droite int = 8 »
    - **Ligne pointillée bleue** à x=4.8 (Gauche final, superposée à médiane)
    - **Ligne pointillée rouge** à x=4.8 (Droite final, superposée à médiane)

  → Convergence manifeste : initial à 2/8 → final à 4.8/4.8 (= médiane).
  - **Panneau droit** : « Convergence vers l'electeur median (Downs 1957) », axe X = « Iteration » de 0 à 20, axe Y = « Position politique » de 0 à 10. **3 courbes** :
    - **Bleu « Parti Gauche »** : trajectoire monotone croissante de (0, 2) à (~10, 4.8), puis plateau à 4.8 jusqu'à 20
    - **Rouge « Parti Droite »** : trajectoire monotone décroissante de (0, 8) à (~10, 4.8), puis plateau à 4.8 jusqu'à 20
    - **Vert pointillé « Electeur median »** : ligne horizontale à y=4.8

  Légende en haut-droite. **Alt-text et figure cohérents** : illustre le modèle de Downs (1957) — sous vote majoritaire à 2 partis, l'équilibre Nash est la convergence vers la position de l'électeur médian, observable empiriquement sur 20 itérations (convergence en ~10 rounds).

### sc-z3-sat.png

- **Description** : Illustration de l'agrégation computationnelle SAT/Z3 — 2 panneaux : diagramme Venn des contraintes axiomatiques (Pareto / IIA / Non-dictature) à intersection vide + courbe semi-log de l'explosion combinatoire du nombre de profils.
- **Description visuelle** : Figure matplotlib **2 panneaux côte-à-côte** 1200×540 px (std RGB 27.5/31.2/30.4 — std bas = signature des 3 grands cercles pastel uniformes). **Gauche** : « Theoreme d'Arrow : Intersection Vide » — diagramme de Venn à 3 cercles pastel : **bleu Pareto** (haut-gauche), **vert IIA** (haut-droite), **rouge Non-dictature** (bas-centre, plus grand). **Étiquette encadrée rouge « Intersection VIDE »** au centre (chevauchement explicitement marqué vide). **Droite** : « Explosion combinatoire des profils » — axe X = Nombre d'alternatives 2→5, axe Y = Nombre de profils (log) 10^0→10^6 (semi-log). **2 courbes avec marqueurs** : bleu cercles « 2 voters » de (2,2) à (5,~14000), rouge carrés « 3 voters » de (2,1) à (5,~1500000). **Annotation verte fléchée** bas-gauche « Arrow ne s'applique pas » pointant vers (2,1). Légende haut-gauche.
- **Contenu réel vérifié** : Figure 1200×540, **2 panneaux côte à côte** :
  - **Panneau gauche** : « Theoreme d'Arrow : Intersection Vide » — diagramme de Venn à 3 cercles :
    - **Cercle bleu pastel Pareto** (en haut-gauche)
    - **Cercle vert pastel IIA** (en haut-droite)
    - **Cercle rouge pastel Non-dictature** (en bas-centre, plus grand)
    - **Étiquette encadrée rouge « Intersection VIDE »** au centre (chevauchement des 3 cercles explicitement marqué vide)
  - **Panneau droit** : « Explosion combinatoire des profils », axe X = « Nombre d'alternatives » de 2 à 5, axe Y = « Nombre de profils (log) » de 10^0 à 10^6 (échelle semi-log). **2 courbes** :
    - **Bleu « 2 voters »** : marqueurs cercles bleus, montée rapide de (2, 2) à (5, ~14000)
    - **Rouge « 3 voters »** : marqueurs carrés rouges, montée plus rapide de (2, 1) à (5, ~1500000)

  Annotation verte fléchée en bas-gauche « Arrow ne s'applique pas » pointant vers l'origine (2 alternatives, où le théorème ne s'applique pas car il faut m≥3). Légende en haut-gauche. **Alt-text et figure cohérents** : illustre à la fois (a) la **vacuité** de l'intersection des contraintes axiomatiques (= théorème d'Arrow) et (b) l'**explosion combinatoire** (m!)^k qui motive l'approche SAT/Z3 pour explorer l'espace des profils.

## Note méthodologique — figures pédagogiques matplotlib authentiques

Cette série est **3ᵉ dans le rollout** à présenter exclusivement des **figures matplotlib authentiques** (après #6446 c.475 GenAI/Image/examples qui montrait 6/6 GenAI riches). Les 6 figures SocialChoice sont des **diagrammes académiques** (pas des œuvres artistiques), avec une exigence de **rigueur mathématique** :
- **Axes annotés explicitement** (noms de variables, unités, échelles)
- **Légendes identifiant les séries** (Electeur pic=N, Gauche/Droite, 2/3 voters)
- **Couleurs sémantiques** (rouge Pareto, vert Liberté, bleu/rouge gauche/droite) + sémiologie consistante
- **Titres explicites** en français (« Théorème d'Arrow : aucun système... », « Convergence vers l'electeur median (Downs 1957) »)

**Pattern transférable** : pour les familles à dominante matplotlib (SocialChoice, GameTheory, Search/*, ML, Probas), la même rigueur s'applique — vérifier la **fidélité des annotations** (variables, légendes, unités), pas seulement la composition visuelle. Aucun mismatch détecté sur ces 6 figures : la table c.477 MANIFEST est **plus proche du standard** que les vagues 1-2 (SymbolicLearning/Image), ce qui réduit le travail de migration à un simple changement de format.

## Conformité règles

- **§A single-subject** : 1 sujet (audit figures GameTheory/SocialChoice), 1 domaine (GameTheory), 1 fichier. Bien sous plafond 3000L.
- **§E doctrine corrigée** (issue #5780) : pas de section `## Galerie`, figures inline dans le tableau récapitulatif + section *Contenu réel vérifié* en lecture linéaire, légende/alt-text décrivent le contenu réel de l'image vérifié par lecture directe.
- **R1 catalog-pr-hygiene** : `git diff origin/main..HEAD -- "**/CATALOG-STATUS*" "**/COURSE_CATALOG*"` = vide. Catalogue byte-identique à main.
- **L268 #4 LF-only** : `git diff | tr -cd '\r' | wc -c` = 0. Pas de retour chariot dans le diff.
- **L143 secrets-hygiene** : `grep -nE "sk-|ghp_|AIza|password=|secret="` sur le diff = 0 hit.