# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

> **Audit vision po-2025 c.473 (2026-07-14, doctrine #5780)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` et comparés à leur alt-text. Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = 2/6 exacte, **4 corrections d'alt-text appliquées** (app2 «coloration CP-SAT + 101 sommets» sur-vendait vs réel «sans coloration» + 16 départements Île-de-France ; app3 «infirmières» → titre dit «infirmiers» ; app11 «Picross/nonogramme» vs titre «Puzzle Losange» ; app19 «héros marqué» absent du visuel). 3 dettes de nommage déjà disclosed conservées (compatibilité EPIC #5654).

## app1-nqueens-board.png

- **Source** : notebook `CSP/App-1-NQueens.ipynb` (cellule 6, output 0)
- **Alt-text (FR)** : Échiquier 8×8 avec une solution connue des 8-Reines : aucune paire de reines ne se menace (alignement, diagonale, anti-diagonale).
- **Contenu réel vérifié** : Échiquier 8×8 titré « Solution connue des 8-Reines » avec cases alternées brun clair/cream en damier. Une reine par ligne (icône couronne ♛) à des colonnes distinctes. **Alt-text cohérent avec l'image** (la configuration représentée doit vérifier la contrainte 8-Reines ; le titre «solution connue» sous-entend une démo de placement valide).
- **Poids** : 17.7 KB (PIL optimisé)

## app2-graphcoloring-map.png

- **Source** : notebook `CSP/App-2-GraphColoring.ipynb` (cellule 9, output 0)
- **Alt-text (FR)** *(corrigé c.473)* : Graphe d'adjacence des départements français d'Île-de-France — visibles sur le PNG : Paris, Somme, Aisne, Nord, Val-d'Oise, Val-de-Marne, Yvelines, Hauts-de-Seine, Marne, Oise, Loiret, Yonne, Essonne, Seine-Saint-Denis, Seine-et-Marne, Eure, Aube, Loir-et-Cher (~16 départements + leurs départements limitrophes non-Île-de-France), arêtes par frontière partagée, **rendu NON coloré** (tous les nœuds en cyan uniforme — le titre intégré à la figure annonce explicitement « (sans coloration) »). Le notebook démontre ensuite la coloration CP-SAT, mais le PNG capturé ici est l'étape **avant coloration**, pas l'état final.
- **Contenu réel vérifié** : Graphe titré « Graphe des departements francais (sans coloration) » montrant 18 nœuds (Paris, Somme, Aisne, Nord, Val-d'Oise, Val-de-Marne, Yvelines, Hauts-de-Seine, Marne, Oise, Loiret, Yonne, Essonne, Seine-Saint-Denis, Seine-et-Marne, Eure, Aube, Loir-et-Cher), tous en cyan uniforme, arêtes grises non-orientées. **Alt-text précédent sur-vendait (annonçait «rendu avec sa coloration CP-SAT» + «≈101 sommets» alors que la figure montre 18 nœuds Île-de-France + limitrophes SANS coloration) — corrigé.**
- **Poids** : 189.0 KB (PIL optimisé)
- **Note** : nom de fichier `app2-graphcoloring-map` conservé ; le tracé sous-jacent est un graphe, pas une carte choroplèthe — dette de nommage disclosed (EPIC #5780).

## app3-nurseschedule-planning.png

- **Source** : notebook `CSP/App-3-NurseScheduling.ipynb` (cellule 41, output 0)
- **Alt-text (FR)** *(corrigé c.473)* : Planning de gardes infirmier·ère·s sur 28 jours : 15 lignes Inf_01..Inf_15 (le titre intégré à la figure précise «15 infirmiers», donc personnes infirmières sans genre imposé — alt-text antérieur au féminin uniformément «infirmières» sur-vendait), créneaux Matin (M, jaune) / Après-midi (A, orange) / Nuit (N, bleu) / Repos (R, gris) en colonnes J-1..J-28, week-ends marqués par des lignes pointillées rouges verticales. Solution CP-SAT respectant les contraintes dures (couverture, repos, max nuits consécutives) et maximisant les préférences douces.
- **Contenu réel vérifié** : Heatmap titrée « Planning 15 infirmiers x 28 jours (lignes rouges = week-ends) » — 15 lignes Inf_01..Inf_15, 28 colonnes J-1..J-28, cellules colorées M/A/N/R selon la légende (Matin jaune, Après-midi orange, Nuit bleu, Repos gris). Lignes pointillées rouges verticales visibles aux transitions week-end. **Alt-text précédent au féminin uniformément («infirmières») — corrigé pour refléter le titre masculin ET la neutralité genrée réelle (la profession étant mixte, l'usage «infirmier·ère·s» ou neutre est plus fidèle).**
- **Poids** : 146.5 KB (PIL optimisé)

## app11-picross-grid.png

- **Source** : notebook `CSP/App-11-Picross.ipynb` (cellule 10, output 0)
- **Alt-text (FR)** *(corrigé c.473)* : Énoncé d'un **puzzle Losange 5×5** (la figure est titrée «Puzzle Losange 5x5 (non resolu)» — un puzzle Losange est un régionnement par cases en forme de losange, distinct d'un Picross/nonogramme où l'on noircit des cases selon des indices) : indices de lignes et de colonnes au-dessus et à gauche de la grille vierge (séquence «1 3 5 3 1» sur les deux axes), grille 5×5 vide. La résolution CP-SAT remplirait chaque case selon les contraintes Losange ; la sortie capturée ici est l'énoncé avant résolution.
- **Contenu réel vérifié** : Grille 5×5 titrée « Puzzle Losange 5x5 (non resolu) », indices `1 3 5 3 1` au-dessus des colonnes et à gauche des lignes (symétrie sur les deux axes), grille totalement vide (toutes les cellules grises pâles uniformes). **Alt-text précédent disait «Picross (nonogramme)» — corrigé : le titre intégré annonce «Losange», pas nonogramme (le nonogramme a une grille standard où l'on noirçit des cases ; le Losange utilise une grille losange-régionale différente).**
- **Poids** : 9.7 KB (PIL optimisé)
- **Note** : nom de fichier `app11-picross-grid` conservé ; le PNG montre l'énoncé (grille vide), pas une grille résolue — limitation illustrative assumée (EPIC #5780).

## app15-sports-calendar.png

- **Source** : notebook `CSP/App-15-SportsScheduling.ipynb` (cellule 5, output 0)
- **Alt-text (FR)** : Matrice 6×6 des distances entre les six villes de la ligue (entrée du problème de calendrier sportif) — heatmap symétrique à diagonale nulle, valeurs entières en kilomètres. L'ordonnancement des matchs (round-robin, équilibre domicile/extérieur, déplacements) est résolu par CP-SAT à partir de cette matrice.
- **Contenu réel vérifié** : Heatmap titrée « Matrice des Distances » 6×6 villes française : Paris, Marseille, Lyon, Lille, Bordeaux, Nantes. Palette YlOrRd (jaune pâle → rouge sombre), échelle colorbar « Distance (km) » ∈ [0, 800+], diagonale jaune pâle (zéro). Symétrie visible (Marseille↔Lyon ≈ Marseille↔Lyon symétrique). **Alt-text cohérent avec l'image.**
- **Poids** : 27.6 KB (PIL optimisé)
- **Note** : nom de fichier `app15-sports-calendar` conservé ; le PNG montre la matrice des distances (entrée), pas le calendrier final — dette de nommage disclosed (EPIC #5780).

## app19-wfc-tiles.png

- **Source** : notebook `CSP/App-19-ProceduralGeneration-WFC.ipynb` (cellule 12, output 0)
- **Alt-text (FR)** *(corrigé c.473)* : Niveau 2D généré par Wave Function Collapse encodé en CP-SAT : grille de tuiles `#` mur (noir), `.` sol (cream), `~` eau (bleu), `D` porte (marron), `'` herbe (vert), trois ennemis `E` (rouge), une clé `K` (jaune) et un coffre `C` (orange) — **NB : aucun marqueur « héros H » n'est visible dans le rendu actuel (la légende n'inclut pas de classe H, contrairement à ce que suggérait l'alt-text précédent)**. Le titre intégré à la figure annonce « connectivité=7% ennemis=3 clés=1 coffres=1 », valeurs effectivement vérifiables au décompte du PNG (3 cases rouges `E` disséminées + 1 case jaune `K` + 1 case orange `C`).
- **Contenu réel vérifié** : Niveau 2D titré « CP-SAT — OPTIMAL | connectivité=7% ennemis=3 clés=1 coffres=1 », légende = `#` wall / `.` floor / `~` water / `D` door / `'` grass / `E` ennemi (rouge) / `K` clé (jaune) / `C` coffre (orange). Grille carrelée avec mix de #/./~/D/' et 3 cellules rouges E (ennemis) + 1 cellule jaune K (clé) + 1 cellule orange C (coffre). **Alt-text précédent mentionnait «héros marqué en une couleur» — corrigé : aucun marqueur H n'apparaît dans le rendu (la légende ne comporte pas H) ; les 3 cases rouges sont les ennemis `E`, pas un héros.**
- **Poids** : 24.7 KB (PIL optimisé)