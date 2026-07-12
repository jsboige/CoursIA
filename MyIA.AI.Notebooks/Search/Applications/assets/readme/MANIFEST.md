# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

## app1-nqueens-board.png

- **Source** : notebook `CSP/App-1-NQueens.ipynb` (cellule 6, output 0)
- **Alt-text (FR)** : Échiquier 8×8 avec une solution connue des 8-Reines : aucune paire de reines ne se menace (alignement, diagonale, anti-diagonale).
- **Poids** : 17.7 KB (PIL optimisé)

## app2-graphcoloring-map.png

- **Source** : notebook `CSP/App-2-GraphColoring.ipynb` (cellule 9, output 0)
- **Alt-text (FR)** : Graphe d'adjacence des départements français métropolitains (≈101 sommets, arêtes par frontière partagée) rendu avec sa coloration CP-SAT — couleurs voisines distinctes, nœuds aux positions géographiques approximatives.
- **Poids** : 189.0 KB (PIL optimisé)
- **Note** : nom de fichier `app2-graphcoloring-map` conservé ; le tracé sous-jacent est un graphe, pas une carte choroplèthe — dette de nommage disclosed (EPIC #5780).

## app3-nurseschedule-planning.png

- **Source** : notebook `CSP/App-3-NurseScheduling.ipynb` (cellule 41, output 0)
- **Alt-text (FR)** : Planning de gardes infirmières sur 28 jours : 15 infirmières en lignes, créneaux Matin / Après-midi / Nuit / Repos en colonnes, week-ends marqués en rouge. Solution CP-SAT respectant les contraintes dures (couverture, repos, max nuits consécutives) et maximisant les préférences douces.
- **Poids** : 146.5 KB (PIL optimisé)

## app11-picross-grid.png

- **Source** : notebook `CSP/App-11-Picross.ipynb` (cellule 10, output 0)
- **Alt-text (FR)** : Énoncé d'un puzzle Picross (nonogramme) 5×5 : indices de lignes et de colonnes au-dessus et à gauche de la grille vierge. La résolution CP-SAT noircirait les cases pour révéler l'image ; la sortie capturée ici est l'énoncé, pas la grille résolue.
- **Poids** : 9.7 KB (PIL optimisé)
- **Note** : nom de fichier `app11-picross-grid` conservé ; le PNG montre l'énoncé (grille vide), pas une grille résolue — limitation illustrative assumée (EPIC #5780).

## app15-sports-calendar.png

- **Source** : notebook `CSP/App-15-SportsScheduling.ipynb` (cellule 5, output 0)
- **Alt-text (FR)** : Matrice 6×6 des distances entre les six villes de la ligue (entrée du problème de calendrier sportif) — heatmap symétrique à diagonale nulle, valeurs entières en kilomètres. L'ordonnancement des matchs (round-robin, équilibre domicile/extérieur, déplacements) est résolu par CP-SAT à partir de cette matrice.
- **Poids** : 27.6 KB (PIL optimisé)
- **Note** : nom de fichier `app15-sports-calendar` conservé ; le PNG montre la matrice des distances (entrée), pas le calendrier final — dette de nommage disclosed (EPIC #5780).

## app19-wfc-tiles.png

- **Source** : notebook `CSP/App-19-ProceduralGeneration-WFC.ipynb` (cellule 12, output 0)
- **Alt-text (FR)** : Niveau 2D généré par Wave Function Collapse encodé en CP-SAT : grille de tuiles mur / sol / eau / porte / herbe, le héros marqué en une couleur, trois ennemis placés, une clé et un coffre. Sortie du solveur avec contraintes d'adjacence (sol adjacent au sol, herbe à l'herbe, mur entouré de sol, etc.) — connectivité 7 %, ennemis 3, clés 1, coffres 1.
- **Poids** : 24.7 KB (PIL optimisé)