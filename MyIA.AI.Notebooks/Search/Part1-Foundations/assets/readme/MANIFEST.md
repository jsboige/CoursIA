# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

## search1-statespace.png

- **Source** : notebook `Search-1-StateSpace.ipynb` (cellule 13, output 0)
- **Alt-text (FR)** : Monde de l'aspirateur (Russell & Norvig) — espace d'états à 8 configurations en grille 2×4, colorées par catégorie (état initial orange, états buts verts, autres bleus), transitions étiquetées par action (Gauche / Droite / Aspirer).
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.470) : grille 2×4, deux colonnes de 4 nœuds, labels `*G` / `*D` = position aspirateur, encodage position+sale/Propre = 8 états, légende haut gauche.
- **Poids** : 94.8 KB (downscale max-dim 1200)

## search2-bfs-dfs.png

- **Source** : notebook `Search-2-Uninformed.ipynb` (cellule 28, output 0)
- **Alt-text (FR)** : BFS vs DFS : deux arbres 8-puzzle (3×3 tuiles + case vide), ordre d'expansion comparé — BFS en largeur (nœuds 1→8 coloriés niveau par niveau), DFS en profondeur (chemin 1→2→3 colorié en profondeur).
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.470) : deux sous-arbres côte-à-côte, nœuds numérotés, BFS colorie nœuds bleus niveau par niveau, DFS colorie chemin vert en profondeur. Le notebook Search-2 utilise un arbre d'exemple (pas explicitement "8-puzzle binaire"), mais le rendu visuel est bien un arbre 8-nœuds.
- **Poids** : 57.3 KB (downscale max-dim 1200)

## search3-astar.png

- **Source** : notebook `Search-3-Informed.ipynb` (cellule 48, output 0)
- **Alt-text (FR)** : Progression A* (heuristique Manhattan) sur 8-puzzle : 6 étapes annotées (g = coût réel depuis l'état initial, h = heuristique jusqu'au but, f = g+h).
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.470) : grille 3×3 × 6 étapes, chaque tuile numérotée 1-8 + case vide, en-têtes `g=… h=… f=…` corrects étape par étape. Le chemin A* suit le plus court Manhattan (étape finale = but).
- **Poids** : 25.7 KB (natif)

## search11-metaheuristics.png

- **Source** : notebook `Search-11-Metaheuristics.ipynb` (cellule 33, output 0)
- **Alt-text (FR)** : Comparaison de 4 métaheuristiques (PSO / ABC / SA / BRO) sur 4 fonctions de benchmark (Sphere, Rastrigin, Rosenbrock, Ackley) — fitness (échelle log) et temps d'exécution en ms.
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.470) : deux sous-graphes côte-à-côte, barres groupées par fonction (4) × algorithme (4) = 16 mesures annotées. PSO = Particle Swarm Optimization ; ABC = Artificial Bee Colony ; SA = Simulated Annealing (recuit simulé) ; BRO = Brown Rush Optimization. **Note : la cellule 130 du notebook importe aussi `GA` (Genetic Algorithm) et `GWO`/`WOA`/`DE`, mais la figure cell.33 n'en montre que 4.**
- **Poids** : 78.4 KB (downscale max-dim 1200)

## search11-convergence.png

- **Source** : notebook `Search-11-Metaheuristics.ipynb` (cellule 40, output 0)
- **Alt-text (FR)** : Impact du paramètre `pop_size` sur PSO : fitness final (V-shape : 91.8 → 71.7 → 85.6, optimum ≈ pop_size 50) et temps d'exécution (croissance linéaire 95 → 605 ms).
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.470) : deux sous-graphes côte-à-côte, X = taille de population (10/30/50/100), Y = fitness final (gauche, échelle non-log) ou temps en ms (droite, linéaire). Le V-shape de fitness trahit un compromis exploration/exploitation propre à PSO sur la fonction testée.
- **Poids** : 81.6 KB (downscale max-dim 1200)

## search15-networkx.png

- **Source** : notebook `Search-15-NetworkX.ipynb` (cellule 30, output 0)
- **Alt-text (FR)** : Réseau routier 5×5 nœuds-arêtes pondérées : plus court chemin optimal en rouge (Dijkstra = A* sur ce graphe à poids positifs, annoncé dans le titre de la figure).
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.470) : grille 5×5 de 25 nœuds bleus, arêtes colorées par gradient de poids (jaune pâle → orange → rouge selon le coût), nœud source en haut-gauche (vert), nœud but en bas-droite (rouge), chemin optimal Dijkstra superposé en rouge vif. Titre intégré à la figure : « Dijkstra = A* ».
- **Poids** : 72.8 KB (natif)
