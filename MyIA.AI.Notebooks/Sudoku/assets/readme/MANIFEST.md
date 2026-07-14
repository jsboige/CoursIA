# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

## sudoku1-backtracking.png

- **Source** : notebook `Sudoku-1-Backtracking-Python.ipynb` (cellule `7c13432e`, output 1 — `plot_sudoku(solved_grid, "Solution (bleu = valeurs ajoutées)", initial_grid)`)
- **Alt-text (FR)** : Backtracking : grille 9×9 résolue par le solveur MRV, code couleur distinguant les valeurs initiales (noir) des valeurs trouvées (bleu).
- **Poids** : 29.2 KB (natif)
- **Audit juillet 2026 (PR c.431, EPIC #5780)** : régénéré depuis l'output 1 de la cellule `7c13432e` (la cellule produit 2 figures : output 0 = `plot_sudoku(initial_grid, "Puzzle Initial")` = grille non résolue, output 1 = `plot_sudoku(solved_grid, "Solution (bleu = valeurs ajoutées)", initial_grid)` = grille résolue avec overlay). L'asset précédent correspondait à l'output 0 alors que le README et le MANIFEST décrivaient l'output 1 — défaut d'alt-text (mismatch légende/image) corrigé en régénérant l'asset depuis l'output 1, qui correspond exactement à la légende.

## sudoku3-genetic.png

- **Source** : notebook `Sudoku-3-Genetic-Python.ipynb` (cellule 16, output 3)
- **Alt-text (FR)** : Algorithme génétique : courbe de convergence du meilleur fitness au fil des générations.
- **Poids** : 25.5 KB (natif)

## sudoku11-choco.png

- **Source** : notebook `Sudoku-11-Choco-Python.ipynb` (cellule 33, output 0)
- **Alt-text (FR)** : Programmation par contraintes : grille résolue par le solveur Choco via la modélisation CSP.
- **Poids** : 27.1 KB (natif)

## sudoku16-nn-training.png

- **Source** : notebook `Sudoku-16-NeuralNetwork-Python.ipynb` (cellule 16, output 6)
- **Alt-text (FR)** : Réseau de neurones dense : courbes d'entraînement du MLP sur 20 epochs, écart entre précision par case et précision par grille.
- **Poids** : 73.2 KB (downscale max-dim 1200, source 1789×413 / 55.2 KB)

## sudoku16-nn-errors.png

- **Source** : notebook `Sudoku-16-NeuralNetwork-Python.ipynb` (cellule 43, output 0)
- **Alt-text (FR)** : Carte d'erreurs : identification des cases les plus difficiles à prédire pour le modèle neuronal.
- **Poids** : 47.8 KB (natif)

## sudoku18-comparison.png

- **Source** : notebook `Sudoku-18-Comparison-Python.ipynb` (cellule 39, output 0)
- **Alt-text (FR)** : Comparaison des solveurs : temps moyen de résolution par niveau de difficulté en échelle logarithmique.
- **Poids** : 33.3 KB (natif)
