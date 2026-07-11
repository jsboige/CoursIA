# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks .NET Interactive). Chaque image est une **extraction 1:1** d'un vrai output de cellule (heatmap PNG graphique rendue par `SkiaLandscapeRenderer` / `LandscapeRenderer` du fork), downscalée à max-dim ≤ 1200 (convention maison, cf. `Part1-Foundations/assets/readme/MANIFEST.md`).

## mgs8-landscape.png

- **Source** : notebook `MGS-8-LandscapeExplorer.ipynb` (cellule 6, output 0)
- **Alt-text (FR)** : Paysage de fitness analytique : heatmap de la fonction Sphere (rouge = haut, cyan = bas), l'optimum global en clair au centre.
- **Poids** : 23.0 KB (natif 420×320)

## mgs8-convergence.png

- **Source** : notebook `MGS-8-LandscapeExplorer.ipynb` (cellule 20, output 0)
- **Alt-text (FR)** : Convergence du GA : la population (BlueViolet) et le meilleur individu (Aqua) se contractent génération après génération vers l'optimum du paysage.
- **Poids** : 75.6 KB (natif 360×270)

## mgs9-everest.png

- **Source** : notebook `MGS-9-EverestRelief.ipynb` (cellule 6, output 3 — carte `EverestMount`)
- **Alt-text (FR)** : Relief terrestre réel comme paysage de fitness : la carte d'altitude de l'Everest lue comme champ de fitness, le sommet (pixel le plus clair) est la cible de la recherche.
- **Poids** : 175.7 KB (downscale max-dim 600, natif 1037×560)

## mgs13-rotation.png

- **Source** : notebook `MGS-13-LandscapeDebias.ipynb` (cellule 10, output 1 — panneau « après rotation »)
- **Alt-text (FR)** : Rastrigin après rotation : les crêtes cosinus, alignées sur les axes à l'origine, basculent hors de la grille d'échantillonnage axe-par-axe — le mécanisme géométrique par lequel la rotation brise la séparabilité.
- **Poids** : 77.2 KB (natif 400×320)
