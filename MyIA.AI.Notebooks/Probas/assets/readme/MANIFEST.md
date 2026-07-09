# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

## probas-utility-functions.png

- **Source** : notebook `DecisionTheory/PyMC/DecPyMC-2-Utility-Money.ipynb`, cellule 10 (index **toutes-cellules**, convention `extract_readme_figures.py`), output 1. La cellule 10 (`# Demonstration numerique : utilite marginale decroissante`) trace `fig, axes = plt.subplots(1, 3, figsize=(14, 4))` sur 3 panneaux cote-a-cote. Preuve mecanique : source PNG 1389x390 (aspect 3.56) -> figure commitee 1200x336 (aspect 3.57, PIL downscale 1389->1200).
- **Alt-text (FR)** : Trois fonctions d'utilite fondamentales tracees sur 3 panneaux cote-a-cote — racine carree `U(x) = sqrt(x)` (concave), logarithme `U(x) = ln(x)` (concave), et lineaire `U(x) = x` (neutre au risque, en reference) — montrant l'utilite marginale decroissante : les deux courbes concaves s'aplatissent quand la richesse x augmente (chaque euro supplementaire apporte moins d'utilite que le precedent), tandis que la lineaire reste constante (aversion nulle). Fondement de la theorie de la decision sous incertitude (Pratt 1964, Arrow 1965). Extrait du notebook DecPyMC-2-Utility-Money.
- **Poids** : 64.9 KB (PIL optimise)
