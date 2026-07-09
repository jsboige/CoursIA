# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

**Audit visuel juillet 2026** : chaque PNG a été rouvert via l'outil Read et son **contenu réel** documenté ci-dessous. Les légendes dans `README.md` ont été ré-auditées pour refléter exactement ce qui est visible (et signaler honnêtement ce qui ne l'est pas).

## sl6-modernilp.png

- **Source** : notebook `SL-6-ModernILP.ipynb` (cellule 18, output 0)
- **Contenu réel vérifié** : courbe 2D simple — perte (entropie croisée, axe y de 0,0 à 0,7) en fonction de l'étape d'optimisation (axe x de 0 à 80). Une seule série tracée en rouge, intitulée « dILP / Lernd -- descente de gradient sur ancestor/2 ». Convergence en ~10 étapes à perte quasi-nulle. Pas de comparaison côte-à-côte des 4 moteurs dans cette figure.
- **Alt-text (FR)** : Convergence du moteur ∂ILP/Lernd sur la tâche `ancestor/2`.
- **Poids** : 23.0 KB (PIL optimisé)

## sl10-angluin-lstar.png

- **Source** : notebook `SL-10-ActiveAutomataLearning.ipynb` (cellule 39, output 5)
- **Contenu réel vérifié** : courbe 2D — exactitude vs vérité terrain (axe y de 0,70 à 1,00) en fonction du nombre d'observations bruitées agrégées k (axe x de 1 à 25). Deux séries tracées : « forward, bruit epsilon=0.20 » (bleu, monte à ~0,99) et « forward, bruit epsilon=0.30 » (rouge, monte à ~0,95), plus une ligne pointillée horizontale « DFA dur, 1 observation (plafond) » à ~0,79. L'automate fini minimal lui-même n'est PAS rendu dans cette figure.
- **Alt-text (FR)** : Agrégation bayésienne de preuves : k observations indépendantes d'un mot corrompu.
- **Poids** : 44.2 KB (PIL optimisé)

## sl12-difflogic.png

- **Source** : notebook `SL-12-DifferentiableLogicGateNetworks.ipynb` (cellule 11, output 0)
- **Contenu réel vérifié** : deux panneaux côte-à-côte. Gauche : « Loss (entraînement, MNIST 20×20) » — CrossEntropyLoss (axe y de 1,0 à 2,3) vs itération (axe x de 0 à 600), courbe bleue qui chute de ~2,3 à ~1,2 avec bruit. Droite : « Accuracy » — accuracy (axe y de 0,68 à 0,78) vs itération (axe x de 200 à 600), courbe bleue « train (sub) » à trois points (0,69 / 0,67 / 0,74) et ligne horizontale pointillée rouge « test = 0.790 ». Le circuit booléen final discrétisé n'est PAS rendu dans cette figure.
- **Alt-text (FR)** : Courbes d'entraînement MNIST 20×20 d'un réseau de portes logiques différentiables.
- **Poids** : 49.8 KB (PIL optimisé)