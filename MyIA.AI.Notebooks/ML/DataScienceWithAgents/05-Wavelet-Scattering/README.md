# 05 — Wavelet Scattering : ondelettes et scattering

[↑ DataScienceWithAgents](../README.md) · [Entrée : ondelettes 1D](WS-00a-Ondelettes-1D-from-scratch.ipynb)

Comment représenter un signal ou une image pour que l'essentiel tienne en peu de nombres, puis pour que deux images décalées de quelques pixels se ressemblent encore ? Cette sous-série de [DataScienceWithAgents](../README.md) répond en deux temps. Elle construit d'abord à la main la transformée en ondelettes, en une puis deux dimensions, et la transformée de scattering — la cascade ondelette, module, moyenne locale. Elle confronte ensuite ces moteurs écrits ligne à ligne aux bibliothèques de référence, sur les mêmes bancs de mesure, et referme l'arc en comparant cette représentation construite aux caractéristiques apprises par un réseau pré-entraîné.

Elle s'adresse aux étudiants en science des données, en traitement du signal et en apprentissage automatique. Les bases d'algèbre linéaire (orthonormalité, adjoint) et la transformée de Fourier discrète suffisent pour commencer ; la régression logistique sert de sonde de classification à partir du scattering. Tous les carnets sont en Python.

## Comment lire ce README — découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue parcours principal, approfondissements et prolongements de recherche.

- **Vous découvrez** : suivez le parcours principal dans l'ordre des numéros. L'étape 00 se lit en trois temps — une dimension, deux dimensions, scattering — et pose le vocabulaire que les étapes 01 à 03 réutilisent.
- **Vous creusez un palier** : la section « Approfondissements » décrit chaque carnet, ses mesures clés et ses exercices. Les trois carnets lettrés 00a, 00b et 00c y sont présentés un par un.
- **Vous cherchez la recherche** : « Pour aller plus loin » rassemble la reproductibilité des mesures, les limites des bancs et les sources primaires.

## Parcours principal — lecture guidée et prérequis

Le fil de la sous-série tient en une discipline : **construire d'abord, consommer ensuite, et mesurer l'écart**. À l'étape 00, NumPy calcule et les bibliothèques ne servent qu'à vérifier ; aux étapes 01 et 02, les rôles s'inversent — les bibliothèques calculent et le moteur écrit à la main devient la référence à battre ; l'étape 03 pose la question de synthèse, représentation construite ou représentation apprise.

| # | Notebook | Ce qu'on y apprend | Public et prérequis | Pour approfondir |
|---|---|---|---|---|
| 00 | Construire à la main — [ondelettes 1D](WS-00a-Ondelettes-1D-from-scratch.ipynb) · [ondelettes 2D](WS-00b-Ondelettes-2D-from-scratch.ipynb) · [scattering](WS-00c-Scattering-from-scratch.ipynb) | Écrire la transformée en ondelettes orthonormale, l'étendre à l'image par produit séparable, puis bâtir la cascade de scattering et mesurer son invariance par translation. Chaque moteur est validé coefficient par coefficient contre une bibliothèque de référence. | Découverte pour la partie 1D, Licence ensuite. Algèbre linéaire, transformée de Fourier discrète, NumPy. | [Autour de 00](#autour-de-00) : les trois carnets, un par un. |
| 01 | [Débruitage d'images : du seuillage maison aux estimateurs de référence](WS-01-Denoising-SOTA.ipynb) | Comparer, à transformée identique, le seuil universel de l'étape 00 et les estimateurs adaptatifs par sous-bande (BayesShrink, SureShrink) : l'écart de qualité vient du choix du seuil, pas du moteur. | Licence. Après les parties 1D et 2D de l'étape 00. | [Autour de 01](#autour-de-01) : le banc, l'effet de l'extension aux bords, les exercices. |
| 02 | [Scattering : kymatio contre le moteur maison](WS-02-Scattering-SOTA.ipynb) | Rejouer le banc de classification de l'étape 00 avec une implémentation vectorisée et séparer ce que l'ingénierie achète (vitesse, mémoire) de ce qu'elle ne garantit pas (la précision dépend des filtres). | Licence. Après la partie scattering de l'étape 00 ; PyTorch installé. | [Autour de 02](#autour-de-02) : conventions de canaux, loi de l'échantillon, tableau comparatif. |
| 03 | [Synthèse : représentation construite ou représentation apprise](WS-03-Synthese-Scattering-vs-ResNet.ipynb) | Confronter le scattering aux caractéristiques d'un ResNet18 pré-entraîné, avec la même sonde et le même test translaté : aucune des deux représentations ne domine tous les axes. | Licence à Recherche. Après 02 ; notions de réseaux convolutifs. | [Autour de 03](#autour-de-03) : les quatre axes du tableau final. |

## Approfondissements — Licence et lectures avancées

Chaque carnet se termine par trois exercices à compléter, un bloc « À retenir », des questions « Vérifiez votre compréhension » avec leurs réponses repliées, et des renvois « Pour aller plus loin ». Les exercices sont des gabarits : le carnet s'exécute de bout en bout tant qu'ils ne sont pas complétés. Les valeurs citées ci-dessous sont celles des sorties enregistrées dans les carnets.

### Autour de 00

L'étape 00 n'a pas de carnet unique : elle se compose de trois carnets lettrés, à lire dans l'ordre, qui partagent une règle — NumPy calcule, PyWavelets et kymatio ne servent qu'à la validation croisée.

- **00a — [Ondelettes 1D](WS-00a-Ondelettes-1D-from-scratch.ipynb).** Haar par paires, puis un moteur général par filtrage et sous-échantillonnage (filtres à quatre et huit coefficients, `db2` et `db4` dans la nomenclature de PyWavelets), dont la synthèse est écrite comme l'adjoint exact de l'analyse. Le moteur s'accorde avec PyWavelets coefficient par coefficient, à condition d'épingler deux conventions — la phase et le signe du filtre miroir — que le seul test de reconstruction ne détecte pas. Le profil d'énergie par échelle sert ensuite d'empreinte du signal, puis un duel de débruitage oppose le seuillage des coefficients, réglé sans connaître le signal, à un passe-bas de Fourier dont la coupure est choisie en le connaissant. Le seuillage dur l'emporte sur le chirp Doppler (17,83 dB contre 13,36 dB), Fourier sur le signal stationnaire (21,19 dB contre 16,37 dB) : aucune base n'est parcimonieuse pour tous les signaux. Le carnet ne trace aucune figure, toutes les lectures portent sur des nombres. Exercices : entropie par échelle, seuil par échelle, localisation d'un transitoire.
- **00b — [Ondelettes 2D](WS-00b-Ondelettes-2D-from-scratch.ipynb).** La transformée d'image n'est pas un nouvel algorithme : deux passes du moteur 1D, sur les rangées puis sur les colonnes, donnent une approximation et trois bandes de détail. Des motifs d'orientation connue montrent que chaque bande est un détecteur d'orientation — une marche verticale place toute son énergie de détail dans une seule bande — et qu'une image constante n'en produit aucune, ce qui contrôle le moteur. Après l'affichage de la pyramide de Mallat et la validation contre PyWavelets, le carnet compare la compression par ondelettes à une DCT par blocs 8×8, à nombre égal de coefficients conservés : l'avantage de l'ondelette atteint +16,40 dB quand on ne garde que 0,2 % des coefficients, et tombe à environ +0,2 dB à 5 %. Exercices : conservation de l'énergie en 2D, budget réparti par bande, détection de l'orientation d'un contour.
- **00c — [Scattering](WS-00c-Scattering-from-scratch.ipynb).** Quand on ne veut plus reconstruire mais comparer, il faut un descripteur stable par translation. Le carnet écrit un banc de morlets orientés directement en domaine de Fourier, puis la cascade à deux couches qui transforme une image 32×32 en 1 600 coefficients. L'invariance est mesurée : pour un décalage de 8 pixels, l'écart relatif du scattering plafonne à 0,73 quand celui des pixels (1,14) et celui d'un descripteur sans module (1,07) continuent de croître. Le moteur est validé contre kymatio par trois voies complémentaires, puis mis au travail sur un extrait de Fashion-MNIST : sous une translation de ±2 pixels du jeu de test, la précision des pixels passe de 0,790 à 0,430, celle du scattering complet de 0,825 à 0,760. Exercices : passer à huit orientations, mesurer l'apport de la deuxième couche sur plusieurs graines, tester l'invariance par rotation que la cascade n'a pas.

### Autour de 01

[WS-01](WS-01-Denoising-SOTA.ipynb) reprend le moteur 2D et le seuil universel de l'étape 00 comme référence, et leur oppose trois estimateurs : VisuShrink et BayesShrink, fournis par scikit-image, et SureShrink, que le carnet implémente à la main parce que la bibliothèque ne le propose pas, en validant la formule du risque contre une recherche exhaustive. Le banc croise quatre images de `skimage.data`, trois niveaux de bruit et trois graines. Sur la moyenne du banc, le seuil universel dur atteint 28,13 dB, BayesShrink 30,62 dB et SureShrink 30,73 dB : les deux estimateurs adaptatifs par sous-bande occupent le haut du tableau alors que la transformée est la même partout.

Le carnet isole aussi le seul écart qui ne relève pas de l'estimation. Le moteur maison étend le signal par périodisation, scikit-image laisse PyWavelets à son extension symétrique par défaut ; à seuil égal, la différence mesurée est de 0,25 dB, une fraction de ce que le choix du seuil apporte. Exercices : réécrire BayesShrink, changer d'ondelette des deux côtés du banc, comparer plusieurs estimateurs du niveau de bruit sur une image riche en contours.

### Autour de 02

[WS-02](WS-02-Scattering-SOTA.ipynb) reprend à l'identique le moteur de scattering et le corpus de l'étape 00, puis leur oppose kymatio sur son backend PyTorch, avec les mêmes échelles, les mêmes orientations et le même classifieur. Trois lectures en sortent.

- **Les conventions se mesurent.** Les deux implémentations n'ordonnent pas leurs canaux de la même façon et n'utilisent pas les mêmes filtres. Une table de corrélation retrouve, pour chaque canal du moteur maison, son partenaire kymatio : même échelle, orientation inversée, corrélations comprises entre 0,64 et 0,81.
- **L'ingénierie achète la vitesse, pas la précision.** kymatio précalcule son banc de filtres et traite le corpus entier en un seul tenseur : le rapport de latence imprimé par le carnet dépasse un ordre de grandeur. Sur ce protocole, le moteur maison garde pourtant l'avantage en précision (0,825 et 0,765 contre 0,775 et 0,645, test propre puis translaté), parce que ses morlets anisotropes sont plus sélectifs que les filtres isotropes par défaut de la bibliothèque.
- **Plus de données n'achètent pas l'invariance.** Avec cinq fois plus d'images par classe, les pixels rejoignent le scattering sur le test propre (0,826 contre 0,829) mais restent loin derrière sur le test translaté (0,445 contre 0,645).

Le carnet se termine par un tableau qui met côte à côte les carnets construits à la main et leurs pendants appuyés sur les bibliothèques ; ses longueurs de code sont recalculées à l'exécution à partir des fichiers voisins. Exercices : ajouter une troisième échelle, doubler le nombre d'orientations, encoder la permutation de canaux mesurée.

### Autour de 03

[WS-03](WS-03-Synthese-Scattering-vs-ResNet.ipynb) compare trois représentations d'un même extrait de Fashion-MNIST : les pixels bruts, le scattering de kymatio et la sortie de l'avant-dernière couche d'un ResNet18 pré-entraîné sur ImageNet, utilisé en inférence seule. Une même régression logistique sur caractéristiques standardisées sert de sonde, et le jeu de test est rejoué sous une translation de ±2 pixels.

| Représentation | Test propre | Test translaté | Écart relatif sous ±2 px | Dimensions |
|---|---|---|---|---|
| Pixels bruts | 0,780 | 0,311 | 0,742 | 784 |
| Scattering (construit) | 0,836 | 0,577 | 0,425 | 1 225 |
| ResNet18 (appris) | 0,811 | 0,751 | 0,331 | 512 |

Le scattering gagne le test propre sans avoir vu une seule image d'entraînement et coûte plus d'un ordre de grandeur de moins à l'extraction ; le ResNet gagne la robustesse au décalage et la compacité. Le carnet explique pourquoi l'invariance garantie par construction n'est pas l'invariance maximale en pratique : un décalage de 2 pixels représente la moitié de la fenêtre de moyenne du scattering à deux échelles. La sonde n'est pas celle de l'étape 00 — caractéristiques standardisées ici, brutes là-bas — et les précisions des deux carnets ne se comparent donc pas terme à terme. Exercices : chercher la couche du ResNet où la robustesse s'installe, concaténer les deux représentations, tracer la précision quand les données se raréfient.

## Installation — pratique, tous niveaux

Les six carnets tournent sur le noyau Python standard de Jupyter (`python3`), sans GPU. La sous-série n'a pas de fichier de dépendances propre ; les paquets nécessaires se répartissent ainsi.

| Carnets | Paquets importés |
|---|---|
| WS-00a, WS-00b | `numpy`, `pywt` (paquet PyWavelets) ; `scipy` et `matplotlib` pour WS-00b |
| WS-00c | `numpy`, `matplotlib`, `scikit-learn`, `threadpoolctl`, `kymatio`, `torchvision` |
| WS-01 | `numpy`, `matplotlib`, `pywt`, `scikit-image` |
| WS-02 | `numpy`, `scikit-learn`, `kymatio`, `torch`, `torchvision` |
| WS-03 | `numpy`, `matplotlib`, `pandas`, `scikit-learn`, `kymatio`, `torch`, `torchvision` |

```bash
pip install numpy scipy matplotlib pandas PyWavelets scikit-image scikit-learn threadpoolctl kymatio torch torchvision
```

La première cellule de code de chaque carnet imprime les versions des bibliothèques utilisées lors de l'exécution enregistrée. Trois ressources sont téléchargées au premier lancement, puis mises en cache :

- **Fashion-MNIST**, par `torchvision`, dans `~/.cache/ft00a` (WS-00c, WS-02, WS-03). WS-00c s'en tient à cette seule source : une autre ne range pas les images dans le même ordre, et l'extrait prélevé ne serait plus le même.
- **Les poids ImageNet de ResNet18**, par `torchvision` (WS-03).
- Les signaux et images de test des autres carnets sont fournis par PyWavelets (`pywt.data`) et scikit-image (`skimage.data`) : rien à télécharger.

## Pour aller plus loin — recherche

### Reproductibilité des mesures

Les précisions de classification citées par la sous-série dépendent de réglages que les carnets épinglent explicitement : la source des images et la tolérance d'arrêt du solveur dans WS-00c, les graines de tirage et de sonde dans WS-03. La note [Reproduction hors carnet des sondes wavelet scattering](../../../../docs/reference/ws-probes-repro.md) établit ce qui se reproduit hors d'une session Jupyter, avec le script autonome [`ws_probes_repro.py`](../../../../scripts/repro/ws_probes_repro.py). Elle relève aussi que WS-00c et WS-03 n'appliquent pas exactement le même test translaté : le geste est le même, l'alternance des décalages ne porte pas sur le même index.

### Limites des bancs

- Les corpus de classification sont volontairement petits pour que les carnets s'exécutent vite : sur un jeu de test de deux cents images, une image pèse 0,005 de précision, et un écart de cet ordre ne départage rien.
- Un seul jeu de données d'images, une seule famille de classifieur linéaire, une seule perturbation (translation périodique de ±2 pixels) : les conclusions valent pour ce protocole.
- Dans WS-03, le ResNet reçoit des silhouettes en niveaux de gris agrandies, loin des photographies de son entraînement ; ce décalage de domaine joue contre lui et le carnet le signale.
- Les pics mémoire de WS-02 sont mesurés par `tracemalloc`, qui ne voit que les allocations Python et ignore les réserves internes de PyTorch.

### Liens avec les autres parcours

- [4.1 — Le neurone convolutif from scratch](../04-Vision/4.1-Conv-NumPy-Torch-Allclose.ipynb) applique la même discipline — écrire en NumPy, puis vérifier la parité numérique avec la bibliothèque — à la convolution.
- [4.3 — Transfer learning](../04-Vision/4.3-TransferLearning-ResNet.ipynb) réutilise le même ResNet18 pré-entraîné, cette fois comme point de départ d'un entraînement.
- [2.3 — Régression linéaire et régression logistique](../02-ML-Cours/2.3-Regression-lineaire-logistique.ipynb) présente le modèle qui sert ici de sonde.
- Les séries [03-Deep-Learning](../03-Deep-Learning/README.md) et [04-Vision](../04-Vision/README.md) donnent le contexte des réseaux convolutifs que WS-03 prend comme terme de comparaison.

## Ressources — tous niveaux

Les notices complètes des articles sont portées par les carnets, auprès des expériences qui s'y appuient :

- les deux articles sur le seuillage des coefficients d'ondelettes — seuil universel et risque SURE pour le premier, BayesShrink pour le second — sont référencés dans la conclusion du [carnet de débruitage](WS-01-Denoising-SOTA.ipynb) ;
- les deux articles fondateurs de la transformée de scattering, l'un pour sa construction, l'autre pour sa stabilité, sont référencés dans la section « Pour aller plus loin » du [carnet de scattering](WS-00c-Scattering-from-scratch.ipynb) ;
- les documentations de [PyWavelets](https://pywavelets.readthedocs.io/), de [`skimage.restoration`](https://scikit-image.org/docs/stable/api/skimage.restoration.html) et de [kymatio](https://www.kymat.io/).
