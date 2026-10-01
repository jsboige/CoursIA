# Glossaire — 3.2 Optimisateurs · 3.3 Régularisation · 3.4 Attention & Transformer

> **Volet** : module 03-DeepLearning de la série DataScienceWithAgents/ML.
> **Carnets couverts** : `3.2-Optimisateurs.ipynb`, `3.3-Regularisation.ipynb`,
> `3.4-Attention-Transformer-From-Scratch.ipynb` (volets 3.0 et 3.1 couverts par
> la PR #18505, hors-périmètre de cette note).
> **Statut** : référentiel de termes tel qu'employé dans les carnets ;
> chaque entrée cite sa ou ses première et notes carnet-source.
> **Convention de citation** : `carnet-NN` = cellule NN du carnet cité.

## Pourquoi ce glossaire

Les trois carnets partagent un même vocabulaire technique dont les mots revétent
souvent plusieurs acceptions dans la littérature. Pour qu'un même apprentissage
serve à comparer les implémentations maison et les implémentations PyTorch
sans confusion, on fixe ici le sens tel qu'il est *prouvé* par les mesures
des carnets. Là où le carnet fixe un vocabulaire, on le reprend ; là où un
terme change de statut d'un carnet à l'autre, on le note explicitement.

---

## A. Optimiseurs (3.2)

### Adam
Estimateur adaptatif combinant moyenne glissante du gradient (premier moment,
β₁ ≈ 0.9) et de son carré (second moment, β₂ ≈ 0.999), avec correction de
biais aux premiers pas. **Source** : `3.2` cellule 11 (implémentation
NumPy) + cellule 12 (validation contre `torch.optim.Adam`, écart mesuré
`1.11e-16` à float64 près).

### Adagrad
Adaptive gradient : learning rate par paramètre, normalisé par la racine
carrée de la somme cumulée des carrés des gradients passés. Le carnet
souligne que cette accumulation est **non bornée** et cause la *mort* du
learning rate en fin d'entraînement (« meurt de son accumulation infinie »,
cellule 31). **Source** : `3.2` cellules 8-9 (validation bit-à-bit contre
`torch.optim.Adagrad`, écart `0.00e+00`).

### Biais (correction de biais Adam)
Facteur multiplicatif `1 - d / (1 - β^t)` appliqué aux estimateurs des
deux moments aux premiers pas, sans quoi ces estimateurs sont nuls par
construction et l'optimiseur n'avance pas. **Source** : `3.2` cellule 11
(code) + cellule 12 (validation). Le carnet précise que c'est un point de
diagnostic clé en cas de stagnation.

### Bruit de gradient
En mini-batch, le gradient calculé sur un sous-échantillon aléatoire est
un **estimateur bruité** du gradient complet : son espérance est le vrai
gradient, sa variance est non nulle. **Source** : `3.2` cellule 24 (régime
(b) mini-batch 32) — le carnet distingue explicitement le « plancher de
bruit » que le schedule cosine vient *casser*.

### GD (gradient descent) / SGD
Descente de gradient **batch** (full-batch, gradient exact) ou
**stochastique** (mini-batch). Le carnet les distingue nettement :
le full-batch est déterministe (régime (a)), le mini-batch est bruité
(régime (b)). **Source** : `3.2` cellules 2, 5, 22-25.

### Momentum
Moyenne glissante exponentielle des gradients passés (β ≈ 0.9), qui
*accélère le mouvement cohérent et amortit l'oscillation* (analogie de
la boule dans le ravin, cellule 31). **Source** : `3.2` cellule 5
(implémentation NumPy) + cellule 6 (validation).

### Nesterov
Variante du momentum qui *regarde un pas devant* : la vélocité est
calculée en appliquant d'abord le momentum aux paramètres, puis en
évaluant le gradient à ces paramètres «展望és ». **Source** : `3.2`
cellule 19 (Exercice 1) — distinction explicite avec le momentum
classique dans l'énoncé.

### Plateau de bruit
Niveau minimal de loss qu'un optimiseur peut atteindre en régime
mini-batch bruité, indépendamment du modèle : c'est le plancher
déterministe imposé par la variance du gradient stochastique. **Source** :
`3.2` cellule 25 — le schedule cosine *casse* ce plateau, le schedule
constant le *respecte*.

### RMSProp
Tieleman & Hinton, 2012 (référence cellule 33). Comme Adagrad mais la
somme cumulée est remplacée par une moyenne glissante exponentielle :
le learning rate reste *vivant*. **Source** : `3.2` cellule 11
(implémentation) + cellule 12 (validation, écart `2.22e-16`).

### Schedule (de learning rate)
Plan de décroissance du learning rate au cours de l'entraînement :
*step* (paliers) ou *cosine* (cosinus décroissant). **Contre-intuitif
mais mesuré** dans `3.2` : en full-batch déterministe le schedule
*coûte* (cellule 23), en mini-batch bruité il *casse le plancher de
bruit* (cellule 25). **Source** : `3.2` cellules 21-25.

### Validation bit-à-bit
Test de conformité entre une implémentation NumPy from scratch et
l'implémentation PyTorch de référence, mesurant l'écart relatif entre
leurs trajectoires d'optimisation. **Source** : `3.2` cellules 6, 9, 12
(écarts `1.11e-16` à `0.00e+00` à float64 près — contre quelques `4e-6` à
`1e-5` permis par défaut). Cette convention se prolonge en 3.4 (PREUVE
D'ÉQUIVALENCE, cellules 18-21).

### Warmup
Croissance **progressive** du learning rate depuis une valeur faible
vers la valeur nominale, sur les premiers pas d'entraînement. **Source** :
`3.2` cellule 29 (Exercice 3) — distinction avec un démarrage à froid
direct, qui se révèle problématique avec un optimiseur adaptatif en
mini-batch bruité.

---

## B. Régularisation (3.3)

### Biais / Variance (décomposition)
Décomposition classique de l'erreur de généralisation : `erreur = biais² +
variance + bruit irréductible`. **Source** : `3.3` cellule 24 (lien vers
[2.5](../02-ML-Cours/2.5-Biais-Variance-CV-ROC.ipynb) qui établit la
décomposition sur arbres de profondeur croissante). Le carnet 3.3
*transpose* la décomposition aux réseaux profonds en la lisant
directement dans les courbes train/val.

### Capacité (d'un modèle)
Aptitude d'un modèle à mémoriser des valeurs d'entraînement *arbitraires*.
Le carnet 3.3 utilise un ratio paramètres/exemples ≈ 170:1 (17 000
paramètres pour 100 points d'entraînement) comme seuil garantissant la
capacité de tout mémoriser. **Source** : `3.3` cellule 2.

### Courbe en U
Forme caractéristique de la val loss en régime de surapprentissage :
elle descend, atteint un minimum, puis remonte pendant que la train
loss continue de baisser. **Source** : `3.3` cellule 7 (mesure
quantitative : minimum à epoch 1052, remontée de `+0.154`, soit 67 %
de sa valeur minimale).

### Dropout (Srivasastava et al., 2014)
Mise à zéro aléatoire de chaque unité cachée avec probabilité `p` à
chaque passe d'entraînement, avec *dropout inversé* (mise à l'échelle
`1/(1-p)` des activations survivantes pendant l'entraînement pour
conserver l'espérance). **Source** : `3.3` cellules 8-12. Référence :
Srivastava, Hinton, Krizhevsky, Sutskever, Salakhutdinov, JMLR 15 (2014).

### Dropout inversé (Inverted dropout)
Mise à l'échelle `1/(1-p)` des activations survivantes **pendant
l'entraînement** (et non à l'évaluation), qui conserve l'espérance de
l'activation sans avoir à modifier l'inférence. **Source** : `3.3`
cellule 8. Le carnet valide explicitement l'invariant sur 100 000
valeurs : espérance de sortie `-0.0050` vs entrée `-0.0014`, écart
`0.0036` ≈ fluctuation d'échantillonnage.

### Early stopping
Arrêt de l'entraînement quand la val loss ne s'est pas améliorée
pendant `N` epochs (*patience*), avec **restauration des meilleurs poids**
capturés dans la trajectoire. **Source** : `3.3` cellules 18-20. Le
carnet insiste : c'est *un pur contrôle de trajectoire*, il ne touche
ni à la loss ni au gradient.

### L2 dans la loss vs decay dans l'update
Deux conventions pour la régularisation par norme des poids :
- **L2 dans la loss** : ajouter `(λ/2)·‖w‖²` à la loss ; le gradient
  porte un terme `λ·w` qui entre dans la vélocité avec momentum ;
- **decay dans l'update** (style AdamW, Loshchilov & Hutter 2019) :
  appliquer `w ← w·(1 − lr·λ)` directement, indépendamment de la
  vélocité.
**Ces deux conventions sont strictement équivalentes en SGD simple ;
avec momentum elles divergent.** Mesure : à λ = 3e-3 et momentum 0.9,
‖W‖ final de 8.81 (L2 dans la loss) contre 22.43 (decay dans
l'update) — rapport 2,5×. **Source** : `3.3` cellules 13-17.

### Mémorisation
Capacité d'un réseau à coller à des points dont la classe contredit la
géométrie (labels bruités). En `3.3`, 12 labels faux sur 100 points
d'entraînement sont la *composante de bruit d'annotation* — le réseau
de 17 000 paramètres a la capacité de les mémoriser (ratio 170:1),
mais le surapprentissage nuisible vient précisément de cette
mémorisation. **Source** : `3.3` cellules 7, 24.

### Patience (early stopping)
Nombre d'epochs sans amélioration de la val loss toléré avant arrêt.
**Source** : `3.3` cellule 19 — `patience = 400` produit un arrêt à
l'epoch 1452/3000 (52 % de calcul économisé), avec restauration des
poids de l'epoch 1052 (le minimum de val loss).

### Régularisation par trajectoire
Caractérisation de l'early stopping comme une régularisation qui ne touche
*ni à la loss ni au gradient*, mais seulement au point de la
trajectoire d'entraînement qui est livré. **Source** : `3.3`
cellule 20.

### Weight decay
Terme générique couvrant les deux conventions ci-dessus (L2 dans la
loss / decay dans l'update). Le carnet 3.3 utilise *decay* seul quand
la convention est non encore tranchée, et précise la convention dès que la
mesure dépend du distingué (cellules 16-17). **Source** : `3.3`
cellules 13-17.

---

## C. Attention et Transformer (3.4)

### Anti-diagonale
Dans la matrice d'attention d'une tâche d'inversion de séquence, le
poids est concentré sur l'anti-diagonale : la position de sortie `i`
fait attention à la position d'entrée `n - i` (la plus éloignée pour
sa position représentative). **Source** : `3.4` cellule 8 (énoncé de
l'exercice) + cellule 10 (interprétation).

### Bloc transformer
Composition canonique : `LayerNorm → attention → add (résiduelle) →
LayerNorm → MLP → add (résiduelle)`. Le carnet 3.4 insiste sur les
*connexions résiduelles* et la *LayerNorm* (cellule 22). **Source** :
`3.4` cellules 22-24.

### Connexions résiduelles
Court-circuits qui ajoutent l'entrée d'une couche à sa sortie, sans
transformation. Sans elles, le gradient se dilue dans la profondeur
(le carnet le mentionne dans la discussion du bloc, cellule 22).
**Source** : `3.4` cellule 22.

### Distribution d'attention
Ligne (ou colonne) de la matrice d'attention A ∈ ℝ^{T×T}, qui doit
sommer à 1 par construction du softmax sur la dernière dimension.
**Source** : `3.4` cellule 10 (interprétation).

### Échantillonnage (caractère suivant)
Prédiction d'un caractère par échantillonnage sur la distribution
apprise, paramétrisée par une *température* T. À T = 1.0
échantillonner tel quel, à T < 1.0 la distribution se concentre (moins
de variété, plus de déterminisme), à T > 1.0 elle s'aplatit (plus de
variété, plus de bruit). **Source** : `3.4` cellules 31-32.

### Encodage positionnel sinusoïdal
Schéma de Vaswani et al. 2017 : pour chaque position `t` et chaque
dimension `2i` (cosinus) ou `2i+1` (sinus) de l'encodage,
`PE(t, 2i) = sin(t / 10000^{2i/d})`,
`PE(t, 2i+1) = cos(t / 10000^{2i/d})`. Le carnet insiste sur le
double rôle : *injecter la position* et *laisser les positions
communiquer entre elles* (cellule 4). **Source** : `3.4` cellules 5-7.

### Masque causal
Matrice booléenne qui, dans l'attention d'un Transformer causal (langue
modèle), empêche la position `i` de lire les positions `> i` (futur).
**Source** : `3.4` cellule 11 — sans ce masque, le modèle ne peut pas
*prédire le suivant* sans tricher.

### Multi-têtes
Décomposition du mécanisme d'attention en `h` regards indépendants de
dimension `d/h` chacun, dont les sorties sont concaténées puis
reprojetées en dimension `d`. **Source** : `3.4` cellules 14-16
(implémentation) + 17-19 (PREUVE D'ÉQUIVALENCE contre
`torch.nn.MultiheadAttention`, mêmes poids).

### Produit scalaire mis à l'échelle (scaled dot product)
Forme canonique de l'attention : `A = softmax((Q·Kᵀ) / √d) · V`. Le
facteur `√d` compense l'amplification des produits scalaires en
grande dimension, sans quoi le softmax sature. **Source** : `3.4`
cellule 21 (`F.scaled_dot_product_attention`).

### Q, K, V (query, key, value)
Trois projections apprises (W_Q, W_K, W_V) à partir du même vecteur
d'entrée x. L'attention est `softmax((Q·Kᵀ) / √d) · V`. Le carnet
insiste : ce ne sont pas des *projections séparées* mais trois
*projections apprises* de la même entrée (cellule 10). **Source** :
`3.4` cellules 8-10.

### Sac de mots (bag-of-words)
Représentation qui ignore l'ordre des mots d'un document — la
séquence « le chien mord » et « mord le chien » sont **indiscernables**.
Le carnet 3.4 utilise cette observation pour introduire la notion de
*problème séquentiel*. **Source** : `3.4` cellule 2.

### Softmax
Fonction qui transforme un vecteur de réels en distribution de
probabilités : `softmax(x)_i = exp(x_i) / Σ_j exp(x_j)`. Saturation
quand un `x_i` est grand devant les autres (la distribution se
concentre). **Source** : `3.4` cellule 8 (mention) + cellule 10
(« la netteté du softmax est un **réglage**, pas un hasard »).

### Température (échantillonnage)
Paramètre T appliqué aux logits avant softmax :
`softmax(logits / T)`. Voir *Échantillonnage*. **Source** : `3.4`
cellules 31-32.

### Top-k (échantillonnage)
Variante de l'échantillonnage qui restreint le tirage aux `k`
caractères de plus haute probabilité, renormalisant sur ce sous-set.
**Source** : `3.4` cellule 33 (Exercice 2) — utile à température
élevée pour éviter les tirages catastrophiques.

---

## D. Conventions transverses aux trois carnets

### Validation contre PyTorch
Tous les trois carnets valident leurs implémentations from scratch
contre les implémentations PyTorch équivalentes, à **epsilon de
float64 près** quand le calcul est exact (`3.2` cellules 6, 9, 12),
ou à **mêmes poids** quand la comparaison porte sur une
architecture (`3.4` PREUVE D'ÉQUIVALENCE, cellules 18-21). Cette
convention est ce qui distingue une *implémentation* d'une
*illustration*.

### Mesure avant verdict
Aucune affirmation de superiority (sur les systèmes d'optimisation, sur
les mécanismes de régularisation, sur les têtes d'attention) n'est
posée dans les carnets sans une mesure quantitative derrière — la
plupart sont assorties d'un écart numérique (`1.11e-16`, `+0.154`,
`2,5×`, `98,5 % ± 0,0 %`). Le glossaire suit la même règle.

### Multi-seed
Toute comparaison entre mécanismes est répétée sur 3 graines au moins
(`3.3` cellule 21). Le carnet précise qu'*un seul seed ne distingue
pas un gain d'un coup de chance*. Cette règle vaut aussi pour les
**advancements** qu'on annonce : un gain annoncé sur un seul seed
n'est rien.