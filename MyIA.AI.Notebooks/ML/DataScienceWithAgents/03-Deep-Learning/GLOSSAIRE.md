# Glossaire — 3.0 Théorie de l'information · 3.1 Rétropropagation · 3.2 Optimisateurs · 3.3 Régularisation · 3.4 Attention & Transformer

> **Volet** : module 03-Deep-Learning de la série DataScienceWithAgents/ML.
> **Carnets couverts** : `3.0-Theorie-Information.ipynb`, `3.1-Retropropagation.ipynb`,
> `3.2-Optimisateurs.ipynb`, `3.3-Regularisation.ipynb`,
> `3.4-Attention-Transformer-From-Scratch.ipynb`. Les autres carnets du module
> (3.4c, 3.4d, 3.5 et suivants) ne sont pas couverts par cette note.
> **Statut** : référentiel de termes tel qu'employé dans les carnets ;
> chaque entrée cite son ou ses carnets sources.
> **Convention de citation** : `carnet-NN` = cellule NN du carnet cité, numérotée
> à partir de 0 (index de la cellule dans le fichier `.ipynb`).

## Pourquoi ce glossaire

Les cinq carnets partagent un même vocabulaire technique dont les mots revêtent
souvent plusieurs acceptions dans la littérature. Pour qu'un même apprentissage
serve à comparer les implémentations maison et les implémentations PyTorch
sans confusion, on fixe ici le sens tel qu'il est *prouvé* par les mesures
des carnets. Là où le carnet fixe un vocabulaire, on le reprend ; là où un
terme change de statut d'un carnet à l'autre, on le note explicitement.

---

## A. Théorie de l'information (3.0)

### Bigramme (et unigramme)
Modèle de langue de caractères : la probabilité du caractère suivant est
conditionnée au seul caractère précédent, `P(j | i)`, estimée par comptage avec
lissage additif. L'unigramme ignore le contexte et se réduit à la distribution
empirique des caractères. Sur le texte de la fable, le bigramme prédit mieux
(`4,009` contre `4,533` bits/car., soit un gain de `0,525` bit/car.) : ce gain
mesure la structure des suites de caractères, pas la taille du modèle.
**Source** : `3.0` cellules 11 (définition) et 12 (mesure).

### Cross-entropy (entropie croisée)
`H(p, q) = −Σ p(x) log₂ q(x)` : nombre moyen de bits qu'un code optimal pour `p`
paie quand il encode avec les probabilités de `q`. C'est le coût de croire le
modèle `q` quand la vérité est `p`, et elle vaut `H(p) + D_KL(p‖q)`. Minimiser la
cross-entropy revient donc à minimiser la divergence de KL vers la vérité, puisque
`H(p)` ne dépend pas du modèle. Attention à la base du logarithme : `3.0` compte en
bits (`log₂`), alors que la loss de `3.1` (`np.log`) compte en nats. Les deux
diffèrent d'un facteur constant `ln 2`, qui ne change pas le minimiseur.
**Source** : `3.0` cellules 4 (définition), 5 (identité vérifiée, écart `0,00e+00`) ;
`3.1` cellules 4 (« entropie croisée moyenne ») et 5 (fonction `loss_ce`, en nats).

### Divergence de Kullback-Leibler (KL)
`D_KL(p‖q) = Σ p(x) log₂(p(x) / q(x))` : surcoût, en bits, que `q` ajoute au codage
optimal de `p`. Elle est positive (inégalité de Gibbs, nulle si et seulement si
`p = q`) et asymétrique, `D_KL(p‖q) ≠ D_KL(q‖p)` : c'est une *divergence*, pas une
distance. Sur le couple de la section 2, `D(p‖q) = 0,4980` contre `D(q‖p) = 0,8270`.
**Source** : `3.0` cellules 4 (définition et propriétés), 5 (balayage de positivité,
asymétrie mesurée), 6 (lecture).

### Entropie
`H(p) = −Σ p(x) log₂ p(x)` : surprise moyenne par tirage d'une source, en bits, soit
le nombre moyen de bits qu'un code optimal paie pour coder la source. Elle est bornée,
`0 ≤ H(p) ≤ log₂ K` pour un alphabet de `K` symboles, et maximale quand la
distribution est uniforme. Mesurée sur un texte de La Fontaine (`K = 59` caractères
distincts) : `4,53` bits/caractère, contre `5,88` pour l'uniforme.
**Source** : `3.0` cellules 1 (définition et bornes), 2 (mesure), 3 (lecture).

### Gradient qui disparaît (saturation)
Avec une sortie sigmoïde `p = σ(z)` saturée et fausse (`p → 0` alors que `y = 1`),
le gradient de la MSE passe par `p(1 − p)`, qui tend vers `0` : le modèle reste
faux. La cross-entropy garde un gradient proportionnel à `(p − y)`, de l'ordre de
`1`. Mesure depuis des poids initiaux saturés et faux (`[−8, −8, −8]`) : la
cross-entropy atteint `0,882` d'accuracy, la MSE reste à `0,393` ; à `p = 0,02`, le
gradient de la MSE est `51` fois plus faible.
**Source** : `3.0` cellules 7 (mécanisme), 9 (expérience et rapport des gradients),
10 (lecture).

### KL collapse
Phénomène nommé par le carnet dans sa section sur les ponts vers DPO et GRPO : si le
coefficient de régularisation KL `β` est trop faible, la policy diverge de sa
référence, le log-ratio sature et la loss se corrompt. C'est le piège du `log 0` de la
section 2, vu en pratique.
**Source** : `3.0` cellules 15 (définition) et 17 (« le KL collapse que les deux
notebooks signalent »).

### Log-ratio (rapport de probabilités)
`log π_θ − log π_ref` : différence des log-probabilités d'une policy `π_θ` et de sa
référence `π_ref`. C'est la quantité sous-jacente à la récompense implicite de DPO
(`β · log-ratio`) et au penalty KL de GRPO. Le carnet la rapproche du `log₂(p / q)` de
la section 2, dont elle ne diffère que par la base du logarithme.
**Source** : `3.0` cellules 15 (définition, ponts DPO et GRPO) et 16 (calcul sur un
vocabulaire-jouet à quatre tokens).

### MSE (moindres carrés)
Erreur quadratique moyenne, `mean((p − y)²)`, objectif de la régression linéaire
de 2.3. Appliquée à un classifieur à sortie sigmoïde, son gradient porte le facteur
`p(1 − p)` qui s'annule dans les zones saturées : voir *Gradient qui disparaît*.
**Source** : `3.0` cellules 7 (définition et comparaison) et 8 (fonction `entrainer`,
branche `mse`).

### Piège du log 0 (lissage)
Si le modèle `q` met une masse nulle là où la vérité `p` est strictement positive, la
cross-entropy vaut `+∞` et son gradient explose. Le remède pratique est un epsilon
ajouté dans le logarithme (clip `EPS`), ou un lissage additif des comptes. Mesure :
sans clip, la cross-entropy vaut `inf` ; avec `EPS = 10⁻¹²`, elle reste finie à
`11,30` bits.
**Source** : `3.0` cellules 4 et 6 (définition et remède), 5 (mesure), 12 (lissage
additif du bigramme).

### Redondance
`1 − H(p) / log₂ K` : écart entre l'entropie de la source et son maximum uniforme.
Le rapport `H / log₂ K` mesure son efficacité ; plus la redondance est haute, plus la
source est compressible. Sur le texte de la fable, la redondance vaut `22,9 %`.
**Source** : `3.0` cellules 1 (définitions), 2 (mesure), 3 (lecture).

### Surprise
`−log₂ p(x)` : information apportée par un symbole `x` de probabilité `p(x)`, en
bits. Un symbole fréquent surprend peu, un symbole rare beaucoup ; l'entropie est la
surprise moyenne.
**Source** : `3.0` cellule 1.

---

## B. Rétropropagation (3.1)

### Autograd
Différenciation automatique de PyTorch, déclenchée par `loss.backward()`. Elle applique
la règle de la chaîne automatiquement : le carnet 3.1 la traite d'abord comme une
boîte noire, puis écrit à la main ce qu'elle fait en silence.
**Source** : `3.1` cellules 0 (boîte noire), 19 (« la chain rule du §3 appliquée
automatiquement »), 32 (conclusion).

### Delta (δ)
`δ(ℓ) = ∂L / ∂Z(ℓ)` : gradient de la loss par rapport à la pré-activation `Z(ℓ)` de la
couche ℓ. Le signal `δ(ℓ)` se calcule à partir de `δ(ℓ+1)` via les poids, multiplié par
la dérivée locale de l'activation. Pour la sortie softmax avec cross-entropy,
`δ(2) = (P − Y) / n`.
**Source** : `3.1` cellules 7 (définition et équations) et 8 (fonction `backward`).

### Gradient
Vecteur des dérivées partielles de la loss par rapport aux paramètres, noté `∇L`. La
mise à jour de la descente de gradient est `θ ← θ − η∇L`, avec `η` le learning rate.
Le carnet confronte le gradient analytique à un gradient numérique, paramètre par
paramètre.
**Source** : `3.1` cellules 7 (gradients `dW`, `db`), 9 (dérivées partielles), 12
(règle de mise à jour).

### Gradient numérique (vérification par différences centrales)
Approximation de chaque dérivée partielle par différence centrale,
`(L(θ + ε) − L(θ − ε)) / (2ε)`, avec `ε = 10⁻⁵` en float64. L'écart avec le gradient
analytique doit être de l'ordre de `10⁻⁹` ou moins, sinon le backward contient un bug.
Mesure : écart max de `1,286 × 10⁻¹¹` sur les quatre tenseurs, sous le seuil de `10⁻⁶`.
**Source** : `3.1` cellules 9 (méthode et tolérance), 10 (fonction `num_grad_check`),
11 (lecture).

### Initialisation He
Initialisation des poids `W ∼ N(0, √(2 / n_in))`, celle d'origine pour ReLU (He, 2015).
Le carnet l'applique à `W(1)` et `W(2)` (fonction `init_he`). L'initialisation aléatoire
est nécessaire à l'existence même du gradient, voir *Rupture de symétrie*.
**Source** : `3.1` cellules 4 (définition), 5 (fonction `init_he`), 24 (référence He, 2015).

### Initialisation de Xavier (Glorot)
Initialisation des poids `W ∼ N(0, √(1 / n_in))`, adaptée à `tanh` (Glorot & Bengio,
2010). Le carnet la propose en remplacement de He pour l'activation `tanh` (exercice 1).
**Source** : `3.1` cellules 15 (énoncé de l'exercice 1), 16 (TODO `init_xavier`), 24
(référence Glorot & Bengio, 2010).

### Jacobienne (produit vecteur-Jacobien)
Matrice des dérivées partielles d'une étape `z = f(x)` du réseau. La rétropropagation
est le produit de ces matrices pris dans l'ordre inverse (reverse-mode), appliqué à un
vecteur : on ne matérialise jamais la Jacobienne complète, seulement des produits
vecteur-Jacobien. C'est ce qui rend la passe arrière à peine plus coûteuse qu'une passe
avant, quel que soit le nombre de paramètres.
**Source** : `3.1` cellules 28 (capstone : définition et question bonus), 29 (exercice :
produits vecteur-Jacobien dans l'ordre inverse).

### Passe avant (forward pass)
Calcul de la sortie à partir de l'entrée, chaîne de produits matriciels et de
non-linéarités : `Z(1) = XW(1) + b(1)`, `A(1) = ReLU(Z(1))`, `Z(2) = A(1)W(2) + b(2)`,
`P = softmax(Z(2))`. Le réseau est un perceptron multicouche (MLP) de 2 entrées, 32
neurones cachés ReLU et 2 sorties softmax, écrit en NumPy pur sans autograd.
**Source** : `3.1` cellules 0 (MLP), 4 (architecture et équations), 5 (fonction
`forward`), 32 (conclusion).

### Règle de la chaîne (chain rule)
Dérivée d'une fonction composée : la dérivée de `L` par rapport à un poids profond est
le produit des dérivées locales le long du chemin qui relie la sortie à ce poids. Pour
les deux couches du MLP : `∂L/∂W(2) = A(1)ᵀ δ(2)`, `δ(1) = (δ(2) W(2)ᵀ) ⊙ ReLU'(Z(1))`
et `∂L/∂W(1) = Xᵀ δ(1)`. Le carnet souligne qu'un seul forward et un seul backward
suffisent, quel que soit le nombre de couches.
**Source** : `3.1` cellules 7 (principe, équations, « théorème de différentiation en
chaîne appliqué à un graphe »), 8 (fonction `backward`), 32 (conclusion).

### ReLU
Activation `ReLU(z) = max(z, 0)`, de dérivée locale `ReLU'(z) = 1[z > 0]`. Elle annule
le gradient des unités inactives : avec des poids nuls, `A(1) = 0` et le gradient de
`W(2)` s'annule aussi (voir *Rupture de symétrie*).
**Source** : `3.1` cellules 4-5 (fonction `relu`), 7 (dérivée), 8 (`dZ1 = dA1 * (Z1 > 0)`),
23 (init nulle).

### Rétropropagation (passe arrière)
Calcul des gradients de la loss par rapport à tous les paramètres, couche par couche,
de la sortie vers l'entrée, à partir d'une passe avant : `∂L/∂Z(2)`, puis `δ(1)` par
`W(2)` et la dérivée de ReLU, puis les gradients `dW` et `db`. Le carnet l'écrit à la
main (fonction `backward`) avant de la confronter à PyTorch.
**Source** : `3.1` cellules 0 (titre « La rétropropagation : la chaîne des gradients à la
main »), 7-8 (principe et code `backward`), 18-19 (parité avec PyTorch).

### Rupture de symétrie
Avec une initialisation nulle (poids identiques), chaque neurone d'une couche reçoit
exactement le même gradient et reste identique à ses voisins : la symétrie n'est jamais
brisée. Mesure : la norme du gradient de `W(1)` vaut exactement `0`, le réseau reste à
`0,500` d'accuracy et la loss est figée à `ln 2 ≈ 0,6931`. Une initialisation nulle
produit un réseau mort.
**Source** : `3.1` cellules 22 (principe), 23 (mesure : `||grad W1|| = 0`, loss
`0,6931`), 24 (lecture), 32 (conclusion).

---

## C. Optimiseurs (3.2)

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
cellule 8). **Source** : `3.2` cellules 8-9 (validation bit-à-bit contre
`torch.optim.Adagrad`, écart `0.00e+00`).

### Biais (correction de biais Adam)
Facteur multiplicatif `1 / (1 - β^t)` appliqué aux estimateurs des
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
la boule dans le ravin, cellule 5). **Source** : `3.2` cellule 5
(implémentation NumPy) + cellule 6 (validation).

### Nesterov
Variante du momentum qui *regarde un pas devant* : la vélocité est
calculée en appliquant d'abord le momentum aux paramètres, puis en
évaluant le gradient à ces paramètres « extrapolés ». **Source** : `3.2`
cellule 19 (Exercice 1) — distinction explicite avec le momentum
classique dans l'énoncé.

### Plateau de bruit
Niveau minimal de loss qu'un optimiseur peut atteindre en régime
mini-batch bruité, indépendamment du modèle : c'est le plancher
déterministe imposé par la variance du gradient stochastique. **Source** :
`3.2` cellule 25 — le schedule cosine *casse* ce plateau, le schedule
constant le *respecte*.

### RMSProp
Tieleman & Hinton, 2012 (référence cellule 32). Comme Adagrad mais la
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

## D. Régularisation (3.3)

### Biais / Variance (décomposition)
Décomposition classique de l'erreur de généralisation : `erreur = biais² +
variance + bruit irréductible`. **Source** : `3.3` cellule 25 (lien vers
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

## E. Attention et Transformer (3.4)

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
(« la netteté du softmax est un **réglage**, pas un hasard ») ; `3.1` cellules 4-5
(sortie du MLP, calcul stabilisé par soustraction du maximum).

### Température (échantillonnage)
Paramètre T appliqué aux logits avant softmax :
`softmax(logits / T)`. Voir *Échantillonnage*. **Source** : `3.4`
cellules 31-32 ; `3.0` cellules 11 et 13 (même opération, mesurée par la KL : minimum
en `T = 1`).

### Top-k (échantillonnage)
Variante de l'échantillonnage qui restreint le tirage aux `k`
caractères de plus haute probabilité, renormalisant sur ce sous-set.
**Source** : `3.4` cellule 33 (Exercice 2) — utile à température
élevée pour éviter les tirages catastrophiques.

---

## F. Conventions transverses aux carnets 3.2 à 3.4

### Validation contre PyTorch
Tous les trois carnets valident leurs implémentations from scratch
contre les implémentations PyTorch équivalentes, à **epsilon de
float64 près** quand le calcul est exact (`3.2` cellules 6, 9, 12),
ou à **mêmes poids** quand la comparaison porte sur une
architecture (`3.4` PREUVE D'ÉQUIVALENCE, cellules 18-21). Cette
convention est ce qui distingue une *implémentation* d'une
*illustration*. Le carnet 3.1 suit la même convention : parité NumPy / PyTorch en
float64, écart de loss initiale de `1,11 × 10⁻¹⁶` (cellules 18-19).

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