# Executions reelles sous JupyterLite (Pyodide)

<!-- Genere par scripts/notebook_tools/pyodide_browser_run.py -- ne pas editer a la main. -->

Les carnets ci-dessous ont ete **realement executes** dans un navigateur (Chromium headless)
contre le noyau Pyodide du site JupyterLite construit localement : le menu « Run » puis
« Run All Cells » a ete declenche dans la page, et les sorties sont lues dans le DOM.
« Cellules executees » compte les cellules de code dont le compteur d'execution est passe
de `[ ]:` a `[n]:`.

| Carnet | Cellules code | Cellules executees | Cellules avec sortie | Erreurs | Duree (s) | Premier resultat (s) | Verdict |
|---|---:|---:|---:|---:|---:|---:|---|
| `10-SIG-3D-Tiles-Python.ipynb` | 6 | 6 | 6 | 0 | 29.6 | 9.9 | **succes** |
| `AgentSystems-02-Perception-Active-Valeur-Information-Python.ipynb` | 6 | 6 | 3 | 0 | 15.8 | 6.7 | **succes** |
| `Quotients-Fibres-Recollement-Python.ipynb` | 9 | 9 | 9 | 0 | 20.4 | 6.8 | **succes** |
| `Argumentation-01-Toulmin-Model-Python.ipynb` | 7 | 7 | 7 | 0 | 14.4 | 6.8 | **succes** |
| `Audio-06-3-AudioDiffusion-Comparison-A-vs-B-Python.ipynb` | 1 | 1 | 1 | 0 | 14.1 | 6.6 | **succes** |
| `Causalite-00-Echelle-de-Pearl-Intro-Python.ipynb` | 10 | 10 | 5 | 0 | 20.4 | 6.8 | **succes** |
| `Chaines-05-Energie-Hamiltonien-Premiere-Puissance-Python.ipynb` | 8 | 8 | 7 | 0 | 17.5 | 6.9 | **succes** |
| `Coalitions-04-Munkres-Affectation-Python.ipynb` | 10 | 10 | 10 | 0 | 34.0 | 6.8 | **succes** |

## `10-SIG-3D-Tiles-Python.ipynb`

Verdict : **succes** · cellules executees 6/6 · duree 29.6 s · declenchement : `menu Run > Run All Cells`

### Cellule 1 (`[1]:`)

```
NumPy 2.4.6 — graine fixée : 2026
```

### Cellule 3 (`[2]:`)

```
Raster : (120, 120), pas nominal 1.0 m ; bâtiments : 3
```

### Cellule 6 (`[3]:`)

```
Contrôle hors emprise : Point hors emprise du raster
```

### Cellule 8 (`[4]:`)

```
Pas | dimensions | sommets | fraction de la grille complète
  1 | 120 × 120 |  14400 | 100.0%
  2 | 60 × 60 |   3600 | 25.0%
  4 | 30 × 30 |    900 | 6.2%
  8 | 15 × 15 |    225 | 1.6%
 16 | 8 × 8 |     64 | 0.4%
```

### Cellule 11 (`[5]:`)

```
Image synthétique : 120 × 120 pixels ; aperçu simulé : 24 × 24 pixels.
Aucune mesure de latence, requête HTTP ou qualité 3D n'est effectuée ici.
```

### Cellule 14 (`[6]:`)

```
Exercice à compléter
```

## `AgentSystems-02-Perception-Active-Valeur-Information-Python.ipynb`

Verdict : **succes** · cellules executees 6/6 · duree 15.8 s · declenchement : `menu Run > Run All Cells`

### Cellule 3 (`[1]:`)

```
Seuil bayesien q* = L_OPP/(L_ACT+L_OPP) = 0.231
A priori q0 = 0.40  ->  action optimale : ne pas lancer
Risque bayesien a priori : 18.00
```

### Cellule 6 (`[2]:`)

```
capteur                     EVOI   cout  valeur nette
test de marche             10.40   10.0          0.40
analyse concurrentielle     0.00   10.0        -10.00
```

### Cellule 9 (`[3]:`)

```
POLITIQUE ACTIVE
  achete test de marche  (lecture: bonne)
  ->  decision: lancer   |   cout total: 10.0

POLITIQUE NAIVE
  achete test de marche  (lecture: bonne)
  achete analyse concurrentielle  (lecture: bonne)
  ->  decision: lancer   |   cout total: 20.0
```

## `Quotients-Fibres-Recollement-Python.ipynb`

Verdict : **succes** · cellules executees 9/9 · duree 20.4 s · declenchement : `menu Run > Run All Cells`

### Cellule 2 (`[1]:`)

```
numpy 2.4.6 · scipy 1.18.0
Graine fixée : RNG.bit_generator.state['state']['state'] = 165599870888322723834153514999483032662
```

### Cellule 4 (`[2]:`)

```
N = 5000 observations, rho = 0.6
X1 : mean = 0.0130, std = 1.0063
X2 : mean = -0.0097, std = 1.0146
Empirical corr(X1, X2) = 0.6081  (cible: 0.6)
```

### Cellule 6 (`[3]:`)

```
Discretisation : bins = 24 x 24
H(X1)          = 2.5980 nats
H(X2)          = 2.6966 nats
H(X1,X2)       = 5.0301 nats
I(X1;X2)       = 0.2645 nats   (commun)
H(X1)-I        = 2.3335 nats  (perdu par projection sur X2)
H(X1,X2)-H1-H2 = -0.2645 nats  (toujours <= 0 en discret)
I theorique (gauss. bivariee, rho=0.6) = 0.2231 nats
Biais plug-in = +0.0414 nats (sur-estimation mesuree sur ce tirage)
Terme de Miller-Madow pour I (m1=24, m2=24, m12=294, N=5000) = +0.0247 nats
```

### Cellule 8 (`[4]:`)

```
graine  20260822 : I = 0.2645 nats, ecart a la theorie = +0.0414 nats, Miller-Madow(I) = +0.0247 nats
graine         1 : I = 0.2542 nats, ecart a la theorie = +0.0311 nats, Miller-Madow(I) = +0.0219 nats
graine         7 : I = 0.2613 nats, ecart a la theorie = +0.0381 nats, Miller-Madow(I) = +0.0249 nats
graine        42 : I = 0.2383 nats, ecart a la theorie = +0.0151 nats, Miller-Madow(I) = +0.0280 nats
graine        99 : I = 0.2489 nats, ecart a la theorie = +0.0257 nats, Miller-Madow(I) = +0.0228 nats
graine       123 : I = 0.2459 nats, ecart a la theorie = +0.0227 nats, Miller-Madow(I) = +0.0221 nats
graine      2024 : I = 0.2387 nats, ecart a la theorie = +0.0156 nats, Miller-Madow(I) = +0.0213 nats
graine     31337 : I = 0.2712 nats, ecart a la theorie = +0.0481 nats, Miller-Madow(I) = +0.0240 nats
Ecart plug-in sur 8 tirages : min = +0.0151, moyenne = +0.0297, max = +0.0481 nats
Tous les ecarts de meme signe que le terme de Miller-Madow : True
```

### Cellule 11 (`[5]:`)

```
Exercice 1 a completer : voir la cellule precedente pour les etapes
```

### Cellule 13 (`[6]:`)

```
Q : 4 bins equipopulants de S = X1 + X2
  Q = 0 : 1250 obs  (25.0%)
  Q = 1 : 1250 obs  (25.0%)
  Q = 2 : 1250 obs  (25.0%)
  Q = 3 : 1250 obs  (25.0%)

I(X1;X2 | Q) = 0.4453 nats
I(X1;X2)     = 0.2645 nats
Ratio I(X1;X2|Q) / I(X1;X2) = 1.684

=> Q N'EST PAS operationnel : la dependance ne se factorise pas par une variable 1D simple.
   Le temps 4 ne sera pas tente (cf critere d'acceptation).
```

### Cellule 15 (`[7]:`)

```
Exercice 2 a completer : voir la cellule precedente pour les etapes
```

### Cellule 17 (`[8]:`)

```
Temps 4 NON TENTE : Q non operationnel au temps 3.
Conclusion : la dependance entre X1 et X2 ne se factorise pas par une variable 1D.
Le critere de Finetti n'est PAS atteint a ce niveau de finesse.
Pour aller plus loin : quotient multidimensionnel (PCA / ICA) ou raffinement.
```

### Cellule 19 (`[9]:`)

```
Exercice 3 a completer : voir la cellule precedente pour les etapes
```

## `Argumentation-01-Toulmin-Model-Python.ipynb`

Verdict : **succes** · cellules executees 7/7 · duree 14.4 s · declenchement : `menu Run > Run All Cells`

### Cellule 3 (`[1]:`)

```
[X] Argument Toulmin (complet: True)
  Claim    : Le projet X doit etre finance
  Data     : X a un ROI projete de 15%
  Warrant  : Les projets a ROI eleve meritent financement
  Backing  : Principe d'allocation rationnelle du capital
  Qualifier: probablement
  Rebuttals cibles: ['(aucun)']

Complet ? True ; pieces manquantes : []
```

### Cellule 5 (`[2]:`)

```
[leak] Argument Toulmin (complet: False)
  Claim    : X doit etre finance
  Data     : X a un ROI de 15%
  Warrant  : (manquant)
  Backing  : (non precise)
  Qualifier: (non precise)
  Rebuttals cibles: ['(aucun)']

>>> Argument INCOMPLET : piece(s) essentielle(s) manquante(s) = ['warrant']
>>> Le warrant (D -> C) doit etre explicite : sur quelle regle d'inference passe-t-on du ROI a l'obligation de financer ?
```

### Cellule 7 (`[3]:`)

```
=== Debat a 2 arguments (rebuttal mutuel) ===
[A] Argument Toulmin (complet: True)
  Claim    : Le projet X doit etre finance
  Data     : X a un ROI projete de 15%
  Warrant  : Les projets a ROI eleve meritent financement
  Backing  : Principe d'allocation rationnelle du capital
  Qualifier: probablement
  Rebuttals cibles: ['B']

[B] Argument Toulmin (complet: True)
  Claim    : Le projet X ne doit pas etre finance
  Data     : X presente un risque de defaut de 40%
  Warrant  : Les projets trop risques doivent etre evites
  Backing  : Principe de prudence
  Qualifier: possiblement
  Rebuttals cibles: ['A']

Cadre de Dung : args=['A', 'B'], attacks=[('A', 'B'), ('B', 'A')]
Extension grounded : {} (vide)
>>> Verdict : A<->B forment un cycle. Ni l'un ni l'autre ne defend l'autre
    -> grounded VIDE = standoff, aucune conclusion ne survit seule.
```

### Cellule 9 (`[4]:`)

```
=== Debat a 3 arguments (C arbitre en refutant B) ===
[C] Argument Toulmin (complet: True)
  Claim    : Le risque de defaut de X est surestime
  Data     : L'historique montre 10% de defaut reel sur projets similaires
  Warrant  : Les projections de risque doivent etre calibrees sur donnees passees
  Backing  : Principe de calibration empirique
  Qualifier: fortement
  Rebuttals cibles: ['B']

Cadre de Dung : args=['A', 'B', 'C']
                attacks=[('A', 'B'), ('B', 'A'), ('C', 'B')]
Extension grounded : ['A', 'C']

>>> Lecture : C defait B -> B ne peut plus attaquer A -> A est defendu.
    Les claims A et C survivent ; B (le contre-argument) est exclu.
    Le warrant sous-jacent : un seul arbitre peut faire basculer un debat
    indécis vers une conclusion, SANS toucher aux arguments principaux.
```

### Cellule 12 (`[5]:`)

```
Exercice 1 a completer.
```

### Cellule 14 (`[6]:`)

```
Exercice 2 a completer.
```

### Cellule 16 (`[7]:`)

```
Exercice 3 a completer.
```

## `Audio-06-3-AudioDiffusion-Comparison-A-vs-B-Python.ipynb`

Verdict : **succes** · cellules executees 1/1 · duree 14.1 s · declenchement : `menu Run > Run All Cells`

### Cellule 8 (`[1]:`)

```
==============================================================================
Critere                                Bloc A (scratch)       Bloc B (SOTA)         
==============================================================================

-- Chaine AudioLDM (texte -> audio) --
lignes de code coeur                   472 (A.1)              8 (B.4)               
parametres (M)                         ~0.06 (A.1)            421.0 (B.4)           
MCD qualite (dB)                       A.1: latent sigma 0.69 20.7 (distrib.)       
dependance                             torch + torchaudio     diffusers + transforme

-- Chaine vocodeur (mel -> waveform) --
lignes de code coeur                   173 (A.2)              3 (B.5)               
parametres (M)                         30.76 (A.2)            13.94 (B.5)           
MCD qualite (dB)                       71.58 -> entrain.      8.93 (B.5)            
latence inference                      selon subset (entrain. 25 ms chaud (B.5)     
VRAM (GiB)                             CPU ou GPU modeste     0.11 (B.5)            
dependance                             torch + torchaudio     transformers + torch  

==============================================================================
Notes :
 - Bloc A mesure la *comprehension* (chaque couche est lisible et modifiable).
 - Bloc B mesure la *production* (qualite native, latence, determinisme industriel).
 - Le facteur ~59x d abstraction de B.4 vs A.1 documente la barriere du SO
```

## `Causalite-00-Echelle-de-Pearl-Intro-Python.ipynb`

Verdict : **succes** · cellules executees 10/10 · duree 20.4 s · declenchement : `menu Run > Run All Cells`

### Cellule 4 (`[1]:`)

```
Taux de cholera par quartier (DGP illustre) :
  Soho (pompe Broad)                  : 9.10 %
  Bloomsbury (autre pompe)            : 0.40 %
  Westminster (riviere)               : 0.90 %
  Camden (puits profond)              : 0.10 %
```

### Cellule 6 (`[2]:`)

```
Aretes du DAG : [('Z', 'X'), ('Z', 'Y'), ('X', 'M'), ('M', 'Y')]
```

### Cellule 8 (`[3]:`)

```
P(Y = 1 | X = 1) = 0.7078  (sur 44,050 unites traitees)
P(Y = 1 | X = 0) = 0.3221  (sur 55,950 unites non traitees)
Association observee (difference) : +0.3857

Note : Z est distribue differemment dans les deux groupes.
  E[Z | X = 1] = +0.5239  (les traites sont plus aptes)
  E[Z | X = 0] = -0.4201  (les non-traites sont moins aptes)
  => P(Y | X) reflete a la fois l'effet causal et le biais de selection par Z.

Bruits exogenes conserves (requis par le contrefactuel individuel, cellule a9c3e450) :
  eps_M : N(0, 0.5^2)   -- 100,000 tirages
  U_Y   : Uniform(0, 1) -- 100,000 tirages
```

### Cellule 10 (`[4]:`)

```
P(Y = 1 | do(X = 1)) = 0.6063  (backdoor adjustment sur Z)
P(Y = 1 | do(X = 0)) = 0.4039
Effet causal (difference) : +0.2024

Comparaison :
  P(Y | X = 1) - P(Y | X = 0)  = +0.3857  (biaise par Z)
  P(Y | do(X=1)) - P(Y | do(X=0)) = +0.2024  (effet causal ajuste)

L'association naive surestime (ou sous-estime) l'effet causal selon la direction du confounding.
Le backdoor adjustment par Z neutralise ce biais.
```

### Cellule 12 (`[5]:`)

```
Pool d'Alice-like (X=0, Y=1) : 18,024 unites (sur 55,950 avec X=0)

Abduction : bruits exogenes conserves pour 18,024 Alice-like (Z, eps_M, U_Y)
  Factuel (X=0) : Y0 = 1.0000  (doit valoir 1.0 -- selection sur Y == 1)
Action    : do(X=1) -- meme eps_M, meme U_Y, X force a 1
Prediction: P(Y_1=1 | X=0, Y=1) = 1.0000  (contrefactuel individuel)

Temoin monotone (algebrique, propre a CE SCM) :
  M_1 - M_0 = 0.7 * (1 - 0) = 0.7  =>  logit_1 - logit_0 = 1.5 * 0.7 = 1.05
  (mesure : min 1.0500, max 1.0500 -- constant)
  sigmoid croissante => sigmoid(logit_0 + 1.05) > sigmoid(logit_0) > U_Y pour toute
  Alice-like (Y_0 = 1 signifie precisement U_Y < sigmoid(logit_0)).
  => Y_1 = 1 pour CHAQUE unite observee Y_0 = 1 : P(Y_1=1 | X=0, Y=1) = 1 exactement.

Lecture : le contrefactuel individuel n'est PAS la prediction moyenne P(Y | do(X=1)).
  L'effet est monotone et positif : toute Alice ayant reussi sans mentorat reussit
  encore avec. La question 'aurait-elle reussi ?' a donc la reponse 100%, pas une
  moyenne de probabilites sur des unites fraiches. L'ecart entre les deux lectures
  est precisement ce que le 3e echelon de Pearl ajoute : l'information que porte
  l'observation Y_0 = 1 sur le bruit U_Y de CETTE unite.

Note SCM : ce resultat a 100% est une CONSEQUENCE DE LA STRUCTURE DU SCM choisi
  (logit monotone, pas d'effet heterogene, bruit U_Y conserve au niveau de l'unite).
  Pas une decouverte EMPIRIQUE sur les effets reels du mentorat, qui pourraient
  etre heterogenes dans la
```

## `Chaines-05-Energie-Hamiltonien-Premiere-Puissance-Python.ipynb`

Verdict : **succes** · cellules executees 8/8 · duree 17.5 s · declenchement : `menu Run > Run All Cells`

### Cellule 4 (`[2]:`)

```
mesure de la toile : 116 (les deux sites qubits)
produit hub        : 36 (cite)
S0 = 116 * 36      = 4176 (eq. 64 annonce 4176) -> True
```

### Cellule 7 (`[3]:`)

```
gain 1 : 24 enregistrements
gain 2 : 30 enregistrements
gain 4 : 3 enregistrements
N = 24 + 30 + 3                = 57 (eq. 65 annonce 57) -> True
somme des gains entiers        = 96 = Z = 96 -> True
tr G = 30 + 30*sqrt(2)         ~ 72.426 (citee, element de l'anneau)
eq. 58 (ch. 42) : 24+18+12+3   = 57 -> meme espace, deux decompositions : True
```

### Cellule 10 (`[4]:`)

```
H psi = 4176 psi, multiplicite = 57 enregistrements (cite : 57)
[H, G_step] = 0 aux 12 tests de commutation (CITE -- construction du pas = source)
niveau a l'unite hub   : (4176/3)/67 = 1392 / 67 = 1392/67 ~ 20.776119
niveau a l'unite dock  : 4176/67     = 4176/67 ~ 62.328358
decoding PDF '139267'  -> 1392/67 egal au niveau hub   -> True
decoding PDF '417667'  -> 4176/67 egal au niveau dock  -> True
```

### Cellule 13 (`[5]:`)

```
Exercice a completer
```

### Cellule 15 (`[6]:`)

```
lien coeur B-C    type (3,3) extremites 3/3 -> coherent : True
lien dock B-w1    type (2,3) extremites 3/2 -> coherent : True
lien dock C-w2    type (2,3) extremites 3/2 -> coherent : True
S = 67 * 3                     = 201 (eq. 67 annonce 201) -> True
niveau a l'unite hub   : 201/(3*67) = 1 et carre de Born = 1
niveau a l'unite dock  : 201/67     = 3 et carre de Born = 9
energie de repos debout egalee aux deux unites (correspondance [78], PAR NOM)
```

### Cellule 18 (`[7]:`)

```
Exercice a completer
```

### Cellule 22 (`[8]:`)

```
Exercice a completer
```

## `Coalitions-04-Munkres-Affectation-Python.ipynb`

Verdict : **succes** · cellules executees 10/10 · duree 34.0 s · declenchement : `menu Run > Run All Cells`

### Cellule 2 (`[1]:`)

```
Matrice de couts C :
[[9. 2. 7. 8.]
 [6. 4. 3. 7.]
 [5. 8. 1. 8.]
 [7. 6. 9. 4.]]

Taille de l'espace de recherche : 4! = 24 permutations
```

### Cellule 4 (`[2]:`)

```
Optimum par force brute : 13  (permutation [1, 0, 2, 3])
Permutations testees : 24
```

### Cellule 6 (`[3]:`)

```
Kuhn-Munkres from scratch : valeur = 13, affectation = [1, 0, 2, 3]
```

### Cellule 7 (`[4]:`)

```
scipy (SOTA)              : valeur = 13, affectation = [np.int64(1), np.int64(0), np.int64(2), np.int64(3)]
Coincidence from scratch == SOTA : True
50 instances aleatoires 6x6 : max |KM - scipy| = 0.0
```

### Cellule 11 (`[5]:`)

```
(1) Realisabilite duale  : max(u_i + v_j - c_ij) = 0.00e+00 (<= 0 attendu)
(2) Valeur primale (matching) = 13
    Valeur duale  (u.sum + v.sum) = 13
    Gap de dualite = 0.00e+00 (0 attendu)
(3) Toutes les aretes du matching sont d'egalite : True
```

### Cellule 14 (`[6]:`)

```
Surplus optimal : 23  (= n*M - 13 = 23)
Parts non negatives pour tout U dans [6, 9] ; on prend U = 6
Coalitions testees : 254
Violations du coeur par l'imputation KM : 0
Efficacite : somme des parts = 23 == surplus grand coalition = 23 ? True
```

### Cellule 18 (`[7]:`)

```
Gale-Shapley (stable)   : valeur = 13, affectation = [1, 0, 2, 3]
Kuhn-Munkres (optimal)  : valeur = 13, affectation = [1, 0, 2, 3]
Ecart sur l'exemple fil rouge : 0
Instance divergente (essai 1) : GS stable = 12, KM optimal = 9
Matrice :
[[1 7 1 4]
 [7 2 3 2]
 [6 2 8 4]
 [4 4 5 4]]
La stabilite se paie : +3 par rapport a l'optimum
```

### Cellule 22 (`[8]:`)

```
Exercice a completer
```

### Cellule 24 (`[9]:`)

```
Exercice a completer
```

### Cellule 26 (`[10]:`)

```
Exercice a completer
```

