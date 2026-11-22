# Executions reelles sous JupyterLite (Pyodide)

<!-- Genere par scripts/notebook_tools/pyodide_browser_run.py -- ne pas editer a la main. -->

Les carnets ci-dessous ont ete **realement executes** dans un navigateur (Chromium headless)
contre le noyau Pyodide du site JupyterLite construit localement : le menu « Run » puis
« Run All Cells » a ete declenche dans la page, et les sorties sont lues dans le DOM.
« Cellules executees » compte les cellules de code dont le compteur d'execution est passe
de `[ ]:` a `[n]:`.

| Carnet | Cellules code | Cellules executees | Cellules avec sortie | Erreurs | Duree (s) | Premier resultat (s) | Verdict |
|---|---:|---:|---:|---:|---:|---:|---|
| `10-SIG-3D-Tiles-Python.ipynb` | 6 | 6 | 6 | 0 | 26.9 | 7.2 | **succes** |
| `AgentSystems-02-Perception-Active-Valeur-Information-Python.ipynb` | 6 | 6 | 3 | 0 | 16.0 | 7.0 | **succes** |
| `Quotients-Fibres-Recollement-Python.ipynb` | 9 | 9 | 9 | 0 | 23.7 | 7.0 | **succes** |
| `Argumentation-01-Toulmin-Model-Python.ipynb` | 7 | 7 | 7 | 0 | 22.1 | 7.0 | **succes** |
| `06-3-AudioDiffusion-Comparison-A-vs-B.ipynb` | 1 | 1 | 1 | 0 | 17.6 | 7.0 | **succes** |

## `10-SIG-3D-Tiles-Python.ipynb`

Verdict : **succes** · cellules executees 6/6 · duree 26.9 s · declenchement : `menu Run > Run All Cells`

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

Verdict : **succes** · cellules executees 6/6 · duree 16.0 s · declenchement : `menu Run > Run All Cells`

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

Verdict : **succes** · cellules executees 9/9 · duree 23.7 s · declenchement : `menu Run > Run All Cells`

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

Verdict : **succes** · cellules executees 7/7 · duree 22.1 s · declenchement : `menu Run > Run All Cells`

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

## `06-3-AudioDiffusion-Comparison-A-vs-B.ipynb`

Verdict : **succes** · cellules executees 1/1 · duree 17.6 s · declenchement : `menu Run > Run All Cells`

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

