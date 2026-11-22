# Notions interactives — atelier Python

Un atelier unique qui rassemble **dix notions-clés** du cursus, prises dans **sept séries**
différentes. Chaque notion tient sur **un paramètre unique** : un curseur, et l'effet se voit sur
la figure.

Le carnet [NotionsInteractives-01-Atelier-Python.ipynb](NotionsInteractives-01-Atelier-Python.ipynb)
est le seul livrable exécutable. Les carnets d'origine ne sont pas modifiés : celui-ci les cite en
fin de parcours pour qui veut approfondir.

## Les dix notions

| # | Notion | Série d'origine | Le paramètre | Ce qu'on voit changer |
|---|--------|-----------------|--------------|------------------------|
| 1 | Température d'échantillonnage | GenAI | température `T` | La distribution passe du piqué à l'uniforme, entropie croissante |
| 2 | Top-p (nucleus) | GenAI | seuil de masse `p` | La taille du noyau et la part de masse conservée |
| 3 | Pas d'apprentissage | ML | pas `eta` | Convergence, puis divergence au-delà de `2 / f''` |
| 4 | Seuil de décision | ML | seuil `t` | L'échange précision / rappel et le maximum de F1 |
| 5 | Mise à jour bayésienne Beta | Probas | pseudo-comptes `(a, b)` | Le posterior se resserre autour de la moyenne empirique |
| 6 | Acceptation Metropolis-Hastings | Probas | largeur de proposition `sigma` | Le taux d'acceptation s'effondre quand `sigma` grandit |
| 7 | Température du recuit simulé | Search | température `T` | Le recuit quitte un puits local là où la descente gloutonne reste |
| 8 | Epsilon-greedy sur bandit | RL | exploration `epsilon` | Le regret cumulé a un minimum intérieur |
| 9 | Équilibre de Nash du dilemme du prisonnier | GameTheory | tentation `T` | La bascule coopération / défection quand `T` franchit `R` |
| 10 | Seuil de satisfiabilité 3-SAT | Complexity | ratio clauses/variables `alpha` | La probabilité de satisfiabilité bascule — pente autour de `5` à dix variables, seuil asymptotique `4,26` |

Trois formes d'effet sont représentées : **monotone** (notions 1, 2, 5, 7), **à optimum**
(3, 4, 6, 8) et **à seuil** (9, 10). Savoir dans quelle classe tombe le paramètre qu'on règle évite
deux erreurs coûteuses : chercher un optimum là où il n'y en a pas, et pousser une valeur monotone
jusqu'à ce que quelque chose casse.

## Deux rendus, deux usages

- **Une figure statique par notion**, committée avec le carnet. Elle montre plusieurs valeurs du
  paramètre et suffit à comprendre l'effet : GitHub et le site n'exécutent pas les widgets.
  Chaque paragraphe « Lecture du résultat » cite les nombres produits par sa propre figure, et un
  contrôle automatique vérifie que chaque valeur citée figure bien dans la sortie de la cellule.
- **Un widget par notion**, sous le paragraphe « À manipuler ». Il faut un noyau vivant et
  `ipywidgets` ; hors de là, le carnet bascule en **mode batch** (`BATCH_MODE = True`, injecté par
  Papermill) et chaque widget imprime une ligne au lieu de s'afficher.

## Exécution

```bash
# Rendu complet, sans interaction (celui du fichier committé)
python scripts/notebook_tools/notebook_tools.py execute \
    MyIA.AI.Notebooks/cross-series/NotionsInteractives/NotionsInteractives-01-Atelier-Python.ipynb \
    --kernel python3 --batch-mode
```

Dépendances : `numpy`, `matplotlib`, `ipywidgets` (8.x). Sans `ipywidgets`, seule la branche batch
du carnet est atteignable.

## Trois exercices

Le carnet contient trois exercices stub, répartis après les notions 3, 6 et 9 : descente avec élan,
estimateur de moyenne par MCMC, puis seuil de tentation pour un jeu `(R, S, P)` quelconque. Aucun
n'utilise d'erreur volontaire — le carnet s'exécute de bout en bout, exercices non complétés
compris.

## Portée

Cet atelier ne remplace pas les séries : il les **met côte à côte**, sur un même geste (déplacer un
curseur) et une même lecture (ce que la figure montre). Chaque notion est traitée en profondeur
dans sa série d'origine, indiquée par la colonne « Série d'origine » et rappelée en fin de carnet.
