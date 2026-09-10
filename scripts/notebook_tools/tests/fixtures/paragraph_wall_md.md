# Probas - Programmation Probabiliste (fixture self-test, PR B #15507)

Le monde réel est incertain. Un diagnostic médical n'est jamais sûr à 100%, un classement sportif dépend de performances intrinsèquement variables, et les données que nous collectons sont toujours bruitées ou incomplètes. La programmation probabiliste offre un cadre rigoureux pour modéliser cette incertitude.

Cette série couvre trois stacks complémentaires : **Infer.NET** (Microsoft, C#/.NET Interactive) pour l'inférence par message passing déterministe (EP/VMP, plus un échantillonneur de Gibbs disponible), **PyMC** (Python) pour l'échantillonnage stochastique MCMC (NUTS), et des applications standalone (RSA, identification causale avec DoWhy, percolation de liens sur tore fini). Elle totalise 69 notebooks — 28 en C#/.NET Interactive, 38 en Python, 3 en Lean 4. Le corpus bayésien compte 21 notebooks — socle numéroté 1-20 — couvrant fondements, modèles classiques, frontières, géométrie catégorique. L'arc décision Infer.NET en extrait 8 notebooks C# — utilité espérée, EVPI, MDPs, bandits, jusqu'au Thompson Sampling. Le versant PyMC porte ces modèles en Python avec l'échantillonnage NUTS : 19 notebooks corpus en parité 1:1 avec Infer et 12 miroirs de l'arc décision renumérotés 1-12 dont la jambe actuarielle 8-12. L'arc décision est en outre certifié par un lake compagnon Lean 4 et ses 2 notebooks à kernel Lean : les identités d'escompte y sont démontrées (0 sorry), le théorème d'optimalité restant énoncé. La percolation complète ce trio Lean avec Percolation-Lean (noyau fini prouvé sans sorry, compagnon du lake percolation_lean), jumeau de la simulation Python Percolation-Supercritique (trois régimes mesurés). Enfin, un pont causal (4 notebooks Python) fédère les quatre traitements de la causalité disséminés dans le dépôt — Tweety, Infer.NET, PyMC et l'émergence causale (PyPhi) — autour de l'échelle de Pearl et du do-calculus. Sur l'outil de référence dowhy, le pont identifie l'estimande (backdoor, front-door, variable instrumentale), l'estime puis le réfute ; il monte au troisième échelon de Pearl (contrefactuel individuel) et couvre les méthodes quasi-expérimentales (DiD, contrôle synthétique, RDD). Cette paragraphe fondateur, reconstitué ici pour la fixture du détecteur, dépasse les 2000 caractères sur une seule ligne physique afin de prouver que le détecteur tire sur le mur pédagogique type PR #15405 (commit 76d7a5bc).

## Pourquoi cette série

La programmation probabiliste occupe une place singulière dans le paysage de l'IA. Alors que le machine learning classique fournit des prédictions ponctuelles, il ne dit pas à quel point il a confiance. La programmation probabiliste quantifie cette incertitude de façon native.

```python
# Bloc code exempté par _FENCE_RE — peut être > 2000 c sans tirer.
import numpy as np
def foo(x):
    """Une fonction pédagogique."""
    return x + 1
```

| Colonne 1 | Colonne 2 |
|-----------|-----------|
| valeur A  | valeur B  |

<!-- Ce commentaire HTML est volontairement très long pour vérifier que le détecteur ignore les blocs <!-- ... -->. La fixture ajoute ici plusieurs lignes pour s'assurer que le nettoyage retire l'ensemble du commentaire d'un seul tenant et ne le découpe pas en paragraphes séparés. Le test _self_test#3 "fences/tableaux/titres ignores" vérifie ce comportement. -->
