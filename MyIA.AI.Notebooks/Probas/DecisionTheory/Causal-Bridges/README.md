# Du graphe causal au do-calculus — le pont causal

[← Série Probas](../../README.md) | [↑ Arc Théorie de la Décision](../README.md) | [Corpus bayésien Infer (C#) →](../../Infer/README.md) | [Corpus PyMC (Python) →](../../PyMC/README.md)

**Notebook-pont** de la constellation causale du dépôt. La causalité est traitée à **quatre endroits**, chacun avec son moteur et son angle ; ce répertoire n'ajoute pas un cinquième moteur, il fournit l'**armature formelle unifiée** — l'échelle de Pearl et les trois règles du do-calculus — et la fait tourner sur l'**outil de référence** [`dowhy`](https://www.pywhy.org/dowhy/) (installé et exécuté réellement, règle F / SOTA-OK, **pas** de réimplémentation jouet), avant de renvoyer à chaque série pour l'instanciation par son moteur.

**Stack** : Python 3 (kernel `coursia-ml-training`), [`dowhy`](https://www.pywhy.org/dowhy/) pour l'identification / estimation / réfutation d'estimandes causaux. Aucun kernel .NET ni GPU requis.

## Contenu

| Notebook | Durée | Concepts |
|----------|-------|----------|
| [Do-Calculus-Bridge](Do-Calculus-Bridge.ipynb) | ~55 min | Échelle de Pearl, trois règles du do-calculus, critères *backdoor* / *front-door* exécutés avec `dowhy`, Pearl (intervention) vs Hoel (émergence causale) |

**Prérequis** : probabilités conditionnelles, graphes orientés acycliques (DAG), notions d'inférence bayésienne. Une lecture préalable de l'un des quatre notebooks de la constellation (ci-dessous) rend le pont plus concret.

## Ce que le pont ajoute

Ce que ce notebook apporte, que les quatre notebooks de moteur ne font pas chacun séparément :

1. La **théorie unifiée** du do-calculus, présentée une bonne fois : l'échelle de Pearl (observation < intervention < contrefactuel) et les trois règles, lues comme des *chirurgies du graphe* suivies d'un test de $d$-séparation.
2. Une exécution sur l'**outil SOTA** `dowhy` qui **identifie** l'estimande (backdoor / front-door / variable instrumentale), l'**estime**, puis le **réfute** — le pipeline qu'on utiliserait pour une vraie étude causale.
3. La **mise en regard** des deux grands paradigmes causaux : l'interventionnisme de Pearl et l'émergence causale de Hoel (information effective).

## La constellation causale — où approfondir

Les quatre séries **implantent le même formalisme** avec des outils différents. Partout, $do(X=x)$ se traduit par une **mutilation du graphe** (on supprime les arêtes entrant dans $X$, puis on fige $X=x$).

| Direction | Notebook | Moteur | Ce qu'il apporte de plus |
|-----------|----------|--------|--------------------------|
| Logique + SCM + contrefactuels | [Tweety-11](../../../SymbolicAI/Tweety/Tweety-11-Causal.ipynb) | Tweety (.NET) | backend causal logique, opérateur `do` natif |
| Message passing exact | [Infer-5](../../Infer/Infer-5-Causal-Inference.ipynb) | Infer.NET | backdoor, front-door, Simpson, médiation, capstone contrefactuel |
| MCMC bayésien | [PyMC-5](../../PyMC/PyMC-5-Causal-Inference.ipynb) | PyMC | incertitude postérieure sur l'effet, contrefactuel bayésien |
| Émergence causale (Hoel) | [ICT-5](../../../IIT/ICT-Series/ICT-5-CausalEmergence.ipynb), [ICT-6](../../../IIT/ICT-Series/ICT-6-SortingToTPM-CausalEmergence.ipynb) | PyPhi (CE 2.0) | information effective, coarse-graining, multiscale |

Là où Infer-5 et PyMC-5 instrumentent le `do` à la main sur leur moteur, `dowhy` **automatise l'identification** puis estime et réfute. Là où Pearl demande « quel est l'effet d'une intervention sur $X$ ? » dans un graphe **fixé**, Hoel (ICT-5/6) demande « **quelle échelle** de description porte le plus de causalité ? » — deux réponses complémentaires à la question causale.

## Exercices

Le notebook suit la convention du dépôt (stubs à compléter, sans erreur volontaire) :

1. **Ajouter un second confondeur à la backdoor** — étendre l'ensemble d'ajustement à `{aptitude, motivation}`.
2. **Rompre le critère front-door** — ajouter un chemin direct qui contourne le médiateur et vérifier que l'identification front-door échoue.
3. **Comparer effet naïf et effet ajusté** — générer un nouveau jeu à effet vrai connu, mesurer l'écart dû au confondeur.
