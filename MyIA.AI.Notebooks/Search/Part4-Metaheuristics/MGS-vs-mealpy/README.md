# MGS vs mealpy — campagne comparative

[↑ Partie 4 : Metaheuristiques composables](../README.md) | [← MGS-21 (représentation vs algorithme)](../MGS-21-Representation-vs-Algorithme.ipynb)

Cette sous-série regroupe les **dix notebooks comparatifs** de l'Epic « MGS face à mealpy » : un même protocole apparié (même grille, même budget, mêmes graines, déterminisme vérifié), deux bibliothèques comparées (la nôtre en C# .NET 9 contre la référence Python/NumPy), un verdict quantitatif. La campagne n'est pas un benchmark exploratoire — c'est une **décomposition systématique** d'une bibliothèque à l'autre, paire par paire, qui sépare les deux axes que la performance brute mêle (coût d'évaluation vs qualité de solution) et isole l'origine des écarts (moteur vs stratégie).

## Question directrice

À budget d'évaluations égal et problème fixé, **quels écarts la bibliothèque C# (MetaGeneticSharp) présente-t-elle face à mealpy 3.0.2 ?** Ces écarts sont-ils **systématiques** (le coût d'évaluation) ou **spécifiques** (la qualité de la solution, signe et ampleur variables) ? Et ces écarts viennent-ils du **moteur** (formules, opérateurs) ou de la **stratégie** (sélection, réinsertion, exploration vs exploitation) ?

La réponse, étalée sur les neuf paires, distingue deux axes :

- **Coût systématique** — mealpy est **plus cher par évaluation** sur 8/9 paires (médiane 2,38×, jusqu'à 7,86×), l'unique inversion P1 étant documentée comme un artefact d'instrumentation (écart runtime/noyau, pas algorithme). Le fork C# est systématiquement plus rapide par évaluation, mais cet écart est en partie **absorbé** par la mécanique du moteur (coût Python vs coût C#, fitness-isolée 5-7× plus rapide en C#).
- **Qualité spécifique** — mealpy gagne **6/9 paires**, MGS **3/9**, médianes de −6,5 à +17 conflits. La **direction de l'écart de qualité dépend de la paire** : mealpy écrase en PSO (séparation totale) et EO (étendues disjointes, plus grand écart qualité de l'Epic) ; MGS gagne en SA (premier doublé de l'Epic : qualité et vitesse) et FBI (séparation totale, record de vitesse).

La question « quel moteur choisir ? » est ainsi **déplacée** : le coût d'évaluation est une donnée d'ingénierie (runtime, GPU, contraintes de latence), mais la qualité dépend du paysage de fitness et de la stratégie de recherche — pas du langage ni de l'écosystème.

## Protocole commun

Toutes les paires partagent un **protocole apparié strict** (hérité de MGS-22 et tenu jusqu'à MGS-31) :

- **Grille** : `Easy[0]` de Sudoku_Easy51 (36 vides), sauf mention contraire dans le notebook.
- **Représentation** : R1 — vecteur continu $[1,10)^{36}$ décodé par arrondi+clamp (cf. MGS-21 pour l'analyse de cette représentation).
- **Budget** : ~8 000 évaluations par course (instrumenté, exactement mesuré dans chaque notebook).
- **Fonction de coût** : conflits lignes + colonnes + blocs.
- **Graines** : `{0, 1, 7, 42}` (4 graines minimum, déterminisme 8/8 ou 12/12 vérifié in-notebook).
- **Sanity check coût** : trois témoins LCG (C# = Python sur des tirages identiques), protégeant contre les biais d'instrumentation.
- **Contre-vérification croisée** : le vainqueur dans une langue est relancé dans l'autre (vérification que le verdict n'est pas un artefact d'un port défectueux).
- **Fitness isolée** : mesure du coût de la fonction de fitness seule (sans la mécanique moteur), pour distinguer l'écart langage de l'écart algorithme.

Ce protocole est **ferme** : tout écart au protocole est déclaré explicitement dans le notebook (ex. MGS-27 ajuste la génération pour neutraliser les confonds MGS pop×gén vs mealpy pop×epoch ; MGS-26 ajuste l'epoch mealpy à 156 pour le centroïde coûté en 51e évaluation).

## Table des paires

| # | Notebook | Paire | Verdict qualité | Verdict vitesse | Fitness isolée C# |
|---|----------|-------|----------------|----------------|-------------------|
| 1 | [MGS-22](MGS-22-MGS-vs-Mealpy.ipynb) | PSO MGS vs OriginalPSO mealpy | mealpy devant (séparation totale 28,5 [26-31] vs 43,5 [39-48]) | ex æquo (0,99×) | 5,72× |
| 2 | [MGS-23](MGS-23-DifferentialEvolution-vs-Mealpy.ipynb) | DE MGS vs OriginalDE mealpy | mealpy devant mais resserré (21,5 vs 25,5, étendues chevauchées, MGS gagne la graine 0) | **MGS 3,45× moins cher** | 6,70× |
| 3 | [MGS-24](MGS-24-SimulatedAnnealing-vs-Mealpy.ipynb) | SA MGS (population-based) vs OriginalSA mealpy (marcheur) | **MGS devant** (27,0 vs 31,0) — premier doublé qualité + vitesse | MGS 3,04× moins cher | 4,20× |
| 4 | [MGS-25](MGS-25-WhaleOptimisation-vs-Mealpy.ipynb) | WOA MGS vs OriginalWOA mealpy + jumeau MGS-Naive | ex æquo MGS-MGS (49,5 = 49,5), mealpy derrière (51,0) | MGS 1,69× moins cher | 3,49× |
| 5 | [MGS-26](MGS-26-EquilibriumOptimizer-vs-Mealpy.ipynb) | EO MGS vs OriginalEO mealpy | **mealpy écrase** (25,0 vs 42,0, étendues disjointes) — plus grand écart qualité de l'Epic | MGS 1,21× (plus faible de l'Epic) | 7,75× |
| 6 | [MGS-27](MGS-27-ForensicBasedInvestigation-vs-Mealpy.ipynb) | FBI MGS vs OriginalFBIO mealpy | **MGS devant** (séparation totale 37,0 vs 43,5) — deuxième doublé | **MGS 4,11× moins cher** (record de l'Epic) | 6,36× |
| 7 | [MGS-28](MGS-28-BareBonesPSO-vs-Mealpy.ipynb) | BBPSO MGS vs jumeau mealpy construit (Kennedy 2003 strict) | mealpy devant à sémantique alignée (25,5 vs 30,5) | MGS 0,50× (2× moins cher) | 4,59× |
| 8 | [MGS-29](MGS-29-GA-vs-Mealpy.ipynb) | Default GA MGS vs BaseGA mealpy | qualité comparable (12,5 vs 13,5, étendues chevauchées — l'écart PSO ne se reproduit pas) | MGS 6,12× moins cher (record) | n/a (sanity check coût IDENTIQUE post #13396) |
| 9 | [MGS-30](MGS-30-ScatterSearch-Decomposition.ipynb) | SS MGS vs jumeau mealpy construit (213 optimisateurs scannés, zéro SS) | **jumeau mealpy gagne** (51,5 vs 54,0, la plus resserrée de l'Epic) | mealpy 0,92× (première défaite vitesse MGS sur le bras complet) | 5,25× |

**Tableau récapitulatif** (synthèse croisée 9 paires) : [MGS-31](MGS-31-Synthese-Croisee.ipynb).

## Ordre de lecture

L'arc n'est **pas** un benchmark exploratoire : chaque notebook ferme un verdict et ouvre une hypothèse pour le suivant.

1. **Pose du protocole** — [MGS-22](MGS-22-MGS-vs-Mealpy.ipynb) (PSO). Premier duel, séparation totale en qualité, ex æquo en vitesse. La fitness-isolée C# 5,72× est engloutie par la mécanique moteur (~1,8× plus coûteuse côté C#). Hypothèse ouverte : l'écart qualité vient-il du moteur ou de la stratégie de réinsertion ?

2. **L'écart se resserre-t-il ?** — [MGS-23](MGS-23-DifferentialEvolution-vs-Mealpy.ipynb) (DE). Oui : étendues chevauchées, MGS gagne la graine 0, écart vitesse inversé. Hypothèse ouverte : la stratégie de réinsertion population-side est-elle plus importante que le moteur ?

3. **Premier doublé** — [MGS-24](MGS-24-SimulatedAnnealing-vs-Mealpy.ipynb) (SA, recuit population-based vs marcheur). MGS gagne qualité ET vitesse. Hypothèse ouverte : la divergence d'architecture (population-based vs single-solution) creuse-t-elle l'écart ?

4. **Paire canonique** — [MGS-25](MGS-25-WhaleOptimisation-vs-Mealpy.ipynb) (WOA). Trois colonnes, jumeau MGS-Naive comme ablation. Verdict : ex æquo MGS-MGS, mealpy derrière — l'opérateur spiral ne paie pas sur cette géométrie.

5. **Paire symétrique** — [MGS-26](MGS-26-EquilibriumOptimizer-vs-Mealpy.ipynb) (EO). mealpy écrase avec étendues disjointes. Hypothèse ouverte : la sélection greedy par individu (mealpy) bat-elle la réinsertion de population (MGS) ?

6. **Paire miroir** — [MGS-27](MGS-27-ForensicBasedInvestigation-vs-Mealpy.ipynb) (FBI, port MGS revendiqué depuis mealpy). Les équations ont dérivé (bruit A1 N(0,1) vs uniforme). MGS gagne les deux mains. Hypothèse ouverte : la dérive de bruit est-elle l'origine de l'écart ?

7. **Décomposition de l'écart d'ancrage** — [MGS-28](MGS-28-BareBonesPSO-vs-Mealpy.ipynb) (BBPSO, Kennedy 2003 strict). Trois bras isolent ancrage (nul) et noyau (réel : mealpy devant). Hypothèse : le coût d'évaluation importe-t-il plus que la sémantique ?

8. **Revanche du GA** — [MGS-29](MGS-29-GA-vs-Mealpy.ipynb) (GA, après correction #13396 du décalage d'index de colonne). L'écart PSO ne se reproduit pas GA contre GA. Hypothèse : la sémantique moteur (composants) domine-t-elle la sémantique stratégie (réinsertion) ?

9. **Paire sans équivalent mealpy** — [MGS-30](MGS-30-ScatterSearch-Decomposition.ipynb) (Scatter Search, construit en jumeau par subclass). Le jumeau mealpy gagne les deux mains. Hypothèse : la diversité de RefSet (b2) porte-t-elle le bénéfice ?

10. **Synthèse croisée** — [MGS-31](MGS-31-Synthese-Croisee.ipynb). Récolte des médianes/étendues/coûts depuis les seuls outputs committés (zéro re-run, intégrité re-dérivée 9/9), tableau croisé qualité × coût, deux graphiques SVG, deux lectures d'isolation (P7 jumeaux mealpy à formules distinctes → noyau ; P9 ablation SS → stratégie).

## Distinction benchmark diagnostique / amélioration MGS

Cette sous-série est **explicitement diagnostique**, pas prescriptive. Aucune des neuf paires ne conclut « il faut remplacer X par Y dans MGS » ; aucune n'ouvre une branche d'amélioration MGS. La boucle benchmark → diagnostic → correctif → re-benchmark est suivie **séparément** (cf. issue #13778 : « MGS vs mealpy : convertir les benchmarks en correctifs MGS puis re-mesurer »).

Ce qui est livré ici, c'est la **photographie mesurée** d'un instant — fork C# à commit `501beeac7` × mealpy 3.0.2 — avec :

- les écarts reproductibles (sanity check coût, déterminisme 8/8 ou 12/12) ;
- les sources identifiées (sélection greedy vs réinsertion population, bruit N(0,1) vs uniforme, opérateurs de sélection/recuit) ;
- les impasses déclarées (l'écart qualité PSO ne se reproduit pas GA — ce n'est pas un signal unidirectionnel).

**Ce qui n'est PAS livré** : une prescription d'amélioration, un re-benchmark après correction, un classement final des deux bibliothèques. La campagne laisse les **questions ouvertes** documentées et reproductibles ; les réponses sont une autre campagne.

## Configuration requise

Identique à la série parente ([Partie 4 README §Configuration requise](../README.md#configuration-requise)) :

- Kernel `dotnet-interactive` 1.0.707101+ (hôte .NET moderne, charge net8.0/net9.0/net10).
- Sous-module `MetaGeneticSharp/` buildé (DLLs `net9.0`).
- Pont PythonNet pour les comparaisons mealpy (kernel `.NET` charge `mealpy` 3.0.2 via Python.NET).
- Reproductibilité seedée pour MGS-22 à MGS-31 (graines `{0, 1, 7, 42}` + `FastRandomRandomization.ResetSeed`).

Règle C.2 : notebooks committés **avec leurs outputs** (exécution réelle, kernel .NET).

## Conventions

- **Repères entre paires** : chaque notebook déclare ses confonds paramétriques neutralisés et ses écarts au protocole commun. Une lecture transverse requiert MGS-31 (synthèse), pas une moyenne des neuf verdicts isolés.
- **Pas de préférence affichée** : les verdict « MGS devant » / « mealpy devant » / « ex æquo » / « comparable » sont publiés tels quels, sans tri de présentations. L'Epic ne « gagne » ni ne « perd » : elle mesure.
- **Limites disclosed** : checkpoints 2/9 (sept paires perdent les checkpoints intermédiaires), un seul paysage (Sudoku-Easy[0]), un seul budget (8 000 évals), 4 graines, un seul fork à un instant donné.

## Liens

- [Série parente — Partie 4 : Metaheuristiques composables](../README.md) — vue d'ensemble de la thèse « composants > métaphores » et du side-track C#/.NET 9
- [Fork jsboige/MetaGeneticSharp](https://github.com/jsboige/MetaGeneticSharp) — code source, tests unitaires, ROADMAP
- [Issue #13777 — MGS vs mealpy : isoler les face-à-face dans une sous-série dédiée](https://github.com/jsboige/CoursIA/issues/13777) — fondatrice de cette sous-série
- [Issue #13778 — MGS vs mealpy : convertir les benchmarks en correctifs MGS puis re-mesurer](https://github.com/jsboige/CoursIA/issues/13778) — campagne d'amélioration (séparée, non livrée ici)
- [Search-11-Métaheuristiques](../../Part1-Foundations/Search-11-Metaheuristics.ipynb) — introduction Python (PSO, ABC, SA, BRO via mealpy, benchmark comparatif)
