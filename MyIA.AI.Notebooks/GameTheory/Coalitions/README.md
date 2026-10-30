# Coalitions — pouvoir, assistance, appariement

La théorie coopérative répond à une question que les jeux non coopératifs laissent ouverte : que vaut un **groupe** de joueurs, et comment cette valeur se partage-t-elle ? Cette sous-série du parcours [GameTheory](../README.md) en déplie trois moments — le pouvoir d'une coalition dans un vote, l'assistance entre un humain et un agent, l'appariement d'agents sur un marché sans prix.

Elle s'ouvre depuis deux paliers de la série mère, et c'est ce qui la distingue d'un simple rangement :

- **[GT-15 — Jeux coopératifs](../GameTheory-15-CooperativeGames-Python.ipynb)** fournit la valeur de Shapley, le Core et la condition de Bondareva-Shapley. Le carnet 01 en tire la question pratique : le **poids nominal** d'un votant mesure-t-il son pouvoir réel de faire basculer une décision ?
- **[GT-16 — Conception de mécanismes](../GameTheory-16-MechanismDesign-Python.ipynb)** fournit le principe de révélation et le vocabulaire des mécanismes. Le carnet 03 en suit une institution réelle — l'échange de reins — et les carnets 04 et 05 en traitent l'algorithme d'affectation.

L'organe Python de la famille reste [`cooperative_games/`](../cooperative_games/) à la racine de la série : noyau et cœur d'un jeu coopératif, appariement stable de Gale-Shapley. Les carnets 01 à 04 l'invoquent plutôt que de le réimplémenter ; seul le carnet 05 change de substrat, en lisant le lake Lean [`assignment_lean/`](../assignment_lean/).

**À qui s'adresse cette sous-série** : étudiants en économie, informatique et mathématiques appliquées, à l'aise avec la notion de fonction caractéristique. Les carnets 01, 02 et 04 ne demandent que Python ; le 03 est un carnet Python à lecture formelle ; le 05 exige un kernel Lean et le lake `assignment_lean` construit (procédure dans le [README parent](../README.md)).

## Notebooks

| # | Notebook | Ce qu'on y apprend | Noyau | Public |
|---|----------|--------------------|-------|--------|
| 01 | [Pouvoir coalitionnel et SMT](Coalitions-01-Pouvoir-Coalitionnel-SMT-Python.ipynb) | Le poids nominal contre le pouvoir réel : coalitions minimales gagnantes, trois indices de pouvoir (Shapley-Shubik, Banzhaf, Deegan-Packel), énumération exhaustive puis **encodage SMT borné** en seconde voie, hiérarchie des garanties SAT/UNSAT, photographie structurelle d'une assemblée et contrefactuel contrôlé | Python | Recherche |
| 02 | [Assistance Games (résultat 2026)](Coalitions-02-Assistance-Games-Python.ipynb) | La coopération humain-assistant formalisée en jeu d'assistance : modèle (Θ, A_H, A_A, r), oracle de politique jointe en hindsight, puis **EXP3** comme apprenant sans regret côté assistant — la borne empirique √T contre T^(3/4) est mesurée, pas postulée (Ananthakrishnan et al., 2026) | Python | Recherche |
| 03 | [Échange de reins](Coalitions-03-Echange-de-Reins-Lean-Python.ipynb) | Un mécanisme d'appariement réel : graphe de compatibilité, cycles et chaînes de donneurs altruistes, arbitrage entre cardinalité et équité — la boucle `G_t → R_t → A_t → G_{t+1}` quand le mécanisme devient une institution | Python | Licence |
| 04 | [Affectation de Kuhn-Munkres](Coalitions-04-Munkres-Affectation-Python.ipynb) | L'affectation optimale en arithmétique entière exacte, certifiée par **dualité LP** : implémentation pédagogique de la méthode hongroise, lecture par potentiels, pont vers le jeu d'affectation de **Shapley-Shubik**, et confrontation Gale-Shapley contre Kuhn-Munkres — deux notions d'optimum qui ne coïncident pas | Python | Licence |
| 05 | [Affectation en Lean](Coalitions-05-Lean-Affectation-Lean.ipynb) | Le certificat du carnet 04, exécuté depuis le lake `assignment_lean` en kernel natif : valeur d'affectation, couple dual `DualFeasible`, **dualité faible**, **certificat à gap nul**, charpente de correction `KuhnMunkres` et resserrement hongrois `dualFeasible_tighten` en action | Lean | Recherche |

## Ordre de lecture

Deux vols indépendants, qui se rejoignent sur la notion d'optimum :

1. **Pouvoir et assistance** — 01 puis 02. Le carnet 01 mesure qui compte dans une coalition ; le carnet 02 déplace la question vers un collectif de deux agents dont l'un ignore l'objectif de l'autre.
2. **Appariement** — 03, puis 04, puis 05. Le carnet 03 montre le problème dans une institution réelle ; le carnet 04 en donne l'algorithme exact et sa preuve par dualité ; le carnet 05 en transporte les énoncés en Lean, où la dualité faible et le gap nul deviennent des théorèmes plutôt que des observations numériques.

Le carnet 05 suit son jumeau d'objet (04) : il suppose la matrice de coûts et le triple test du carnet 04 déjà lus. Les carnets 01 et 02 se lisent dans n'importe quel ordre après GT-15.

## Ce que la sous-série ne couvre pas

La décomposition de Möbius sur le treillis des coalitions et les dividendes de Harsanyi relèvent de l'organe d'agrégation, dans la [sous-série SocialChoice](../SocialChoice/README.md) (SC-06). La valeur de Shapley individuelle, le Core et Bondareva-Shapley restent au palier [GT-15](../GameTheory-15-CooperativeGames-Python.ipynb) et à son approfondissement Lean [15b](../GameTheory-15b-Lean-CooperativeGames-Lean.ipynb). Les populations d'agents de langage et les mécanismes d'Othman-Sandholm restent dans la chaîne 16, à la racine.

## Provenance

Ce dossier a été créé par la réorganisation de la série GameTheory ([#20316](https://github.com/jsboige/CoursIA/issues/20316)). Les cinq carnets y sont entrés depuis la racine sous leurs anciennes lettres — 15e, 15g, 16d, 16f et 16f-Lean — sans modification de leur contenu exécuté : seul le préfixe d'identité a changé, et les liens de navigation ont été réécrits pour le nouveau niveau de dossier. Les carnets 03 et 04, qui n'avaient aucune ligne de navigation, en ont reçu une, et le carnet 02 pointe désormais vers le 03 : la sous-série se lit comme une chaîne, pas comme cinq fichiers posés côte à côte. Le carnet 04 portait un affichage « 23 » et le carnet 05 un affichage « 23b » hérités de leur livraison ; ces numéros ne désignaient aucune étape du parcours et disparaissent avec le déplacement.
