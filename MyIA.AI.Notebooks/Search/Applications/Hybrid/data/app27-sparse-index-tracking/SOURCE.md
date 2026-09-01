# App-27 — Sparse index tracking walk-forward

Ce dossier documente la provenance de la distillation pédagogique App-27. Le notebook reconstruit l'expérience de façon autonome avec des données synthétiques seedées ; il n'importe ni code étudiant, ni prix de marché, ni output du rendu source.

| Champ | Valeur |
|---|---|
| Travail original | M2 — Sparse Index Tracking |
| Auteur | Godric Bouteloup |
| Dépôt source | https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes |
| Répertoire source | `M2-godric_bouteloup/` |
| PR source | https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/52 |
| Commit source | `bbc372b492f03ab181a68d149b1c22a5d44cd94f` |
| Licence | MIT |
| Date de reproduction | 2026-09-01 |

## Geste étudiant conservé

Le rendu source formule le sparse index tracking avec des lots entiers, des variables booléennes de sélection, une contrainte de cardinalité, des plafonds sectoriels et un objectif L1 sous CP-SAT. Cette combinaison est le point de départ de la distillation.

## Défauts reproduits avant transformation

La reproduction fraîche du notebook source a établi les limites suivantes :

1. la contrainte nommée turnover relie les solutions successives de la boucle sur K, pas deux dates de rebalancement ;
2. le meilleur hyperparamètre Lasso est choisi sur le jeu de test ensuite rapporté ;
3. le backtest annoncé réutilise la période d'estimation et n'est pas exécuté ;
4. plusieurs runs CP-SAT sont `FEASIBLE`, sans borne ni gap publiés ;
5. l'expérience dépend d'un snapshot Wikipédia absent et d'un téléchargement Yahoo Finance vivant ;
6. les comparaisons mélangent objectifs, univers et tailles de train différents ;
7. `np.std` est présenté comme l'unique tracking error malgré l'objectif quadratique annoncé et sans reporting séparé du biais actif.

## Transformation CoursIA

App-27 conserve le geste de modélisation mais remplace le benchmark source par un protocole audit-able :

- marché factoriel synthétique seedé, autonome et à changement de régime ;
- séparation chronologique calibration / validation / test ;
- sélection de l'univers sur calibration seulement ;
- choix de K sur validation seulement ;
- turnover entre portefeuilles de dates consécutives ;
- cardinalité exacte, budget et caps validés indépendamment ;
- statut, incumbent, borne et gap publiés ;
- RMSE active, biais actif et tracking error annualisée rapportés séparément ;
- contre-protocole contaminé exécuté pour quantifier l'optimisme induit par la fuite.

## Limites et bon usage

Les sorties ne sont pas des performances financières réelles et ne doivent pas être présentées comme un backtest du S&P 500. Le marché synthétique sert à vérifier le protocole et les invariants. Une extension aux marchés réels demanderait un univers point-in-time licencié, des prix ajustés figés, les corporate actions, les coûts de transaction et un backtest strictement futur.

Aucun code de solveur étudiant n'est recopié. Le notebook CoursIA est une ré-implémentation indépendante sous la licence MIT du dépôt cible.
