# Programmation Probabiliste avec PyMC

Port Python de la serie Infer.NET — **20 notebooks** couvrant l'inference bayesienne avec PyMC (NUTS, echantillonnage MCMC), des fondamentaux aux modeles relationnels avances, incluant une section complete sur la theorie de la decision.

**20 notebooks** | Python 3.10+ | PyMC 5.x | ~19h

## Vue d'ensemble

| # | Notebook | Duree | Concepts |
|---|----------|-------|----------|
| 1 | [PyMC-1-Setup](PyMC-1-Setup.ipynb) | 15 min | Installation, premier modele Beta-Bernoulli |
| 2 | [PyMC-2-Gaussian-Mixtures](PyMC-2-Gaussian-Mixtures.ipynb) | 50 min | Posterieurs, melanges, Dirichlet |
| 3 | [PyMC-3-Factor-Graphs](PyMC-3-Factor-Graphs.ipynb) | 45 min | Inference discrete, Monty Hall |
| 4 | [PyMC-4-Bayesian-Networks](PyMC-4-Bayesian-Networks.ipynb) | 55 min | CPT, D-separation, causalite |
| 5 | [PyMC-5-Skills-IRT](PyMC-5-Skills-IRT.ipynb) | 60 min | IRT, DINA, many-to-many |
| 6 | [PyMC-6-TrueSkill](PyMC-6-TrueSkill.ipynb) | 55 min | Ranking, online learning, equipes |
| 7 | [PyMC-7-Classification](PyMC-7-Classification.ipynb) | 50 min | Classification bayesienne, tests A/B |
| 8 | [PyMC-8-Model-Selection](PyMC-8-Model-Selection.ipynb) | 45 min | Evidence, Bayes factors, ARD |
| 9 | [PyMC-9-Topic-Models](PyMC-9-Topic-Models.ipynb) | 60 min | LDA, Dirichlet, documents-topics-mots |
| 10 | [PyMC-10-Crowdsourcing](PyMC-10-Crowdsourcing.ipynb) | 55 min | Workers, communautes, agregation de labels |
| 11 | [PyMC-11-Sequences](PyMC-11-Sequences.ipynb) | 65 min | HMM, series temporelles, motifs |
| 12 | [PyMC-12-Recommenders](PyMC-12-Recommenders.ipynb) | 60 min | Factorisation de matrices, recommandation |
| 13 | [PyMC-13-Debugging](PyMC-13-Debugging.ipynb) | 45 min | Troubleshooting, diagnostics NUTS, convergence |
| 14 | [PyMC-14-Decision-Utility-Foundations](PyMC-14-Decision-Utility-Foundations.ipynb) | 50 min | Loteries, axiomes VNM, utilite esperee |
| 15 | [PyMC-15-Decision-Utility-Money](PyMC-15-Decision-Utility-Money.ipynb) | 45 min | Paradoxe St-Petersbourg, CARA, CRRA |
| 16 | [PyMC-16-Decision-Multi-Attribute](PyMC-16-Decision-Multi-Attribute.ipynb) | 50 min | MAUT, SMART, swing weights |
| 17 | [PyMC-17-Decision-Networks](PyMC-17-Decision-Networks.ipynb) | 55 min | Diagrammes d'influence, politique optimale |
| 18 | [PyMC-18-Decision-Value-Information](PyMC-18-Decision-Value-Information.ipynb) | 45 min | EVPI, EVSI, valeur de l'information |
| 19 | [PyMC-19-Decision-Expert-Systems](PyMC-19-Decision-Expert-Systems.ipynb) | 50 min | Systemes experts, Minimax, regret |
| 20 | [PyMC-20-Decision-Sequential](PyMC-20-Decision-Sequential.ipynb) | 60 min | MDPs, bandits, POMDPs |

**Duree totale** : ~19h

## Progression Pedagogique

```
FONDAMENTAUX (1-3)
+-- 1-Setup : Variables, inference basique, Beta-Bernoulli
+-- 2-Gaussian-Mixtures : Distributions continues, melanges
+-- 3-Factor-Graphs : Inference discrete, conditionnement

MODELES CLASSIQUES (4-6)
+-- 4-Bayesian-Networks : CPT, causalite, D-separation
+-- 5-Skills-IRT : Relations many-to-many, IRT/DINA
+-- 6-TrueSkill : Online learning, message passing

CLASSIFICATION & SELECTION (7-8)
+-- 7-Classification : BPM, regression logistique, A/B tests
+-- 8-Model-Selection : Evidence, ARD, comparaison bayesienne

MODELES AVANCES (9-12)
+-- 9-Topic-Models : LDA, documents-topics-mots
+-- 10-Crowdsourcing : Hierarchique, communautes
+-- 11-Sequences : HMM, series temporelles
+-- 12-Recommenders : Factorisation, systemes de recommandation

REFERENCE (13)
+-- 13-Debugging : Diagnostics NUTS, convergence, troubleshooting

THEORIE DE LA DECISION (14-20)
+-- 14-Utility-Foundations : Axiomes VNM, loteries
+-- 15-Utility-Money : Aversion au risque, CARA/CRRA
+-- 16-Multi-Attribute : MAUT, SMART, compromis
+-- 17-Decision-Networks : Influence diagrams, politique optimale
+-- 18-Value-Information : EVPI, EVSI, echantillonnage optimal
+-- 19-Expert-Systems : Regret Minimax, decisions robustes
+-- 20-Sequential : MDPs, bandits, POMDPs
```

## Installation

```bash
pip install pymc arviz pandas numpy scipy matplotlib
```

## Prerequis

- Python 3.10+
- Connaissance de base en probabilites et statistiques
- Familiarite avec Python et Jupyter notebooks

## Concepts cles

- **Inference bayesienne** : Posterieurs, priors conjugues, MCMC
- **PyMC** : Modeles probabilistes, echantillonneur NUTS, ArviZ
- **Modeles graphiques** : Reseaux bayesiens, graphes de facteurs
- **Theorie de la decision** : Utilite esperee, valeur de l'information, MDPs

## Serie complementaire

Ce port Python est le pendant de la serie [Infer.NET](../Infer/) (C# / .NET Interactive) couvrant les memes sujets avec un moteur d'inference different (message passing vs MCMC).

---

[Retour au README Probas](../README.md)
