# Programmation Probabiliste avec PyMC

Port Python de la serie Infer.NET — **20 notebooks** couvrant l'inference bayesienne avec PyMC (NUTS, echantillonnage MCMC), des fondamentaux aux modeles relationnels avances, incluant une section complete sur la theorie de la decision.

**20 notebooks** | Python 3.10+ | PyMC 5.x | ~19h

**A qui s'adresse cette serie** : praticiens Python, data scientists et etudiants souhaitant maitriser l'inference bayesienne moderne avec l'ecosysteme PyMC/ArviZ. Aucun prerequis en C# ou Infer.NET : chaque notebook est autonome.

## Pourquoi cette serie

PyMC est le framework d'inference bayesienne le plus utilise en Python pour la modelisation probabiliste appliquee. La ou scikit-learn fournit des predictions ponctuelles, PyMC produit des **distributions posterieures completes** qui quantifient l'incertitude de chaque parametre.

Cette serie couvre les **meme 20 modeles** que la serie [Infer.NET](../Infer/) mais avec un moteur d'inference radicalement different :

| Aspect | Infer.NET (C#) | PyMC (Python) |
|--------|----------------|---------------|
| **Moteur** | Message passing (EP/VMP) | Echantillonnage MCMC (NUTS) |
| **Resultats** | Deterministes, analytiques | Stochastiques, convergents |
| **Flexibilite** | Modeles conjugues | Presque tout modele |
| **Diagnostics** | Factor graphs | ArviZ (trace, ESS, R-hat) |
| **Ecosysteme** | .NET | NumPy/Pandas/Matplotlib |

Avoir les deux approches sur les memes modeles permet de comprendre les **compromis** entre inference exacte et approchee, une competence cle pour tout praticien.

## Objectifs d'apprentissage

A l'issue de cette serie, vous serez capable de :

1. **Construire** un modele probabiliste avec PyMC (definition du prior, vraisemblance, echantillonnage)
2. **Diagnostiquer** la convergence MCMC avec ArviZ (R-hat, ESS, trace plots, divergences)
3. **Comparer** message passing (Infer.NET) vs MCMC (PyMC) sur le meme modele
4. **Appliquer** l'inference bayesienne a des problemes concrets (ranking, classification, recommandation)
5. **Integrer** inference probabiliste et theorie de la decision (EVPI, MDPs, bandits)

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
# Environnement dedie (recommande)
conda create -n pymc-env python=3.12
conda activate pymc-env

# Dependances principales
pip install pymc arviz pandas numpy scipy matplotlib

# Verification
python -c "import pymc; print(f'PyMC {pymc.__version__}')"
```

### kernels Jupyter

```bash
python -m ipykernel install --user --name pymc-env --display-name "Python 3 (PyMC)"
jupyter kernelspec list  # doit afficher pymc-env
```

## Prerequis

- Python 3.10+ (3.12 recommande)
- Connaissance de base en probabilites et statistiques
- Familiarite avec Python et Jupyter notebooks
- Optionnel : avoir suivi la serie [Infer.NET](../Infer/) pour la comparaison message passing vs MCMC

## Quel parcours choisir

### Parcours data scientist Python (~10h)

Notebooks 1-3 (fondations) puis 7-8 (classification/selection) puis 9-12 (modeles avances). Ce parcours couvre les modeles les plus utiles en pratique sans passer par la theorie de la decision.

1. [PyMC-1-Setup](PyMC-1-Setup.ipynb) -> premier modele
2. [PyMC-2](PyMC-2-Gaussian-Mixtures.ipynb) + [PyMC-3](PyMC-3-Factor-Graphs.ipynb) -> distributions et inference
3. [PyMC-7](PyMC-7-Classification.ipynb) + [PyMC-8](PyMC-8-Model-Selection.ipynb) -> classification bayesienne
4. [PyMC-9](PyMC-9-Topic-Models.ipynb) -> [PyMC-12](PyMC-12-Recommenders.ipynb) -> modeles avances

### Parcours theorie de la decision (~7h)

Notebooks 14-20 en sequence. Ce parcours couvre l'utilite esperee, la valeur de l'information et les MDPs avec un moteur MCMC.

1. [PyMC-14](PyMC-14-Decision-Utility-Foundations.ipynb) -> axiomes VNM
2. [PyMC-15](PyMC-15-Decision-Utility-Money.ipynb) -> aversion au risque
3. [PyMC-17](PyMC-17-Decision-Networks.ipynb) -> reseaux de decision
4. [PyMC-18](PyMC-18-Decision-Value-Information.ipynb) -> [PyMC-20](PyMC-20-Decision-Sequential.ipynb) -> EVPI, MDPs

### Parcours comparatif Infer.NET vs PyMC (~15h)

Alterner chaque notebook PyMC avec son equivalent [Infer.NET](../Infer/).Comparer les implementations (message passing vs MCMC) sur les memes modeles pour comprendre les compromis.

### Parcours rapide (~2h)

[PyMC-1-Setup](PyMC-1-Setup.ipynb) + [PyMC-4-Bayesian-Networks](PyMC-4-Bayesian-Networks.ipynb) + [PyMC-7-Classification](PyMC-7-Classification.ipynb). Les trois notebooks les plus representatifs pour une premiere prise en main.

## FAQ / Troubleshooting

### PyMC ne s'installe pas sur Windows (compilateur C manquant)

PyMC 5.x requiert un compilateur C pour les extensions natives. Solution :

```bash
# Option 1 : installer via conda (inclut le compilateur)
conda install -c conda-forge pymc

# Option 2 : installer les build tools Visual Studio
# Telecharger depuis https://visualstudio.microsoft.com/visual-cpp-build-tools/
# Cocher "Desktop development with C++"
```

### L'echantillonnage NUTS est tres lent ou ne converge pas

- Verifier les priors : des priors trop larges causent des explorations inutiles
- Augmenter `target_accept` : `pm.sample(target_accept=0.95)` (defaut 0.8)
- Utiliser `init="advi"` pour une initialisation plus robuste
- Consulter [PyMC-13-Debugging](PyMC-13-Debugging.ipynb) pour les diagnostics complets

### ArviZ affiche des divergences

Les divergences indiquent que l'echantillonneur n'a pas explore correctement certaines regions de l'espace posterieur. Actions :

1. `az.plot_trace(trace)` -> verifier le melange des chaines
2. `az.summary(trace)` -> verifier que `r_hat < 1.05` et `ess_bulk > 400`
3. Reparametriser le modele (centrage, log-transform)
4. Augmenter le nombre de tirages : `pm.sample(draws=4000, tune=2000)`

### Erreur "SamplingError: Initial evaluation of model failed"

Le prior et la vraisemblance sont incompatibles avec les donnees observes. Verifier :

- Les valeurs observes sont dans le support du prior (pas de valeurs negatives pour une distribution Gamma)
- Les dimensions correspondent (pas de shape mismatch)
- Les priors ne sont pas trop restrictifs

### Comment passer de Infer.NET a PyMC ?

La serie suit le meme ordre que [Infer.NET](../Infer/). Les concepts se correspondent :

| Concept Infer.NET | Equivalent PyMC |
|-------------------|-----------------|
| `Variable.Bernoulli(p)` | `pm.Bernoulli('x', p=p)` |
| `InferenceEngine` | `pm.sample()` |
| `Infer<DistributionType>` | `trace['x']` |
| `ShowFactorGraph` | `pm.model_to_graphviz()` |

## Concepts cles

- **Inference bayesienne** : Posterieurs, priors conjugues, MCMC
- **PyMC** : Modeles probabilistes, echantillonneur NUTS, ArviZ
- **Modeles graphiques** : Reseaux bayesiens, graphes de facteurs
- **Theorie de la decision** : Utilite esperee, valeur de l'information, MDPs

## Serie complementaire

Ce port Python est le pendant de la serie [Infer.NET](../Infer/) (C# / .NET Interactive) couvrant les memes sujets avec un moteur d'inference different (message passing vs MCMC).

## Ressources

- [PyMC Documentation](https://www.pymc.io/projects/docs/en/stable/)
- [ArviZ Documentation](https://python.arviz.org/)
- [Bayesian Methods for Hackers](https://github.com/CamDavidsonPilon/Probabilistic-Programming-and-Bayesian-Methods-for-Hackers)
- [Statistical Rethinking (McElreath)](https://xcelab.net/rm/statistical-rethinking/) — livre de reference pour l'inference bayesienne appliquee

---

[Retour au README Probas](../README.md)

## FAQ rapide

| Probleme | Solution |
|----------|----------|
| `ModuleNotFoundError: pymc` | `pip install pymc arviz` -- PyMC 5.x et ArviZ pour les diagnostics |
| Echantillonnage tres lent (>5 min par modele) | Verifier qu'un compilateur C est disponible (PyMC utilise PyTensor avec compilation C). Sinon, reduire `draws` et `tune` (ex: 500/500 au lieu de 1000/1000) |
| Convergence non atteinte (R-hat > 1.05) | Augmenter le nombre de `tune` steps. Le notebook 13 (Debugging) detaille les strategies de diagnostic |
| Divergences dans l'echantillonnage | Re-parametrer le modele (centered vs non-centered). Voir notebook 2 (Gaussian Mixtures) et 13 (Debugging) |
| `SamplingError: Initial evaluation failed` | Les priors sont incompatibles avec les observations. Verifier les distributions a priori et les valeurs initiales |

## Ponts inter-series

| Serie | Lien | Relation |
|-------|------|----------|
| [Infer.NET](../Infer/) | Meme 20 modeles en C# / message passing | Comparaison MCMC vs inference exacte |
| [Probas (parent)](../README.md) | Vue d'ensemble Probas | Contexte et parcours |
| [ML](../../ML/) | Pipeline ML classique | PyMC comme alternative bayesienne |
| [QuantConnect](../../QuantConnect/) | Strategies de trading | Modeles bayesiens appliques au trading |

## Navigation

[<- Retour a la serie Probas](../README.md) \| [Infer.NET (C#) ->](../Infer/README.md)
