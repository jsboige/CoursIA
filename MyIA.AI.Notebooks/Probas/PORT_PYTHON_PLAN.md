# Plan de portage Infer.NET → Python

**Issue** : #297
**Statut** : Phase de recherche
**Auteur** : po-2025 (Cycle 22, Track 3)
**Date** : 2026-05-11

> Version anglaise originale préservée dans [PORT_PYTHON_PLAN.en.md](PORT_PYTHON_PLAN.en.md).

## Contexte

20 notebooks Infer.NET (.NET Interactive / C#) couvrent la programmation probabiliste, des fondamentaux jusqu'à la théorie de la décision. Objectif : créer des équivalents Python à l'aide de bibliothèques modernes de programmation probabiliste, afin de rendre le contenu accessible sans dépendance .NET.

Un notebook Python existant `Pyro_RSA_Hyperbole.ipynb` (13/13 cellules exécutées) démontre l'utilisation de Pyro dans ce dépôt.

## Recommandation de bibliothèques

| Bibliothèque | Atouts | Limites | Verdict |
|---------|-----------|------------|---------|
| **PyMC v5+** | Échantillonneur NUTS, contexte `Model()` intuitif, visualisation ArviZ, meilleure documentation | Lent pour les gros modèles, pas d'orientation variationnelle native | **Principale** pour les notebooks 1-8, 14-20 |
| **NumPyro** | HMC/NUTS + SVI rapides via JAX, passe bien à l'échelle, compatible Pyro | Complexité JAX, API moins intuitive | **Principale** pour les notebooks 9-12 (LDA, HMM, gros modèles) |
| **pgmpy** | Primitives de réseaux bayésiens (CPT, D-séparation, inférence) | Limité aux réseaux bayésiens discrets | Complémentaire pour le notebook 4 |
| **hmmlearn** | HMM fit/predict/score prêts à l'emploi | Pas de traitement bayésien des paramètres | Complémentaire pour le notebook 11 |
| **Pyro** | PPL généraliste, SVI, architecture de guide | Plus bas niveau que PyMC | Dépendance existante, utilisé pour le notebook RSA |

**Recommandation** : **PyMC v5+** comme bibliothèque principale (couvre 16/20 notebooks nativement), **NumPyro** pour les modèles avancés (LDA, HMM), **pgmpy** pour les fondations des réseaux bayésiens.

## Correspondance des notebooks

### Phase 1 : Fondamentaux (Notebooks 1-3) — PyMC

| # | Notebook Infer | Motif | Bibliothèque Python | Effort | Traduction d'API clé |
|---|---------------|---------|-----------|--------|---------------------|
| 1 | Setup (Two Coins) | Beta-Bernoulli conjugué | PyMC | 2h | `Variable.Bernoulli` → `pm.Bernoulli`, `InferenceEngine` → `pm.sample()` |
| 2 | Gaussian Mixtures | GMM, a priori conjugués, `Variable.Switch` | PyMC + sklearn | 4h | `Variable.Switch` → `pm.Mixture` ou indexation des poids par `pm.Categorical` |
| 3 | Factor Graphs | Inférence discrète, Monty Hall | PyMC | 3h | `Variable.If/Case` → `pm.math.switch`, `pt.where` |

### Phase 2 : Modèles classiques (Notebooks 4-6) — PyMC + pgmpy

| # | Notebook Infer | Motif | Bibliothèque Python | Effort | Traduction d'API clé |
|---|---------------|---------|-----------|--------|---------------------|
| 4 | Bayesian Networks | CPT, D-séparation, do-calcul | pgmpy + PyMC | 5h | `Variable.Case` CPT → `pgmpy.factors.discrete.TabularCPD`, D-sép → `pgmpy.independence` |
| 5 | Skills IRT | IRT, DINA, Q-matrix | PyMC | 5h | `Variable.Gaussian` pour l'habileté → `pm.Normal`, DINA → `pm.Deterministic` avec `pt.prod` |
| 6 | TrueSkill | Classement gaussien, apprentissage en ligne | PyMC | 4h | `ConstrainBetween` → `pm.Potential` ou `pm.Normal` avec transformation ordonnée |

### Phase 3 : Classification et sélection (Notebooks 7-8) — PyMC

| # | Notebook Infer | Motif | Bibliothèque Python | Effort | Traduction d'API clé |
|---|---------------|---------|-----------|--------|---------------------|
| 7 | Classification | Bayes Point Machine, test A/B | PyMC + scipy | 4h | BPM → `pm.Bernoulli` avec `pm.math.invprobit`, A/B → comparaison `pm.Beta` |
| 8 | Model Selection | Évidence, facteur de Bayes, ARD | PyMC + ArviZ | 4h | Évidence → `pm.compute_log_marginal_likelihood`, ARD → `pm.Horseshoe` ou a priori parcimonieux |

### Phase 4 : Modèles avancés (Notebooks 9-12) — NumPyro

| # | Notebook Infer | Motif | Bibliothèque Python | Effort | Traduction d'API clé |
|---|---------------|---------|-----------|--------|---------------------|
| 9 | Topic Models (LDA) | Dirichlet-Multinomial, VMP | NumPyro | 6h | `Variable.Dirichlet` → `numpyro.distributions.Dirichlet`, SVI + guide |
| 10 | Crowdsourcing | Modèles d'annotateurs, communautés | NumPyro | 5h | Matrice de confusion d'annotateur biaisé → `numpyro.plates` + catégorielle |
| 11 | Sequences (HMM) | HMM, Forward-Backward | hmmlearn + NumPyro | 5h | Forward-Backward manuel avec `numpyro.scan` ou `hmmlearn.GaussianHMM` |
| 12 | Recommenders | Factorisation de matrice, modèle de clic | NumPyro | 5h | Traits `Variable.Array` → `numpyro.sample` avec `numpyro.plate` |

### Phase 5 : Référence (Notebook 13) — PyMC/NumPyro

| # | Notebook Infer | Motif | Bibliothèque Python | Effort | Traduction d'API clé |
|---|---------------|---------|-----------|--------|---------------------|
| 13 | Debugging | Diagnostics, comparaison EP vs VMP | ArviZ + PyMC | 3h | EP/VMP → comparaison NUTS/ADVI, `arviz.plot_trace`, `az.summary` |

### Phase 6 : Théorie de la décision (Notebooks 14-20) — PyMC + numpy

| # | Notebook Infer | Motif | Bibliothèque Python | Effort | Traduction d'API clé |
|---|---------------|---------|-----------|--------|---------------------|
| 14 | Decision Foundations | Loteries, axiomes VNM, utilité | numpy + scipy | 3h | Surtout numpy/math, `scipy.optimize` pour la calibration |
| 15 | Utility of Money | St-Pétersbourg, CARA/CRRA | numpy + scipy | 3h | Fonctions d'utilité comme tableaux numpy, Monte Carlo |
| 16 | Multi-Attribute | MAUT, SMART, poids swing | numpy + scipy | 3h | Somme pondérée, analyse de sensibilité |
| 17 | Decision Networks | Diagrammes d'influence | pgmpy + numpy | 4h | `pgmpy.models.BayesianNetwork` + nœuds de décision |
| 18 | Value of Information | EVPI, EVSI | PyMC + numpy | 3h | Analyse pré-postérieure via `pm.sample_posterior_predictive` |
| 19 | Expert Systems | Minimax, regret | numpy + scipy | 3h | Opérations sur matrices de décision |
| 20 | Sequential Decisions | MDP, itération de valeur/politique | numpy | 3h | Itération de l'équation de Bellman (numpy pur) |

## Synthèse de l'effort

| Phase | Notebooks | Heures estimées | Bibliothèque |
|-------|-----------|----------------|---------|
| 1 : Fondamentaux | 1-3 | 9h | PyMC |
| 2 : Classiques | 4-6 | 14h | PyMC + pgmpy |
| 3 : Classification | 7-8 | 8h | PyMC |
| 4 : Avancés | 9-12 | 21h | NumPyro |
| 5 : Référence | 13 | 3h | ArviZ |
| 6 : Théorie de la décision | 14-20 | 22h | numpy + PyMC |
| **Total** | **20** | **~77h** | |

## Référentiel de traduction d'API

### Infer.NET → PyMC

| Infer.NET | PyMC v5+ | Notes |
|-----------|----------|-------|
| `Variable.Bernoulli(p)` | `pm.Bernoulli('x', p=p)` | Direct |
| `Variable.GaussianFromMeanAndVariance(m, v)` | `pm.Normal('x', mu=m, sigma=pt.sqrt(v))` | Attention sigma vs variance |
| `Variable.GaussianFromMeanAndPrecision(m, p)` | `pm.Normal('x', mu=m, tau=p)` | PyMC accepte le paramètre tau |
| `Variable.Beta(a, b)` | `pm.Beta('x', alpha=a, beta=b)` | Direct |
| `Variable.Dirichlet(a)` | `pm.Dirichlet('x', a=a)` | Direct |
| `Variable.Gamma(s, r)` | `pm.Gamma('x', alpha=s, beta=r)` | Attention rate vs scale |
| `Variable.Discrete(probs)` | `pm.Categorical('x', p=probs)` | Discret → Categorical |
| `Variable.Switch(idx, values)` | `pm.Mixture('x', w=w, comp=components)` | Ou `pt.switch` |
| `Variable.If(cond) { ... }` | `pm.math.switch(cond, then, else)` | Opération PyTensor |
| `VariableArray<T>(range)` | `pm.Normal('x', ..., shape=N)` | Paramètre shape |
| `observed.ObservedValue(data)` | `pm.Normal('x', ..., observed=data)` | Argument observed |
| `InferenceEngine(EP)` | `pm.sample(draws=1000)` | NUTS par défaut |
| `InferenceEngine(VMP)` | `pm.fit(method='advi')` | Approximation ADVI |
| `engine.Infer<Gaussian>(x)` | `trace.posterior['x']` | ArviZ InferenceData |

### Infer.NET → NumPyro

| Infer.NET | NumPyro | Notes |
|-----------|---------|--------|
| `Variable.Dirichlet` dans un plate | `numpyro.sample('theta', dist.Dirichlet(a), sample_intermediates=True)` | |
| `Variable.Discrete` avec plate | `numpyro.sample('z', dist.Categorical(probs), with numpyro.plate(...))` | |
| Itération VMP | `numpyro.infer.SVI(model, guide, optim, loss=Trace_ELBO())` | |
| `Range` | `numpyro.plate('name', size)` | Gestionnaire de contexte |

## Priorité d'échafaudage

**Sprint 1** (victoires les plus simples, construit les fondations) :
1. `Infer-1-Setup` → `PyMC-1-Setup` (2h)
2. `Infer-3-Factor-Graphs` → `PyMC-3-Factor-Graphs` (3h)

Ces deux notebooks couvrent le flux de travail fondamental (modèle → échantillonnage → postérieure) et l'inférence discrète (Monty Hall), fournissant un modèle pour tous les notebooks suivants.

**Sprint 2** (plus grande valeur pédagogique) :
3. `Infer-4-Bayesian-Networks` → `PyMC-4-Bayesian-Networks` (5h)
4. `Infer-2-Gaussian-Mixtures` → `PyMC-2-Gaussian-Mixtures` (4h)

## Dépendances

```
# requirements-python-port.txt
pymc>=5.10           # PPL principal (NUTS, ADVI, prédictive postérieure)
arviz>=0.17          # Visualisation + diagnostics
numpyro>=0.13        # Backend JAX pour les modèles avancés
jax>=0.4             # Backend NumPyro
pgmpy>=0.9           # Primitives de réseaux bayésiens
hmmlearn>=0.3        # HMM fit/predict
scipy>=1.11          # Optimisation, statistiques
matplotlib>=3.7      # Tracé
seaborn>=0.13        # Visualisation statistique
numpy>=1.24          # Cœur
pandas>=2.0          # Manipulation de données
```

Tout en CPU uniquement, aucun GPU requis.

## Convention de nommage

- Répertoire : `MyIA.AI.Notebooks/Probas/PyMC/`
- Fichiers : `PyMC-{N}-{Title}.ipynb` pour les notebooks basés sur PyMC, `NumPyro-{N}-{Title}.ipynb` pour ceux basés sur NumPyro
- Données : réutiliser directement les fichiers CSV/JSON de `Infer/data/` (mêmes jeux de données)
- Kernel : `python3`

## Questions ouvertes

1. **Notebooks de théorie de la décision (14-20)** : Ce sont principalement des maths/numpy, pas du PPL. Devraient-ils utiliser PyMC du tout, ou rester en numpy pur ? Recommandation : numpy + scipy pour 14-16, 19-20 ; PyMC pour 17 (réseaux de décision) et 18 (EVPI/EVSI).
2. **LDA (notebook 9)** : La SVI de NumPyro est complexe. Alternative : utiliser `gensim` ou `sklearn.decomposition.LatentDirichletAllocation` pour la comparaison, puis montrer NumPyro pour le traitement bayésien.
3. **Parité des exercices** : Les notebooks Python doivent-ils avoir exactement les mêmes exercices que les originaux en C#, ou s'adapter aux idiomes Python ? Recommandation : mêmes concepts, implémentations idiomatiques en Python.
