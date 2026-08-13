# Portage Infer.NET → Python — `MyIA.AI.Notebooks/Probas/`

> Référence pérenne. Ce document porte le **périmètre intentionnel** et la **recommandation de bibliothèques** d'un portage de la série Infer.NET (.NET Interactive, C#) vers des notebooks Python (PyMC, NumPyro, pgmpy, hmmlearn, Pyro). Il ne porte **PAS** le mapping d'API détaillé (daté PyMC v5, 2026-05-11) — voir section *« Mapping d'API = à re-dériver »*.

**Source canonique :** issue **#297** (CLOSED 2026-05-02 — le plan détaillé a été suivi en partie mais n'est plus défendable comme artefact commité).

**Substance portée ici depuis `MyIA.AI.Notebooks/Probas/PORT_PYTHON_PLAN.md`** (sha `48428c7e3d2fd20c682a2f4e49cec4b9894f4f30`, supprimé par #9914 c.1284) **+** `PORT_PYTHON_PLAN.en.md` (sha `0fc67bae3da3902722dc943225d4ea5238d22a3a`, supprimé idem).

## Note sur ce qui est pérenne et ce qui ne l'est pas

La colonne de droite de ce document mélange deux natures. **Le périmètre intentionnel** (combien de notebooks, quelle bibliothèque pour quel concept, quelle convention de nommage) **est durable** : ce sont des décisions de conception du dépôt, et c'est l'objet de cette référence. **Le mapping d'API ligne-à-ligne** (`Variable.Bernoulli → pm.Bernoulli(...)` et la table de traduction C# ↔ Python complète) **est périssable** : les API des PPL bougent à chaque release mineure, et un mapping non re-vérifié est un *poison* (un lecteur qui l'utiliserait sans le re-tester reproduirait du faux).

C'est pourquoi **la table d'API détaillée n'est pas reproduite ici**. Pour tout portage concret, re-dériver contre la version actuelle de la bibliothèque cible (PyMC v5+, NumPyro, pgmpy, hmmlearn).

## Contexte

Le dossier `MyIA.AI.Notebooks/Probas/` contient deux séries parallèles :

1. **Infer.NET** (C# .NET Interactive) — notebooks `Infer-1..19-*.ipynb`, série canonique pour le contenu probabiliste.
2. **PyMC** (Python) — notebooks `PyMC-1..19-*.ipynb`, portage en cours depuis 2024.

L'objectif du portage (intent original, 2024) : **rendre la série accessible aux profils Python** sans imposer le runtime .NET. Le portage **n'est pas une refonte** : la couverture thématique doit rester équivalente (mêmes concepts, mêmes exercices, mêmes sorties). Le lecteur doit pouvoir passer d'un Infer-X à un PyMC-X et trouver les mêmes notions.

## Recommandation de bibliothèques

| Bibliothèque | Usage | Justification |
|---|---|---|
| **PyMC v5+** | Bibliothèque principale pour ~85% du portage | Active, samplers NUTS robustes, JAX backend optionnel pour la perf, doc exhaustive |
| **NumPyro** | LDA (topic models), HMM, modèles à grandes dimensions | Backend JAX, très performant sur GPU, primitives HMM/LDS natives |
| **pgmpy** | Réseaux bayésiens structurés, inference exacte | API plus proche d'Infer.NET `Variable.BayesianNetwork` que PyMC |
| **hmmlearn** | Modèles de Markov cachés simples | API légère et lisible, complémentaire de NumPyro |
| **Pyro** | Précédent pour RSA (sémantique hyperbole) | Pré-installé sur la machine, déjà utilisé par `Pyro_RSA_Hyperbole.ipynb` |

**NumPyro n'est PAS un remplacement universel de PyMC** : sur les modèles où PyMC excelle (factor graphs, modèle hiérarchique standard, classification), NumPyro n'apporte rien. Inversement, PyMC est mal adapté pour les modèles où NumPyro est conçu (LDA, HMM de grande taille). **Le plan détaillé (daté) suggérait de tout basculer vers PyMC ; ce n'est PAS la position actuelle** : on choisit la bibliothèque la mieux adaptée au concept, pas une bibliothèque par défaut.

## Périmètre du portage (20 notebooks, 6 phases)

| # | Notebook | Concept dominant | Bibliothèque recommandée | Statut sur main (2026-08-07) |
|---|---|---|---|---|
| 1 | Setup | Environnement + sanity checks | PyMC | **Absorbé** (`PyMC-1-Setup.ipynb`) |
| 2 | Gaussian Mixtures | Modèles de mélange | PyMC | **Absorbé** (`PyMC-2-Gaussian-Mixtures.ipynb`) |
| 3 | Factor Graphs | Message passing, inférence exacte | PyMC | **Absorbé** (`PyMC-3-Factor-Graphs.ipynb`) |
| 4 | Bayesian Networks | DAG, conditional probability | pgmpy | **Absorbé** (`PyMC-4-Bayesian-Networks.ipynb`, `pgmpy` corespondance) |
| 5 | Causal Inference | do-calculus, contrefactuels | PyMC + DoWhy | **Absorbé** (`PyMC-5-Causal-Inference.ipynb`) |
| 6 | Debugging | Diagnostic des chaînes MCMC | PyMC | **Absorbé** (`PyMC-6-Debugging.ipynb`) |
| 7 | Skills / IRT | Item Response Theory | PyMC | **Absorbé** (`PyMC-7-Skills-IRT.ipynb`) |
| 8 | TrueSkill | Matchmaking, ratings | PyMC | **Absorbé** (`PyMC-8-TrueSkill.ipynb`) |
| 9 | Classification | Modèles discriminatifs | PyMC | **Absorbé** (`PyMC-9-Classification.ipynb`) |
| 10 | Model Selection | WAIC, LOO, comparaison | PyMC (ArviZ) | **Absorbé** (`PyMC-10-Model-Selection.ipynb`) |
| 11 | Topic Models (LDA) | Latent Dirichlet Allocation | **NumPyro** | **Absorbé** (`PyMC-11-Topic-Models.ipynb`) |
| 12 | Modèles Hiérarchiques | Partial pooling | PyMC | **Absorbé** (`PyMC-12-Modeles-Hierarchiques.ipynb`) |
| 13 | Crowdsourcing | Worker reliability, Dawid-Skene | PyMC | **Absorbé** (`PyMC-13-Crowdsourcing.ipynb`) |
| 14 | Sequences (HMM) | Hidden Markov Models | **NumPyro ou hmmlearn** | **Absorbé** (`PyMC-14-Sequences.ipynb`) |
| 15 | Recommenders | Collaborative filtering | PyMC | **Absorbé** (`PyMC-15-Recommenders.ipynb`) |
| 16 | Sparse Gaussian Process | Kernel sparse, inducing points | PyMC | **Absorbé** (`PyMC-16-Sparse-Gaussian-Process.ipynb`) |
| 17 | Kalman Filter | Filtre de Kalman, état-espace | PyMC | **Absorbé** (`PyMC-17-Kalman-Filter.ipynb`) |
| 18 | Change Point Detection | Détection de ruptures | PyMC | **Absorbé** (`PyMC-18-Change-Point.ipynb`) |
| 19 | Survival Analysis | Modèles de survie, censures | PyMC (lifelines) | **Absorbé** (`PyMC-19-Survival-Analysis.ipynb`) |
| 20 | Decision Theory (track séparé) | Utility, value of information | PyMC | **Absorbé** (`DecisionTheory/PyMC/DecPyMC-1..7.ipynb`) |

**Total : 20 notebooks PyMC + 7 notebooks DecPyMC + 1 notebook Pyro_RSA = 28 notebooks Python trackés**, soit **largement plus que les 20 initialement planifiés** — le périmètre a été étendu (track Decision Theory) et plusieurs notebooks ont été dédoublés.

## Estimation d'effort (référence, datée 2026-05-11)

Le plan original estimait **77 heures** réparties sur **6 phases** (Setup → Bayesian Networks & Gaussian Mixtures → Models → NumPyro → ArviZ → Finalisation). **Cette estimation est datée et n'est PAS re-validée ici.** Le périmètre a été absorbé sur main sans suivi rigoureux des heures, donc cette borne est **indicative, non auditée**.

Si un nouveau portage équivalent était à planifier aujourd'hui, l'estimer à partir du contenu actuel des notebooks `Infer-X-*.ipynb` (qui restent la source canonique en .NET), pas à partir de cette table.

## Convention de nommage

| Cible | Pattern | Exemple |
|---|---|---|
| Portage direct d'un notebook Infer | `PyMC-{N}-{Title}.ipynb` | `PyMC-2-Gaussian-Mixtures.ipynb` |
| Track Decision Theory | `DecPyMC-{N}-{Title}.ipynb` | `DecPyMC-1-Utility-Foundations.ipynb` |
| Numéro non-Infer | Préfixe thématique | `Pyro_RSA_Hyperbole.ipynb` |

**Nommage par concept, pas par source** : un `PyMC-12-Modeles-Hierarchiques.ipynb` est rangé par le concept qu'il couvre (modèles hiérarchiques), pas par le numéro du notebook Infer correspondant.

## Dépendances (borne haute indicative)

Le plan suggérait `requirements-python-port.txt` avec un environnement conda. La borne haute indicative :

- Python 3.10+
- `pymc>=5.0` (ArviZ, NumPyro, JAX optionnel)
- `pgmpy>=0.1.20`
- `hmmlearn>=0.3`
- `pyro-ppl>=1.9`
- `lifelines>=0.27` (survival analysis)
- `dowhy>=0.11` (causal inference, optionnel)
- `matplotlib>=3.7`, `seaborn>=0.12`

Ces dépendances **ne sont pas figées** : les notebooks trackés utilisent probablement un sous-ensemble, et des versions plus récentes peuvent avoir été adoptées localement. Vérifier contre l'environnement réel (`pip freeze`) avant ajout.

## Mapping d'API = À RE-DÉRIVER (HARD)

**NE PAS reproduire ici le mapping d'API détaillé de `PORT_PYTHON_PLAN.md`.** Pour les raisons suivantes :

1. **API des PPL bougent vite** : PyMC v5 a changé plusieurs signatures depuis 2026-05-11 ; pgmpy et NumPyro idem. Un mapping daté est un piège.
2. **Document poison** : un lecteur qui copie-colle un mapping non re-vérifié produit du code qui ne tourne pas, et perd plus de temps à débugger que s'il avait lu la doc officielle.
3. **Source canonique existe** : `https://www.pymc.io/projects/docs/en/stable/api.html`, `https://num.pyro.org/en/stable/`, `https://pgmpy.org/`. Pour tout portage, **lire la doc cible en parallèle de l'Infer-X-*.ipynb** et traduire concept par concept.

**Si quelqu'un veut malgré tout porter ce mapping** (par exemple pour un sprint de reprise rapide) : le re-dériver **dans une PR dédiée** `docs(probas,#X): add API mapping reference v<date>`, jamais dans ce fichier. Ce fichier-ci porte le **périmètre intentionnel**, pas l'implémentation.

## Voir aussi

- **#9911** — issue qualification (c.1283), contributeur au seed EPIC #9535
- **#9535** — EPIC parent « Nettoyage & rangement du dépôt »
- **#297** — issue cible exemple, CLOSED 2026-05-02 (work absorbé)
- **#9914** — PR d'archive c.1284 (`feature/c1284-9535-port-py-plan-archive`) qui a supprimé `PORT_PYTHON_PLAN.md` + `PORT_PYTHON_PLAN.en.md`
- **#1650** — EPIC traduction multilingue (interdit de traduire des fichiers transitoires)
- `MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-1..7.ipynb` — track Decision Theory en PyMC
- `MyIA.AI.Notebooks/Probas/Pyro_RSA_Hyperbole.ipynb` — précédent Pyro
- `docs/reference/mbml-source-attribution.md` — modèle de référence suivi pour ce document (note *« ce qui est pérenne et ce qui ne l'est pas »*)

## Historique

- **2026-08-07** — Création (c.1285), portée depuis `PORT_PYTHON_PLAN.md` (sha `48428c7e3d2fd20c682a2f4e49cec4b9894f4f30`) suite à la note de préservation user 2026-08-07T18:56:55Z sur #9911 (comment #5220921176) : *« la suppression sans que la substance ait été portée ailleurs d'abord »* est l'interdit, pas la suppression elle-même.
