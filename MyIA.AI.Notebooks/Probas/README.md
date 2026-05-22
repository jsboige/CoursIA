# Probas - Programmation Probabiliste

<!-- CATALOG-STATUS
series: Probas
pedagogical_count: 32
breakdown: Infer=20, _python_port=9, =3
maturity: BETA=25, PRODUCTION=6, ALPHA=1
-->

Le monde reel est incertain. Un diagnostic medical n'est jamais sur a 100%, un classement sportif depend de performances intrinsequement variables, et les donnees que nous collectons sont toujours bruitees ou incompletes. La programmation probabiliste offre un cadre rigoureux pour modeliser cette incertitude : plutot que de calculer une seule reponse, on obtient une **distribution de probabilites** qui quantifie notre confiance dans chaque resultat possible.

Cette serie couvre trois stack complementaires : **Infer.NET** (Microsoft, C#/.NET Interactive) pour l'inference exacte par message passing, **PyMC** (Python) pour l'echantillonnage MCMC moderne, et des **applications standalone** (RSA, HMM trading). Les 20 notebooks Infer.NET couvrent les fondements mathematiques (distributions, graphs de facteurs), les modeles classiques (reseaux bayesiens, TrueSkill, LDA, HMM), puis la theorie de la decision bayesienne. Les 9 notebooks PyMC reprennent les memes modeles en Python avec l'echantillonnage NUTS, offrant un pont naturel vers l'ecosysteme data science.

**32 notebooks** | **3 stack** | **~30h**

**A qui s'adresse cette serie** : etudiants en IA, data scientists, et developpeurs souhaitant aller au-dela des modeles deterministes. Aucun prerequis en probabilites avancees : les concepts sont introduits progressivement.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 32 (20 Infer.NET + 9 PyMC + 3 standalone) |
| Duree totale | ~30h |
| Langages | C# (.NET), Python |
| Kernels | .NET Interactive, Python 3 |

## Parcours d'apprentissage

### Phase 1 : Fondations (Notebooks 1-3, ~2h)

Le parcours commence par le notebook 1 (Setup) qui installe Infer.NET et construit le premier modele bayesien — le classique "Two Coins" — en quelques lignes de C#. Le notebook 2 (Gaussian Mixtures) plonge dans les distributions continues avec les melanges gaussiens, outil fondamental du clustering. Le notebook 3 (Factor Graphs) introduit la representation graphique qui unifie tous les modeles : les graphs de facteurs, illustres par le probleme de Monty Hall. A l'issue de cette phase, vous comprenez comment exprimer un probleme incertain en termes de variables, de facteurs et de messages.

### Phase 2 : Modeles classiques (Notebooks 4-13, ~8h)

Les notebooks 4 a 13 construisent des modeles de complexite croissante, chacun illustre par une application concrete : reseaux bayesiens (diagnostic medical), Item Response Theory (evaluation de competences), TrueSkill (classement Xbox Live), classification bayesienne, selection de modeles (Bayes Factors), LDA (topic modeling), crowdsourcing (agregation de labels), HMM (sequences temporelles), systemes de recommandation, et debugging. Chaque notebook est autonome mais presuppose la maitrise des concepts des notebooks 1-3. Le notebook 13 (Debugging) est une reference pratique a consulter tout au long du parcours.

### Phase 3 : Decision bayesienne (Notebooks 14-20, ~7h)

La seconde moitie de la serie passe de l'inference a la decision : comment choisir une action quand on ne connait que des probabilites ? Les notebooks 14-16 posent les fondations (axiomes de l'utilite, fonctions d'utilite mono- et multi-attributs). Les notebooks 17-20 appliquent ces concepts aux reseaux de decision, a la valeur de l'information, aux systemes experts robustes, et aux processus decisionnels de Markov (MDPs) — qui relient cette serie a la serie [RL](../RL/).

### Parcours alternatif : Python (Infer-101 + Pyro RSA + HMM, ~2h)

Si vous preferez Python au C#, commencez par Infer-101.ipynb (introduction standalone avec modeles Two Coins et Cyclist) puis Pyro_RSA_Hyperbole.ipynb (application a la linguistique pragmatique avec le framework RSA). Le notebook PyMC-HMM-Trading-Alpha.ipynb applique les HMM gaussiens a la generation de signaux de trading.

### Parcours PyMC (9 notebooks, ~6h)

Les notebooks PyMC dans `_python_port/` reprennent les 9 premiers modeles Infer.NET en Python avec PyMC et l'echantillonnage NUTS. Ils constituent un excellent complement pour comparer les approches d'inference (message passing vs MCMC) et rejoindre l'ecosysteme Python data science.

## Structure

```
Probas/
├── Infer-101.ipynb              # Introduction Python/C# (standalone)
├── Pyro_RSA_Hyperbole.ipynb     # Pragmatique linguistique (Python)
├── PyMC-HMM-Trading-Alpha.ipynb # HMM gaussien pour trading (Python)
├── _python_port/                # Port PyMC des modeles Infer.NET (9 notebooks)
│   ├── PyMC-1-Setup.ipynb ... PyMC-9-Topic-Models.ipynb
│   └── README.md
└── Infer/                       # Serie complete Infer.NET (20 notebooks)
    ├── Infer-1-Setup.ipynb ... Infer-20-Decision-Sequential.ipynb
    ├── README.md                # Documentation detaillee de la serie
    └── scripts/
```

## Notebooks racine (Python)

| Notebook | Kernel | Contenu | Duree |
|----------|--------|---------|-------|
| [Infer-101](Infer-101.ipynb) | Python + C# | Introduction Infer.NET, Two Coins, Cyclist | 45 min |
| [Pyro_RSA_Hyperbole](Pyro_RSA_Hyperbole.ipynb) | Python | Rational Speech Acts, hyperboles | 60 min |

### Infer-101.ipynb

Point d'entree accessible pour la programmation probabiliste :
- Concepts de base (variables aleatoires, modeles probabilistes)
- Premier modele Infer.NET (Two Coins)
- Exemple du cycliste (priors Gaussiens)
- Apprentissage en ligne et comparaison de modeles

### Pyro_RSA_Hyperbole.ipynb

Application avancee a la linguistique pragmatique :
- Framework RSA (Rational Speech Acts)
- Implicatures scalaires (none/some/all)
- Modelisation des hyperboles (prix, excitation)
- Question Under Discussion (QUD)

## Serie Infer.NET (20 notebooks)

La serie complete est documentee dans [Infer/README.md](Infer/README.md).

### Progression en 3 parties

| Partie | Notebooks | Focus | Duree |
|--------|-----------|-------|-------|
| **Fondations** | 1-3 | Setup, distributions, factor graphs | 2h |
| **Modeles classiques** | 4-13 | Bayesian networks, IRT, TrueSkill, LDA, HMM | 8h |
| **Decision** | 14-20 | Theorie de la decision bayesienne | 7h |

### Vue d'ensemble des notebooks

| # | Notebook | Sujet |
|---|----------|-------|
| 1 | Setup | Configuration, Two Coins, Beta-Bernoulli |
| 2 | Gaussian Mixtures | Distributions continues, Gamma priors |
| 3 | Factor Graphs | Monty Hall, explaining away |
| 4 | Bayesian Networks | CPTs, D-separation, causalite |
| 5 | Skills (IRT) | Item Response Theory, DINA |
| 6 | TrueSkill | Ranking, skill gaussien, equipes |
| 7 | Classification | Probit, Bayes Point Machine |
| 8 | Model Selection | Evidence, Bayes Factors, ARD |
| 9 | Topic Models | LDA, Dirichlet priors |
| 10 | Crowdsourcing | Worker models, active learning |
| 11 | Sequences | HMM, detection meteo, motifs |
| 12 | Recommenders | Factorisation matricielle, Click Model |
| 13 | Debugging | EP vs VMP, diagnostic erreurs |
| 14-20 | Decision Theory | Utilite, MAUT, influence diagrams, MDPs |

## Serie PyMC (9 notebooks, Python)

Port Python des memes modeles Infer.NET, utilisant l'echantillonnage MCMC (NUTS) au lieu du message passing. Permet de comparer les deux approches d'inference sur des modeles identiques.

| # | Notebook | Sujet |
|---|----------|-------|
| 1 | [PyMC-1-Setup](_python_port/PyMC-1-Setup.ipynb) | Configuration PyMC, modele Beta-Bernoulli |
| 2 | [PyMC-2-Gaussian-Mixtures](_python_port/PyMC-2-Gaussian-Mixtures.ipynb) | Distributions continues, melanges gaussiens |
| 3 | [PyMC-3-Factor-Graphs](_python_port/PyMC-3-Factor-Graphs.ipynb) | Graphes de facteurs, inference discrete |
| 4 | [PyMC-4-Bayesian-Networks](_python_port/PyMC-4-Bayesian-Networks.ipynb) | Reseaux bayesiens, CPTs |
| 5 | [PyMC-5-Skills-IRT](_python_port/PyMC-5-Skills-IRT.ipynb) | Item Response Theory, modeles de competences |
| 6 | [PyMC-6-TrueSkill](_python_port/PyMC-6-TrueSkill.ipynb) | Classement, TrueSkill |
| 7 | [PyMC-7-Classification](_python_port/PyMC-7-Classification.ipynb) | Classification bayesienne |
| 8 | [PyMC-8-Model-Selection](_python_port/PyMC-8-Model-Selection.ipynb) | Selection de modeles, Bayes Factors |
| 9 | [PyMC-9-Topic-Models](_python_port/PyMC-9-Topic-Models.ipynb) | LDA, Dirichlet priors |

## Applications standalone (3 notebooks)

| Notebook | Kernel | Contenu | Duree |
| -------- | ------- | ------- | ----- |
| [Infer-101](Infer-101.ipynb) | .NET (C#) + Python | Introduction Infer.NET, Two Coins, Cyclist | 1h |
| [Pyro_RSA_Hyperbole](Pyro_RSA_Hyperbole.ipynb) | Python 3 | Rational Speech Acts, hyperboles | 30 min |
| [PyMC-HMM-Trading-Alpha](PyMC-HMM-Trading-Alpha.ipynb) | Python 3 | HMM gaussien pour signaux de trading | 45 min |

## Installation

### Notebooks PyMC (Python)

```bash
pip install pymc numpy scipy matplotlib arviz
```

### Notebooks Infer.NET (C# .NET Interactive)

```bash
# 1. Installer .NET SDK 9.0+ depuis https://dotnet.microsoft.com/download
# 2. Installer le kernel dotnet-interactive
dotnet tool install -g Microsoft.dotnet-interactive
dotnet interactive jupyter install

# 3. Ou utiliser le script PowerShell (installe tout automatiquement) :
cd MyIA.AI.Notebooks/Probas/Infer/scripts
.\setup_environment.ps1
```

### Notebooks Python (Infer-101, Pyro_RSA)

```bash
pip install pyro-ppl torch matplotlib numpy
```

### Verification

```bash
jupyter kernelspec list  # doit afficher .net-csharp et python3
```

### Tester tous les notebooks

```bash
python MyIA.AI.Notebooks/Probas/Infer/scripts/test_notebooks.py --validate-only
```

## Prerequisites

### Pour Infer.NET (C#)

```bash
# .NET SDK 9.0+
dotnet --version

# VS Code + extension Polyglot Notebooks
# Packages (auto-references dans notebooks):
# - Microsoft.ML.Probabilistic
# - CompilerChoice = Roslyn
```

### Pour Python

```bash
# Environnement Python 3.8+
pip install pyro-ppl torch matplotlib numpy
```

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Inference bayesienne** | Mise a jour de croyances avec des observations |
| **Prior / Posterior** | Distribution avant/apres observations |
| **Factor Graph** | Representation graphique de distributions jointes |
| **Message Passing** | Algorithmes EP (Expectation Propagation), VMP |
| **Decision Theory** | Maximisation d'utilite esperee |

## Domaines d'application

| Domaine | Notebooks |
|---------|-----------|
| Jeux video | 6 (TrueSkill) |
| Education | 5 (IRT), 14 |
| NLP | 9 (LDA) |
| Medecine | 4, 7, 17-19 |
| Finance | 11, 15, 20 |
| E-commerce | 12 |

## Ressources

### Infer.NET

- [Infer.NET Documentation](https://dotnet.github.io/infer/)
- [MBML Book (Model-Based Machine Learning)](https://mbmlbook.com/)
- [Infer.NET GitHub](https://github.com/dotnet/infer)

### Pyro

- [Pyro Documentation](https://pyro.ai/)
- [Pyro Tutorials](https://pyro.ai/examples/)

### Theorie

- Bishop, C. (2006) - *Pattern Recognition and Machine Learning*
- Koller & Friedman (2009) - *Probabilistic Graphical Models*

## Licence

Voir la licence du repository principal.

## Cross-series Bridges

| Serie | Lien | Connection |
| ------- | ------ | ----------- |
| [IIT](../IIT/README.md) | PyPhi | L'integration informationnelle (phi) repose sur les memes fondements probabilistes |
| [SymbolicAI/SemanticWeb](../SymbolicAI/SemanticWeb/README.md) | OWL reasoning | Les ontologies OWL utilisent la logique probabiliste pour le raisonnement incertain |
| [GameTheory](../GameTheory/README.md) | Bayesian games | Les jeux bayesiens combinent probabilites et theorie des jeux |
| [QuantConnect](../QuantConnect/README.md) | HMM trading | PyMC-HMM-Trading-Alpha applique les modeles probabilistes aux signaux de trading |
| [Search](../Search/README.md) | Optimisation bayesienne | La selection de modeles (PyMC-8) utilise les memes techniques que l'optimisation bayesienne |
