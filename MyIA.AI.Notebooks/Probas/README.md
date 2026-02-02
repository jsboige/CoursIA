# Probas - Programmation Probabiliste

Serie complete de notebooks sur la programmation probabiliste, couvrant l'inference bayesienne avec **Infer.NET** (C#) et **Pyro** (Python).

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 22 (20 Infer.NET + 2 Python) |
| Duree totale | ~18h |
| Langages | C# (.NET), Python |

## Structure

```
Probas/
├── Infer-101.ipynb              # Introduction Python/C# (standalone)
├── Pyro_RSA_Hyperbole.ipynb     # Pragmatique linguistique (Python)
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

## Prerequisites

### Pour Infer.NET (C#)

```bash
# .NET SDK 6.0+
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
