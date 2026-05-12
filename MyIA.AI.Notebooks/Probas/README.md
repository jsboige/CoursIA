# Probas - Programmation Probabiliste

<!-- CATALOG-STATUS
series: Probas
pedagogical_count: 32
breakdown: Infer=20, _python_port=9, =3
maturity: ALPHA=17, BETA=9, PRODUCTION=6
-->

Le monde reel est incertain. Un diagnostic medical n'est jamais sur a 100%, un classement sportif depend de performances intrinsequement variables, et les donnees que nous collectons sont toujours bruitees ou incompletes. La programmation probabiliste offre un cadre rigoureux pour modeliser cette incertitude : plutot que de calculer une seule reponse, on obtient une **distribution de probabilites** qui quantifie notre confiance dans chaque resultat possible.

Cette serie vous apprend a construire des modeles probabilistes decomplexes en quelques lignes de code. Vous decouvrirez comment Infer.NET (Microsoft) permet de definir des variables aleatoires, d'exprimer des observations, et d'obtenir automatiquement les distributions posterieures — sans ecrire d'integrales ni deriver d'equations. Le parcours couvre les fondements mathematiques (distributions, graphs de facteurs), les modeles classiques (reseaux bayesiens, TrueSkill, LDA, HMM), puis la theorie de la decision bayesienne pour prendre des decisions optimales sous incertitude.

**A qui s'adresse cette serie** : etudiants en IA, data scientists, et developpeurs souhaitant aller au-dela des modeles deterministes. Les 20 notebooks Infer.NET utilisent le kernel .NET Interactive (C#), tandis que les 2 notebooks racine (Infer-101, Pyro RSA) sont en Python. Aucun prerequis en probabilites avancees : les concepts sont introduits progressivement.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 22 (20 Infer.NET + 2 Python) |
| Duree totale | ~20h |
| Langages | C# (.NET), Python |

## Parcours d'apprentissage

### Phase 1 : Fondations (Notebooks 1-3, ~2h)

Le parcours commence par le notebook 1 (Setup) qui installe Infer.NET et construit le premier modele bayesien — le classique "Two Coins" — en quelques lignes de C#. Le notebook 2 (Gaussian Mixtures) plonge dans les distributions continues avec les melanges gaussiens, outil fondamental du clustering. Le notebook 3 (Factor Graphs) introduit la representation graphique qui unifie tous les modeles : les graphs de facteurs, illustres par le probleme de Monty Hall. A l'issue de cette phase, vous comprenez comment exprimer un probleme incertain en termes de variables, de facteurs et de messages.

### Phase 2 : Modeles classiques (Notebooks 4-13, ~8h)

Les notebooks 4 a 13 construisent des modeles de complexite croissante, chacun illustre par une application concrete : reseaux bayesiens (diagnostic medical), Item Response Theory (evaluation de competences), TrueSkill (classement Xbox Live), classification bayesienne, selection de modeles (Bayes Factors), LDA (topic modeling), crowdsourcing (agregation de labels), HMM (sequences temporelles), systemes de recommandation, et debugging. Chaque notebook est autonome mais presuppose la maitrise des concepts des notebooks 1-3. Le notebook 13 (Debugging) est une reference pratique a consulter tout au long du parcours.

### Phase 3 : Decision bayesienne (Notebooks 14-20, ~7h)

La seconde moitie de la serie passe de l'inference a la decision : comment choisir une action quand on ne connait que des probabilites ? Les notebooks 14-16 posent les fondations (axiomes de l'utilite, fonctions d'utilite mono- et multi-attributs). Les notebooks 17-20 appliquent ces concepts aux reseaux de decision, a la valeur de l'information, aux systemes experts robustes, et aux processus decisionnels de Markov (MDPs) — qui relient cette serie a la serie [RL](../RL/).

### Parcours alternatif : Python (Infer-101 + Pyro RSA, ~2h)

Si vous preferez Python au C#, commencez par Infer-101.ipynb (introduction standalone avec modeles Two Coins et Cyclist) puis Pyro_RSA_Hyperbole.ipynb (application a la linguistique pragmatique avec le framework RSA). Ces deux notebooks ne dependent pas d'Infer.NET.

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

## Installation

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
|-------|------|-------------|
| [IIT](../IIT/README.md) | PyPhi | L'integration informationnelle (phi) repose sur les memes fondements probabilistes |
| [SymbolicAI/SemanticWeb](../SymbolicAI/SemanticWeb/README.md) | OWL reasoning | Les ontologies OWL utilisent la logique probabiliste pour le raisonnement incertain |
| [GameTheory](../GameTheory/README.md) | Bayesian games | Les jeux bayesiens combinent probabilites et theorie des jeux |
