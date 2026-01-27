# Programmation Probabiliste avec Infer.NET

Serie de **12 notebooks** couvrant la programmation probabiliste avec Microsoft Infer.NET, des fondamentaux aux modeles relationnels avances.

## Vue d'ensemble

| # | Notebook | Duree | Concepts |
|---|----------|-------|----------|
| 1 | [Infer-1-Setup](Infer-1-Setup.ipynb) | 15 min | Installation, premier modele |
| 2 | [Infer-2-Gaussian-Mixtures](Infer-2-Gaussian-Mixtures.ipynb) | 50 min | Posterieurs, melanges, Dirichlet |
| 3 | [Infer-3-Factor-Graphs](Infer-3-Factor-Graphs.ipynb) | 45 min | Inference discrete, Monty Hall |
| 4 | [Infer-4-Bayesian-Networks](Infer-4-Bayesian-Networks.ipynb) | 55 min | CPT, D-separation, causalite |
| 5 | [Infer-5-Skills-IRT](Infer-5-Skills-IRT.ipynb) | 60 min | IRT, DINA, many-to-many |
| 6 | [Infer-6-TrueSkill](Infer-6-TrueSkill.ipynb) | 55 min | Ranking, online learning, equipes |
| 7 | [Infer-7-Classification](Infer-7-Classification.ipynb) | 50 min | BPM, regression logistique, A/B |
| 8 | [Infer-8-Model-Selection](Infer-8-Model-Selection.ipynb) | 45 min | Evidence, Bayes factors, ARD |
| 9 | [Infer-9-Topic-Models](Infer-9-Topic-Models.ipynb) | 60 min | LDA, documents-topics-mots |
| 10 | [Infer-10-Crowdsourcing](Infer-10-Crowdsourcing.ipynb) | 55 min | Workers, communautes, agregation |
| 11 | [Infer-11-Sequences](Infer-11-Sequences.ipynb) | 65 min | HMM, series temporelles, motifs |
| 12 | [Infer-12-Recommenders](Infer-12-Recommenders.ipynb) | 60 min | Factorisation, Click Model |

**Duree totale** : ~10h15

## Progression Pedagogique

```
FONDAMENTAUX (1-3)
+-- 1-Setup : Variables, inference basique
+-- 2-Gaussian-Mixtures : Distributions continues, melanges
+-- 3-Factor-Graphs : Inference discrete, conditionnement

MODELES CLASSIQUES (4-6)
+-- 4-Bayesian-Networks : CPT, causalite
+-- 5-Skills-IRT : Relations many-to-many
+-- 6-TrueSkill : Online learning, message passing

CLASSIFICATION & SELECTION (7-8)
+-- 7-Classification : BPM, regression logistique
+-- 8-Model-Selection : Evidence, ARD, comparaison

MODELES AVANCES (9-12)
+-- 9-Topic-Models : LDA, documents-topics-mots
+-- 10-Crowdsourcing : Hierarchique, communautes
+-- 11-Sequences : HMM, series temporelles
+-- 12-Recommenders : Factorisation, multi-vues
```

## Prerequis

- .NET 6.0 ou superieur
- .NET Interactive / Polyglot Notebooks
- VS Code avec extension Polyglot Notebooks (recommande)

## Installation

### 1. .NET SDK

```bash
# Verifier l'installation
dotnet --version
```

### 2. Extension VS Code

Installer l'extension "Polyglot Notebooks" depuis le marketplace VS Code.

### 3. Packages NuGet (automatique)

Chaque notebook inclut les references necessaires :

```csharp
#r "nuget: Microsoft.ML.Probabilistic"
#r "nuget: Microsoft.ML.Probabilistic.Compiler"
```

## Concepts Cles

### Types de Variables

| Type | Description | Exemple |
|------|-------------|---------|
| `Variable<bool>` | Variable booleenne | `Variable.Bernoulli(0.5)` |
| `Variable<double>` | Variable continue | `Variable.GaussianFromMeanAndVariance(0, 1)` |
| `Variable<int>` | Variable discrete | `Variable.DiscreteUniform(5)` |
| `VariableArray<T>` | Tableau 1D | `Variable.Array<double>(range)` |
| `VariableArray2D<T>` | Tableau 2D | `Variable.Array<double>(range1, range2)` |

### Distributions

| Distribution | Usage | Parametres |
|--------------|-------|------------|
| Bernoulli | Bool | prob |
| Gaussian | Continue | mean, variance/precision |
| Gamma | Precision | shape, scale |
| Beta | Probabilite | alpha, beta |
| Dirichlet | Proportions | concentrations |
| Discrete | Categorique | probs |

### Structures de Controle

```csharp
// Conditionnement
using (Variable.If(condition)) { ... }
using (Variable.IfNot(condition)) { ... }

// Selection (switch)
using (Variable.Switch(variable)) { ... }
using (Variable.Case(variable, value)) { ... }

// Boucles
using (Variable.ForEach(range)) { ... }
```

### Inference

```csharp
InferenceEngine moteur = new InferenceEngine();
moteur.Compiler.CompilerChoice = CompilerChoice.Roslyn;  // Important pour notebooks
moteur.Algorithm = new ExpectationPropagation();         // ou VariationalMessagePassing

var posterior = moteur.Infer<DistributionType>(variable);
```

## Structure des Fichiers

```
Infer/
+-- Infer-1-Setup.ipynb
+-- Infer-2-Gaussian-Mixtures.ipynb
+-- Infer-3-Factor-Graphs.ipynb
+-- Infer-4-Bayesian-Networks.ipynb
+-- Infer-5-Skills-IRT.ipynb
+-- Infer-6-TrueSkill.ipynb
+-- Infer-7-Classification.ipynb
+-- Infer-8-Model-Selection.ipynb
+-- Infer-9-Topic-Models.ipynb
+-- Infer-10-Crowdsourcing.ipynb
+-- Infer-11-Sequences.ipynb
+-- Infer-12-Recommenders.ipynb
+-- README.md
```

## Sources et References

### Documentation Officielle
- [Infer.NET Documentation](https://dotnet.github.io/infer/)
- [Infer.NET GitHub](https://github.com/dotnet/infer)

### Livre de Reference
- [Model-Based Machine Learning (MBML)](https://mbmlbook.com/) - Bishop et al.

### Exemples Utilises
- WetGrassSprinklerRain (Bayesian Networks)
- Murder Mystery (Factor Graphs, MBML Ch1)
- TrueSkill (Ranking, MBML Ch3)
- StudentSkills (IRT/DINA, MBML Ch2)
- ClinicalTrial (A/B Testing)
- LDA (Topic Models)
- Crowdsourcing (MBML Ch7)
- RecommenderSystem (Factorisation)
- ClickModel (Multi-vues)

## Applications

| Domaine | Modeles | Notebook |
|---------|---------|----------|
| Jeux video | TrueSkill, ranking | 6 |
| Education | IRT, DINA, competences | 5 |
| NLP | LDA, topics | 9 |
| Medecine | A/B testing, diagnostic | 4, 7 |
| Crowdsourcing | Agregation labels | 10 |
| Finance | Detection regimes | 11 |
| E-commerce | Recommandation | 12 |
| Bioinformatique | Motif finding | 11 |

## Conseils

1. **Suivre l'ordre** : Les notebooks sont conçus pour etre suivis sequentiellement
2. **Executer tout** : Chaque notebook est autonome, executez toutes les cellules
3. **Experimenter** : Modifiez les parametres pour comprendre leur impact
4. **Exercices** : Chaque notebook contient des exercices pratiques

## Algorithmes d'Inference

| Algorithme | Avantage | Utilisation |
|------------|----------|-------------|
| EP (Expectation Propagation) | Rapide, approximatif | Par defaut |
| VMP (Variational Message Passing) | Converge toujours | Modeles complexes |
| Gibbs Sampling | Exact (asymptotique) | Petits modeles |

## Troubleshooting

### Erreur de compilation
```csharp
moteur.Compiler.CompilerChoice = CompilerChoice.Roslyn;
```
Cette ligne est **obligatoire** pour les notebooks .NET Interactive.

### Convergence lente
- Reduire le nombre d'iterations : `moteur.NumberOfIterations = 50`
- Simplifier le modele
- Utiliser VMP au lieu d'EP

### Memoire insuffisante
- Reduire la taille des tableaux
- Utiliser des boucles `ForEach` au lieu de developpements explicites

---

Bonne exploration de la programmation probabiliste !
