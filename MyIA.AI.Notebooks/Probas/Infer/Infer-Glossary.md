# Glossaire Infer.NET

Ce glossaire recapitule les termes techniques utilises dans la serie de notebooks Infer.NET.

---

## Algorithmes d'Inference

| Terme | Definition | Notebook(s) |
|-------|------------|-------------|
| **EP (Expectation Propagation)** | Algorithme d'inference approchee qui propage des messages gaussiens entre facteurs. Rapide mais peut diverger. | Tous |
| **VMP (Variational Message Passing)** | Algorithme variationnel qui minimise la divergence KL. Plus stable que EP, mais sous-estime l'incertitude. | Infer-2, Infer-9 |
| **Gibbs Sampling** | Methode MCMC qui echantillonne chaque variable conditionnellement aux autres. Exact asymptotiquement mais lent. | Infer-13 |
| **Message Passing** | Paradigme ou les distributions sont propagees entre variables via des "messages". | Infer-3, Infer-6 |

---

## Distributions

| Distribution | Support | Parametres | Usage typique |
|--------------|---------|------------|---------------|
| **Bernoulli** | {0, 1} | p (probabilite) | Evenements binaires |
| **Beta** | [0, 1] | alpha, beta | Prior sur probabilites |
| **Gaussian** | R | mean, precision | Valeurs continues |
| **TruncatedGaussian** | [a, b] | mean, variance, lower, upper | Valeurs contraintes |
| **Gamma** | R+ | shape, scale | Prior sur precisions |
| **Dirichlet** | Simplex | alpha[] | Prior sur poids de melange |
| **Discrete** | {0, ..., K-1} | probs[] | Variables categoriques |

---

## Concepts Probabilistes

| Terme | Definition | Exemple |
|-------|------------|---------|
| **Prior** | Distribution a priori sur un parametre avant observation | Beta(1,1) = uniform |
| **Posterior** | Distribution mise a jour apres observations | Beta(8,4) |
| **Likelihood** | Probabilite des observations sachant les parametres | P(donnees \| theta) |
| **Conjugate Prior** | Prior dont le posterior a la meme forme | Beta-Bernoulli |
| **Evidence** | Probabilite marginale des observations P(donnees) | Pour comparaison de modeles |
| **Latent Variable** | Variable non observee a inferer | Capacite etudiant (IRT) |

---

## Structures Infer.NET

| Element | Syntaxe | Description |
|---------|---------|-------------|
| **Variable<T>** | `Variable<double>` | Variable aleatoire scalaire |
| **VariableArray<T>** | `Variable.Array<double>(range)` | Tableau de variables |
| **VariableArray2D<T>** | `Variable.Array<double>(r1, r2)` | Matrice de variables |
| **Range** | `new Range(n)` | Indice pour les boucles de plaque |
| **Variable.ForEach** | `using (Variable.ForEach(range))` | Plaque (repetition independante) |
| **Variable.Switch** | `using (Variable.Switch(idx))` | Selection dynamique |
| **Variable.If** | `using (Variable.If(condition))` | Branchement conditionnel |

---

## Modeles Specifiques

### IRT (Item Response Theory)
- **Capacite** : Variable latente representant le niveau d'un etudiant
- **Difficulte** : Parametre d'une question
- **Discrimination** : Sensibilite de la question a la capacite

### DINA (Deterministic Input, Noisy And)
- **Matrice Q** : Indique quelles competences sont requises par question
- **Slip** : P(incorrect | a toutes les competences)
- **Guess** : P(correct | manque une competence)

### TrueSkill
- **Skill** : Capacite estimee d'un joueur
- **Performance** : Realisation bruitee du skill dans un match
- **Dynamic Factor** : Evolution du skill dans le temps

### LDA (Latent Dirichlet Allocation)
- **Topic** : Distribution sur le vocabulaire
- **Theta** : Distribution de topics par document
- **Phi** : Distribution de mots par topic

### HMM (Hidden Markov Model)
- **Etat cache** : Variable latente discrete a chaque temps
- **Emission** : Distribution d'observation par etat
- **Transition** : Probabilite de changement d'etat

---

## Patterns de Code

### Creation de modele
```csharp
// Variable avec prior
Variable<double> x = Variable.GaussianFromMeanAndPrecision(0, 1).Named("x");

// Observation
x.ObservedValue = 5.0;

// Variable dependante
Variable<double> y = Variable.GaussianFromMeanAndPrecision(x, precision);
```

### Inference
```csharp
InferenceEngine engine = new InferenceEngine(new ExpectationPropagation());
engine.Compiler.CompilerChoice = CompilerChoice.Roslyn;
Gaussian xPost = engine.Infer<Gaussian>(x);
```

### Modele de melange
```csharp
Variable<int> z = Variable.Discrete(weights);  // Composante
using (Variable.Switch(z))
{
    x.SetTo(Variable.GaussianFromMeanAndPrecision(means[z], precisions[z]));
}
```

---

## Erreurs Communes

| Message | Cause | Solution |
|---------|-------|----------|
| "Model has no support" | Observation impossible sous le prior | Elargir le prior |
| "Improper distribution" | Divergence | Regulariser ou changer d'algorithme |
| "Experimental quality band" | Operateur non stable | Verifier les resultats manuellement |

---

## Ressources

- [Documentation officielle](https://dotnet.github.io/infer/)
- [Tutorials](https://dotnet.github.io/infer/userguide/Infer.NET%20tutorials%20and%20examples.html)
- [MBML Book](https://mbmlbook.com/)
- [GitHub](https://github.com/dotnet/infer)
