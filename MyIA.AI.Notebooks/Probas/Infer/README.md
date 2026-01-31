# Programmation Probabiliste avec Infer.NET

Serie de **20 notebooks** couvrant la programmation probabiliste avec Microsoft Infer.NET, des fondamentaux aux modeles relationnels avances, incluant une section complete sur la theorie de la decision.

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
| 13 | [Infer-13-Debugging](Infer-13-Debugging.ipynb) | 45 min | Troubleshooting, diagnostics, algorithmes |
| 14 | [Infer-14-Decision-Utility-Foundations](Infer-14-Decision-Utility-Foundations.ipynb) | 50 min | Loteries, axiomes VNM, utilite esperee |
| 15 | [Infer-15-Decision-Utility-Money](Infer-15-Decision-Utility-Money.ipynb) | 45 min | Paradoxe St-Petersbourg, CARA, CRRA |
| 16 | [Infer-16-Decision-Multi-Attribute](Infer-16-Decision-Multi-Attribute.ipynb) | 50 min | MAUT, SMART, swing weights |
| 17 | [Infer-17-Decision-Networks](Infer-17-Decision-Networks.ipynb) | 55 min | Diagrammes d'influence, politique optimale |
| 18 | [Infer-18-Decision-Value-Information](Infer-18-Decision-Value-Information.ipynb) | 45 min | EVPI, EVSI, valeur de l'information |
| 19 | [Infer-19-Decision-Expert-Systems](Infer-19-Decision-Expert-Systems.ipynb) | 50 min | Systemes experts, Minimax, regret |
| 20 | [Infer-20-Decision-Sequential](Infer-20-Decision-Sequential.ipynb) | 60 min | MDPs, iteration valeur/politique |

**Duree totale** : ~17h

**Ressource complementaire** : [Glossaire](Infer-Glossary.md) - Definitions des termes techniques

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

REFERENCE (13)
+-- 13-Debugging : Troubleshooting, diagnostics, comparaison algorithmes

THEORIE DE LA DECISION (14-20)
+-- 14-Decision-Utility-Foundations : Loteries, axiomes VNM
+-- 15-Decision-Utility-Money : Aversion au risque, CARA/CRRA
+-- 16-Decision-Multi-Attribute : Decisions multi-criteres, SMART
+-- 17-Decision-Networks : Diagrammes d'influence
+-- 18-Decision-Value-Information : EVPI, EVSI
+-- 19-Decision-Expert-Systems : Systemes experts, Minimax
+-- 20-Decision-Sequential : MDPs, planification
```

---

## Theorie de la Decision (Notebooks 14-20)

Les notebooks 14-20 forment une serie complete sur la theorie de la decision bayesienne.

### Infer-14 : Axiomes et Fondements

**Duree** : 50 min | **Prerequis** : Notebooks 1-8

**Objectifs** :

- Comprendre les **loteries** comme representation des choix stochastiques
- Maitriser les **axiomes de Von Neumann-Morgenstern** (Completude, Transitivite, Continuite, Independance)
- Deriver la **fonction d'utilite** par calibration
- Comprendre l'**agent rationnel** (maximise E[U])

**Sections** :

1. Pourquoi l'Utilite ?
2. Loteries : Representation Formelle
3. Axiomes de Preferences Rationnelles
4. Theoreme de Representation
5. Calibration par Mise a l'Indifference
6. Modelisation avec Infer.NET
7. Exercice : Calibrer Votre Fonction d'Utilite

**Applications** : Decision medicale, assurance automobile, investissement

---

### Infer-15 : Utilite de l'Argent et Aversion au Risque

**Duree** : 45 min | **Prerequis** : Notebook 14

**Objectifs** :

- Comprendre le **Paradoxe de Saint-Petersbourg** (valeur esperee infinie)
- Maitriser les fonctions **CARA** et **CRRA**
- Calculer les **coefficients Arrow-Pratt** (aversion absolue/relative)
- Appliquer la **dominance stochastique** (1er et 2nd ordre)

**Concepts cles** :

| Fonction | Formule | Propriete |
|----------|---------|-----------|
| CARA | U(x) = -e^(-ax) | Aversion absolue constante |
| CRRA | U(x) = x^(1-rho)/(1-rho) | Aversion relative constante |
| Logarithmique | U(x) = ln(x) | Cas special CRRA (rho=1) |

**Sections** :

1. Paradoxe de Saint-Petersbourg (Bernoulli 1713)
2. Utilite Marginale Decroissante
3. Fonctions d'Utilite Classiques
4. Coefficients Arrow-Pratt
5. Equivalent Certain et Prime de Risque
6. Dominance Stochastique
7. Application : Choix d'Investissement
8. Exercice : Votre Profil de Risque
9. Inference Bayesienne de l'Aversion avec Infer.NET

**Applications** : Simulation Monte Carlo, selection de portefeuille (Livret A vs Fonds vs Actions)

---

### Infer-16 : Utilite Multi-Attributs

**Duree** : 50 min | **Prerequis** : Notebooks 14-15

**Objectifs** :

- Modeliser des decisions avec **plusieurs criteres**
- Comprendre l'**independance preferentielle**
- Appliquer les **theoremes d'additivite et multiplicativite**
- Utiliser la methode **SMART**

**Concepts cles** :

| Forme | Formule | Condition |
|-------|---------|-----------|
| Additive | V(x) = Sum wi x vi(xi) | Independance mutuelle |
| Multiplicative | 1+kU = Prod(1+kki.Ui) | Interactions entre attributs |

**Sections** :

1. Decisions Multi-Criteres
2. Fonctions de Valeur vs Utilite
3. Independance Preferentielle
4. Theoreme d'Additivite (Debreu-Gorman)
5. Determination des Poids (Swing Weights)
6. Utilite Multiplicative
7. Methode SMART
8. Analyse de Sensibilite
9. Integration avec Infer.NET
10. Exercice : Votre Decision Multi-Attributs
11. Apprentissage Bayesien des Poids

**Applications** : Achat automobile (prix, securite, conso, confort), choix de carriere, selection de site

---

### Infer-17 : Reseaux de Decision

**Duree** : 55 min | **Prerequis** : Notebooks 3, 14-16

**Objectifs** :

- Etendre les reseaux bayesiens avec **noeuds de decision et d'utilite**
- Calculer la **politique optimale** (backward induction)
- Comprendre les **arcs informationnels**
- Modeliser des **decisions sequentielles**

**Types de noeuds** :

| Noeud | Forme | Role |
|-------|-------|------|
| Chance | Ovale | Variable aleatoire |
| Decision | Rectangle | Choix de l'agent |
| Utilite | Losange | Fonction de recompense |

**Sections** :

1. Des Reseaux Bayesiens aux Reseaux de Decision
2. Types de Noeuds
3. Arcs Informationnels
4. Calcul de la Politique Optimale
5. Exemple : Investissement avec Test de Marche
6. Decisions Sequentielles
7. Implementation avec Infer.NET
8. Visualisation du Factor Graph
9. Exercice : Reseau de Decision Personnalise
10. Application MAUT : Choix de Site d'Aeroport

**Applications** : Diagnostic medical avec decision de traitement, investissement avec etude de marche

---

### Infer-18 : Valeur de l'Information

**Duree** : 45 min | **Prerequis** : Notebooks 14-17

**Objectifs** :

- Calculer la **valeur de l'information parfaite** (EVPI)
- Calculer la **valeur de l'information d'echantillon** (EVSI)
- Comprendre **quand l'information a de la valeur**

**Formules cles** :

| Mesure | Formule | Interpretation |
|--------|---------|----------------|
| EVPI | E[max U given omega] - max E[U] | Gain si on connait l'etat du monde |
| EVSI | E[max U given signal] - max E[U] | Gain avec test imparfait |
| Efficacite | EVSI / EVPI | Qualite relative du test |

**Sections** :

1. Information et Reduction d'Incertitude
2. Valeur de l'Information Parfaite (EVPI)
3. Exemple : Droits de Forage Petrolier
4. Exemple : Chasse au Tresor
5. Quand l'Information a-t-elle de la Valeur ?
6. Implementation avec Infer.NET
7. Exercice : Faut-il Faire un Test Medical ?
8. Diagnostic Medical avec Tests Successifs

**Applications** : Droits petroliers (test sismique), diagnostic medical (sensibilite 95%, specificite 90%)

---

### Infer-19 : Systemes Experts et Robustesse

**Duree** : 50 min | **Prerequis** : Notebooks 14-18

**Objectifs** :

- Comprendre les **systemes experts** et leur architecture
- Appliquer le critere **Minimax** (decisions robustes)
- Implementer le critere **Minimax Regret**
- Gerer l'**incertitude sur les probabilites** (Knightienne)

**Criteres de decision** :

| Critere | Formule | Attitude |
|---------|---------|----------|
| Maximax | max_a max_omega U(a,omega) | Optimiste |
| Minimax | max_a min_omega U(a,omega) | Pessimiste |
| Minimax Regret | min_a max_omega [U*(omega) - U(a,omega)] | Minimise le pire regret |
| Hurwicz | alpha x max + (1-alpha) x min | Compromis |

**Sections** :

1. Systemes Experts : Architecture et Historique
2. Decision sous Incertitude Severe
3. Critere Minimax
4. Critere Minimax Regret
5. Comparaison Complete des Criteres
6. Critere Hurwicz
7. Robustesse aux Erreurs de Modelisation
8. Systeme Expert Bayesien Multi-Sources avec Infer.NET
9. Exercice : Systeme Expert de Diagnostic

**Applications** : Diagnostic informatique, diagnostic medical multi-sources, decisions financieres robustes

---

### Infer-20 : Decisions Sequentielles (MDPs)

**Duree** : 60 min | **Prerequis** : Notebooks 14-19

**Objectifs** :

- Comprendre les **Processus de Decision Markoviens** (MDPs)
- Maitriser l'**iteration de valeur** et l'**iteration de politique**
- Decouvrir les alternatives : **LP, Expectimax, RTDP**
- Appliquer le **reward shaping** avec preservation de politique

**Composants d'un MDP** :

| Composant | Notation | Description |
|-----------|----------|-------------|
| Etats | S | Ensemble des situations possibles |
| Actions | A | Choix disponibles |
| Transition | P(s' given s,a) | Probabilite de changement d'etat |
| Recompense | R(s,a) | Gain immediat |
| Discount | gamma in [0,1] | Facteur d'actualisation |

**Equation de Bellman** :

```
V(s) = max_a [R(s,a) + gamma x Sum P(s'|s,a) x V(s')]
```

**Sections** :

1. Decisions Sequentielles vs One-Shot
2. Processus de Decision Markoviens
3. Equation de Bellman
4. Iteration de Valeur
5. Iteration de Politique
6. Alternatives : LP, Expectimax, RTDP
7. Reward Shaping
8. Bandits Multi-Bras
9. Indice de Gittins
10. POMDPs : MDPs Partiellement Observables

**Applications** : Navigation robotique, allocation de ressources, jeux de strategie

---

## Prerequis

- .NET 6.0 ou superieur
- .NET Interactive / Polyglot Notebooks
- VS Code avec extension Polyglot Notebooks (recommande)
- Graphviz (optionnel, pour visualisation des factor graphs)

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

### 4. Graphviz (optionnel)

Pour les visualisations de factor graphs dans les notebooks 11, 14-20 :

```bash
# Windows (chocolatey)
choco install graphviz

# Ou telechargement direct depuis https://graphviz.org/download/
```

## Concepts Cles Infer.NET

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
+-- Infer-1-Setup.ipynb ... Infer-20-Decision-Sequential.ipynb
+-- Infer-Glossary.md
+-- FactorGraphHelper.cs          # Helper pour visualisation Graphviz
+-- README.md
+-- scripts/                      # Scripts de maintenance
```

## Domaines d'Application

| Domaine | Modeles | Notebooks |
|---------|---------|-----------|
| Jeux video | TrueSkill, ranking | 6 |
| Education | IRT, DINA, competences | 5 |
| NLP | LDA, topics | 9 |
| Medecine | A/B testing, diagnostic, systemes experts | 4, 7, 17, 18, 19 |
| Crowdsourcing | Agregation labels | 10 |
| Finance | Detection regimes, aversion risque, MDPs | 11, 15, 20 |
| E-commerce | Recommandation | 12 |
| Bioinformatique | Motif finding | 11 |
| Planification | Diagrammes d'influence, MDPs | 17, 20 |
| Controle qualite | Valeur de l'information | 18 |

## Sources et References

### Documentation Officielle

- [Infer.NET Documentation](https://dotnet.github.io/infer/)
- [Infer.NET GitHub](https://github.com/dotnet/infer)

### Livre de Reference

- [Model-Based Machine Learning (MBML)](https://mbmlbook.com/) - Bishop et al.

### References Theorie de la Decision

- von Neumann & Morgenstern (1944) : Theory of Games and Economic Behavior
- Arrow (1965) : Aspects of the Theory of Risk Bearing
- Keeney & Raiffa (1976) : Decisions with Multiple Objectives
- Howard (1966) : Information Value Theory
- Bellman (1957) : Dynamic Programming

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
- St-Petersburg Paradox (Decision Theory)
- Investment Portfolio (Decision Networks)
- Medical Diagnosis (Expert Systems)
- Inventory Management (MDPs)

## Algorithmes d'Inference

| Algorithme | Avantage | Utilisation |
|------------|----------|-------------|
| EP (Expectation Propagation) | Rapide, approximatif | Par defaut |
| VMP (Variational Message Passing) | Converge toujours | Modeles complexes |
| Gibbs Sampling | Exact (asymptotique) | Petits modeles |

## Troubleshooting

Pour un guide complet de troubleshooting, voir [Infer-13-Debugging](Infer-13-Debugging.ipynb).

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

### Factor Graph non affiche

- Verifier que Graphviz est installe et dans le PATH
- Verifier que `FactorGraphHelper.cs` est present dans le repertoire
- Essayer `engine.ShowFactorGraph = true` avant l'inference

### Erreurs connues dans les notebooks de decision

- `Beta.GetQuantile` n'existe pas : utiliser l'approximation normale pour les intervalles de credibilite
- `ShowFactorGraph` peut causer un crash du kernel : utiliser avec precaution

### Glossaire

Consultez le [Glossaire](Infer-Glossary.md) pour les definitions des termes techniques (EP, VMP, Factor Graph, EVPI, MDP, etc.)

---

Bonne exploration de la programmation probabiliste et de la theorie de la decision !
