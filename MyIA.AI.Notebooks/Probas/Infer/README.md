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

## Fondamentaux (Notebooks 1-3)

Les notebooks 1-3 introduisent les concepts fondamentaux de la programmation probabiliste avec Infer.NET.

### Infer-1 : Configuration et Premier Modele

**Duree** : 45 min | **Prerequis** : Notions de probabilites

**Objectifs** :

- Installer et configurer Infer.NET dans .NET Interactive
- Comprendre le workflow en 3 etapes : Modele → Moteur → Inference
- Implementer un premier modele bayesien (Two Coins)
- Maitriser les priors conjugues Beta-Bernoulli

**Sections** :

1. Configuration de l'environnement (.NET Interactive, CompilerChoice.Roslyn)
2. Introduction a la programmation probabiliste
3. Exemple : Probleme des deux pieces (Two Coins)
4. Exemple avance : Estimation de piece biaisee avec prior Beta
5. Apprentissage en ligne : mise a jour sequentielle

**Concepts cles** :

| Concept | Description |
|---------|-------------|
| Variable\<T\> | Representation des quantites incertaines |
| Prior conjugue | Beta-Bernoulli pour inference analytique |
| ExpectationPropagation | Algorithme d'inference par defaut |

**Applications** : Estimation de piece biaisee, apprentissage en ligne

---

### Infer-2 : Distributions Continues et Melanges

**Duree** : 50 min | **Prerequis** : Notebook 1

**Objectifs** :

- Modeliser des donnees continues avec distributions gaussiennes
- Maitriser les priors conjugues Gaussian-Gaussian et Gamma-Gamma
- Implementer l'apprentissage en ligne
- Decouvrir les modeles de melange avec `Variable.Switch`

**Sections** :

1. Modelisation de temps de trajet de cycliste
2. Priors conjugues et apprentissage en ligne
3. Melanges gaussiens pour donnees multimodales
4. Visualisation des factor graphs

**Concepts cles** :

| Distribution | Usage | Parametres |
|--------------|-------|------------|
| Gaussian | Quantites continues | mean, precision |
| Gamma | Prior sur precision | shape, scale |
| Variable.Switch | Selection de composante | index, values |

**Applications** : Temps de trajet cycliste, detection de modes multiples, clustering

---

### Infer-3 : Graphes de Facteurs et Inference Discrete

**Duree** : 55 min | **Prerequis** : Notebooks 1-2

**Objectifs** :

- Comprendre la representation en graphes de facteurs
- Maitriser `Variable.If/IfNot` et `Variable.Case` pour branchements
- Observer le phenomene d'explaining away
- Implementer le paradoxe de Monty Hall

**Sections** :

1. Introduction aux graphes de facteurs
2. Exemple Murder Mystery (MBML Ch.1)
3. Paradoxe de Monty Hall avec `Variable.Case`
4. Phenomene Explaining Away
5. Visualisation Graphviz

**Concepts cles** :

| Structure | Usage | Exemple |
|-----------|-------|---------|
| Variable.If | Conditionnement binaire | P(Y\|X=true) |
| Variable.Case | Conditionnement multi-value | Switch sur enum |
| Explaining away | Causes alternatives | P(A\|B,C) < P(A\|C) |

**Applications** : Murder Mystery, Monty Hall (2/3 vs 1/3), systemes experts

---

## Modeles Classiques (Notebooks 4-6)

Les notebooks 4-6 couvrent les modeles bayesiens classiques : reseaux, competences et classement.

### Infer-4 : Reseaux Bayesiens

**Duree** : 60 min | **Prerequis** : Notebook 3

**Objectifs** :

- Construire des reseaux bayesiens avec tables de probabilite conditionnelle (CPT)
- Comprendre D-separation et independance conditionnelle
- Distinguer inference causale (do) vs observationnelle
- Implementer des modeles hierarchiques

**Sections** :

1. Reseau Wet Grass/Sprinkler/Rain
2. Construction de CPTs avec `Variable.Case`
3. D-separation et independance
4. Inference causale vs observationnelle
5. Modele hierarchique Rats (BUGS)

**Concepts cles** :

| Concept | Formule | Description |
|---------|---------|-------------|
| CPT | P(X \| Parents(X)) | Table de probabilite conditionnelle |
| D-separation | - | Critere graphique d'independance |
| do-calculus | P(Y \| do(X)) ≠ P(Y \| X) | Intervention vs observation |
| Hierarchique | θᵢ ~ F(λ) | Pooling partiel entre groupes |

**Applications** : Wet Grass, diagnostic medical, modele Rats (8 laboratoires)

---

### Infer-5 : Theorie de la Reponse a l'Item (IRT)

**Duree** : 65 min | **Prerequis** : Notebook 4

**Objectifs** :

- Implementer IRT (Item Response Theory) Difficulty-Ability
- Decouvrir DINA pour competences discretes
- Modeliser les parametres slip et guess
- Gerer les relations many-to-many avec Q-matrix
- Evaluer avec courbes ROC

**Sections** :

1. Modele IRT Difficulty-Ability (continu)
2. Modele DINA avec competences binaires
3. Parametres slip et guess
4. Q-matrix pour competences multiples
5. Evaluation ROC

**Concepts cles** :

| Modele | Formule | Usage |
|--------|---------|-------|
| IRT | P(correct) = σ(ability - difficulty) | Competence continue |
| DINA | ηᵢⱼ = Πₖ αⱼₖ^qᵢₖ | Competences binaires |
| Slip | P(erreur \| maitrise) | Erreur d'inattention |
| Guess | P(succes \| non-maitrise) | Reponse au hasard |

**Applications** : Tests educatifs, diagnostic de competences, adaptive testing

---

### Infer-6 : TrueSkill

**Duree** : 50 min | **Prerequis** : Notebook 2

**Objectifs** :

- Comprendre le systeme TrueSkill (Xbox Live)
- Modeliser le skill comme Gaussian(μ, σ²)
- Gerer les matchs avec `ConstrainBetween`
- Implementer l'apprentissage en ligne
- Etendre au 2v2 et free-for-all

**Sections** :

1. Modele TrueSkill de base (1v1)
2. Representation du skill : N(μ, σ²)
3. Modeling matches avec performance = skill + bruit
4. Gestion des ex-aequo
5. Extensions : Teams (2v2), Multi-player

**Concepts cles** :

| Composant | Formule | Description |
|-----------|---------|-------------|
| Skill | N(μ, σ²) | Niveau + incertitude |
| Performance | pᵢ = skillᵢ + N(0, β²) | Skill + bruit de match |
| Team skill | Σ skills individuels | Somme des membres |
| Update | μ_new ∝ surprise | Plus grande si upset |

**Applications** : Classement Xbox Live, tournois esports, matchmaking equilibre

---

## Classification et Selection (Notebooks 7-8)

Les notebooks 7-8 couvrent la classification bayesienne et la selection de modeles.

### Infer-7 : Classification Bayesienne

**Duree** : 55 min | **Prerequis** : Notebook 4

**Objectifs** :

- Implementer la regression logistique bayesienne (probit model)
- Decouvrir le Bayes Point Machine (BPM)
- Modeliser les tests A/B cliniques avec Beta-Binomial
- Propager l'incertitude dans les predictions

**Sections** :

1. Regression logistique bayesienne (probit)
2. Bayes Point Machine (BPM) multi-features
3. Test A/B clinique avec Beta-Binomial
4. Propagation d'incertitude
5. Exercice : Classification de spam

**Concepts cles** :

| Modele | Formule | Description |
|--------|---------|-------------|
| Probit | P(y=1\|x) = Φ(w·x) | CDF gaussienne |
| BPM | Moyenne du posterior sur w | Classification robuste |
| Beta-Binomial | Hierarchique pour proportions | Test A/B |

**Applications** : Classification spam/ham, test A/B clinique, detection d'anomalies

---

### Infer-8 : Selection de Modeles

**Duree** : 50 min | **Prerequis** : Notebook 7

**Objectifs** :

- Calculer l'evidence (marginal likelihood)
- Comparer modeles avec Bayes Factor
- Comprendre Occam's Razor automatique
- Implementer ARD (Automatic Relevance Determination)

**Sections** :

1. Evidence et marginal likelihood
2. Bayes Factor pour comparaison de modeles
3. Occam's Razor : penalisation automatique
4. ARD pour selection de features
5. LOO-CV bayesien vs frequentiste

**Concepts cles** :

| Concept | Formule | Interpretation |
|---------|---------|----------------|
| Evidence | P(D\|M) = ∫ P(D\|θ)P(θ\|M)dθ | Vraisemblance marginale |
| Bayes Factor | BF₁₂ = P(D\|M₁) / P(D\|M₂) | >10 = forte evidence |
| ARD | wᵢ ~ N(0, λᵢ⁻¹) | λᵢ → ∞ si non pertinent |

**Applications** : Comparaison polynomes, feature selection, model averaging

---

## Modeles Avances (Notebooks 9-12)

Les notebooks 9-12 couvrent les modeles avances : topics, crowdsourcing, sequences et recommandation.

### Infer-9 : Topic Models (LDA)

**Duree** : 60 min | **Prerequis** : Notebook 4

**Objectifs** :

- Implementer LDA (Latent Dirichlet Allocation)
- Maitriser les priors Dirichlet
- Resoudre la convergence VMP vers solutions degenerees
- Utiliser des priors asymetriques

**Sections** :

1. Introduction a LDA et bag-of-words
2. Priors Dirichlet conjugues
3. Probleme : VMP + priors symetriques → modes degeneres
4. Solution : Priors asymetriques
5. Prediction sur nouveaux documents

**Concepts cles** :

| Composant | Distribution | Role |
|-----------|--------------|------|
| θ_d | Dirichlet(α) | Proportions topics/document |
| z_dn | Categorical(θ_d) | Topic du mot n |
| φ_k | Dirichlet(β) | Distribution mots/topic |

**Note** : Utilise VMP au lieu d'EP pour les modeles LDA.

**Applications** : Analyse de corpus, detection de themes, recommandation de contenu

---

### Infer-10 : Crowdsourcing

**Duree** : 55 min | **Prerequis** : Notebook 4

**Objectifs** :

- Agreger des annotations de multiples annotateurs
- Modeliser Honest Worker (capacite unique)
- Implementer Biased Worker (matrice de confusion)
- Decouvrir le modele Community
- Appliquer l'apprentissage actif

**Sections** :

1. Modele Honest Worker
2. Modele Biased Worker (matrice de confusion)
3. Modele Community (groupes hierarchiques)
4. Active learning : selection d'items
5. Gold standard pour calibration

**Concepts cles** :

| Modele | Formule | Description |
|--------|---------|-------------|
| Honest | P(label\|true, worker) = α_worker | Capacite unique |
| Biased | C_worker[true, observed] | Matrice de confusion |
| Uncertainty | H(c \| y₁:ₙ) | Entropie pour active learning |

**Applications** : Amazon Mechanical Turk, controle qualite, optimisation budget annotation

---

### Infer-11 : Sequences (HMM)

**Duree** : 65 min | **Prerequis** : Notebook 10

**Objectifs** :

- Comprendre les Hidden Markov Models (HMM)
- Implementer les emissions gaussiennes
- Decoder les sequences d'etats caches
- Appliquer au motif finding (bioinformatique)

**Sections** :

1. Introduction aux HMM
2. HMM avec emissions gaussiennes
3. Approche simplifiee : classification independante
4. HMM complet avec Forward-Backward
5. Detection de regimes meteo
6. Motif finding ADN
7. Exercice : Detection de promotions

**Concepts cles** :

| Algorithme | Formule | Usage |
|------------|---------|-------|
| Forward | αₜ(k) = P(x₁:ₜ, zₜ=k) | Probabilite jointe |
| Backward | βₜ(k) = P(xₜ₊₁:T \| zₜ=k) | Complement |
| Posterior | γₜ(k) ∝ αₜ(k)·βₜ(k) | Etat a chaque t |

**Note** : Infer.NET ne supporte pas nativement les HMM complets. Implementation manuelle Forward-Backward recommandee.

**Applications** : Detection d'anomalies capteur, prevision meteo, motif finding ADN

---

### Infer-12 : Systemes de Recommandation

**Duree** : 70 min | **Prerequis** : Notebook 7

**Objectifs** :

- Implementer la factorisation matricielle probabiliste
- Gerer le cold-start avec features
- Decouvrir le Click Model pour sources multiples
- Classer des documents par pertinence

**Sections** :

1. Introduction aux systemes de recommandation
2. Factorisation matricielle (User × Item traits)
3. Probleme de sous-determination avec peu de donnees
4. Cold-start : regression avec features
5. Click Model : aggregation de sources
6. Classement de documents
7. Exercice : Recommandation de films

**Concepts cles** :

| Modele | Formule | Description |
|--------|---------|-------------|
| Factorisation | R_ui ≈ U_u · I_i | Traits latents |
| Cold-start | R ~ w·features | Features utilisateur/item |
| Click Model | P(click) = P(examine) × P(relevant) | Sources multiples |

**Applications** : Netflix/Amazon, moteurs de recherche, e-commerce

---

## Reference (Notebook 13)

### Infer-13 : Debugging et Bonnes Pratiques

**Duree** : 60 min | **Prerequis** : Tous les notebooks precedents

**Objectifs** :

- Diagnostiquer les erreurs courantes
- Comparer EP vs VMP
- Maitriser les outils de debug Infer.NET
- Appliquer les bonnes pratiques

**Sections** :

1. Erreurs courantes et solutions
2. Comparaison EP vs VMP
3. Outils de debug (ShowFactorGraph, BrowserMode)
4. Bonnes pratiques de modelisation
5. Checklist de debugging
6. Fonctions de diagnostic
7. Exercice : Debugger un modele bugue

**Problemes courants** :

| Probleme | Symptome | Solution |
|----------|----------|----------|
| Observed + Inferred | PointMass | Ne pas ObservedValue sur variable inferee |
| Label switching | Modes symetriques | Priors asymetriques |
| Variance nulle | IsPointMass = true | Verifier prior, observations |
| Convergence lente | Iterations > 50 | Verifier graphe, utiliser VMP |

**Comparaison EP vs VMP** :

| Critere | EP | VMP |
|---------|-----|-----|
| Exactitude | Exact (gaussiennes) | Approximation |
| Vitesse | Plus lent | Rapide |
| Convergence | Garantie | Peut diverger |

**Bonnes pratiques** :

1. Nommer toutes les variables : `.Named("theta")`
2. Verifier le factor graph systematiquement
3. Tester avec donnees simulees
4. Choisir priors informatifs (Beta(2,2) > Beta(1,1))
5. Valider posteriors (variance > 0, IsProper = true)

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
