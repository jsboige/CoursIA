# Probas - Programmation Probabiliste

<!-- CATALOG-STATUS
series: Probas
pedagogical_count: 44
breakdown: Infer=21, PyMC=20, root=3
maturity: PRODUCTION=44
-->

[← Notebooks](../README.md) | [Série Infer (C#) →](Infer/README.md) | [Série PyMC (Python) →](PyMC/README.md) | [GameTheory →](../GameTheory/README.md)

Le monde réel est incertain. Un diagnostic medical n'est jamais sur a 100%, un classement sportif depend de performances intrinsequement variables, et les données que nous collectons sont toujours bruitees ou incompletes. La programmation probabiliste offre un cadre rigoureux pour modeliser cette incertitude : plutôt que de calculer une seule reponse, on obtient une **distribution de probabilités** qui quantifie notre confiance dans chaque resultat possible.

Cette série couvre trois stack complémentaires : **Infer.NET** (Microsoft, C#/.NET Interactive) pour l'inference exacte par message passing, **PyMC** (Python) pour l'echantillonnage MCMC moderne, et des **applications standalone** (RSA). Les 21 notebooks Infer.NET couvrent les fondements mathematiques (distributions, graphs de facteurs), les modèles classiques (reseaux bayesiens, TrueSkill, LDA, HMM), puis la théorie de la décision bayésienne — jusqu'a un compagnon **Lean 4** (Infer-20b, adosse au projet Lake `gittins_lean`) qui demontre formellement les identites d'escompte de l'indice de Gittins. Les 20 notebooks PyMC reprennent l'intégralité des modèles Infer.NET en Python avec l'echantillonnage NUTS, offrant un pont naturel vers l'ecosysteme data science : fondations 1-3, modèles classiques 4-13, et théorie de la décision 14-20.

## Pourquoi cette série

La programmation probabiliste occupe une place singuliere dans la paysage de l'IA. Alors que le machine learning classique fournit des predictions ponctuelles (un score, une classe), il ne dit pas a quel point il a confiance en cette prediction. La programmation probabiliste, elle, quantifie cette incertitude de facon native.

Cette série repose sur une **double approche d'inference**, deliberatement juxtaposee :

- **Inference exacte par message passing** (Infer.NET) : pour les modèles où les distributions posterieures peuvent être calculees exactement (ou approchées par EP/VMP). C'est la methode des graphes de facteurs, ou les probalilites se propagent le long des aretes comme des messages. Avantage : résultats deterministes, rapide, visualisation du graphe de facteurs. Limite : ne s'applique qu'a une famille restreinte de modèles.
- **Inference approchée par echantillonnage MCMC** (PyMC) : pour les modèles plus generiques ou l'inference exacte est intractable. NUTS (No-U-Turn Sampler) explore l'espace posterior en simulant une dynamique hamiltonienne. Avantage : s'applique a presque tout modèle. Limite : results stochastiques, temps de convergence variable, diagnostic nécessaire.

Avoir les deux approches sur les mêmes modèles permet de comprendre leur **champ d'application** et leurs **compromis**, une connaissance cruciale pour tout praticien.

Au-delà de la méthodologie, cette série couvre des **applications réelles** qui utilisent la programmation probabiliste en production : TrueSkill (Xbox Live, 100M+ joueurs), Item Response Theory (GMAT/GRE, millions de candidats), LDA (Google News, classement de documents), et les reseaux bayesiens pour le diagnostic medical. Chaque modèle est une brique construite sur les precedentes, formant un edifice coherent.

## Qu'est-ce que la programmation probabiliste ?

| Aspect | ML classique (deterministe) | Programmation probabiliste |
|--------|---------------------------|--------------------------|
| **Sortie** | Un seul resultat (ex: 0.73) | Une distribution complete (ex: N(0.73, 0.12)) |
| **Incertaince** | Non quantifiee | Integree nativement (intervalles de credibilite) |
| **Donnees manquantes** | Problématique | Naturelles (variables latentes) |
| **Combinaison de sources** | Requiert ingenierie manuelle | Probabilites conditionnelles structurees |
| **Decisions** | Basées sur un point | Basées sur E[U] (utilite esperee) |

## Objectifs d'apprentissage

À l'issue de cette série, vous serez capable de :

1. **Construire** un modèle probabiliste en Infer.NET ou PyMC (definition, inference, validation)
2. **Interpreter** les distributions posterieures (moyenne, variance, intervalles de credibilite)
3. **Comparer** message passing vs MCMC sur le même modèle
4. **Decaler** d'un problème real vers sa formulation probabiliste (variables, facteurs, observations)
5. **Integrer** inference probabiliste et théorie de la décision (maximisation d'utilite esperee)

## Parcours d'apprentissage

### Phase 1 : Fondations (Notebooks 1-3, ~2h)

Le parcours commence par le notebook 1 (Setup) qui installe Infer.NET et construit le premier modèle bayesien — le classique "Two Coins" — en quelques lignes de C#. Le notebook 2 (Gaussian Mixtures) plonge dans les distributions continues avec les melanges gaussiens, outil fondamental du clustering. Le notebook 3 (Factor Graphs) introduit la representation graphique qui unifie tous les modèles : les graphs de facteurs, illustres par le problème de Monty Hall. À l'issue de cette phase, vous comprenez comment exprimer un problème incertain en termes de variables, de facteurs et de messages.

### Phase 2 : Modèles classiques (Notebooks 4-13, ~8h)

Les notebooks 4 a 13 construisent des modèles de complexité croissante, chacun illustre par une application concrete : reseaux bayesiens (diagnostic medical), Item Response Theory (evaluation de compétences), TrueSkill (classement Xbox Live), classification bayésienne, sélection de modèles (Bayes Factors), LDA (topic modeling), crowdsourcing (agregation de labels), HMM (sequences temporelles), systemes de recommandation, et debugging. Chaque notebook est autonome mais presuppose la maitrise des concepts des notebooks 1-3. Le notebook 13 (Debugging) est une référence pratique a consulter tout au long du parcours.

### Phase 3 : Decision bayésienne (Notebooks 14-20, ~7h)

La seconde moitie de la série passe de l'inference a la décision : comment choisir une action quand on ne connait que des probabilités ? Les notebooks 14-16 posent les fondations (axiomes de l'utilite, fonctions d'utilite mono- et multi-attributs). Les notebooks 17-20 appliquent ces concepts aux reseaux de décision, a la valeur de l'information parfaite et d'echantillon, aux systemes experts robustes, et aux processus decisionnels de Markov (MDPs) — qui relient cette série a la série [RL](../RL/). Le compagnon Infer-20b (kernel Lean 4 via WSL) clot la phase en formalisant les identites d'escompte geometrique de l'indice de Gittins dans le projet Lake [`decision_theory_lean`](decision_theory_lean/) — place a la **racine de la serie** pour etre visible des deux pistes (Infer.NET / PyMC) ; le theoreme d'optimalite y est enonce, sa preuve complete exigeant une formalisation des MDP qui manque encore a Mathlib.

### Parcours alternatives

#### Parcours inference comparee (Infer.NET vs PyMC, ~15h)

Suivez le même modèle dans les deux stacks pour comparer les approches :

| Concept | Infer.NET | PyMC | Différence principale |
|---------|-----------|------|----------------------|
| Fondations | Infer-1 → 2 → 3 | PyMC-1 → 2 → 3 | EP/VMP (exact) vs NUTS (MCMC) |
| Reseaux bayesiens | Infer-4 | PyMC-4 | Compilation statique vs echantillonnage dynamique |
| IRT (compétences) | Infer-5 | PyMC-5 | Variable.If vs pm.Bernoulli |
| TrueSkill | Infer-6 | PyMC-6 | Message passing exact vs MCMC approximatif |
| Classification | Infer-7 | PyMC-7 | Bayes Point Machine vs regression logistique |
| Model sélection | Infer-8 | PyMC-8 | Bayes Factors vs LOO/Pareto-SMI |
| Topic modeling | Infer-9 | PyMC-9 | VMP vs NUTS sur variables latentes |
| Debugging | Infer-13 | PyMC-13 | ShowFactorGraph vs trace plot diagnostics |

#### Parcours applications (modèles concrets, ~6h)

Si vous préférez commencer par les cas d'usage, suivez cet ordre :

1. **TrueSkill** (Infer-6 / PyMC-6) : classement bayesien, application Xbox Live
2. **IRT** (Infer-5 / PyMC-5) : evaluation de compétences, application GMAT
3. **Crowdsourcing** (Infer-10 / PyMC-10) : aggregation de labels, application Mechanical Turk
4. **Recommenders** (Infer-12 / PyMC-12) : factorisation matricielle bayésienne
5. **LDA** (Infer-9 / PyMC-9) : discovery de themes dans des corpus textuels
6. **HMM** (Infer-11 / PyMC-11) : regimes caches en finance et traitement du signal

#### Parcours décision (théorie de la décision, ~7h)

Pour les étudiants en recherche operationnelle ou finance :

1. **Foundations** (14) : axiomes VNM, loteries, theoreme de representation
2. **Money & risk** (15) : CARA, CRRA, paradoxe Saint-Petersbourg
3. **Multi-attribute** (16) : MAUT, SMART, decidons avec plusieurs criteres
4. **Networks** (17) : diagrammes d'influence, politiques optimales
5. **Value of information** (18) : EVPI, EVSI — quand un test est-il rentable ?
6. **Expert systems** (19) : Minimax, Minimax Regret, robustesse
7. **Sequential** (20) : MDPs, bandits, POMDPs — passerelle vers le RL
8. **Gittins en Lean** (20b) : identites d'escompte demontrees, theoreme d'optimalite enonce — pont vers [SymbolicAI/Lean](../SymbolicAI/Lean/README.md)

#### Parcours rapide Python (standalone, ~2h)

Si vous préférez Python au C#, commencez par Infer-101.ipynb (introduction standalone avec modèles Two Coins et Cyclist) puis Pyro_RSA_Hyperbole.ipynb (application a la linguistique pragmatique avec le framework RSA).

#### Parcours PyMC complet (20 notebooks, ~14h)

Les notebooks PyMC dans `PyMC/` reprennent l'intégralité des 20 modèles Infer.NET en Python avec PyMC et l'echantillonnage NUTS : fondations (1-3), modèles classiques (4-13), et théorie de la décision (14-20). Ils constituent un excellent complement pour comparer les approches d'inference (message passing vs MCMC) et rejoindre l'ecosysteme Python data science. La progression suit la même structure pédagogique en 3 phases que la série Infer.NET.

## Quel stack choisir ?

### Si vous venez du C# / .NET

**Commencez par Infer.NET.** L'API est native C# (`Variable.GaussianFromMeanAndVariance`), le compilateur Roslyn integre au .NET Interactive gere la compilation dynamique, et la visualisation des graphes de facteurs via FactorGraphHelper offre une compréhension intuitive de la structure du modèle. C'est le choix ideal pour comprendre l'inference exacte et le message passing.

**Passez a PyMC quand :** vous avez un modèle trop complexe pour Infer.NET (variables latentes discretes a grande taille), ou vous voulez integrer le modèle dans un pipeline Python (pandas, scikit-learn, visualisation).

### Si vous venez du Python / data science

**Commencez par PyMC.** La syntaxe `with pm.Model(): ...` est plus familiere aux data scientists, l'echantillonnage NUTS gere automatiquement les geometries complexes du posterior, et l'ecosysteme (arviz, pandas, matplotlib) est naturel.

**Passez a Infer.NET quand :** vous voulez comprendre l'inference exacte (VMP/EP) qui donne des results deterministes et rapides, ou vous etes dans un environnement .NET. La visualisation du factor graph (FactorGraphHelper) est aussi un outil pédagogique unique pour comprendre les dépendances du modèle.

### Si vous ne savez pas quoi choisir

| Critere | Recommandation |
|---------|---------------|
| Juste découvrir la programmation probabiliste | **Infer-101.ipynb** (standalone, 45 min) |
| Comprendre les graphes de facteurs | **Infer-3** (Monty Hall, Murder Mystery) |
| Un premier modèle qui marche | **Infer-101** ou **PyMC-1-Setup** |
| Application concrete rapide | **Infer-6 TrueSkill** ou **Infer-9 LDA** |
| Comparer les deux approches | Suivre la table "inference comparee" ci-dessus |
| Production data science | **PyMC** (ecosysteme Python, NUTS, arviz) |
| Apprentissage embarque / temps réel | **Infer.NET** (compilation statique = inference rapide) |

## Structure

```
Probas/
├── Infer-101.ipynb              # Introduction Python/C# (standalone)
├── Pyro_RSA_Hyperbole.ipynb     # Pragmatique linguistique (Python)
├── PyMC/                # Port PyMC complet des modeles Infer.NET (20 notebooks)
│   ├── PyMC-1-Setup.ipynb ... PyMC-20-Decision-Sequential.ipynb
│   └── (port en cours d'enrichissement)
├── decision_theory_lean/        # Projet Lake (racine serie) : escompte geometrique + theoreme de Gittins ; accueillera VNM (#4049) + Dutch Book (#4050)
└── Infer/                       # Serie complete Infer.NET (21 notebooks)
    ├── Infer-1-Setup.ipynb ... Infer-20-Decision-Sequential.ipynb
    ├── Infer-20b-Lean-Gittins.ipynb   # Compagnon Lean 4 (kernel WSL, -> ../decision_theory_lean)
    ├── README.md                # Documentation detaillee de la serie
    └── scripts/
```

## Ce que chaque notebook apporte

Chaque notebook introduit un concept ou modèle spécifique. Le tableau ci-dessous resume en une ligne l'apport pédagogique de chacun — au-delà du titre, c'est le **concept clé** qu'il enseigne.

### Série Infer.NET

| # | Notebook | Apport pédagogique |
|---|----------|-------------------|
| 1 | Setup | Boucle fondamentale : definition du modèle → creation du moteur → inference |
| 2 | Gaussian Mixtures | Distributions continues, melanges gaussiens, estimation de params |
| 3 | Factor Graphs | Monty Hall + Murder Mystery : inference discrete, Variable.If/Case |
| 4 | Bayesian Networks | Wet Grass, CPT, D-separation, explaining away, inference causale |
| 5 | Skills (IRT) | Modélisation de compétences (DINA), evaluation adaptive |
| 6 | TrueSkill | Ranking bayesien, online learning, rating conservatif (mu - 3*sigma) |
| 7 | Classification | Bayes Point Machine, classification probit, tests A/B bayesiens |
| 8 | Model Sélection | Bayes Factors, evidence marginale, ARD (Automatic Relevance Determination) |
| 9 | Topic Models | LDA, Dirichlet, prior asymetrique pour briser la symetrie VMP |
| 10 | Crowdsourcing | Worker models, communautes d'annotateurs, aggregation de labels |
| 11 | Sequences | HMM, detection de regimes, forward-backward, motifs temporels |
| 12 | Recommenders | Factorisation matricielle bayésienne, Click Model |
| 13 | Debugging | EP vs VMP, diagnostic de divergence, ShowFactorGraph, ShowSchedule |
| 14 | Decision Foundations | Axiomes VNM, loteries, theoreme de representation, calibration U |
| 15 | Decision Utility-Money | CARA, CRRA, aversion au risque, paradoxe Saint-Petersbourg |
| 16 | Decision Multi-Attribute | MAUT, SMART, swing weights, decisions multi-criteres |
| 17 | Decision Networks | Diagrammes d'influence, politique optimale, inference + décision |
| 18 | Decision Value-Info | EVPI, EVSI, valeur de l'information, when-to-test |
| 19 | Decision Expert-Systems | Minimax, Minimax Regret, robustesse face a l'incertitude |
| 20 | Decision Sequential | MDPs, itération valeur/politique, bandits, POMDPs |
| 20b | Lean Gittins | Formalisation Lean 4 : identites d'escompte prouvees, optimalite de Gittins enoncee |

### Série PyMC

| # | Notebook | Apport pédagogique |
|---|----------|-------------------|
| 1 | Setup | Boucle PyMC : pm.Model() → pm.sample(NUTS) → arviz |
| 2 | Gaussian Mixtures | Melanges gaussiens MCMC, trace plots, convergence diagnostics |
| 3 | Factor Graphs | Inference discrete avec PyMC, comparaison Infer.NET vs PyMC |
| 4 | Bayesian Networks | Reseaux bayesiens MCMC, CPT, explaining away |
| 5 | Skills (IRT) | IRT en Python, estimation de compétences par MCMC |
| 6 | TrueSkill | TrueSkill avec NUTS, online learning bayesien |
| 7 | Classification | Classification bayésienne, regression logistique |
| 8 | Model Sélection | Model comparison MCMC, LOO, WAIC, Bayes Factors empiriques |
| 9 | Topic Models | LDA avec NUTS, gestion variables latentes, inference approximation |
| 10 | Crowdsourcing | Agregation de labels crowdsourcing, worker communities |
| 11 | Sequences | HMM MCMC, forward-backward avec echantillonnage |
| 12 | Recommenders | Factorisation matricielle bayésienne MCMC |
| 13 | Debugging | Trace plots, R-hat, effective sample size, bonnes pratiques MCMC |
| 14 | Decision Foundations | Axiomes VNM en PyMC, loteries, décision bayésienne |
| 15 | Decision Utility-Money | CARA/CRRA en PyMC, calibration utilite, aversion au risque |
| 16 | Decision Multi-Attribute | MAUT avec PyMC, multi-criteria décision making |
| 17 | Decision Networks | Reseaux de décision MCMC, politiques optimales |
| 18 | Decision Value-Info | EVPI/EVSI en PyMC, valeur informationnelle |
| 19 | Decision Expert-Systems | Minimax/Minimax Regret robuste avec PyMC |
| 20 | Decision Sequential | MDPs MCMC, bandits, POMDPs |

## Notebooks racine (Python)

| Notebook | Kernel | Contenu | Durée |
|----------|--------|---------|-------|
| [Infer-101](Infer-101.ipynb) | Python + C# | Introduction Infer.NET, Two Coins, Cyclist | 45 min |
| [Pyro_RSA_Hyperbole](Pyro_RSA_Hyperbole.ipynb) | Python | Rational Speech Acts, hyperboles | 60 min |

### Infer-101.ipynb

Point d'entree accessible pour la programmation probabiliste :
- Concepts de base (variables aleatoires, modèles probabilistes)
- Premier modèle Infer.NET (Two Coins)
- Exemple du cycliste (priors Gaussiens)
- Apprentissage en ligne et comparaison de modèles

### Pyro_RSA_Hyperbole.ipynb

Application avancée a la linguistique pragmatique :
- Framework RSA (Rational Speech Acts)
- Implicatures scalaires (none/some/all)
- Modélisation des hyperboles (prix, excitation)
- Question Under Discussion (QUD)

## Série Infer.NET (21 notebooks)

La série complete est documentee dans [Infer/README.md](Infer/README.md), qui fournit des descriptions detaillees de chaque notebook, les patterns Infer.NET avancés, et des exercices corriges.

### Progression en 3 parties

| Partie | Notebooks | Focus | Durée |
|--------|-----------|-------|-------|
| **Fondations** | 1-3 | Setup, distributions, factor graphs | 2h |
| **Modèles classiques** | 4-13 | Bayesian networks, IRT, TrueSkill, LDA, HMM | 8h |
| **Decision** | 14-20, 20b | Theorie de la décision bayésienne + preuve Lean de Gittins | 8h |

Les 21 notebooks Infer.NET sont détaillés individuellement dans [*Ce que chaque notebook apporte*](#ce-que-chaque-notebook-apporte) ci-dessus (apport pédagogique par notebook) ; le contenu exhaustif — patterns avancés, exercices corrigés — vit dans [Infer/README.md](Infer/README.md).

## Série PyMC (20 notebooks, Python)

Port Python complet des modèles Infer.NET, utilisant l'echantillonnage MCMC (NUTS) au lieu du message passing. Permet de comparer les deux approches d'inference sur des modèles identiques. La progression suit les mêmes trois phases que la série Infer.NET : fondations (1-3), modèles classiques (4-13), et théorie de la décision (14-20).

### Phase 1 — Fondations (notebooks 1-3, ~2h)

| # | Notebook | Sujet |
|---|----------|-------|
| 1 | [PyMC-1-Setup](PyMC/PyMC-1-Setup.ipynb) | Configuration PyMC, modèle Beta-Bernoulli |
| 2 | [PyMC-2-Gaussian-Mixtures](PyMC/PyMC-2-Gaussian-Mixtures.ipynb) | Distributions continues, melanges gaussiens |
| 3 | [PyMC-3-Factor-Graphs](PyMC/PyMC-3-Factor-Graphs.ipynb) | Graphes de facteurs, inference discrete |

### Phase 2 — Modèles classiques (notebooks 4-13, ~9h)

| # | Notebook | Sujet |
|---|----------|-------|
| 4 | [PyMC-4-Bayesian-Networks](PyMC/PyMC-4-Bayesian-Networks.ipynb) | Reseaux bayesiens, CPTs |
| 5 | [PyMC-5-Skills-IRT](PyMC/PyMC-5-Skills-IRT.ipynb) | Item Response Theory, modèles de compétences |
| 6 | [PyMC-6-TrueSkill](PyMC/PyMC-6-TrueSkill.ipynb) | Classement, TrueSkill |
| 7 | [PyMC-7-Classification](PyMC/PyMC-7-Classification.ipynb) | Classification bayésienne |
| 8 | [PyMC-8-Model-Sélection](PyMC/PyMC-8-Model-Selection.ipynb) | Sélection de modèles, Bayes Factors |
| 9 | [PyMC-9-Topic-Models](PyMC/PyMC-9-Topic-Models.ipynb) | LDA, Dirichlet priors |
| 10 | [PyMC-10-Crowdsourcing](PyMC/PyMC-10-Crowdsourcing.ipynb) | Agregation de labels, workers, communautes |
| 11 | [PyMC-11-Sequences](PyMC/PyMC-11-Sequences.ipynb) | HMM, chaines de Markov cachees, sequences temporelles |
| 12 | [PyMC-12-Recommenders](PyMC/PyMC-12-Recommenders.ipynb) | Systemes de recommandation bayesiens, factorisation |
| 13 | [PyMC-13-Debugging](PyMC/PyMC-13-Debugging.ipynb) | Troubleshooting MCMC, diagnostics NUTS, bonnes pratiques |

### Phase 3 — Theorie de la décision (notebooks 14-20, ~6h)

| # | Notebook | Sujet |
|---|----------|-------|
| 14 | [PyMC-14-Decision-Utility-Foundations](PyMC/PyMC-14-Decision-Utility-Foundations.ipynb) | Loteries, axiomes Von Neumann-Morgenstern, utilite esperee |
| 15 | [PyMC-15-Decision-Utility-Money](PyMC/PyMC-15-Decision-Utility-Money.ipynb) | Aversion au risque, CARA, CRRA, paradoxe Saint-Petersbourg |
| 16 | [PyMC-16-Decision-Multi-Attribute](PyMC/PyMC-16-Decision-Multi-Attribute.ipynb) | MAUT, SMART, swing weights, decisions multi-criteres |
| 17 | [PyMC-17-Decision-Networks](PyMC/PyMC-17-Decision-Networks.ipynb) | Reseaux de décision, diagrammes d'influence, politique optimale |
| 18 | [PyMC-18-Decision-Value-Information](PyMC/PyMC-18-Decision-Value-Information.ipynb) | EVPI, EVSI, valeur de l'information parfaite et d'echantillon |
| 19 | [PyMC-19-Decision-Expert-Systems](PyMC/PyMC-19-Decision-Expert-Systems.ipynb) | Systemes experts, Minimax, Minimax Regret, decisions robustes |
| 20 | [PyMC-20-Decision-Sequential](PyMC/PyMC-20-Decision-Sequential.ipynb) | MDPs, itération de valeur/politique, bandits, POMDPs |

## Applications standalone (2 notebooks)

| Notebook | Kernel | Contenu | Durée |
| -------- | ------- | ------- | ----- |
| [Infer-101](Infer-101.ipynb) | .NET (C#) + Python | Introduction Infer.NET, Two Coins, Cyclist | 1h |
| [Pyro_RSA_Hyperbole](Pyro_RSA_Hyperbole.ipynb) | Python 3 | Rational Speech Acts, hyperboles | 30 min |

## Prerequisites

### Niveau mathematique attendu

Cette série suppose une **maîtrise de base en probabilités et statistiques** :

| Concept | Utilite dans la série | Notes de revision |
|---------|---------------------|------------------|
| Variables aleatoires (discretes/continues) | Partout, notebook 1+ | Loi de proba, espérance, variance |
| Distributions usuelles (Bernoulli, Gaussian, Beta, Gamma) | Notebook 1 (Beta-Bernoulli), 2 (Gaussian) | Parametres, formes, conjugaison |
| Probabilites conditionnelles | Notebook 3+ (Variable.If, CPT) | P(A|B), theoreme de Bayes |
| Independance conditionnelle | Notebook 3 (Monty Hall), 4 (D-separation) | Collider, explaining away |
| Esperance mathematique | Partout (calcul de EU) | E[X] = sum x*P(x) ou integral |
| Distributions conjuguees | Notebook 1 (Beta-Bernoulli), 9 (Dirichlet-Discrete) | Prior + likelihood = posterior (famille même) |
| Integrals (niveau 1) | Notebook 2, 15 (CARA/CRRA) | Calcul d'esperance avec fonctions non-linéaires |

**Inutile de maitriser** : derivation multivariee, algèbre linéaire avancée (sauf pour les modèles hierarchiques en notebook 4). Les concepts sont introduits progressivement et reexpliques dans le contexte.

### Prerequisites techniques

#### Pour Infer.NET (C#)

```bash
# .NET SDK 9.0+
dotnet --version

# VS Code + extension Polyglot Notebooks
# Packages (auto-references dans notebooks):
# - Microsoft.ML.Probabilistic
# - CompilerChoice = Roslyn
```

#### Pour Python

```bash
# Environnement Python 3.8+
pip install pyro-ppl torch matplotlib numpy
```

## Concepts clés

| Concept | Description |
|---------|-------------|
| **Inference bayésienne** | Mise a jour de croyances avec des observations |
| **Prior / Posterior** | Distribution avant/après observations |
| **Factor Graph** | Representation graphique de distributions jointes |
| **Message Passing** | Algorithmes EP (Expectation Propagation), VMP |
| **MCMC / NUTS** | Echantillonnage pour modèles complexes (PyMC) |
| **D-separation** | Critere graphique d'independance conditionnelle |
| **Explaining Away** | Causes alternatives deviennent moins probables |
| **Decision Theory** | Maximisation d'utilite esperee |
| **Valeur de l'information** | EVPI, EVSI — coût d'un test complementaire |

## Domaines d'application

| Domaine | Notebooks |
|---------|-----------|
| Jeux video | 6 (TrueSkill) |
| Education | 5 (IRT), 14 |
| NLP | 9 (LDA) |
| Medecine | 4, 7, 17-19 |
| Finance | 11, 15, 20 |
| E-commerce | 12 |

### Exemples concrets

Derriere chaque modèle de la série se cache un systeme réel déjà en production :

- **TrueSkill** (notebook 6) est l'algorithme que Microsoft utilise pour apparier des millions de joueurs sur Xbox Live : il maintient pour chaque joueur une compétence *gaussienne* (moyenne + incertitude) mise a jour après chaque partie, generalisant l'Elo des echecs aux jeux en equipe.
- **Item Response Theory** (notebook 5) est le moteur des tests adaptatifs comme le GMAT ou le GRE : la difficulte de chaque question est calibree probabilistiquement, et le test s'ajuste en temps réel au niveau estime du candidat.
- **Les reseaux bayesiens** (notebooks 4, 7) fondent les systemes d'aide au diagnostic medical (de QMR-DT aux outils modernes) et le filtrage anti-spam : ils propagent l'incertitude entre symptomes, causes et observations.
- **LDA / topic models** (notebook 9) structurent automatiquement de grands corpus — decouverte de thematiques dans des archives de presse, cartographie de la litterature scientifique, analyse de tickets support.
- **Les HMM** (notebook 11) detectent les regimes caches : phases de marche en finance, reconnaissance de la parole, segmentation de sequences biologiques.
- **Les systemes de recommandation bayesiens** (notebook 12) sont la version « avec barre d'incertitude » du collaborative filtering de Netflix ou Amazon — utile pour decider quand explorer un nouvel item plutôt que d'exploiter une preference connue.
- **Le crowdsourcing** (notebook 10) modelise la fiabilite de chaque annotateur (Mechanical Turk, labellisation de datasets) pour reconstruire la verite terrain malgre des votes bruites.
- **La théorie de la décision et les MDPs** (notebooks 14-20) relient la série au controle sequentiel : gestion de stocks, maintenance predictive, et passerelle directe vers le [reinforcement learning](../RL/).

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

## FAQ / Troubleshooting

### Le kernel .NET Interactive n'apparait pas dans Jupyter

- Vérifiez que `dotnet interactive jupyter install` a reussi (sortie : `Kernel installed`).
- Redemarrez Jupyter. Si le kernel persiste a ne pas apparaitre, verifiez que .NET SDK 9.0+ est installe : `dotnet --version`.
- Sur Windows, les notebooks Infer.NET doivent être ouverts avec l'extension **Polyglot Notebooks** dans VS Code ou jupyterlab.

### `CompilerChoice.Roslyn` obligatoire

Tous les notebooks Infer.NET utilisent `moteur.Compiler.CompilerChoice = CompilerChoice.Roslyn`. C'est **obligatoire** dans .NET Interactive car Infer.NET compile dynamiquement le modèle en code C#. Sans Roslyn, la compilation echoue. Ce pattern est presente dans **chaque** notebook de la série (section 1 "Configuration").

### PyMC ne s'installe pas sur Windows (compilateur C manque)

PyMC nécessite un compilateur C pour certaines dépendances. Sur Windows :
- Installez **Microsoft Visual C++ Build Tools** (la version "Build Tools" suffit, pas besoin de Visual Studio complet).
- Ou utilisez un **environnement conda** : `conda install -c conda-forge pymc`.
- Ou utilisez un **conteneur Docker** avec une image preconfiguree.

### Erreur Graphviz / FactorGraphHelper

La visualisation des factor graphs nécessite **Graphviz installe**. Si `dot` n'est pas trouve :
- Les fichiers `.gv` sont sauvegardes dans le repertoire courant.
- Vous pouvez les visualiser sur [viz-js.com](https://viz-js.com/) ou [edotor.net](https://edotor.net/).
- Installation Graphviz Windows : telecharger depuis https://graphviz.org/download/, puis ajouter `C:\Program Files\Graphviz\bin` au PATH.

### Switcher entre kernels C# et Python dans un même notebook

Le notebook `Infer-101.ipynb` est le seul a melanger les deux kernels. Il utilise le mode **polyglot** de .NET Interactive, ou chaque cellule specifie son kernel via le tag `#kernel name`. Pour la série standard, chaque sous-série (Infer/ ou PyMC/) utilise un seul kernel.

### PyMC : echantillonnage tres lent ou divergence NUTS

- Augmentez `target_energy` et `adapt_delta` (défaut 0.8 → essai 0.95).
- Vérifiez le `R-hat` (devrait être < 1.01 pour toutes les variables).
- Consultez [PyMC-13-Debugging](PyMC/PyMC-13-Debugging.ipynb) pour des diagnostics detaillés (trace plots, effective sample size, tree depth).

## Ressources

### Infer.NET

- [Infer.NET Documentation](https://dotnet.github.io/infer/)
- [MBML Book (Model-Based Machine Learning)](https://mbmlbook.com/)
- [Infer.NET GitHub](https://github.com/dotnet/infer)

### PyMC

- [PyMC Documentation](https://www.pymc.io/)
- [PyMC Examples](https://www.pymc.io/projects/examples/en/latest/)
- [arviz — Visualization et diagnostics MCMC](https://python.arviz.org/)

### Theorie

- Bishop, C. (2006) - *Pattern Recognition and Machine Learning*
- Koller & Friedman (2009) - *Probabilistic Graphical Models*
- Von Neumann & Morgenstern (1944) - *Theory of Games and Economic Behavior*
- Russell & Norvig - *Artificial Intelligence*, Chapter 16 (Decision Theory)

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette série vous a fait changer de regard sur l'incertitude : plutôt que de la fuir ou de l'ignorer, vous avez appris à la **modéliser, la quantifier et la traduire en décisions**. L'arc pédagogique se déploie en trois temps, porté par trois stacks complémentaires :

- **Le geste fondateur** — remplacer une prédiction ponctuelle par une **distribution**. Un modèle probabiliste ne dit pas « la probabilité est 0.73 » mais « voici la distribution complète N(0.73, 0.12) », et cette densité porte l'information que la moyenne dissimule : la confiance, les queues, les modes multiples. C'est ce déplacement qui ouvre tout le reste.
- **La double inference** — Infer.NET (message passing, EP/VMP) et PyMC (NUTS, MCMC) résolvent les mêmes modèles par des voies opposées. Le traverser sur des modèles jumeaux (notebook à notebook, Infer-N ↔ PyMC-N) ancre une intuition qu'aucun cours théorique ne donne : **quand l'inférence exacte est tractable, elle est déterministe et rapide ; quand elle ne l'est plus, l'échantillonnage prend le relais mais exige des diagnostics** (R-hat, effective sample size, trace plots).
- **La décision** — la seconde moitié franchit le pas : des croyances (distributions) aux **actions**. Utilité espérée E[U], valeur de l'information (EVPI/EVSI), réseaux de décision, et enfin les MDP qui relient cette série à l'apprentissage par renforcement. Le compagnon Lean 4 (Infer-20b) pousse l'exigence jusqu'à **formaliser** les identités d'escompte de l'indice de Gittins — l'assurance que les identités numériques ne sont pas des approximations accidentelles mais des théorèmes.

La thèse pratique est honnête : un modèle probabiliste est plus lourd à bâtir qu'un classifieur, mais il est le seul à pouvoir dire « je ne sais pas » — et dans le diagnostic médical, le classement sportif ou l'évaluation de compétences, cette honnêteté est précisément ce qu'on cherche.

### Prochaines étapes

- **Passer à la décision séquentielle** : les MDP des notebooks 17-20 préparent directement [RL](../RL/README.md), où l'agent **apprend** la politique optimale par interaction plutôt que de la calculer hors ligne — la frontière naturelle entre inférence probabiliste et apprentissage par renforcement.
- **Croiser la théorie des jeux** : [GameTheory](../GameTheory/README.md) partage la notion de **décision sous incertitude**, mais l'incertitude y vient d'un adversaire rationnel plutôt que d'un processus stochastique. Les fonctions d'utilité multi-attributs (notebooks 15-16) trouvent leur miroir dans le choix social et l'utilité collective.
- **Revenir au ML appliqué** : le [TP prévision de ventes](../ML/ML.Net/TP-prevision-ventes.ipynb) de la série ML est une porte d'entrée — il traite la régression bayésienne comme cas d'application ; cette série en donne le langage complet (distributions, facteurs, inférence).
- Pour la pratique : reprenez un même modèle (par exemple TrueSkill, Infer-6 / PyMC-6) dans les deux stacks, comparez les intervalles de crédibilité, et observez comment EP (déterministe) et NUTS (stochastique) convergent vers des conclusions cohérentes — c'est l'exercice le plus formateur pour saisir le champ d'application de chaque approche.

### Le fil rouge

La programmation probabiliste propose un changement de posture : ne plus demander « quelle est la bonne réponse ? » mais **« à quel point suis-je sûr de cette réponse, et que dois-je faire compte tenu de cette incertitude ? »**. Cette série vous a donné les trois couches — modéliser (facteurs, distributions), inférer (message passing ou échantillonnage), décider (utilité espérée, valeur de l'information) — pour transformer une question qualitative en un calcul, en gardant à l'esprit qu'une distribution honnête vaut mieux qu'une certitude illusoire.

## Licence

Voir la licence du repository principal.

---

*Version 1.1.0 — Juin 2026*
