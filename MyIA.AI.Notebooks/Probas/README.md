# Probas - Programmation Probabiliste

<!-- CATALOG-STATUS
series: Probas
pedagogical_count: 44
breakdown: Infer=22, PyMC=20, root=2
maturity: PRODUCTION=43, BETA=1
-->

[← Notebooks](../README.md) | [Série Infer (C#) →](Infer/README.md) | [Série PyMC (Python) →](PyMC/README.md) | [GameTheory →](../GameTheory/README.md)

Le monde réel est incertain. Un diagnostic médical n'est jamais sur a 100%, un classement sportif dépend de performances intrinsèquement variables, et les données que nous collectons sont toujours bruitées ou incomplètes. La programmation probabiliste offre un cadre rigoureux pour modéliser cette incertitude : plutôt que de calculer une seule réponse, on obtient une **distribution de probabilités** qui quantifie notre confiance dans chaque résultat possible.

Cette série couvre trois stack complémentaires : **Infer.NET** (Microsoft, C#/.NET Interactive) pour l'inférence exacte par message passing, **PyMC** (Python) pour l'échantillonnage MCMC moderne, et des **applications standalone** (RSA). Les 21 notebooks Infer.NET couvrent les fondements mathématiques (distributions, graphs de facteurs), les modèles classiques (réseaux bayésiens, TrueSkill, LDA, HMM), puis la théorie de la décision bayésienne — jusqu'a un compagnon **Lean 4** (Infer-20b, adossé au projet Lake `gittins_lean`) qui démontre formellement les identités d'escompte de l'indice de Gittins. Les 20 notebooks PyMC reprennent l'intégralité des modèles Infer.NET en Python avec l'échantillonnage NUTS, offrant un pont naturel vers l'écosystème data science : fondations 1-3, modèles classiques 4-13, et théorie de la décision 14-20.

## Pourquoi cette série

La programmation probabiliste occupe une place singuliere dans la paysage de l'IA. Alors que le machine learning classique fournit des predictions ponctuelles (un score, une classe), il ne dit pas a quel point il a confiance en cette prediction. La programmation probabiliste, elle, quantifie cette incertitude de facon native.

Cette série repose sur une **double approche d'inférence**, deliberatement juxtaposée :

- **Inférence exacte par message passing** (Infer.NET) : pour les modèles où les distributions postérieures peuvent être calculées exactement (ou approchées par EP/VMP). C'est la méthode des graphes de facteurs, ou les probalilites se propagent le long des arêtes comme des messages. Avantage : résultats déterministes, rapide, visualisation du graphe de facteurs. Limite : ne s'applique qu'a une famille restreinte de modèles.
- **Inférence approchée par échantillonnage MCMC** (PyMC) : pour les modèles plus génériques ou l'inférence exacte est intractable. NUTS (No-U-Turn Sampler) explore l'espace posterior en simulant une dynamique hamiltonienne. Avantage : s'applique a presque tout modèle. Limite : results stochastiques, temps de convergence variable, diagnostic nécessaire.

Avoir les deux approches sur les mêmes modèles permet de comprendre leur **champ d'application** et leurs **compromis**, une connaissance cruciale pour tout praticien.

Au-delà de la méthodologie, cette série couvre des **applications réelles** qui utilisent la programmation probabiliste en production : TrueSkill (Xbox Live, 100M+ joueurs), Item Response Theory (GMAT/GRE, millions de candidats), LDA (Google News, classement de documents), et les réseaux bayésiens pour le diagnostic médical. Chaque modèle est une brique construite sur les précédentes, formant un édifice cohérent.

## Qu'est-ce que la programmation probabiliste ?

| Aspect | ML classique (déterministe) | Programmation probabiliste |
|--------|---------------------------|--------------------------|
| **Sortie** | Un seul résultat (ex: 0.73) | Une distribution complète (ex: N(0.73, 0.12)) |
| **Incertaince** | Non quantifiée | Intégrée nativement (intervalles de crédibilité) |
| **Données manquantes** | Problématique | Naturelles (variables latentes) |
| **Combinaison de sources** | Requiert ingénierie manuelle | Probabilités conditionnelles structurées |
| **Décisions** | Basées sur un point | Basées sur E[U] (utilité espérée) |

```mermaid
flowchart LR
    D["Données<br/>(observations)"] --> ML["ML classique<br/>(déterministe)"]
    D --> PP["Programmation<br/>probabiliste"]
    ML --> P1["Un seul résultat<br/>ex: 0.73"]
    PP --> P2["Une distribution<br/>ex: N(0.73, 0.12)"]
    P1 --> U1["Incertitude<br/>non quantifiée"]
    P2 --> U2["Incertitude<br/>native<br/>(intervalles de crédibilité)"]
    U2 --> DEC["Décision basée sur<br/>E[U] (utilité espérée)"]
    classDef dist fill:#d1ecf1,stroke:#0c5460,stroke-width:2px;
    class P2,U2,DEC dist;
```

La différence fondatrice : le ML classique produit un **point**, la programmation probabiliste produit une **distribution** (en bleu). Cette incertitude native se propage jusqu'à la décision — on maximise l'utilité espérée `E[U]`, pas un seul score.

## Objectifs d'apprentissage

À l'issue de cette série, vous serez capable de :

1. **Construire** un modèle probabiliste en Infer.NET ou PyMC (définition, inférence, validation)
2. **Interpréter** les distributions postérieures (moyenne, variance, intervalles de crédibilité)
3. **Comparer** message passing vs MCMC sur le même modèle
4. **Décaler** d'un problème real vers sa formulation probabiliste (variables, facteurs, observations)
5. **Intégrer** inférence probabiliste et théorie de la décision (maximisation d'utilité espérée)

## Parcours d'apprentissage

### Phase 1 : Fondations (Notebooks 1-3, ~2h)

Le parcours commence par le notebook 1 (Setup) qui installe Infer.NET et construit le premier modèle bayésien — le classique "Two Coins" — en quelques lignes de C#. Le notebook 2 (Gaussian Mixtures) plonge dans les distributions continues avec les mélanges gaussiens, outil fondamental du clustering. Le notebook 3 (Factor Graphs) introduit la représentation graphique qui unifie tous les modèles : les graphs de facteurs, illustres par le problème de Monty Hall. À l'issue de cette phase, vous comprenez comment exprimer un problème incertain en termes de variables, de facteurs et de messages.

### Phase 2 : Modèles classiques (Notebooks 4-13, ~8h)

Les notebooks 4 a 13 construisent des modèles de complexité croissante, chacun illustre par une application concrète : réseaux bayésiens (diagnostic médical), Item Response Theory (evaluation de compétences), TrueSkill (classement Xbox Live), classification bayésienne, sélection de modèles (Bayes Factors), LDA (topic modeling), crowdsourcing (agrégation de labels), HMM (séquences temporelles), systèmes de recommandation, et debugging. Chaque notebook est autonome mais présuppose la maîtrise des concepts des notebooks 1-3. Le notebook 13 (Debugging) est une référence pratique a consulter tout au long du parcours.

### Phase 3 : Décision bayésienne (Notebooks 14-20, ~7h)

La seconde moitié de la série passe de l'inférence a la décision : comment choisir une action quand on ne connait que des probabilités ? Les notebooks 14-16 posent les fondations (axiomes de l'utilité, fonctions d'utilité mono- et multi-attributs). Les notebooks 17-20 appliquent ces concepts aux réseaux de décision, a la valeur de l'information parfaite et d'échantillon, aux systèmes experts robustes, et aux processus décisionnels de Markov (MDPs) — qui relient cette série a la série [RL](../RL/). Le compagnon Infer-20b (kernel Lean 4 via WSL) clôt la phase en formalisant les identités d'escompte géométrique de l'indice de Gittins dans le projet Lake [`decision_theory_lean`](decision_theory_lean/) — place a la **racine de la série** pour être visible des deux pistes (Infer.NET / PyMC) ; le théorème d'optimalité y est énoncé, sa preuve complète exigeant une formalisation des MDP qui manque encore a Mathlib.

### Parcours alternatives

#### Parcours inférence comparée (Infer.NET vs PyMC, ~15h)

Suivez le même modèle dans les deux stacks pour comparer les approches :

| Concept | Infer.NET | PyMC | Différence principale |
|---------|-----------|------|----------------------|
| Fondations | Infer-1 → 2 → 3 | PyMC-1 → 2 → 3 | EP/VMP (exact) vs NUTS (MCMC) |
| Réseaux bayésiens | Infer-4 | PyMC-4 | Compilation statique vs échantillonnage dynamique |
| IRT (compétences) | Infer-5 | PyMC-5 | Variable.If vs pm.Bernoulli |
| TrueSkill | Infer-6 | PyMC-6 | Message passing exact vs MCMC approximatif |
| Classification | Infer-7 | PyMC-7 | Bayes Point Machine vs régression logistique |
| Model sélection | Infer-8 | PyMC-8 | Bayes Factors vs LOO/Pareto-SMI |
| Topic modeling | Infer-9 | PyMC-9 | VMP vs NUTS sur variables latentes |
| Debugging | Infer-13 | PyMC-13 | ShowFactorGraph vs trace plot diagnostics |

#### Parcours applications (modèles concrets, ~6h)

Si vous préférez commencer par les cas d'usage, suivez cet ordre :

1. **TrueSkill** (Infer-6 / PyMC-6) : classement bayésien, application Xbox Live
2. **IRT** (Infer-5 / PyMC-5) : evaluation de compétences, application GMAT
3. **Crowdsourcing** (Infer-10 / PyMC-10) : aggregation de labels, application Mechanical Turk
4. **Recommenders** (Infer-12 / PyMC-12) : factorisation matricielle bayésienne
5. **LDA** (Infer-9 / PyMC-9) : discovery de thèmes dans des corpus textuels
6. **HMM** (Infer-11 / PyMC-11) : régimes cachés en finance et traitement du signal

#### Parcours décision (théorie de la décision, ~7h)

Pour les étudiants en recherche opérationnelle ou finance :

1. **Foundations** (14) : axiomes VNM, loteries, théorème de représentation
2. **Money & risk** (15) : CARA, CRRA, paradoxe Saint-Petersbourg
3. **Multi-attribute** (16) : MAUT, SMART, décidons avec plusieurs critères
4. **Networks** (17) : diagrammes d'influence, politiques optimales
5. **Value of information** (18) : EVPI, EVSI — quand un test est-il rentable ?
6. **Expert systems** (19) : Minimax, Minimax Regret, robustesse
7. **Sequential** (20) : MDPs, bandits, POMDPs — passerelle vers le RL
8. **Gittins en Lean** (20b) : identités d'escompte démontrées, théorème d'optimalité énoncé — pont vers [SymbolicAI/Lean](../SymbolicAI/Lean/README.md)

#### Parcours rapide Python (standalone, ~2h)

Si vous préférez Python au C#, commencez par Infer-101.ipynb (introduction standalone avec modèles Two Coins et Cyclist) puis Pyro_RSA_Hyperbole.ipynb (application a la linguistique pragmatique avec le framework RSA).

#### Parcours PyMC complet (20 notebooks, ~14h)

Les notebooks PyMC dans `PyMC/` reprennent l'intégralité des 20 modèles Infer.NET en Python avec PyMC et l'échantillonnage NUTS : fondations (1-3), modèles classiques (4-13), et théorie de la décision (14-20). Ils constituent un excellent complément pour comparer les approches d'inférence (message passing vs MCMC) et rejoindre l'écosystème Python data science. La progression suit la même structure pédagogique en 3 phases que la série Infer.NET.

## Quel stack choisir ?

```mermaid
flowchart TD
    START(["Votre profil ?"])
    START --> Q1{"Vous venez du<br/>C# / .NET ?"}
    START --> Q2{"Vous venez du<br/>Python / data science ?"}
    START --> Q3{"Indécis ?<br/>Découverte rapide"}
    Q1 -->|"oui"| INFER["<b>Infer.NET</b><br/>API C# native · Roslyn ·<br/>factor graphs · inference exacte<br/>(EP/VMP)"]
    Q2 -->|"oui"| PYMC["<b>PyMC</b><br/>with pm.Model() · NUTS ·<br/>écosystème pandas/arviz"]
    Q3 --> IN101["<b>Infer-101</b><br/>(standalone, 45 min)"]
    INFER --> PIVOT1{"Modèle trop complexe<br/>ou pipeline Python ?"}
    PYMC --> PIVOT2{"Besoin d'inference exacte<br/>(VMP/EP) ou .NET ?"}
    PIVOT1 -->|"oui"| PYMC
    PIVOT2 -->|"oui"| INFER
    classDef infer fill:#d4edda,stroke:#28a745,stroke-width:2px;
    classDef pymc fill:#cce5ff,stroke:#004085,stroke-width:2px;
    classDef entry fill:#fff3cd,stroke:#856404,stroke-width:2px;
    class INFER infer;
    class PYMC pymc;
    class IN101 entry;
```

Deux stacks, un même parcours de 20 modèles : **Infer.NET** (C#, message passing, déterministe) et **PyMC** (Python, MCMC, flexible). L'arbre ci-dessus donne le point d'entrée selon votre profil — et le pont de bascule vers l'autre stack quand le modèle ou l'environnement l'exige. Le détail comparatif notebook-par-notebook figure dans le [Parcours inférence comparée](#parcours-inference-comparee-infernet-vs-pymc-15h) ci-dessous.

### Si vous venez du C# / .NET

**Commencez par Infer.NET.** L'API est native C# (`Variable.GaussianFromMeanAndVariance`), le compilateur Roslyn intègre au .NET Interactive gere la compilation dynamique, et la visualisation des graphes de facteurs via FactorGraphHelper offre une compréhension intuitive de la structure du modèle. C'est le choix ideal pour comprendre l'inférence exacte et le message passing.

**Passez a PyMC quand :** vous avez un modèle trop complexe pour Infer.NET (variables latentes discrètes a grande taille), ou vous voulez intégrer le modèle dans un pipeline Python (pandas, scikit-learn, visualisation).

### Si vous venez du Python / data science

**Commencez par PyMC.** La syntaxe `with pm.Model(): ...` est plus familiere aux data scientists, l'échantillonnage NUTS gere automatiquement les géométries complexes du posterior, et l'écosystème (arviz, pandas, matplotlib) est naturel.

**Passez a Infer.NET quand :** vous voulez comprendre l'inférence exacte (VMP/EP) qui donne des results déterministes et rapides, ou vous etes dans un environnement .NET. La visualisation du factor graph (FactorGraphHelper) est aussi un outil pédagogique unique pour comprendre les dépendances du modèle.

### Si vous ne savez pas quoi choisir

| Critère | Recommandation |
|---------|---------------|
| Juste découvrir la programmation probabiliste | **Infer-101.ipynb** (standalone, 45 min) |
| Comprendre les graphes de facteurs | **Infer-3** (Monty Hall, Murder Mystery) |
| Un premier modèle qui marche | **Infer-101** ou **PyMC-1-Setup** |
| Application concrète rapide | **Infer-6 TrueSkill** ou **Infer-9 LDA** |
| Comparer les deux approches | Suivre la table "inférence comparée" ci-dessus |
| Production data science | **PyMC** (écosystème Python, NUTS, arviz) |
| Apprentissage embarque / temps réel | **Infer.NET** (compilation statique = inférence rapide) |

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
| 1 | Setup | Boucle fondamentale : définition du modèle → création du moteur → inférence |
| 2 | Gaussian Mixtures | Distributions continues, mélanges gaussiens, estimation de params |
| 3 | Factor Graphs | Monty Hall + Murder Mystery : inférence discrète, Variable.If/Case |
| 4 | Bayesian Networks | Wet Grass, CPT, D-separation, explaining away, inférence causale |
| 5 | Skills (IRT) | Modélisation de compétences (DINA), evaluation adaptive |
| 6 | TrueSkill | Ranking bayésien, online learning, rating conservatif (mu - 3*sigma) |
| 7 | Classification | Bayes Point Machine, classification probit, tests A/B bayésiens |
| 8 | Model Sélection | Bayes Factors, evidence marginale, ARD (Automatic Relevance Détermination) |
| 9 | Topic Models | LDA, Dirichlet, prior asymétrique pour briser la symétrie VMP |
| 10 | Crowdsourcing | Worker models, communautés d'annotateurs, aggregation de labels |
| 11 | Séquences | HMM, detection de régimes, forward-backward, motifs temporels |
| 12 | Recommenders | Factorisation matricielle bayésienne, Click Model |
| 13 | Debugging | EP vs VMP, diagnostic de divergence, ShowFactorGraph, ShowSchedule |
| 14 | Décision Foundations | Axiomes VNM, loteries, théorème de représentation, calibration U |
| 15 | Décision Utility-Money | CARA, CRRA, aversion au risque, paradoxe Saint-Petersbourg |
| 16 | Décision Multi-Attribute | MAUT, SMART, swing weights, décisions multi-critères |
| 17 | Décision Networks | Diagrammes d'influence, politique optimale, inférence + décision |
| 18 | Décision Value-Info | EVPI, EVSI, valeur de l'information, when-to-test |
| 19 | Décision Expert-Systems | Minimax, Minimax Regret, robustesse face a l'incertitude |
| 20 | Décision Sequential | MDPs, itération valeur/politique, bandits, POMDPs |
| 20b | Lean Gittins | Formalisation Lean 4 : identités d'escompte prouvees, optimalité de Gittins énoncée |

### Série PyMC

| # | Notebook | Apport pédagogique |
|---|----------|-------------------|
| 1 | Setup | Boucle PyMC : pm.Model() → pm.sample(NUTS) → arviz |
| 2 | Gaussian Mixtures | Mélanges gaussiens MCMC, trace plots, convergence diagnostics |
| 3 | Factor Graphs | Inférence discrète avec PyMC, comparaison Infer.NET vs PyMC |
| 4 | Bayesian Networks | Réseaux bayésiens MCMC, CPT, explaining away |
| 5 | Skills (IRT) | IRT en Python, estimation de compétences par MCMC |
| 6 | TrueSkill | TrueSkill avec NUTS, online learning bayésien |
| 7 | Classification | Classification bayésienne, régression logistique |
| 8 | Model Sélection | Model comparison MCMC, LOO, WAIC, Bayes Factors empiriques |
| 9 | Topic Models | LDA avec NUTS, gestion variables latentes, inférence approximation |
| 10 | Crowdsourcing | Agrégation de labels crowdsourcing, worker communities |
| 11 | Séquences | HMM MCMC, forward-backward avec échantillonnage |
| 12 | Recommenders | Factorisation matricielle bayésienne MCMC |
| 13 | Debugging | Trace plots, R-hat, effective sample size, bonnes pratiques MCMC |
| 14 | Décision Foundations | Axiomes VNM en PyMC, loteries, décision bayésienne |
| 15 | Décision Utility-Money | CARA/CRRA en PyMC, calibration utilité, aversion au risque |
| 16 | Décision Multi-Attribute | MAUT avec PyMC, multi-criteria décision making |
| 17 | Décision Networks | Réseaux de décision MCMC, politiques optimales |
| 18 | Décision Value-Info | EVPI/EVSI en PyMC, valeur informationnelle |
| 19 | Décision Expert-Systems | Minimax/Minimax Regret robuste avec PyMC |
| 20 | Décision Sequential | MDPs MCMC, bandits, POMDPs |

## Notebooks racine (Python)

| Notebook | Kernel | Contenu | Durée |
|----------|--------|---------|-------|
| [Infer-101](Infer-101.ipynb) | Python + C# | Introduction Infer.NET, Two Coins, Cyclist | 45 min |
| [Pyro_RSA_Hyperbole](Pyro_RSA_Hyperbole.ipynb) | Python | Rational Speech Acts, hyperboles | 60 min |

### Infer-101.ipynb

Point d'entree accessible pour la programmation probabiliste :
- Concepts de base (variables aléatoires, modèles probabilistes)
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

La série complète est documentee dans [Infer/README.md](Infer/README.md), qui fournit des descriptions detaillees de chaque notebook, les patterns Infer.NET avancés, et des exercices corriges.

### Progression en 3 parties

| Partie | Notebooks | Focus | Durée |
|--------|-----------|-------|-------|
| **Fondations** | 1-3 | Setup, distributions, factor graphs | 2h |
| **Modèles classiques** | 4-13 | Bayesian networks, IRT, TrueSkill, LDA, HMM | 8h |
| **Décision** | 14-20, 20b | Théorie de la décision bayésienne + preuve Lean de Gittins | 8h |

Les 21 notebooks Infer.NET sont détaillés individuellement dans [*Ce que chaque notebook apporte*](#ce-que-chaque-notebook-apporte) ci-dessus (apport pédagogique par notebook) ; le contenu exhaustif — patterns avancés, exercices corrigés — vit dans [Infer/README.md](Infer/README.md).

## Série PyMC (20 notebooks, Python)

Port Python complet des modèles Infer.NET, utilisant l'échantillonnage MCMC (NUTS) au lieu du message passing. Permet de comparer les deux approches d'inférence sur des modèles identiques. La progression suit les mêmes trois phases que la série Infer.NET : fondations (1-3), modèles classiques (4-13), et théorie de la décision (14-20).

### Phase 1 — Fondations (notebooks 1-3, ~2h)

| # | Notebook | Sujet |
|---|----------|-------|
| 1 | [PyMC-1-Setup](PyMC/PyMC-1-Setup.ipynb) | Configuration PyMC, modèle Beta-Bernoulli |
| 2 | [PyMC-2-Gaussian-Mixtures](PyMC/PyMC-2-Gaussian-Mixtures.ipynb) | Distributions continues, mélanges gaussiens |
| 3 | [PyMC-3-Factor-Graphs](PyMC/PyMC-3-Factor-Graphs.ipynb) | Graphes de facteurs, inférence discrète |

### Phase 2 — Modèles classiques (notebooks 4-13, ~9h)

| # | Notebook | Sujet |
|---|----------|-------|
| 4 | [PyMC-4-Bayesian-Networks](PyMC/PyMC-4-Bayesian-Networks.ipynb) | Réseaux bayésiens, CPTs |
| 5 | [PyMC-5-Skills-IRT](PyMC/PyMC-5-Skills-IRT.ipynb) | Item Response Theory, modèles de compétences |
| 6 | [PyMC-6-TrueSkill](PyMC/PyMC-6-TrueSkill.ipynb) | Classement, TrueSkill |
| 7 | [PyMC-7-Classification](PyMC/PyMC-7-Classification.ipynb) | Classification bayésienne |
| 8 | [PyMC-8-Model-Sélection](PyMC/PyMC-8-Model-Selection.ipynb) | Sélection de modèles, Bayes Factors |
| 9 | [PyMC-9-Topic-Models](PyMC/PyMC-9-Topic-Models.ipynb) | LDA, Dirichlet priors |
| 10 | [PyMC-10-Crowdsourcing](PyMC/PyMC-10-Crowdsourcing.ipynb) | Agrégation de labels, workers, communautés |
| 11 | [PyMC-11-Séquences](PyMC/PyMC-11-Sequences.ipynb) | HMM, chaines de Markov cachées, séquences temporelles |
| 12 | [PyMC-12-Recommenders](PyMC/PyMC-12-Recommenders.ipynb) | Systèmes de recommandation bayésiens, factorisation |
| 13 | [PyMC-13-Debugging](PyMC/PyMC-13-Debugging.ipynb) | Troubleshooting MCMC, diagnostics NUTS, bonnes pratiques |

### Phase 3 — Théorie de la décision (notebooks 14-20, ~6h)

| # | Notebook | Sujet |
|---|----------|-------|
| 14 | [PyMC-14-Décision-Utility-Foundations](PyMC/PyMC-14-Decision-Utility-Foundations.ipynb) | Loteries, axiomes Von Neumann-Morgenstern, utilité espérée |
| 15 | [PyMC-15-Décision-Utility-Money](PyMC/PyMC-15-Decision-Utility-Money.ipynb) | Aversion au risque, CARA, CRRA, paradoxe Saint-Petersbourg |
| 16 | [PyMC-16-Décision-Multi-Attribute](PyMC/PyMC-16-Decision-Multi-Attribute.ipynb) | MAUT, SMART, swing weights, décisions multi-critères |
| 17 | [PyMC-17-Décision-Networks](PyMC/PyMC-17-Decision-Networks.ipynb) | Réseaux de décision, diagrammes d'influence, politique optimale |
| 18 | [PyMC-18-Décision-Value-Information](PyMC/PyMC-18-Decision-Value-Information.ipynb) | EVPI, EVSI, valeur de l'information parfaite et d'échantillon |
| 19 | [PyMC-19-Décision-Expert-Systems](PyMC/PyMC-19-Decision-Expert-Systems.ipynb) | Systèmes experts, Minimax, Minimax Regret, décisions robustes |
| 20 | [PyMC-20-Décision-Sequential](PyMC/PyMC-20-Decision-Sequential.ipynb) | MDPs, itération de valeur/politique, bandits, POMDPs |

## Applications standalone (2 notebooks)

| Notebook | Kernel | Contenu | Durée |
| -------- | ------- | ------- | ----- |
| [Infer-101](Infer-101.ipynb) | .NET (C#) + Python | Introduction Infer.NET, Two Coins, Cyclist | 1h |
| [Pyro_RSA_Hyperbole](Pyro_RSA_Hyperbole.ipynb) | Python 3 | Rational Speech Acts, hyperboles | 30 min |

## Prerequisites

### Niveau mathématique attendu

Cette série suppose une **maîtrise de base en probabilités et statistiques** :

| Concept | Utilité dans la série | Notes de revision |
|---------|---------------------|------------------|
| Variables aléatoires (discrètes/continues) | Partout, notebook 1+ | Loi de proba, espérance, variance |
| Distributions usuelles (Bernoulli, Gaussian, Beta, Gamma) | Notebook 1 (Beta-Bernoulli), 2 (Gaussian) | Paramètres, formes, conjugaison |
| Probabilités conditionnelles | Notebook 3+ (Variable.If, CPT) | P(A|B), théorème de Bayes |
| Indépendance conditionnelle | Notebook 3 (Monty Hall), 4 (D-separation) | Collider, explaining away |
| Espérance mathématique | Partout (calcul de EU) | E[X] = sum x*P(x) ou integral |
| Distributions conjuguees | Notebook 1 (Beta-Bernoulli), 9 (Dirichlet-Discrète) | Prior + likelihood = posterior (famille même) |
| Integrals (niveau 1) | Notebook 2, 15 (CARA/CRRA) | Calcul d'espérance avec fonctions non-linéaires |

**Inutile de maîtriser** : derivation multivariee, algèbre linéaire avancée (sauf pour les modèles hiérarchiques en notebook 4). Les concepts sont introduits progressivement et reexpliques dans le contexte.

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
| **Inférence bayésienne** | Mise a jour de croyances avec des observations |
| **Prior / Posterior** | Distribution avant/après observations |
| **Factor Graph** | Représentation graphique de distributions jointes |
| **Message Passing** | Algorithmes EP (Expectation Propagation), VMP |
| **MCMC / NUTS** | Échantillonnage pour modèles complexes (PyMC) |
| **D-separation** | Critère graphique d'indépendance conditionnelle |
| **Explaining Away** | Causes alternatives deviennent moins probables |
| **Decision Theory** | Maximisation d'utilité espérée |
| **Valeur de l'information** | EVPI, EVSI — coût d'un test complémentaire |

## Domaines d'application

| Domaine | Notebooks |
|---------|-----------|
| Jeux video | 6 (TrueSkill) |
| Education | 5 (IRT), 14 |
| NLP | 9 (LDA) |
| Médecine | 4, 7, 17-19 |
| Finance | 11, 15, 20 |
| E-commerce | 12 |

### Exemples concrets

Derrière chaque modèle de la série se cache un système réel déjà en production :

- **TrueSkill** (notebook 6) est l'algorithme que Microsoft utilise pour apparier des millions de joueurs sur Xbox Live : il maintient pour chaque joueur une compétence *gaussienne* (moyenne + incertitude) mise a jour après chaque partie, généralisant l'Elo des échecs aux jeux en equipe.
- **Item Response Theory** (notebook 5) est le moteur des tests adaptatifs comme le GMAT ou le GRE : la difficulté de chaque question est calibrée probabilistiquement, et le test s'ajuste en temps réel au niveau estime du candidat.
- **Les réseaux bayésiens** (notebooks 4, 7) fondent les systèmes d'aide au diagnostic médical (de QMR-DT aux outils modernes) et le filtrage anti-spam : ils propagent l'incertitude entre symptomes, causes et observations.
- **LDA / topic models** (notebook 9) structurent automatiquement de grands corpus — découverte de thématiques dans des archives de presse, cartographie de la litterature scientifique, analyse de tickets support.
- **Les HMM** (notebook 11) detectent les régimes cachés : phases de marche en finance, reconnaissance de la parole, segmentation de séquences biologiques.
- **Les systèmes de recommandation bayésiens** (notebook 12) sont la version « avec barre d'incertitude » du collaborative filtering de Netflix ou Amazon — utile pour décider quand explorer un nouvel item plutôt que d'exploiter une préférence connue.
- **Le crowdsourcing** (notebook 10) modélise la fiabilité de chaque annotateur (Mechanical Turk, labellisation de datasets) pour reconstruire la vérité terrain malgré des votes bruités.
- **La théorie de la décision et les MDPs** (notebooks 14-20) relient la série au controle séquentiel : gestion de stocks, maintenance predictive, et passerelle directe vers le [reinforcement learning](../RL/).

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

### Vérification

```bash
jupyter kernelspec list  # doit afficher .net-csharp et python3
```

### Tester tous les notebooks

```bash
python MyIA.AI.Notebooks/Probas/Infer/scripts/test_notebooks.py --validate-only
```

## FAQ / Troubleshooting

### Le kernel .NET Interactive n'apparait pas dans Jupyter

- Vérifiez que `dotnet interactive jupyter install` a réussi (sortie : `Kernel installed`).
- Redémarrez Jupyter. Si le kernel persiste a ne pas apparaitre, vérifiez que .NET SDK 9.0+ est installe : `dotnet --version`.
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

Le notebook `Infer-101.ipynb` est le seul a mélanger les deux kernels. Il utilise le mode **polyglot** de .NET Interactive, ou chaque cellule spécifie son kernel via le tag `#kernel name`. Pour la série standard, chaque sous-série (Infer/ ou PyMC/) utilise un seul kernel.

### PyMC : échantillonnage tres lent ou divergence NUTS

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

### Théorie

- Bishop, C. (2006) - *Pattern Recognition and Machine Learning*
- Koller & Friedman (2009) - *Probabilistic Graphical Models*
- Von Neumann & Morgenstern (1944) - *Theory of Games and Economic Behavior*
- Russell & Norvig - *Artificial Intelligence*, Chapter 16 (Decision Theory)

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette série vous a fait changer de regard sur l'incertitude : plutôt que de la fuir ou de l'ignorer, vous avez appris à la **modéliser, la quantifier et la traduire en décisions**. L'arc pédagogique se déploie en trois temps, porté par trois stacks complémentaires :

- **Le geste fondateur** — remplacer une prédiction ponctuelle par une **distribution**. Un modèle probabiliste ne dit pas « la probabilité est 0.73 » mais « voici la distribution complète N(0.73, 0.12) », et cette densité porte l'information que la moyenne dissimule : la confiance, les queues, les modes multiples. C'est ce déplacement qui ouvre tout le reste.
- **La double inférence** — Infer.NET (message passing, EP/VMP) et PyMC (NUTS, MCMC) résolvent les mêmes modèles par des voies opposées. Le traverser sur des modèles jumeaux (notebook à notebook, Infer-N ↔ PyMC-N) ancre une intuition qu'aucun cours théorique ne donne : **quand l'inférence exacte est tractable, elle est déterministe et rapide ; quand elle ne l'est plus, l'échantillonnage prend le relais mais exige des diagnostics** (R-hat, effective sample size, trace plots).
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
