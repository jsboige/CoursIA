# TweetyProject - Serie de Notebooks Jupyter

<!-- CATALOG-STATUS
series: SymbolicAI-Tweety
pedagogical_count: 10
breakdown: Fondations=3, Revision-Croyances=1, Argumentation=4, Applications=2
maturity: PRODUCTION=6, BETA=4
-->

Serie complete de 10 notebooks pour explorer [TweetyProject](https://tweetyproject.org/), une bibliotheque Java pour l'intelligence artificielle symbolique.

## Serie en quelques mots

**10 notebooks** | **1 kernel** | **~6h de travail** | **Tweety 1.30**

**A qui s'adresse cette serie** : etudiants en IA, chercheurs en argumentation computationnelle, developpeurs interesses par le raisonnement formel, et tout curieux souhaitant comprendre les bases mathematiques derriere le raisonnement explicite. Aucun prerequis en logique formelle n'est suppose : les concepts sont introduces progressivement, des operateurs propositionnels de base jusqu'aux semantiques d'argumentation les plus avancees.

## Presentation

TweetyProject est une collection de bibliotheques Java couvrant plusieurs domaines :

- **Logiques formelles** : Propositionnelle, Premier ordre, Modale, Description, QBF
- **Argumentation computationnelle** : Dung, ASPIC+, DeLP, ABA, ADF
- **Revision de croyances** : AGM, Mesures d'incoherence, MUS/MCS
- **Agents et dialogues** : Multi-agents, Protocoles argumentatifs
- **Preferences et vote** : Ordres de preference, Agregation

Les notebooks utilisent **JPype** pour integrer Java dans Python, permettant un apprentissage interactif.

A l'heure des modeles statistiques et des LLMs, pourquoi etudier ces logiques symboliques ? Parce qu'elles apportent ce que l'apprentissage seul ne garantit pas : un raisonnement **explicite, verifiable et explicable**. L'argumentation computationnelle (cadres de Dung, ASPIC+, ABA) modelise la facon dont des agents confrontent des arguments, gerent les contradictions et aboutissent a des conclusions justifiees — avec des applications en raisonnement juridique, en aide a la decision, en negociation multi-agents, et de plus en plus comme couche de controle au-dessus des LLMs (detecter les incoherences, structurer un debat). La revision de croyances (AGM) formalise comment un agent rationnel met a jour ses connaissances face a une information nouvelle ou contradictoire. L'interet de TweetyProject est de reunir tous ces formalismes sous un meme toit : on experimente d'une logique a l'autre sans avoir a reimplementer chaque solveur.

## Symbolique vs. Statistique

Pour comprendre ou se positionne cette serie, voici une comparaison entre les approches symbolique et statistique de l'IA :

| Aspect | IA Symbolique (TweetyProject) | IA Statistique (ML/LLMs) |
|--------|-------------------------------|--------------------------|
| **Représentation** | Logiques formelles (PL, FOL, DL) | Vecteurs embeddings, poids neuronaux |
| **Raisonnement** | Deduction formelle, verification | Inference probabiliste, approximation |
| **Verifiabilite** | Preuves mathematiques, solveurs | Benchmarks empiriques, statistiques |
| **Explicabilite** | Chaines de raisonnement lisibles | Boite noire, attention maps |
| **Incoherence** | Detection MUS/MCS, SAT solver | Gradient instability, divergence |
| **Force** | Garanties de correction | Adaptabilite, generalisation |
| **Limite** | Complexe a escala | Manque de garanties formelles |

Cette serie ne propose pas de choisir l'un ou l'autre, mais de **comprendre les deux**. L'intersection est d'ailleurs le front actif de la recherche : argumentation pour controler les LLMs, logiques neuronales, verification formelle de modeles generatifs.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 10 |
| Cellules totales | ~375 |
| Duree estimee | ~6h (tutorat) |
| Kernel | Python 3 (JPype/Java) |
| Version Tweety | 1.30 recommande |
| Solveurs externes | Clingo, SPASS, EProver, Z3, PySAT |
| JARs Java | ~35 modules |

## Parcours d'apprentissage

### Phase 1 : Fondations (Notebooks 1-3, ~1.5h)

La serie debute avec le notebook 1 (Setup) qui configure toute l'environnement : telechargement automatique du JDK Zulu, des 35 JARs TweetyProject, et des outils externes (Clingo pour ASP, SPASS pour la logique modale, EProver pour le premier ordre). Une fois la JVM initialisee via JPype, le notebook 2 plonge dans les logiques fondamentales : la logique propositionnelle avec les operateurs booleens, la satisfaisabilite (SAT) via pySAT, et la logique du premier ordre avec la construction de signatures et le raisonnement avec EProver. Le notebook 3 etend ces fondations aux logiques de Description (DL) pour les ontologies, la logique modale (necessite/possibilite) pour le raisonnement sur les mondes possibles, les formules boolean quantifiees (QBF), et la logique conditionnelle pour le raisonnement defeasible. A l'issue de cette phase, vous maitrisez les outils de base du raisonnement formel.

### Phase 2 : Revision de Croyances (Notebook 4, ~45 min)

Ce notebook unique introduit la gestion de l'incoherence dans les systemes intelligents. Plutot que d'echouer face a des connaissances contradictoires, un systeme rationnel doit identifier les sources de conflit (MUS - Minimal Unsatisfiable Subsets), mesurer l'incoherence (scores et indices), et reelaborer ses croyances (revision AGM). Les outils pratiques incluent MaxSAT pour l'optimisation sous contraintes et le raisonnement multi-agents avec CrMas. C'est un pont entre les logiques pures et les systemes multi-agents.

### Phase 3 : Argumentation — De l'abstrait au structure (Notebooks 5-6, ~2h)

Les notebooks 5 et 6 constituent le cœur de la serie. Le notebook 5 introduit l'argumentation abstraite de Dung (1995) : un cadre ou des arguments s'attaquent mutuellement sans regarder leur contenu interne. On y explore les semantiques classiques (grounded, preferred, stable, semi-stable), la semantique CF2 pour les cycles, et les nouveautes 1.30 (equivalence de frameworks, explications, raisonnement causal). Le notebook 6 monte d'un cran de granularite avec l'argumentation structuree : ASPIC+ (arguments construits a partir de regles defeasibles), DeLP (logique defeasible programmee), ABA (argumentation par hypothese), et l'Answer Set Programming (ASP) via Clingo. La comparaison entre ces cadres montre que chacun offre un compromis different entre expressivite et calculabilite.

### Phase 4 : Frameworks avances et probabilistes (Notebooks 7a-7b, ~1h)

Le notebook 7a explore les extensions du cadre de Dung : ADF (Abstract Dialectical Frameworks, ou les arguments peuvent avoir plusieurs preconditions), les frameworks bipolaires (support + attaque), les WAF (Weighted Argument Frameworks avec attaques ponderees), les SAF (Social Argumentation Frameworks), les SetAF (attaques collectives), et les frameworks extends (attaques recursives sur des attaques). Le notebook 7b aborde deux axes differs : les semantiques de classement (ranking) qui assignent un niveau de credibilite a chaque argument plutot que des extensions binaires, et l'argumentation probabiliste ou les arguments portent des probabilities.

### Phase 5 : Applications multi-agents (Notebooks 8-9, ~1h)

La serie se conclut par deux notebooks applicatifs. Le notebook 8 modelise les dialogues argumentatifs entre agents : protocoles d'echange, jeux grounded, et loteries argumentatives. Le notebook 9 traite des preferences et de la theorie du vote : ordres de preference, regles d'agregation (Borda, Condorcet, Copeland), et leur connexion avec l'argumentation. C'est la passerelle vers la theorie des jeux et le choix social.

### Parcours alternatifs

#### Parcours logique (focus fondations, ~2h)

Pour ceux qui souhaitent une base solide en logiques formelles avant l'argumentation :

1. **Setup** (1) → **Logiques de base** (2) → **Logiques avancees** (3) → **Revision** (4)
2. Puis choisir : **Argumentation abstraite** (5) pour la theorie pure, ou **Applications** (8-9) pour les cas d'usage

#### Parcours argumentation intensive (focus 5-7b, ~3.5h)

Pour les etudiants en argumentation computationnelle, aller droit au but :

1. **Setup rapide** (1) : ne garder que la partie configuration JVM
2. **Logiques de base** (2) : section PL uniquement, skip FOL si deja connu
3. **Argumentation abstraite** (5) : Dung + semantiques
4. **Argumentation structuree** (6) : ASPIC+ et DeLP
5. **Frameworks avances** (7a) : ADF + bipolarite
6. **Ranking et probabiliste** (7b) : semantiques de classement

#### Parcours applications (focus 8-9, ~1h)

Pour les praticiens interessés par les applications multi-agents :

1. **Setup** (1) + **Logiques de base** (2) : juste pour l'environnement
2. **Argumentation abstraite** (5) : semantiques de Dung essentielles
3. **Dialogues multi-agents** (8) : protocoles et jeux grounded
4. **Preferences et vote** (9) : theorie du vote et aggregation

## Structure

| # | Notebook | Theme | Duree |
|---|----------|-------|-------|
| **Fondations** |
| 1 | [Tweety-1-Setup](Tweety-1-Setup.ipynb) | Configuration JVM, JARs, outils externes | 20 min |
| 2 | [Tweety-2-Basic-Logics](Tweety-2-Basic-Logics.ipynb) | Logique Propositionnelle et FOL | 45 min |
| 3 | [Tweety-3-Advanced-Logics](Tweety-3-Advanced-Logics.ipynb) | DL, Modale, QBF, Conditionnelle | 40 min |
| **Revision de Croyances** |
| 4 | [Tweety-4-Belief-Revision](Tweety-4-Belief-Revision.ipynb) | CrMas, MUS, MaxSAT, Mesures d'incoherence | 50 min |
| **Argumentation** |
| 5 | [Tweety-5-Abstract-Argumentation](Tweety-5-Abstract-Argumentation.ipynb) | Dung AF, Semantiques, CF2, Generation | 55 min |
| 6 | [Tweety-6-Structured-Argumentation](Tweety-6-Structured-Argumentation.ipynb) | ASPIC+, DeLP, ABA, ASP | 60 min |
| 7a | [Tweety-7a-Extended-Frameworks](Tweety-7a-Extended-Frameworks.ipynb) | ADF, Bipolar, WAF, SAF, SetAF, Extended | 50 min |
| 7b | [Tweety-7b-Ranking-Probabilistic](Tweety-7b-Ranking-Probabilistic.ipynb) | Ranking Semantics, Probabiliste | 40 min |
| **Applications** |
| 8 | [Tweety-8-Agent-Dialogues](Tweety-8-Agent-Dialogues.ipynb) | Agents, Dialogues argumentatifs, Loteries | 35 min |
| 9 | [Tweety-9-Preferences](Tweety-9-Preferences.ipynb) | Preferences, Theorie du vote | 30 min |

**Duree totale estimee** : ~7 heures

## En quoi chaque notebook est unique

Chaque notebook introduit un concept ou cadre theorique specifique. Le tableau ci-dessous resume en une ligne l'apport pedagogique de chacun :

| # | Notebook | Concept clé enseigne |
|---|----------|---------------------|
| 1 | Setup | Boucle configuration : JVM → JPype → JARs → solveurs externes |
| 2 | Basic Logics | SAT solving en pratique (pySAT) + formalisme FOL avec EProver |
| 3 | Advanced Logics | Ontologies OWL (DL) + raisonnement modale (SPASS) + QBF |
| 4 | Belief Revision | Identification de conflits (MUS) + revision AGM + MaxSAT |
| 5 | Abstract Argumentation | Semantiques de Dung (grounded/stable/CF2) + frameworks aleatoires |
| 6 | Structured Argumentation | Comparaison ASPIC+/DeLP/ABA/ASP — le cadre idéal selon le domaine |
| 7a | Extended Frameworks | Au-dela de Dung : ADF, bipolarite, attaques ponderees et collectives |
| 7b | Ranking & Probabilistic | Classement graduel des arguments + incertitude sur les arguments |
| 8 | Agent Dialogues | Protocoles d'echange entre agents + negociation argumentative |
| 9 | Preferences | Agrégation de preferences (Borda, Condorcet) + theorie du vote |

## Quick Start

```bash
# 1. Installer les packages Python
pip install jpype1 requests tqdm clingo z3-solver python-sat

# 2. Ouvrir le notebook de setup (auto-telecharge JDK + JARs)
jupyter notebook Tweety-1-Setup.ipynb

# 3. Executer toutes les cellules, puis passer a Tweety-2
```

JDK 17 et les 35 JARs TweetyProject sont telecharges automatiquement par le notebook de setup. Aucune installation systeme requise.

## Prerequis

### Niveau mathematique attendu

Cette serie suppose une **maîtrise de base en logique et raisonnement** :

| Concept | Utilisation dans la serie | Notes de révision |
|---------|--------------------------|-------------------|
| Logique propositionnelle (ET, OU, NON, →) | Notebook 2 (PL), 5+ (argumentation) | Tables de verite, DNF/CNF, satisfaisabilite |
| Logique du premier ordre (quantificateurs) | Notebook 2 (FOL), 3 (DL) | ∀, ∃, variables, predicats |
| Graphes (noeuds, aretes) | Notebook 5 (Dung AF), 7a (SetAF) | Chemins, cycles, orientes |
| Ensembles (inclusion, union, intersection) | Partout (extensions, bases) | Ensembles finis, parties |
| Raisonnement par recurrence | Notebook 3 (DL), 5 (semantiques) | Principe de recurrence bien-fondee |

**Inutile de maitriser** : theorie de la preuve formelle, complexité computationnelle avancée (la complexite des semantiques de Dung est expliquee en contexte). Les concepts logiques sont introduits progressivement dans chaque notebook.

### Prerequis techniques

#### Python et dependances

```bash
pip install jpype1 requests tqdm clingo z3-solver python-sat
```

#### Java/JVM

- **JDK 17+** — telechargé automatiquement (Zulu) par le notebook de setup
- **JPype** — bridge Python ↔ Java (charge automatiquement les JARs)

#### Outils externes (optionnels mais recommandés)

| Outil | Usage | Installation |
|-------|-------|--------------|
| **Clingo 5.4+** | ASP (Answer Set Programming) | `download_tweety_tools.py --clingo` |
| **SPASS** | Logique modale | Binaire inclus ou auto-download Linux |
| **EProver** | FOL haute performance | Installation manuelle ou dossier inclus |
| **Z3** | SMT solver, MARCO | `pip install z3-solver` |
| **PySAT** | SAT/MaxSAT moderne | `pip install python-sat` |

## Architecture

```
Tweety/
├── Tweety-1-Setup.ipynb          # Configuration
├── Tweety-2-Basic-Logics.ipynb   # PL + FOL
├── Tweety-3-Advanced-Logics.ipynb # DL, ML, QBF, CL
├── Tweety-4-Belief-Revision.ipynb # Revision de croyances
├── Tweety-5-Abstract-Argumentation.ipynb
├── Tweety-6-Structured-Argumentation.ipynb
├── Tweety-7a-Extended-Frameworks.ipynb
├── Tweety-7b-Ranking-Probabilistic.ipynb
├── Tweety-8-Agent-Dialogues.ipynb
├── Tweety-9-Preferences.ipynb
├── libs/                          # JARs Tweety (35 modules)
├── resources/                     # Fichiers d'exemples (.txt, .aba, .aspic)
├── ext_tools/                     # Outils externes (Clingo, SPASS, EProver)
├── jdk-17-portable/              # JDK Zulu (telecharge auto)
├── scripts/
│   ├── download_tweety_tools.py  # Script de téléchargement des dépendances
│   ├── verify_all_tweety.py      # Script de validation
│   └── validate_syntax.py        # Validation syntaxe Python
└── README.md                      # Ce fichier
```

## Outils Externes

### Script de téléchargement automatisé

Un script autonome est disponible pour télécharger toutes les dépendances :

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Tweety

# Télécharger tout (JARs, ressources, outils)
python scripts/download_tweety_tools.py --all

# Télécharger uniquement les JARs
python scripts/download_tweety_tools.py --jars

# Télécharger uniquement les ressources
python scripts/download_tweety_tools.py --resources

# Télécharger Clingo (ASP solver)
python scripts/download_tweety_tools.py --clingo

# Voir toutes les options
python scripts/download_tweety_tools.py --help
```

### Liste des dépendances

| Outil | Usage | Téléchargement Auto | Versionné Git |
|-------|-------|---------------------|---------------|
| **Clingo** | ASP (Answer Set Programming) | Oui (Win/Linux) | Oui (binaire Windows) |
| **SPASS** | Logique Modale | Oui (Linux) | Oui (binaire + docs Windows) |
| **EProver** | FOL haute performance | Non | Oui (installation complète) |
| **Z3** | SMT solver, MARCO | `pip install z3-solver` | N/A (package Python) |
| **PySAT** | SAT/MaxSAT moderne | `pip install python-sat` | N/A (package Python) |
| **Native SAT** | Bibliotheques SAT JNI | Oui | Oui (DLLs Minisat, Lingeling) |
| **JDK 17** | JVM pour JPype | Oui (Zulu) | Non (trop volumineux) |
| **JARs Tweety** | Bibliothèques Java | Oui (Maven Central) | Non (trop volumineux) |
| **Resources** | Fichiers exemples | Oui (GitHub) | Non (fichiers de données) |

### Notes d'installation

#### Clingo

- Télécharge automatiquement pour Windows et Linux
- Version 5.4.0 depuis GitHub releases (potassco/clingo)
- Si déjà installé dans le PATH, utilise la version système

#### SPASS (Windows)

- Le téléchargement automatique n'est PAS disponible sur Windows (l'installeur ne peut pas être automatisé)
- **Deux options** :

  1. Utiliser le binaire déjà inclus dans le dépôt Git (`ext_tools/spass/SPASS.exe`)
  2. Installation manuelle :
     - Télécharger depuis <https://www.spass-prover.org/download/binaries/>
     - Exécuter l'installeur `spass30windows.exe`
     - Copier `SPASS.exe` et le dossier `SPASS-3.0/` vers `ext_tools/spass/`

#### SPASS (Linux)

- Télécharge automatiquement (version 64-bit ou 32-bit selon l'architecture)

#### EProver

- Doit être installé manuellement : <https://eprover.org/>
- L'installation complète est déjà incluse dans `../ext_tools/EProver/`
- Contient tous les utilitaires : eprover, eground, enormalizer, etc.

#### Bibliothèques natives SAT

- DLLs Windows (Minisat, Lingeling, Picosat) pour Tweety JNI
- Téléchargeables automatiquement ou déjà incluses dans `libs/native/`

## Limitations Connues (Tweety 1.28/1.29)

| Limitation | Impact | Contournement |
|------------|--------|---------------|
| **CrMas/InformationObject** | Section revision multi-agents echoue | API refactorisee, classe supprimee |
| **SimpleMlReasoner** | Bloque indefiniment | Utiliser SPASS externe |
| **AF Learning** | ClassCastException | Bug interne, section desactivee |
| **ADF natif SAT** | Raisonnement ADF incomplet | Necessite solveur SAT natif (non JPype) |
| **FOL avec egalite** | Heap space sur grandes requetes | Utiliser EProver externe |

## Modules TweetyProject Couverts

### Logiques (Notebooks 2-3)

| Module | Description | Notebook |
|--------|-------------|----------|
| `logics.pl` | Logique Propositionnelle | 2 |
| `logics.fol` | Logique du Premier Ordre | 2 |
| `logics.dl` | Logique de Description | 3 |
| `logics.ml` | Logique Modale | 3 |
| `logics.qbf` | Quantified Boolean Formulas | 3 |
| `logics.cl` | Logique Conditionnelle | 3 |

### Revision de Croyances (Notebook 4)

| Module | Description |
|--------|-------------|
| `beliefdynamics` | Operateurs de revision AGM |
| `logics.pl.analysis` | Mesures d'incoherence |
| `logics.pl.sat` | MUS, MaxSAT |

### Argumentation (Notebooks 5-7)

| Module | Description | Notebook |
|--------|-------------|----------|
| `arg.dung` | Frameworks de Dung | 5 |
| `arg.aspic` | ASPIC+ | 6 |
| `arg.delp` | Defeasible Logic Programming | 6 |
| `arg.aba` | Assumption-Based Argumentation | 6 |
| `lp.asp` | Answer Set Programming | 6 |
| `arg.adf` | Abstract Dialectical Frameworks | 7a |
| `arg.bipolar` | Frameworks Bipolaires | 7a |
| `arg.weighted` | Frameworks Pondérés | 7a |
| `arg.social` | Argumentation Sociale | 7a |
| `arg.setaf` | Attaques Collectives | 7a |
| `arg.extended` | Attaques Recursives | 7a |
| `arg.rankings` | Semantiques de Classement | 7b |
| `arg.prob` | Argumentation Probabiliste | 7b |

### Agents et Preferences (Notebooks 8-9)

| Module | Description | Notebook |
|--------|-------------|----------|
| `agents` | Framework agents de base | 8 |
| `agents.dialogues` | Dialogues argumentatifs | 8 |
| `agents.dialogues.oppmodels` | Jeux grounded (ArguingAgent) | 8 |
| `agents.dialogues.lotteries` | Loteries argumentatives | 8 |
| `preferences` | Ordres de preference, agregation | 9 |

## Concepts clés

| Concept | Description |
|---------|-------------|
| **Logique Propositionnelle** | Operateurs booléens, DNF, satisfaisabilité (SAT) |
| **Logique du Premier Ordre** | Quantificateurs (∀, ∃), prédicats, fonctions |
| **Logique de Description** | Ontologies, TBox/ABox, sous-typage, OWL |
| **Logique Modale** | Nécessité (□) et possibilité (◇), mondes possibles |
| **Argumentation de Dung** | Frameworks abstraits, attaques, sémantiques (grounded, stable) |
| **Argumentation structurée** | Arguments construits à partir de prémisses et règles |
| **Revision AGM** | Mise à jour rationnelle de croyances face à l'information contradictoire |
| **MUS/MCS** | Sous-ensembles insatisfaisables/maximaux — identifier les conflits |
| **Answer Set Programming** | Programmation par modèles (ASP) via Clingo |
| **Agrégation de préférences** | Borda, Condorcet, Copeland — combiner des opinions |

## Domaines d'application

| Domaine | Notebooks | Exemple concret |
|---------|-----------|----------------|
| **Juridique** | 5, 6, 8 | Argumentation légale, debats en cour, preuve par argument |
| **Aide a la decision** | 4, 9 | Diagnostic médical, planification de ressources, vote |
| **Multi-agents** | 8 | Negociation automatique, protocoles de dialogue |
| **Ontologies** | 3 | Representations de connaissances, OWL, Web semantique |
| **Verification formelle** | 2, 3, 4 | SAT/SMT solving, proof checking, model checking |
| **LLM control** | 5, 6, 7b | Detection d'incoherences, structuration de debats, argumentation probabiliste |

### Exemples concrets

Derriere chaque cadre de la serie se cache une application reelle ou un probleme de recherche actif :

- **L'argumentation de Dung** (notebook 5) est le fondement mathématique de nombreux systemes d'aide a la decision juridique : des arguments se confrontent, les semantiques determinent quels arguments sont "acceptables", et le resultat guide la conclusion. C'est aussi la base des frameworks d'explicabilite des LLMs — detecter les incoherences entre reponses d'un modele.
- **ASPIC+ et DeLP** (notebook 6) modelisent des debats ou les arguments ont une structure interne : premisses, regles defeasibles, et priorités. Applications en aide a la decision medicale, en gestion de conflits de regles, et en verification de contrats.
- **La revision de croyances AGM** (notebook 4) formalise comment un systeme rationnel met a jour ses connaissances quand une information contradictoire arrive. Applications en integration de donnees, diagnostic de bases de connaissance, et fusion de sources d'information.
- **Les frameworks etendus** (notebook 7a) generalisent Dung pour capturer des situations réelles ou des arguments ont plusieurs preconditions (ADF), ou des attaques ont des poids varies (WAF), ou des groupes d'arguments attaquent collectivement (SetAF).
- **La theorie du vote** (notebook 9) est au cœur des systemes de recommandation collective, de l'agregation de preferences en intelligence artificielle, et des mechanisms d'incitation (mechanism design).

## Installation

### Packages Python requis

```bash
pip install jpype1 requests tqdm clingo z3-solver python-sat
```

### Verification de l'environnement

```bash
# Lancer le notebook de setup
jupyter notebook Tweety-1-Setup.ipynb
# Executer toutes les cellules — il telecharge JDK, JARs, outils externes

# Ou utiliser le script de validation
cd scripts
python verify_all_tweety.py --quick
```

JDK 17 et les 35 JARs TweetyProject sont telecharges automatiquement par le notebook de setup. Aucune installation systeme requise.

## Validation des Notebooks

### Script de verification

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Tweety/scripts

# Verification structurelle rapide
python verify_all_tweety.py --quick

# Verification environnement
python verify_all_tweety.py --check-env

# Analyse des sorties existantes
python verify_all_tweety.py --analyze-outputs --verbose

# Execution complete (lent)
python verify_all_tweety.py --execute --verbose

# Notebook specifique
python verify_all_tweety.py --notebook Tweety-2 --analyze-outputs
```

### Options disponibles

| Option | Description |
|--------|-------------|
| `--quick` | Validation structure uniquement |
| `--check-env` | Verifier JDK, JARs, outils |
| `--analyze-outputs` | Analyser sorties existantes |
| `--execute` | Execution Papermill complete |
| `--cell-by-cell` | Execution cellule par cellule |
| `--execute-missing` | Executer cellules sans output |
| `--clean-errors` | Nettoyer sorties en erreur |
| `--verbose` | Sortie detaillee |
| `--json` | Format JSON (CI/CD) |

## FAQ / Troubleshooting

### `JPypeError` ou JVM deja démarree

Tweety utilise JPype pour integrer la JVM. Si un notebook signale que la JVM est deja démarree, c'est que le notebook precedent ne l'a pas arreee proprement. Relancer Jupyter et executer depuis le notebook 1.

### Clingo non trouve

Si `clingo` n'est pas dans le PATH, utiliser le script de téléchargement :

```bash
python scripts/download_tweety_tools.py --clingo
```

Le binaire Windows sera telecharge dans `ext_tools/`.

### EProver ne repond pas ou heap space

EProver peut bloquer sur des formules FOL complexes avec egalité. La solution est d'utiliser un solveur plus léger ou de réduire la taille de la base de connaissances. Voir la section "Limitations connues" ci-dessus.

### Erreur de chargement d'un JAR Tweety

Verifier que la version Tweety dans `Tweety-1-Setup.ipynb` correspond a la version telechargee. La version recommandeée est 1.30. Pour changer de version, modifier la variable `TWEETY_VERSION` puis relancer le notebook 1.

### `ClassCastException` en argumentation

Le notebook 5 signale un bug connu (AF Learning — ClassCastException). La section correspondante est desactivée. Suivre les autres sections sans probleme.

### JPype lent au premier appel

Le premier appel a un module Java déclenche le chargement de la JVM et des classes Tweety. Attendez 5-10 secondes avant la premiere reponse. Les appels suivants sont rapides.

### Comment passer d'un notebook a l'autre ?

Chaque notebook presuppose la configuration faite dans Tweety-1-Setup (JDK, JARs, JVM). Une fois le notebook 1 execute, les notebooks 2-9 peuvent etre executes dans l'ordre logique de la serie. Les outils externes (Clingo, SPASS, EProver) sont configures par le notebook 1.

## Versions TweetyProject

| Version | Date | Nouveautes |
|---------|------|------------|
| **1.28** | Janvier 2025 | arg.caf, k-admissibility, API refactoring |
| **1.29** | Juillet 2025 | arg.eaf (Epistemic AF), graph rendering |
| **1.30** | Janvier 2026 | causal reasoning, arg.explanations, equivalence checking |

La version est configurable dans `Tweety-1-Setup.ipynb` (variable `TWEETY_VERSION`). La version 1.30 est recommandeée — elle inclut les semantiques de causalite, les explications en argumentation, et le checking d'equivalence de frameworks.

## Ressources

### References academiques

| Reference | Couverture |
|-----------|------------|
| Dung, "On the Acceptability of Arguments" (1995) | Notebook 5, semantiques de Dung |
| Modgil & Prakken, "The ASPIC+ Framework" (2014) | Notebook 6, argumentation structuree |
| Alchourron, Gardenfors & Makinson, "On the Logic of Theory Change" (1985) | Notebook 4, revision AGM |
| Enderton, *A Mathematical Introduction to Logic* (2001) | Notebooks 2-3, logiques formelles |
| Besnard & Hunter, *Elements of Argumentation* (2008) | Notebooks 5-7, theorie argumentation |
| Brewka, Eiter & Truszczynski, "Answer Set Programming at a Glance" (2011) | Notebook 6, ASP/Clingo |
| Russell & Norvig, *AIMA* 4e ed., ch. 7-8 | Cadre general logique et SAT |

### Ressources en ligne

- **TweetyProject** : https://tweetyproject.org/
- **Documentation API** : https://tweetyproject.org/api/
- **GitHub** : https://github.com/TweetyProjectTeam/TweetyProject
- **JPype** : https://jpype.readthedocs.io/

## Ponts avec les autres series

| Serie | Connection | Details |
|-------|------------|---------|
| **[Argument_Analysis](../Argument_Analysis/)** | Argumentation agentique | Utilise Tweety comme backend Java pour le raisonnement argumentatif. Les semantiques de Dung (notebook 5) sont directement appliquees dans l'analyse de textes. |
| **[Lean](../Lean/)** | Verification formelle | Les logiques propositionnelles et FOL (notebooks 2-3) correspondent aux tactiques de preuve Lean. Les SAT solvers de Tweety completent la verification Lean. |
| **[SmartContracts](../SmartContracts/)** | Methods formelles | La verification formelle SC-14 (Certora/SMTChecker) utilise les memes solveurs SAT/SMT. La logique propositionnelle de Tweety est la base des invariants Solidity. |
| **[GameTheory](../../GameTheory/)** | Theorie du vote | Le notebook 9 (Preferences/Vote) couvre les concepts de choix social formalises dans `social_choice_lean/` (Arrow, Sen, Voting). |
| **[Planners](../Planners/)** | Planification argumentative | Les dialogues argumentatifs (notebook 8) peuvent etre modelises comme des problemes de planification PDDL. |

## Cross-series Bridges

| Serie | Lien | Connection |
| ------- | ------ | ----------- |
| [SymbolicAI/SemanticWeb](../SemanticWeb/README.md) | OWL reasoning | La logique de Description (Tweety-3) est le fondement de l'OWL reasoning — les ontologies OWL DL utilisent les memes solveurs DL que Tweety |
| [IIT](../IIT/README.md) | Argumentation pour la consciousness | L'analyse argumentative des systemes complexes (notebooks 5-7) partage des concepts avec l'analyse IIT — identification de sous-ensembles causaux |
| [SymbolicAI/Planning/](../Planning/README.md) | Planification logique | Les logiques formelles (notebooks 2-3) sont la base de la planification automate PDDL |
| [ML/](../../ML/README.md) | Neuro-symbolic AI | L'intersection logiques + apprentissage : verifier les predictions de modeles neuronaux avec des contraintes logiques |
| [Search](../../Search/README.md) | SAT-based search | Le solving SAT (notebook 2) partage les memes algorithmes que la recherche par contraintes (CSP) |

## Licence

Les notebooks sont distribues sous licence MIT.
TweetyProject est sous licence LGPL 3.0.
