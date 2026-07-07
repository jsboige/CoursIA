# CoursIA

**Apprendre l'intelligence artificielle par la pratique, des fondements théoriques aux applications avancées.**

CoursIA est une collection de notebooks Jupyter interactifs couvrant l'ensemble du spectre de l'IA : algorithmes de recherche, résolution par contraintes, raisonnement formel, théorie des jeux, programmation probabiliste, machine learning, IA générative multimodale et trading algorithmique.

Les notebooks sont disponibles en Python, C# (.NET Interactive) et Lean 4. Beaucoup existent en **jumeaux C#/Python** — même concept, même pédagogie, deux écosystèmes — fruit d'une campagne de parité systématique. Chaque série suit une progression pédagogique, des concepts fondamentaux vers les applications avancées. La plupart fonctionnent en local sans configuration ; les clés API se concentrent sur GenAI, QuantConnect et les volets LLM de quelques séries (section Configuration).

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

---

> **Catalogue vivant** -- Pour l'inventaire exhaustif et à jour (comptes exacts par série, statut READY/DEMO, maturité PRODUCTION/BETA), consultez **[`COURSE_CATALOG.generated.md`](COURSE_CATALOG.generated.md)**. Ce catalogue est régénéré automatiquement chaque jour : il fait foi sur les chiffres et les statuts, ce README en donne la vue d'ensemble pédagogique.

## Commencer ici

Vous avez cloné le dépôt et vous ne savez pas par où commencer ?

1. **Choisissez votre niveau** : voyez les parcours recommandés plus bas pour un plan d'apprentissage guidé
2. **Explorez par série** : chaque série a son propre README détaillé avec une vue d'ensemble, la liste des notebooks, les prérequis et la durée estimée
3. **Documentation projet** : le répertoire [docs/](docs/README.md) centralise les règles de travail, l'infrastructure, les procédés récurrents et les guides d'apprentissage

## Cartographie rapide du dépôt

```
MyIA.AI.Notebooks/
  Search/          -> Algorithmes de recherche (BFS, A*, Métaheuristiques, CSPs) -- point d'entrée idéal pour débutants
  Sudoku/          -> Résolution multi-paradigme -- plusieurs approches pour un seul problème (C#, Python)
  ML/              -> Machine Learning (ML.NET, agents ADK)
  RL/              -> Reinforcement Learning (PPO, DQN, Stable Baselines3)
  Probas/          -> Programmation probabiliste (Infer.NET,PyMC, Pyro)
  GameTheory/      -> Théorie des jeux, équilibres de Nash, mechanism design, social choice
  IIT/             -> Information intégrée (Tononi, PyPhi) + banc ICT : trajectoires causales, du tri au LLM
  CaseStudies/     -> Études de cas interdisciplinaires
  SymbolicAI/      -> Raisonnement formel (Lean 4, Tweety, Semantic Web, Smart Contracts, Planners, Symbolic Learning)
  GenAI/           -> IA générative (Image, Audio, Video, Texte, Semantic Kernel, Vibe Coding) -- la plus grande série
  QuantConnect/    -> Trading algorithmique (notebooks pédagogiques + stratégies backtestées + pipeline ML)
  cross-series/    -> Applications transverses (matching-cv : data science multi-domaines)
```

---

## Parcours recommandés

**Débutant** -- Commencer par Search (Part 1), Sudoku, puis ML.Net. Ces séries ne nécessitent aucune clé API et introduisent les concepts fondamentaux.

**Intermédiaire** -- Explorer GameTheory, Probas, puis la partie Foundations de GenAI (Image, Texte). Ajoutez les techniques probabilistes et génératives à votre boîte à outils.

**Avancé** -- SymbolicAI (Lean, SmartContracts), QuantConnect (stratégies ML/DL), GenAI Video/Audio. Pour les étudiants à l'aise avec les fondamentaux qui veulent aller plus loin.

**Recherche** -- ML Training Pipeline (forecasting, GNN), SymbolicAI (preuves formelles Lean 4), Infer.NET (programmation probabiliste avancée), IIT/ICT (émergence causale, du tri au LLM).

Pour le détail notebook par notebook -- cinq parcours thématiques triés par maturité -- voir [PARCOURS.md](PARCOURS.md).

---

## Ce qu'on y trouve

Le dépôt couvre un spectre large de l'IA, des algorithmes classiques aux modèles génératifs les plus récents. Quelques points notables :

- **Multi-langages, multi-écosystèmes** : Python pour le machine learning et l'IA générative, C# pour l'écosystème Microsoft (ML.NET, Infer.NET, Semantic Kernel), Lean 4 pour la vérification formelle. Chaque langage est employé là où il excelle, pas par défaut.
- **Du fondamental à la recherche** : les séries partent des algorithmes de base (BFS, A*, backtracking) et vont jusqu'à des sujets de pointe -- transformers pour le forecasting financier, agents de preuve autonomes, intégration neuro-symbolique, deep learning multimodal.
- **Preuves formelles** : au-delà des exercices, les séries Lean et GameTheory mécanisent des théorèmes phares en Lean 4 -- théorème de sensibilité, théorème de Kochen-Specker, théorème du libre arbitre de Conway-Kochen, formalisations des théorèmes d'Arrow et de Sen -- avec des hommages aux mathématiques de Grothendieck et de Conway. L'ensemble forme une couche de plus de vingt lakes Lean 4 / Mathlib, avec un théorème-phare par famille branché sur les notebooks qui l'enseignent.
- **Une série de recherche vivante** : le banc ICT (extension de la théorie de l'information intégrée) mesure des gains d'émergence causale, de surprise et de compression sur des substrats de complexité croissante -- automates cellulaires, algorithmes de tri, jeu de la vie, et désormais les features SAE d'un vrai LLM -- jusqu'à un pont empirique en construction entre information intégrée et Global Workspace.
- **Un dépôt maintenu par des agents** : la maintenance quotidienne (exécution des notebooks, validation, catalogue régénéré chaque jour, revues croisées) est assurée par une flotte d'agents IA coordonnée multi-machines, sous revue humaine -- le dépôt est à la fois un cours d'IA et une démonstration grandeur nature d'ingénierie agentique ([détail](MyIA.AI.Notebooks/README.md#un-dépôt-vivant--maintenu-par-une-flotte-dagents)).
- **Données et marchés réels** : les notebooks QuantConnect s'appuient sur des données de marché réelles (yfinance, framework LEAN) ; le pipeline d'entraînement ML valide ses modèles par walk-forward strict et multi-seed sur un panier de cryptomonnaies.
- **IA générative déployable** : les notebooks GenAI fonctionnent au choix sur des APIs cloud (OpenAI, Anthropic) ou sur des modèles locaux servis par une infrastructure Docker GPU (Qwen, FLUX, ComfyUI, Whisper, MusicGen).
- **Agents et LLMs transverses** : assistants de preuve, agents de data science autonomes, planification pilotée par LLM, GraphRAG et boucles LLM-vérification symbolique tissent un fil rouge entre les séries.
- **Études de cas intégratrices** : des projets interdisciplinaires (diagnostic médical, planification oncologique) et des applications transverses combinent les techniques apprises en silos en livrables complets.

---

## Philosophie pédagogique

Chaque série est conçue pour être **self-contained** : un étudiant peut ouvrir n'importe quel notebook et suivre la progression sans prérequis externes, les explications étant intégrées au fil des cellules.

Les approches **multi-paradigmes** sont privilégiées : le Sudoku est résolu par backtracking, CSP, métaheuristiques et réseaux de neurones pour comparer les compromis. Les jeux sont formalisés en Python et en Lean 4. Cette diversité d'approches sur un même problème est au cœur de la démarche.

Les notebooks combinent **théorie et implémentation** : les concepts sont introduits progressivement, puis mis en pratique dans des cellules exécutables. La structure **exemple puis exercice** est systématique -- chaque notion est d'abord démontrée par un exemple résolu, puis reprise dans un exercice à compléter ; corrigés et squelettes cohabitent, et le notebook s'exécute de bout en bout même lorsque les exercices ne sont pas faits.

Enfin, **la priorité au local** : la majorité des séries tournent après un simple clone, sans clé API ni GPU. L'essentiel de la configuration se concentre sur GenAI (modèles génératifs) et QuantConnect (données de marché) -- de sorte que rien ne fasse barrage à la prise en main.

---

## Séries de notebooks

### Search -- Algorithmes de recherche et optimisation

Comment un ordinateur trouve-t-il son chemin dans un labyrinthe, ordonne-t-il un atelier, ou bat-il un humain au Puissance 4 ? Tout problème d'IA, du jeu de plateau à la planification logistique, se ramène à un même défi : explorer un espace de solutions possibles pour trouver la meilleure. Le fil conducteur de la série n'est pas l'accumulation d'algorithmes mais une seule compétence -- savoir **quand explorer, quand contraindre, et quand combiner les deux** -- construite autour de l'idée de **réduction de l'espace de recherche** : comment passer d'une énumération aveugle exponentielle à une résolution intelligemment guidée.

**[Fondements](MyIA.AI.Notebooks/Search/Part1-Foundations/README.md)** -- La progression part de la formalisation d'un problème en espace d'états (S, A, T, G), puis déroule les grands paradigmes : recherche non informée (BFS, DFS), recherche guidée par heuristique (A*, avec la garantie d'optimalité lorsque l'heuristique est admissible), optimisation locale (Hill Climbing, recuit simulé, Tabu), évolution (algorithmes génétiques), recherche adversariale dans les jeux (Minimax, Alpha-Beta) et enfin Monte Carlo Tree Search jusqu'à l'architecture AlphaGo (MCTS couplé à un DQN). S'y greffent des extensions de pointe : Dancing Links de Knuth pour la couverture exacte, programmation linéaire, automates symboliques à prédicats Z3, et un banc d'essai de métaheuristiques (essaim particulaire, colonies, recuit).

**[Programmation par contraintes](MyIA.AI.Notebooks/Search/Part2-CSP/README.md)** -- Un changement de paradigme : au lieu de concevoir un algorithme d'exploration, on déclare les contraintes du problème et le solveur trouve les solutions. On y apprend la propagation (AC-3, Forward Checking, MAC) qui élague l'espace avant même de chercher, les contraintes globales d'OR-Tools CP-SAT (AllDifferent, Cumulative), puis les usages industriels -- ordonnancement d'atelier, planification de projet, optimisation combinatoire (sac à dos, bin packing) -- et les frontières du domaine : contraintes souples, raisonnement temporel par algèbre d'Allen, CSP distribués entre agents, et surtout l'hybridation (CP+SAT, CP+ML, et génération de contraintes par LLM). C'est le pont vers SymbolicAI.

**[Applications](MyIA.AI.Notebooks/Search/Applications/README.md)** -- Chaque concept se mesure sur un problème réel, la plupart adaptés de projets étudiants : N-Queens, coloration de cartes, planning d'infirmiers, emploi du temps, démineur (CSP, probabilités et LLM combinés), solveur Wordle par théorie de l'information, nonogrammes, génération procédurale par Wave Function Collapse, Puissance 4 opposé à une batterie d'IA, voyageur de commerce et tournées de véhicules, optimisation de portefeuille et détection de bords par algorithmes génétiques (avec leurs pendants C# sur GeneticSharp), réglage d'hyperparamètres pour le Machine Learning. C'est le terrain où l'on compare, sur une même instance, méthode exacte et méthode approchée.

Cette série est aussi un carrefour : ses algorithmes irriguent Sudoku (DLX, automates), SymbolicAI (Z3, planification PDDL), GameTheory (Minimax, MCTS) et RL (MCTS et DQN), et ses métaheuristiques reviennent régler les hyperparamètres du Machine Learning.

Python et C# | [README détaillé](MyIA.AI.Notebooks/Search/README.md)

### Sudoku -- Résolution multi-paradigme

Et si l'on prenait un seul problème -- une grille de Sudoku -- pour le résoudre d'une dizaine de manières radicalement différentes ? L'objectif n'est pas de remplir des grilles (un solveur industriel le fait en quelques millisecondes) mais de transformer ce casse-tête en **banc d'essai contrôlé** : parce que le problème reste constant, on isole la seule variable qui change d'un notebook à l'autre -- le paradigme algorithmique -- et l'on rend visible l'arbitrage qui traverse toute l'IA, **garantie de solution contre performance contre généralisation**. Le Sudoku généralisé est NP-complet, de la même famille que SAT ou le voyageur de commerce. Et chaque technique existe en miroir C# et Python, pour comparer un paradigme sans changer de langage.

**Les méthodes exactes -- la garantie pour boussole** -- La première moitié de la série réunit les approches qui trouvent toujours la solution si elle existe. On part du backtracking, l'exploration récursive fondamentale, accéléré par l'heuristique MRV (choisir d'abord la case la plus contrainte) ; puis la couverture exacte de Knuth (Dancing Links), où une représentation de données astucieuse -- des listes doublement chaînées -- transforme les performances sans changer l'algorithme. Vient ensuite le grand basculement vers le déclaratif : au lieu de programmer l'exploration, on déclare les contraintes et le solveur cherche. C'est la programmation par contraintes -- propagation de Norvig (l'élagage seul suffit déjà à résoudre les grilles simples), CSP académique à la AIMA, coloration de graphe, et les solveurs industriels OR-Tools CP-SAT et Choco -- prolongée par l'IA symbolique : le solveur SMT Z3, les automates symboliques à prédicats, les diagrammes de décision binaires. Une étape singulière code treize techniques de déduction humaine (paires nues, candidats cachés, pointing) : le pont entre le raisonnement de la machine et celui du joueur.

**Les méthodes approchées -- échanger la garantie contre autre chose** -- L'autre moitié renonce délibérément à la garantie. Les métaheuristiques inspirées de la nature -- algorithme génétique, recuit simulé, essaim particulaire -- explorent l'espace intelligemment sans jamais promettre d'aboutir, mais souvent très vite. Puis le data-driven inverse la logique : au lieu de programmer la résolution, on l'apprend. Un modèle probabiliste (Infer.NET, NumPyro) place une distribution à posteriori sur les cases ; un réseau de neurones apprend, sur un très grand nombre de grilles résolues, les régularités qui mènent à une solution ; un LLM tente de raisonner sans algorithme explicite. Chacun illustre une limite autant qu'une force : le réseau a besoin d'énormément de données, le LLM trébuche sur le raisonnement logique pur.

**Le banc d'essai comparatif** -- Le notebook de synthèse confronte toutes les approches sur une échelle de difficulté croissante, du facile à l'expert, et c'est là que l'arbitrage paie. Deux enseignements ressortent, contre-intuitifs. D'abord, sur les modèles appris, le volume de données pèse plus lourd que la taille du modèle : un petit réseau bien nourri devance un gros réseau affamé. Ensuite -- et c'est le cœur de la série -- même entraîné jusqu'à une précision quasi parfaite, le réseau de neurones reste un **approximateur** : il peut se tromper, là où les solveurs exacts (Norvig, OR-Tools, Z3) garantissent la solution et sont souvent plus rapides en inference. La leçon n'est pas qu'une approche l'emporte, mais que le bon choix dépend du contexte -- garantie, vitesse, ou capacité à généraliser.

Sudoku est ainsi une coupe verticale du dépôt : un seul problème qui traverse **Search** (dont il instancie le backtracking, les métaheuristiques, DLX et le CSP), **SymbolicAI** (par le solveur SMT Z3), **Probas** (par l'inférence bayésienne) et **ML** (par le solveur neuronal et l'évaluation des LLM) -- et qui permet, fait rare, de comparer toutes ces familles sur un pied d'égalité.

C# et Python (OR-Tools, Z3, PyTorch) | [README détaillé](MyIA.AI.Notebooks/Sudoku/README.md)

### SymbolicAI -- Raisonnement formel

Une machine peut-elle raisonner -- non pas approximer une réponse plausible, mais déduire, prouver, justifier ? C'est le pari de l'IA symbolique, l'autre grande tradition de l'intelligence artificielle : représenter la connaissance sous forme de propositions, de règles et de structures logiques, puis en dériver mécaniquement de nouvelles conclusions. L'une des plus vastes séries du dépôt l'explore des systèmes experts des années 80 jusqu'aux assistants de preuve et aux agents LLM d'aujourd'hui. Le fil conducteur n'est pas une technologie mais une promesse : ce raisonnement est **explicite, vérifiable et explicable** -- exactement ce que l'apprentissage statistique seul ne garantit pas. Et là où les deux paradigmes se rencontrent se trouve le front actif de la recherche : le symbolique devient la couche de contrôle du neuronal -- détecter les incohérences d'un LLM, l'ancrer sur des faits, certifier la robustesse d'un réseau.

La progression suit cette logique : formaliser le raisonnement (Tweety), représenter la connaissance (Semantic Web), la prouver mécaniquement (Lean), l'appliquer à des problèmes concrets (Planners, Smart Contracts), puis la ponter vers le neuronal (Argument Analysis, Symbolic Learning). Chaque sous-série est autonome, mais ensemble elles dessinent une vision cohérente de l'IA symbolique moderne.

**[Tweety](MyIA.AI.Notebooks/SymbolicAI/Tweety/README.md) -- logiques formelles et argumentation computationnelle** -- Construite sur TweetyProject (une collection de bibliothèques Java pilotées depuis Python via JPype), cette sous-série réunit une dizaine de formalismes sous un même toit : logiques propositionnelle, du premier ordre, modale, de description et conditionnelle ; révision de croyances AGM -- comment un agent rationnel met à jour ses connaissances face à une information contradictoire ; et surtout l'argumentation computationnelle, son cœur. On y passe des cadres abstraits de Dung -- des arguments qui s'attaquent sans qu'on regarde leur contenu, et des sémantiques qui décident lesquels sont acceptables -- à l'argumentation structurée (ASPIC+, DeLP, ABA, ASP via Clingo), où les arguments ont une structure interne de prémisses et de règles defeasibles, jusqu'aux frameworks étendus, pondérés et probabilistes. La série se conclut sur les dialogues entre agents et la théorie du vote, passerelle directe vers la théorie des jeux. Tout réunir sous un même toit a un intérêt pédagogique précis : on expérimente d'une logique à l'autre sans réimplémenter chaque solveur. Les applications sont concrètes -- raisonnement juridique, aide à la décision médicale, négociation multi-agents -- et de plus en plus, contrôle des LLMs (détecter une incohérence, structurer un débat).

**[Semantic Web](MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/README.md) -- de RDF aux graphes de connaissances qui ancrent les LLMs** -- Le Web Sémantique est la promesse d'un Web où les machines comprennent le sens des données, pas seulement leur syntaxe. La sous-série en couvre le spectre complet, et la raison de cette complétude est que les briques s'articulent en couches : RDF définit les données (le triplet sujet-prédicat-objet, un fait élémentaire), SPARQL les interroge, RDFS et OWL ajoutent le raisonnement (hiérarchies de classes, restrictions, inférence automatique), SHACL valide leur qualité, JSON-LD ponte vers le Web des développeurs, RDF-Star ajoute la provenance, et les graphes de connaissances couplés aux LLMs ferment la boucle. C'est ce dernier maillon qui a relancé le domaine après des années de désillusion : GraphRAG a montré qu'un graphe RDF pouvait ancrer un LLM sur des faits vérifiables -- le Web Sémantique comme garde-fou de l'IA générative. Le parcours est délibérément bilingue : fondations en .NET avec dotNetRDF, standards modernes et IA en Python (rdflib, pySHACL, GraphRAG), chaque notebook C# disposant d'un miroir Python pour qui préfère un seul écosystème.

**[Lean](MyIA.AI.Notebooks/SymbolicAI/Lean/README.md) -- la preuve mécanique, où le noyau a toujours le dernier mot** -- Lean 4 est à la fois un langage de programmation fonctionnel et un assistant de preuve fondé sur la théorie des types dépendants. Son principe est radical : une preuve n'est acceptée que si le noyau du système la vérifie pas à pas -- pas de "ça semble correct", pas d'argument d'autorité. C'est exactement la garantie que cherche l'IA symbolique, poussée à son extrême. La progression part des fondations -- types dépendants, isomorphisme de Curry-Howard où une proposition EST un type et sa preuve un terme, mode tactique avec les briques de Mathlib -- puis bascule vers le front actif : l'assistance par LLM. LeanCopilot et AlphaProof suggèrent des tactiques, des agents autonomes explorent l'espace des preuves (APOLLO, attaques de problèmes d'Erdős), LeanDojo trace des bibliothèques entières pour entraîner ces modèles ; mais le partage des rôles ne change jamais -- le LLM propose, le noyau dispose. C'est l'illustration la plus pure du symbolique comme garde-fou du neuronal. La série applique enfin Lean à trois chantiers : vérifier formellement la robustesse d'un réseau de neurones (IBP, CROWN), porter des théorèmes de recherche récents (théorème de sensibilité de Huang, théorème de Kochen-Specker sur la contextualité quantique), et rendre hommage aux mathématiciens en formalisant leur œuvre -- le langage grothendieckien dans Mathlib, le jeu de la vie et le théorème du libre arbitre de Conway-Kochen. Nécessite WSL sous Windows.

**[Planners](MyIA.AI.Notebooks/SymbolicAI/Planners/README.md) -- non pas "que prédire ?" mais "que faire ?"** -- La planification automatique répond à une question que l'apprentissage ne pose pas : étant donné un état initial, un ensemble d'actions décrites par leurs préconditions et leurs effets, et un but, quelle séquence d'actions y mène ? C'est une technologie éprouvée -- elle pilote des robots, optimise la logistique, et a dirigé des engins spatiaux autonomes (le Remote Agent de Deep Space, les rovers martiens) -- standardisée par le langage PDDL, qui a fait naître tout un écosystème de solveurs comparables. La sous-série suit la montée en puissance habituelle : des fondations STRIPS et de l'explosion combinatoire de l'espace d'états -- celle qui rend les heuristiques indispensables -- on passe à la planification classique avec Fast-Downward, vainqueur des compétitions IPC, et ses heuristiques admissibles ; puis aux approches avancées -- programmation par contraintes avec OR-Tools, planification temporelle, réseaux de tâches hiérarchiques (HTN). La dernière étape ponte vers le neuro-symbolique : faire générer des plans par un LLM, comparer les solveurs derrière une interface unifiée, apprendre les heuristiques par réseaux de neurones. Le fil rouge rejoint celui de la série -- donner à un modèle de langage une capacité d'action vérifiable et orientée vers un but, plutôt qu'une suite d'actions plausible mais non garantie.

**[Smart Contracts](MyIA.AI.Notebooks/SymbolicAI/SmartContracts/README.md) -- quand le code fait foi, le rendre digne de confiance** -- Un smart contract est un programme qui s'exécute tout seul sur une blockchain : une fois déployé, son code fait loi, transfère de la valeur et applique ses règles sans intermédiaire ni retour en arrière. C'est sa force -- des écosystèmes entiers (DeFi, NFT, DAO) reposent dessus -- et son danger : un bug n'est pas un correctif à pousser le lendemain, c'est une faille immuable qui peut coûter des millions, comme l'a montré le hack de The DAO ou les exploits de ponts cross-chain. D'où le poids égal accordé ici au développement ET à la preuve qu'on peut s'y fier : tests, fuzzing, invariants, vérification formelle. Le parcours suit le fil de son titre -- on remonte aux primitives cryptographiques des cypherpunks (hachage, arbres de Merkle, preuve de travail, signatures) pour comprendre pourquoi une blockchain tient, on construit en Solidity (types, héritage, standards ERC, DeFi, gouvernance), on sécurise avec Foundry jusqu'à la vérification formelle, on apprend à protéger la vie privée sur une chaîne pourtant transparente (preuves à connaissance nulle, chiffrement homomorphe, vote vérifiable de bout en bout), avant d'élargir aux chaînes non-EVM (Vyper, XRP, Bitcoin Script, Move/Sui, Solana) et au déploiement réel sur testnet puis mainnet. Le point de contact avec le reste de la série est direct : la vérification formelle d'un contrat par solveur SMT et la preuve d'un théorème en Lean sont deux facettes de la même vérité -- la correction mathématique d'un programme.

**[Argument Analysis](MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/README.md) -- où s'arrête le LLM, où commence le vérificateur** -- Distinguer un argument valide d'un sophisme devient un acte critique dans une société saturée de discours générés à la chaîne : quand un LLM produit à la demande un texte plausible, la frontière entre persuasion légitime et manipulation rhétorique se brouille. Cette sous-série pose une question concrète -- peut-on prendre un texte argumentatif en entrée et en restituer une carte logique formelle, validée par un solveur SAT, avec détection systématique des sophismes connus ? La réponse assemble trois compétences : un agent LLM (orchestré par Semantic Kernel) extrait le tissu informel -- prémisses, conclusions, transitions ; un solveur logique (TweetyProject, via le même pont JPype que la sous-série Tweety) vérifie la cohérence des formalisations propositionnelles ; une couche agentique transforme la chaîne en pipeline reproductible. Tout l'enjeu pédagogique tient dans la jointure -- où le LLM, fiable pour extraire mais faible pour prouver, passe la main au vérificateur formel, et comment une boucle informel/formel converge vers un verdict. C'est l'incarnation appliquée du fil de la série : le symbolique comme garde-fou du neuronal, mis au service de la pensée critique, du fact-checking et de l'audit de contenus générés par IA.

**[Symbolic Learning](MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/README.md) -- apprendre de la connaissance, pas seulement des données** -- Comment un agent apprend-il à partir de ce qu'il sait déjà, et non d'un déluge d'exemples ? Cette sous-série, dans la lignée du chapitre 19 d'AIMA, est la contrepartie symbolique du machine learning statistique -- et elle adresse trois limites que ce dernier ne sait pas traiter : apprendre quand les données sont rares (l'apprentissage basé sur les explications, EBL, généralise depuis un seul exemple prouvé), produire des règles interprétables par un humain (une clause "SI fièvre ET toux ALORS infection" se lit, un réseau de cent millions de paramètres non), et exploiter une théorie du domaine déjà connue. Le parcours part de l'induction pure -- espaces de versions, élimination de candidats -- vers l'apprentissage guidé par la connaissance (EBL, apprentissage par la pertinence et treillis des déterminations) puis la programmation logique inductive (FOIL, résolution inverse, règles apprises sur des graphes de connaissances) et l'apprentissage actif d'automates (l'algorithme L* d'Angluin, où l'on apprend une machine à états en interrogeant un oracle). Sa phase finale est le point de jonction de toute la série SymbolicAI : T-norms différentiables et Logic Tensor Networks qui rendent la logique compatible avec la descente de gradient, fouille de règles sur graphes réels, boucles où un LLM extrait des règles que la vérification symbolique valide. Apprentissage symbolique et apprentissage statistique n'y sont pas rivaux mais complémentaires.

Vue d'ensemble, la série raconte une seule idée déclinée d'une sous-série à l'autre : reformuler une affirmation dans un cadre où elle devient vérifiable. Tweety formalise un débat en sémantiques d'acceptabilité, le Web Sémantique ancre des faits dans un graphe interrogeable, Lean réduit une preuve à ce que son noyau accepte ligne à ligne, les contrats se relisent à l'aune de leur vérification formelle, le planificateur confronte une intention dite en mots à un solveur qui tranche, l'argumentation et l'apprentissage symbolique rebouclent un LLM sur un vérificateur. Ce geste -- changer de représentation jusqu'à ce que la garantie devienne possible -- déborde SymbolicAI : on le retrouve dans les portages Lean de la théorie des jeux (existence de Nash, impossibilité d'Arrow, valeur de Shapley) et dans la théorie de la décision de Probas, partout où le dépôt fait passer un résultat du plausible au contrôlable. C'est la grille que propose [La mer qui monte](docs/grothendieckian-lens.md) : à mesure que l'IA bascule vers les grands modèles, la rendre digne de confiance, ce sera trouver le cadre où son affirmation se vérifie.

Python, Lean 4 et C# | [README détaillé](MyIA.AI.Notebooks/SymbolicAI/README.md)

### Probas -- Programmation probabiliste

Comment raisonner -- et surtout décider -- quand rien n'est certain ? Un diagnostic médical n'est jamais sûr à cent pour cent, un classement de joueurs dépend de performances variables, et les données arrivent toujours bruitées ou incomplètes. La programmation probabiliste refuse de répondre par un seul chiffre : elle calcule une *distribution* qui dit à quel point on croit à chaque issue possible. Mais une croyance ne sert à rien tant qu'on n'agit pas dessus -- et c'est là le fil conducteur de la série : passer d'une réponse unique à une distribution, puis d'une distribution à une décision. La théorie de la décision bayesienne, qui occupe toute la seconde moitié du parcours, est la charnière de ce mouvement, et le socle dont la théorie des jeux a besoin pour modéliser des agents rationnels.

**Deux écosystèmes, les mêmes modèles** -- La série repose sur une juxtaposition délibérée : chaque modèle est traité dans deux écosystèmes complémentaires qui couvrent, à eux deux, plusieurs familles d'algorithmes d'inférence. [Infer.NET](MyIA.AI.Notebooks/Probas/Infer/README.md) (Microsoft, C#) compile le modèle en graphe de facteurs et laisse choisir son moteur -- passage de messages (Expectation Propagation, Variational Message Passing) ou échantillonnage de Gibbs -- avec des résultats exacts sur les modèles conjugués et approchés ailleurs, le tout rapide et dont la structure se visualise. [PyMC](MyIA.AI.Notebooks/Probas/PyMC/README.md) (Python) reprend l'intégralité de ces modèles avec le MCMC moderne à base de gradient (le sampler NUTS), qui s'applique à presque tout modèle au prix d'un diagnostic de convergence outillé par ArviZ (R-hat, taille d'échantillon effective, divergences, trace plots). L'enjeu n'est donc pas de trancher entre exact et approché, ni même entre déterministe et aléatoire -- chaque famille a sa place -- mais d'apprendre, en voyant un même modèle résolu de plusieurs façons, quel moteur convient à quelle structure. Les modèles viennent d'applications réelles : réseaux bayésiens pour le diagnostic médical et l'explaining away, Item Response Theory (le moteur des tests adaptatifs comme le GMAT), TrueSkill (le classement bayésien des joueurs sur Xbox Live), LDA pour la découverte de thèmes, modèles de Markov cachés pour les régimes, agrégation de foules d'annotateurs bruités, recommandation assortie d'une barre d'incertitude.

**De l'inférence à la décision -- la théorie de l'utilité** -- À quoi bon une distribution si elle ne dicte aucune action ? La seconde moitié de la série franchit ce pas, et c'est son cœur. On part des axiomes de Von Neumann-Morgenstern qui fondent l'utilité espérée comme critère rationnel, on modélise l'aversion au risque (utilités CARA et CRRA, paradoxe de Saint-Petersbourg), on décide sur plusieurs critères à la fois (utilité multi-attributs, MAUT), on branche la décision sur l'inférence par les diagrammes d'influence, on chiffre la valeur d'une information avant de payer pour l'acquérir (EVPI, EVSI -- quand un test complémentaire est-il rentable ?), on se protège contre l'incertitude radicale (Minimax Regret), et l'on débouche sur la décision *séquentielle* : processus de décision markoviens, bandits, POMDP. Ce dernier maillon est une double passerelle -- vers le reinforcement learning d'un côté, et de l'autre vers la théorie des jeux, qui suppose précisément des agents maximisant leur utilité espérée. C'est pourquoi cette série précède GameTheory : l'utilité en est le prérequis.

**Jusqu'à la preuve formelle -- l'indice de Gittins en Lean** -- Le problème du bandit -- explorer pour apprendre, ou exploiter ce qu'on croit savoir ? -- admet une solution remarquable : l'indice de Gittins, qui ramène un problème séquentiel intimidant à un simple classement de bras. La série ne se contente pas de l'implémenter ; un volet en Lean 4 (avec Mathlib) cherche à le *prouver*. Les identités d'escompte géométrique qui fondent le calcul d'une valeur actualisée -- la somme escomptée d'une récompense constante -- y sont démontrées rigoureusement, vérifiées ligne à ligne par le noyau. Le théorème d'optimalité de Gittins lui-même, en revanche, est *énoncé* mais laissé à la frontière : sa preuve complète exigerait une formalisation des MDP et de l'équation de Bellman qui manque encore à Mathlib, et le notebook le documente comme tel. Cette distinction entre ce qui est prouvé et ce qui ne l'est pas encore est l'enseignement -- elle relie Probas à la série Lean de SymbolicAI, où le noyau a toujours le dernier mot.

Probas est un carrefour discret du dépôt. Sa théorie de la décision est le socle de **GameTheory** (jeux bayésiens, agents à utilité espérée) et la passerelle vers **RL** (ses MDP et ses bandits y deviennent apprentissage par renforcement) ; son inférence bayesienne nourrit le TP de régression de **ML** et la gestion du risque de **QuantConnect** (où un modèle de Markov caché génère des signaux de trading) ; ses fondements probabilistes sous-tendent le phi de l'**IIT** et le raisonnement incertain des ontologies de **SemanticWeb** ; et son pont vers Lean prolonge le fil de vérification formelle de **SymbolicAI**. Partout la même exigence : ne pas confondre une croyance avec une certitude, ni une prédiction avec une décision.

C# (Infer.NET), Python (PyMC, Pyro) et Lean 4 | [README détaillé](MyIA.AI.Notebooks/Probas/README.md)

### GameTheory -- Théorie des jeux

Comment des agents rationnels interagissent-ils quand le résultat de chacun dépend des choix de tous les autres ? Enchère, négociation, élection, partie de poker, guerre commerciale : partout des décideurs anticipent les décisions d'autrui avant d'arrêter les leurs. La théorie des jeux est le langage mathématique de cette interdépendance, et elle suppose d'emblée des agents qui maximisent une utilité espérée -- c'est pourquoi elle vient ici juste après Probas, dont la théorie de la décision lui sert de socle. Le fil conducteur de la série n'est pas un thème mais une *méthode* : tout résultat y est abordé deux fois, simulé en Python pour le *voir* à l'œuvre, puis prouvé en Lean 4 pour le *certifier*. Le notebook Python montre qu'un équilibre est plausible ; le notebook Lean montre qu'il est inévitable.

**Des jeux statiques aux frontières -- une montée en stratégie** -- Le fil principal suit la maturation historique de la discipline, en trois phases. On part des jeux statiques : matrices de gains et dominance, classification géométrique des jeux deux-contre-deux (la table périodique de Robinson-Goforth), équilibre de Nash pur et mixte par l'algorithme de Lemke-Howson, théorème minimax et sa dualité avec la programmation linéaire, et le tournoi d'Axelrod où la coopération finit par émerger de l'égoïsme répété. La deuxième phase introduit le temps et l'incertitude : formes extensives et arbres de jeu, jeux combinatoires (Nim, théorème de Sprague-Grundy), induction arrière et avant, menaces crédibles et équilibre parfait en sous-jeux, puis jeux bayésiens et jeux de réputation, où l'on raisonne sur les croyances et le signaling. La troisième ouvre les frontières contemporaines : la Counterfactual Regret Minimization -- le moteur des IA de poker Libratus et Pluribus -- les jeux différentiels à la Stackelberg, la théorie coopérative (valeur de Shapley, Core), le design de mécanismes (principe de révélation, enchères VCG), et enfin l'apprentissage multi-agent (NFSP, PSRO, AlphaZero) qui referme la boucle vers le reinforcement learning.

**Simuler, puis prouver -- la dualité Python/Lean** -- À côté du fil principal court un fil de formalisation : les grands théorèmes ne sont pas seulement illustrés, ils sont démontrés dans l'assistant de preuve Lean 4. L'existence d'un équilibre de Nash y est établie via les points fixes de Brouwer et Kakutani ; les jeux combinatoires reposent sur la structure PGame de Mathlib ; la valeur de Shapley est reconstruite à partir de ses axiomes. Plusieurs projets Lake indépendants portent ce travail, et la série est explicite sur sa frontière : la valeur de Shapley comme le théorème d'Arrow sont prouvés sans aucun `sorry`, tandis que des résultats tels que la condition de Bondareva-Shapley ou le treillis de Gale-Shapley sont *énoncés* mais laissés ouverts, leur preuve complète excédant ce que Mathlib offre aujourd'hui. Cette frontière entre ce qui est certifié et ce qui ne l'est pas encore est exactement le fil rouge de vérification formelle partagé avec la série Lean de SymbolicAI.

**L'agrégation des préférences -- choix social et impossibilités** -- Une sous-série dédiée, [SocialChoice](MyIA.AI.Notebooks/GameTheory/SocialChoice/README.md), prolonge le bloc sur l'agrégation collective et l'éclaire sous trois angles à la fois. Le théorème d'impossibilité d'Arrow y apparaît contre-intuitif quand on le simule, inévitable quand on le prouve en Lean, et franchement insatisfiable quand on l'encode en problème SAT résolu par Z3 -- trois façons de saisir un même résultat. S'y ajoutent le paradoxe libéral de Sen, les méthodes de vote classiques (Condorcet, Borda, Copeland) et le modèle spatial de Downs. C'est le pont le plus direct vers la gouvernance on-chain étudiée dans SmartContracts, où un vote de DAO n'est qu'une règle d'agrégation soumise aux mêmes impossibilités.

Au-delà du tableau noir, ces résultats structurent l'économie numérique : les enchères VCG fondent la publicité en ligne de Google et Meta à l'échelle de milliards de transactions par jour, l'algorithme de Gale-Shapley affecte étudiants aux écoles et internes aux hôpitaux -- un mécanisme couronné par le prix Nobel d'économie 2012 -- et la Counterfactual Regret Minimization a permis aux machines de battre les meilleurs joueurs de poker. GameTheory est ainsi un carrefour : elle prolonge la théorie de la décision de **Probas** vers l'interaction stratégique, alimente le **RL** par son volet multi-agent, irrigue **SmartContracts** par le vote vérifiable et la gouvernance, et partage avec **SymbolicAI** l'exigence de la preuve vérifiée par la machine.

Python (Nashpy, OpenSpiel, Z3), C# et Lean 4 | [README détaillé](MyIA.AI.Notebooks/GameTheory/README.md)

### ML -- Machine Learning

Comment passe-t-on d'un tableur rempli de données à un modèle qui prédit, recommande ou anticipe ? Et ce savoir-faire change-t-il selon qu'on code en C# ou en Python ? La série répond par la négative : les concepts du Machine Learning -- features, entraînement, évaluation, généralisation -- sont **invariants**, seuls les outils et le degré d'automatisation diffèrent. Le fil conducteur est justement ce déplacement : *qui* tient le pipeline ? Vous à la main, puis l'AutoML, puis un agent LLM autonome -- la constante étant, à chaque étage, une évaluation qui distingue un modèle qui marche d'un modèle qu'on comprend.

**[ML.NET](MyIA.AI.Notebooks/ML/ML.Net/README.md) -- le Machine Learning sans quitter l'écosystème .NET** -- Le premier volet construit le pipeline complet en C# : point d'entrée `MLContext`, structure colonnaire `IDataView`, feature engineering (encodage, normalisation, concaténation), puis l'entraînement (SDCA, LightGBM, et l'AutoML qui cherche seul l'algorithme et ses hyperparamètres). Vient ensuite l'étape la plus importante -- l'évaluation rigoureuse par validation croisée et l'explication des prédictions (Permutation Feature Importance) -- avant les sujets de production : prévision de séries temporelles par analyse spectrale (SSA), interopérabilité ONNX qui sert des modèles entraînés ailleurs (scikit-learn, PyTorch, jusqu'à BERT ou Whisper) directement dans une application .NET, et systèmes de recommandation par factorisation matricielle. Le TP capstone marie ML.NET et la régression bayésienne d'Infer.NET pour prédire non plus seulement une valeur, mais sa plage de confiance -- pont direct vers Probas.

**[Data Science avec agents](MyIA.AI.Notebooks/ML/DataScienceWithAgents/README.md) (Python)** -- Le second volet part des fondations (NumPy, Pandas, scikit-learn) puis bascule vers un changement de paradigme : non plus *écrire* le code d'analyse, mais *orchestrer* des agents LLM qui le produisent et l'exécutent. Le sous-track LangChain construit l'agent unique outillé -- interroger un DataFrame, nettoyer un jeu de données, parser des appels d'offres, scorer des candidatures. Le sous-track Google ADK monte en puissance vers les systèmes multi-agents : boucles planner-coder, framework DS-STAR pour une data science autonome, MLE-STAR jusqu'à concourir sur Kaggle, et le déploiement cloud (BigQuery, BQML). Tout est multi-provider -- Gemini, OpenAI ou un vLLM local au choix -- pour ne dépendre d'aucun fournisseur unique. L'enjeu pédagogique dépasse la technique : comprendre *quand* un agent accélère réellement l'analyse, et *comment* l'encadrer.

Cette série irrigue le reste du dépôt par sa démarche d'évaluation : on la retrouve dans QuantConnect (modèles prédictifs de trading), RL (mêmes gradients, mêmes réseaux, même méfiance du surapprentissage) et Probas (l'inférence bayésienne du TP) ; son réglage d'hyperparamètres rejoint les métaheuristiques de Search ; et ses agents LLM reposent sur les modèles couverts par GenAI -- où les modèles ONNX de ML.NET servent justement à déployer BERT et Whisper.

C# et Python | [README détaillé](MyIA.AI.Notebooks/ML/README.md)

### GenAI -- IA Generative

Comment générer une image à partir d'une phrase, faire parler une machine, composer un fond musical, animer une vidéo, ou brancher un LLM sur ses propres outils ? La plus grande série du dépôt explore l'IA générative dans toutes ses modalités. Son fil conducteur n'est pas l'accumulation d'APIs : c'est apprendre à **choisir** entre un modèle cloud (DALL-E, GPT-5, Whisper) et un modèle open-source auto-hébergé (FLUX, Stable Diffusion, Qwen, MusicGen) selon le coût, le contrôle, le débit et la sensibilité des données, puis à **combiner** ces briques dans des pipelines qui tiennent en production. Tout commence par [`00-GenAI-Environment`](MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/README.md), le passage obligé qui configure clés API, services Docker et validation.

Chaque modalité (Image, Audio, Video) suit la même montée en quatre niveaux -- Foundation (premiers appels d'API), Advanced (modèles locaux sur GPU, édition fine), Orchestration (workflows multi-modèles) et Applications (cas d'usage concrets) -- et chacune se structure autour d'un fil rouge concret à construire de bout en bout.

**[Image](MyIA.AI.Notebooks/GenAI/Image/README.md)** -- De DALL-E 3 et GPT-5 en cloud jusqu'aux modèles auto-hébergés (FLUX, Stable Diffusion 3.5, Qwen Image Edit, Z-Image/Lumina) orchestrés via ComfyUI. On y apprend à éditer plutôt que régénérer (inpainting, ControlNet), à composer des graphes de nœuds reproductibles, et à gérer la VRAM (quantizations INT4/FP8). Fil rouge : un générateur de visuels pédagogiques.

**[Audio](MyIA.AI.Notebooks/GenAI/Audio/README.md)** -- La chaîne vocale complète : transcription (Whisper), synthèse (OpenAI TTS, Kokoro, Chatterbox), clonage de voix (XTTS), génération musicale (MusicGen, YuE, ACE-Step), séparation de sources (Demucs) et TTS expressif à tags prosodiques. Fil rouge : un podcast entièrement généré, voix clonée et fond musical compris.

**[Video](MyIA.AI.Notebooks/GenAI/Video/README.md)** -- La modalité la plus exigeante : compréhension de séquences (GPT-5, Qwen-VL), génération de mouvement (HunyuanVideo, LTX-Video, Wan, Stable Video Diffusion), super-résolution et interpolation (Real-ESRGAN, RIFE). Fil rouge : transformer un script texte en vidéo pédagogique animée.

**[Texte](MyIA.AI.Notebooks/GenAI/Texte/README.md)** -- Le socle de tout le reste : prompt engineering, structured outputs (JSON Schema, Pydantic), function calling, RAG moderne, code interpreter, modèles de raisonnement (o-series, GPT-5 thinking), patterns de production, et déploiement de LLMs locaux (vLLM, quantization AWQ/GPTQ).

**[Semantic Kernel](MyIA.AI.Notebooks/GenAI/SemanticKernel/README.md)** -- Le SDK d'orchestration agentique de Microsoft, en Python et en C#/.NET Interactive : plugins, agents, filtres, vector stores, Process Framework, multimodalité et MCP. Démonstrateur phare : un NotebookMaker à trois agents (Admin, Coder, Reviewer) qui génère lui-même des notebooks pédagogiques.

**Spécialisation des modèles** -- Au-delà de l'usage, on entraîne : [FineTuning](MyIA.AI.Notebooks/GenAI/FineTuning/README.md) (LoRA, QLoRA, SFT, DPO) pour adapter un modèle sans tout ré-entraîner, et [PostTraining](MyIA.AI.Notebooks/GenAI/PostTraining/README.md) pour les techniques d'alignement de pointe (RLHF, DPO, GRPO, RLVR).

**Industrialisation** -- Les applications GenAI se testent : la série [Playwright-OWUI](MyIA.AI.Notebooks/GenAI/Open-WebUI/Playwright-OWUI/README.md) écrit des tests de bout en bout sur Open WebUI (navigation, streaming, RAG, outils MCP, CI/CD), pour passer de la démonstration jouet au produit déployable.

**[Vibe-Coding](MyIA.AI.Notebooks/GenAI/Vibe-Coding/README.md)** -- Le développement assisté par agents IA, devenu compétence centrale : ateliers progressifs sur Claude Code et Roo Code, plus une introduction aux agents autonomes (Claw-Systems), de la découverte à l'automatisation avancée (skills, sous-agents, MCP, hooks).

Tout converge dans un fil rouge transverse : le **Texte** structure un script, l'**Image** l'illustre, l'**Audio** le narre, la **Video** l'assemble, et **Semantic Kernel** orchestre l'ensemble en agents autonomes -- c'est ce parcours d'intégration qui distingue une demo d'un produit déployable.

Python | [README détaillé](MyIA.AI.Notebooks/GenAI/README.md)

### QuantConnect -- Trading algorithmique

Peut-on appliquer l'IA aux marchés financiers -- et comment savoir si une stratégie *marche* vraiment, plutôt que d'avoir simplement eu de la chance sur un historique ? Le trading algorithmique génère aujourd'hui plus de la moitié des volumes échangés, et cette série -- l'une des plus vastes du dépôt -- apprend à construire, backtester et déployer ses propres stratégies sur le framework open-source **LEAN** de QuantConnect, utilisé par des milliers de quants professionnels. Son fil conducteur n'est pas la course au rendement : c'est la **discipline d'évaluation** qui sépare un edge réel d'un mirage de backtest -- validation hors échantillon, walk-forward, répétition multi-graine, coûts de transaction réels, tests de significativité. Tout se passe en backtest et paper trading, sur le cloud QuantConnect (free tier), sans capital ni installation locale. Le livre de référence est *Hands-On AI Trading*, de Jared Broad, fondateur de QuantConnect.

**[Le cours](MyIA.AI.Notebooks/QuantConnect/Python/README.md) -- des fondations LEAN à l'IA de pointe** -- Le parcours pédagogique monte en huit phases et impose de maîtriser l'écosystème avant tout modèle : architecture LEAN et cycle de vie d'un algorithme, gestion des données, sélection d'univers, classes d'actifs (actions, options, futures, forex), types d'ordres et risk management, puis l'Algorithm Framework modulaire (Alpha, Portfolio Construction, Execution, Risk) qui rend les stratégies scalables. Vient seulement ensuite l'IA : données alternatives et analyse de sentiment, machine learning classique (Random Forest, XGBoost), deep learning pour séries temporelles (LSTM, Transformers, autoencodeurs), et enfin reinforcement learning, LLMs employés comme générateurs de signaux, détection de régime de marché et déploiement live. Chaque notebook s'exécute sur le cloud, avec des contournements documentés pour rester dans le free tier.

**[Les stratégies](MyIA.AI.Notebooks/QuantConnect/projects/README.md) -- ce qui survit au backtest réaliste** -- Un large catalogue de stratégies prêtes à backtester accompagne le cours, du momentum multi-actifs et des facteurs Fama-French jusqu'aux options couvertes, au mean reversion et aux approches ML/DL/RL. Leur singularité pédagogique tient en un point : les performances varient *volontairement*. Quelques stratégies dominent durablement, beaucoup ne battent leur indice que dans certains régimes, quelques-unes perdent -- et c'est précisément l'enseignement. Le suivi de tendance survit aux longues périodes ; un croisement de moyennes brillant sur backtest court s'effondre en hors-échantillon, démonstration concrète du danger du surapprentissage ; des composites censés cumuler les défenses font parfois moins bien que leurs briques isolées. Chaque stratégie vient avec son code source, son notebook de recherche standalone (yfinance/pandas) et ses métriques vérifiées sur le cloud.

**[Le pipeline d'entraînement ML](MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/README.md) -- séparer l'edge du hasard** -- Un pipeline complet entraîne et évalue des modèles de forecasting financier : LSTM, Transformer, PatchTST, iTransformer, Mamba, réseaux de neurones sur graphes, Decision Transformer et mélanges d'experts, plus l'évaluation zero-shot de modèles foundation (Chronos-Bolt, Kronos) et une série systématique de modèles de volatilité (HAR, GARCH, HEAVY, Markov-switching). Mais l'architecture n'est pas le coeur du sujet : la valeur tient au protocole de validation, intentionnellement sévère -- walk-forward expansif à plusieurs plis, répétition sur plusieurs graines, test de Diebold-Mariano pour la significativité statistique, univers expurgé des mégacaps technologiques pour éviter le biais de survie, coûts de transaction appliqués. Le verdict est tranché -- BEATS, NO BEATS ou INCONCLUSIVE -- et la majorité des étages testés sont rejetés, résultats négatifs documentés au même titre que les succès. Un résultat marquant en ressort : les modèles qui *classent une action* (acheter, tenir, vendre) battent ceux qui *prédisent un rendement*, parce que la traduction d'une prévision en position détruit le signal via les coûts et la discrétisation. L'entraînement GPU y est thermalement protégé pour tourner sur du matériel réel.

**[Le cours partenaire](MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/README.md) -- de l'exercice au déploiement** -- Un volet dédié, sponsorisé par Jared Broad (fondateur de QuantConnect) via le palier Trading Firm, propose une progression opérationnelle : des templates gradués (débutant : croisement EMA sur crypto ; intermédiaire : ranking momentum avec Algorithm Framework ; avancé : RandomForest sur BTC avec ré-entraînement mensuel), des exemples d'instructeur validés par des backtests réels, et des notebooks de recherche QuantBook qui matérialisent le workflow canonique du quant -- *idée, recherche, backtest, déploiement*. Plusieurs stratégies déployées sur le cloud sont directement issues des modèles retenus par le pipeline ML, bouclant la chaîne de la recherche à la production.

Cette série est le terrain où convergent les autres : les modèles prédictifs de **ML** s'y appliquent à des données de marché réelles, **RL** y prolonge ses mêmes gradients et sa même méfiance du surapprentissage, **Probas** y nourrit la gestion bayésienne du risque, **Search** y rejoint l'optimisation d'hyperparamètres, et **GenAI** y branche ses LLMs sur l'analyse de sentiment. Surtout, la discipline d'évaluation qu'elle exige -- préférer un "NO BEATS" vérifié à un "prometteur" sans preuve -- est exactement celle que réclame la série ML : ici, elle a le marché pour juge.

Python | [README détaillé](MyIA.AI.Notebooks/QuantConnect/README.md) | [Strategies](MyIA.AI.Notebooks/QuantConnect/projects/README.md)

### RL -- Apprentissage par renforcement

Comment apprendre à décider quand personne ne fournit la bonne réponse ? Là où l'apprentissage supervisé prédit à partir d'exemples étiquetés et l'apprentissage non supervisé dégage des structures, le renforcement **agit** : un agent choisit une action, observe la récompense ou la pénalité que lui renvoie son environnement, et corrige sa stratégie à l'essai et à l'erreur. C'est le paradigme derrière AlphaGo, la marche des robots et les moteurs de recommandation. Le fil conducteur de la série est un pari pédagogique assumé -- *agir d'abord, comprendre ensuite* : on entraîne un agent fonctionnel en quelques lignes avec un framework industriel, puis on réimplémente les mêmes algorithmes à la main pour voir ce qui tourne sous le capot.

**Le framework d'abord -- un agent qui marche en quelques lignes** -- Le point d'entrée est **Stable Baselines3** : on entraîne un agent PPO à équilibrer un bâton (CartPole) et on visualise sa progression avant d'avoir écrit la moindre équation. La prise en main s'enrichit ensuite des outils de production -- wrappers pour reconfigurer un environnement, callbacks pour monitorer et sauvegarder, multiprocessing pour accélérer -- puis franchit un saut qualitatif avec les tâches à objectif (goal-conditioned RL) et l'astuce HER, qui réinterprète les échecs comme des succès : on passe d'équilibrer un bâton à garer une voiture. L'intuition concrète précède la théorie, jamais l'inverse.

**Les maths sous le capot -- réimplémenter pour comprendre** -- Le second temps quitte le framework et reconstruit tout depuis zéro. On commence par la question fondatrice -- explorer de nouvelles options ou exploiter ce qui marche déjà -- sur les bandits manchots (epsilon-greedy, Thompson Sampling, regret cumulé). Vient ensuite la formalisation : processus de décision markovien, équation de Bellman, value et policy iteration, Q-Learning tabulaire. Puis le passage à l'échelle par les réseaux de neurones, en PyTorch pur et par paliers : DQN et REINFORCE, l'architecture acteur-critique (A2C), PPO et son surrogate clippé avec GAE, enfin SAC et le cadre maximum d'entropie pour les actions continues. Chaque algorithme éclaire un compromis -- on-policy contre off-policy, value-based contre policy-based, biais contre variance.

**Plusieurs agents qui apprennent -- du jeu solitaire à l'interaction** -- La série se clôt sur le multi-agent : plusieurs agents qui apprennent simultanément, coopèrent ou s'affrontent. Avec PettingZoo et l'Independent Q-Learning, un agent affronte sa propre copie en self-play sur un jeu à somme nulle -- la même situation que la théorie des jeux, mais où l'équilibre est *appris* plutôt que calculé.

Ce dernier pas ouvre la porte des séries voisines. Le multi-agent prolonge directement **GameTheory** -- équilibre de Nash appris au lieu d'être démontré -- tandis que les MDP généralisent les processus décisionnels bayésiens de **Probas**, dont la théorie de l'utilité fournit le socle. Le renforcement partage avec **ML** ses outils (PyTorch, gradients) et avec **Search** sa parenté entre value iteration et exploration d'un espace d'états ; il s'incarne enfin sur données réelles en **QuantConnect**, où acheter et vendre deviennent des actions et le profit une récompense. Le contraste feed-forward contre récurrent qui structure ses architectures rejoint même la question soulevée par **IIT**.

Python | [README détaillé](MyIA.AI.Notebooks/RL/README.md)

### IIT -- Théorie de l'Information Intégrée

La conscience est-elle mesurable ? La théorie de l'information intégrée, proposée par Giulio Tononi, répond oui : un système est conscient dans la mesure où il intègre de l'information de manière irréductible, et cette quantité porte un nom et une valeur calculable -- **Phi**. C'est la série la plus spéculative du dépôt, et l'une de celles qui ont le plus grandi : partie d'un noyau PyPhi (la bibliothèque de référence du laboratoire Tononi), elle s'est prolongée en un véritable programme de recherche interne, la série **ICT**. Son fil conducteur reste le même : calculer rigoureusement des mesures candidates de l'intégration et de l'émergence, tout en gardant un esprit critique sur ce qu'elles signifient vraiment.

**Calculer Phi -- du réseau causal à la géométrie de l'information** -- On part de circuits binaires élémentaires : une matrice de transition décrit les règles d'évolution du système, et le calcul de Phi sur un petit réseau XOR rend concrète la notion d'intégration irréductible. La structure cause-effet révèle comment un système spécifie sa propre géométrie informationnelle. Un second temps déconstruit le calcul : partition d'information minimale (MIP) pour localiser le maillon faible, répertoires cause-effet, mécanismes maximalement irréductibles (MICE), et distinction entre le Phi du système entier et le phi d'un mécanisme isolé. L'extension à des réseaux plus grands fait surgir une explosion combinatoire qui rend le calcul exact intractable dès qu'on dépasse une poignée de noeuds -- d'où le coarse-graining comme stratégie d'approximation, et un aperçu des évolutions récentes vers IIT 4.0.

**De la mesure aux débats -- ce que Phi engage** -- L'IIT n'est pas qu'une spéculation : ses principes ont inspiré le Perturbational Complexity Index, une mesure clinique (stimulation magnétique transcrânienne plus EEG) qui distingue empiriquement les états conscients des états inconscients chez des patients non communicants. Elle s'oppose frontalement aux théories du Global Workspace dans des tests adversariaux sur données réelles. Et elle touche directement l'IA : un réseau purement feed-forward -- comme l'inférence d'un grand modèle de langage classique -- a un Phi nul, car l'information y transite sans boucle causale intégrée ; il calcule sans "être". Une critique publique retentissante (une lettre ouverte la qualifiant de pseudoscience) fait de l'IIT un cas d'école pour interroger les critères de scientificité d'une théorie de l'esprit.

**ICT -- des états aux trajectoires, jusqu'au LLM** -- L'extension [ICT](MyIA.AI.Notebooks/IIT/ICT-Series/README.md) (*Integrated Causal Trajectories*), développée dans le dépôt même, déplace la question : au lieu de mesurer l'intégration d'un *état*, elle mesure ce qu'une **trajectoire** de système fait émerger causalement au fil du temps. Sa batterie réunit trois gains complémentaires -- émergence causale (le niveau macro prédit-il mieux que le micro, à la Hoel), surprise transitionnelle (énergie libre) et compression (MDL) -- chacun crédité seulement s'il dépasse à la fois un mélange aléatoire et un modèle-contrôle. Ce banc d'essai s'applique à des substrats de complexité croissante : automates cellulaires élémentaires, algorithmes de tri vus comme morphogenèse, jeu de la vie, et désormais un **transformer réel** dont les activations, lues à travers un autoencodeur parcimonieux (SAE), deviennent des trajectoires d'états discrets mesurables. L'étape en cours vise la confrontation empirique des deux grandes théories rivales : détecter dans le même substrat les signatures du Global Workspace (broadcast, ignition) et vérifier si elles co-localisent avec les pics de complexité intégrée -- un pont falsifiable entre IIT et GWT, où un résultat négatif (dissociation) serait tout aussi instructif qu'une convergence.

Cette série dialogue avec **Probas** et **GameTheory**, dont elle partage les concepts de causalité et d'interaction, et avec **RL** : la distinction feed-forward contre récurrent, qui annule ou non Phi, éclaire le choix d'architecture d'un agent. L'ICT rejoint le fil rouge **causalité** du dépôt -- le même opérateur `do(·)` de Pearl s'instancie dans Tweety (symbolique), Infer.NET (message passing), PyMC (MCMC) et ICT (théorie de l'information). Le constat qu'un modèle de langage feed-forward a un Phi nul prolonge enfin les discussions sur la conscience artificielle qui traversent **GenAI** -- que l'ICT reprend désormais par la mesure plutôt que par le débat.

Python | [README détaillé](MyIA.AI.Notebooks/IIT/README.md)

### CaseStudies -- Études de cas interdisciplinaires

Que se passe-t-il quand on cesse d'étudier les techniques en silos ? L'IA réelle ne fonctionne presque jamais avec un seul paradigme : un assistant de diagnostic combine des règles symboliques, des modèles probabilistes, de la recherche heuristique et des contraintes formelles. Cette série, conçue comme un devoir intégrateur de fin de cycle, prend deux problèmes métier -- un diagnostic médical, une planification oncologique -- et y compose plusieurs solveurs en un seul système décisionnel cohérent. Son fil conducteur est l'architecture hybride en couches, et l'idée que l'**ordre de composition** importe autant que les briques elles-mêmes.

**Composer les paradigmes en cascade -- l'architecture hybride** -- Chaque projet empile cinq couches : des connaissances métier (ontologies OWL, règles), un filtre de contraintes dures (CSP, SMT, OR-Tools), une modélisation de l'incertitude (bayésien, Pyro, Infer.NET), une optimisation (recherche A-star, algorithme génétique, et au-delà le renforcement) et une décision finale expliquée. On filtre avant d'optimiser, on modélise l'aléatoire avant de valider sous contraintes : le [Diagnostic Medical](MyIA.AI.Notebooks/CaseStudies/Diagnostic-Medical/README.md) articule recherche informée, algorithme génétique et validation par solveur Z3 ; l'[Oncology Planning](MyIA.AI.Notebooks/CaseStudies/Oncology-Planning/README.md) marie ontologie, planification CP-SAT et inférence probabiliste. Aucune couche ne suffit seule, et c'est tout l'enseignement.

**Le jumeau numérique -- un patient simulé pour décider sans risque** -- Les deux projets reposent sur un modèle de patient simulé : un objet logiciel qui représente un état clinique et réagit aux interventions proposées. Ce pattern de jumeau numérique, devenu central en santé numérique comme en industrie, permet de tester des scénarios de traitement sans toucher au patient réel. La pédagogie privilégie l'autonomie : chaque projet fournit un template étudiant exécutable de bout en bout -- y compris lorsque les exercices ne sont pas complétés -- et une solution de référence pour s'autoévaluer.

Le choix du médical est pédagogique, pas exclusif : la même architecture en couches se transpose telle quelle à la finance (jumeau de marché, contraintes réglementaires, signaux probabilistes), à la logistique ou à la maintenance prédictive. C'est le devoir qui ferme la boucle du cursus, en convoquant simultanément **Search**, **SymbolicAI**, **Probas**, **Planners**, **SemanticWeb** et **RL** autour d'une seule question réelle.

Python | [README détaillé](MyIA.AI.Notebooks/CaseStudies/README.md)

### cross-series -- Applications transverses

Et après le notebook ? Le répertoire `cross-series/` rassemble des applications complètes -- code structuré, tests, interface -- où les techniques vues séparément se rejoignent dans un livrable autonome et déployable. L'exemple de référence, [`matching-cv`](MyIA.AI.Notebooks/cross-series/matching-cv/README.md), est une application web Flask qui confronte trois façons d'apparier un CV à une offre d'emploi : l'appariement stable de Gale-Shapley (rencontré en **GameTheory** et **SymbolicAI**), la similarité sémantique par plongements et le RAG hybride (issus de **GenAI**), avec la recherche en arrière-plan. Comparer ces approches sur le même problème, c'est mesurer ce que chaque paradigme apporte vraiment -- la même démarche que le banc d'essai du **Sudoku**, transposée à une application réelle. Non pas une collection d'outils juxtaposés, mais des manières complémentaires de résoudre, faites pour se combiner.

[README détaillé](MyIA.AI.Notebooks/cross-series/README.md)

---

## Structure du dépôt

```text
CoursIA/
  MyIA.AI.Notebooks/          Notebooks interactifs, organisés par série
    Search/                    Algorithmes de recherche (Python, C#)
    Sudoku/                    Résolution multi-paradigme (Python, C#)
    SymbolicAI/                IA symbolique (Python, Lean 4, C#)
      Tweety/ SemanticWeb/ Lean/ Planners/ SmartContracts/ Argument_Analysis/ SymbolicLearning/
    Probas/                    Programmation probabiliste (C#, Python)
    GameTheory/                Théorie des jeux (Python, Lean 4)
    ML/                        Machine Learning (C#, Python)
    RL/                        Reinforcement Learning (Python)
    GenAI/                     IA Générative (Python)
      Image/ Audio/ Video/ Texte/ SemanticKernel/ Vibe-Coding/
    QuantConnect/              Trading algorithmique (Python)
      Python/                  Notebooks pédagogiques
      projects/                Stratégies backtestées
      ML-Training-Pipeline/    Pipeline DL forecasting
      partner-course-quant-trading/ Projets étudiants
    CaseStudies/               Études de cas interdisciplinaires (Python)
    cross-series/              Applications transverses multi-domaines (Python)
    IIT/                       Information intégrée (Python)
    Config/                    Configuration API

  scripts/                     Validation, exécution, analyse
  docker-configurations/       Infrastructure Docker GPU
  GradeBookApp/                Notation étudiants
  MyIA.AI.Shared/              Bibliothèque C# partagée
  notebook-infrastructure/     Papermill + MCP maintenance
```

---

## Mise en route

### Prérequis

- Python 3.10+ avec pip
- .NET 9.0 SDK (pour notebooks C#)
- VS Code avec extensions Python, Jupyter, .NET Interactive
- WSL (pour Lean et certains outils SymbolicAI)
- Docker + GPU (optionnel, pour GenAI avancé)

### Installation rapide

```bash
# 1. Cloner
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA

# 2. Environnement Python (un venv suffit pour la majorité des séries)
python -m venv venv
venv\Scripts\activate          # Windows ; sous Linux/WSL : source venv/bin/activate
pip install jupyter ipykernel python-dotenv

# 3. Kernel Jupyter Python
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"

# 4. Kernel .NET Interactive (notebooks C#)
dotnet tool install --global Microsoft.dotnet-interactive
dotnet interactive jupyter install
dotnet restore MyIA.CoursIA.sln

# 5. Dépendances de la série visée (chaque série porte son requirements.txt)
pip install -r MyIA.AI.Notebooks/<Serie>/requirements.txt
```

Les clés API éventuelles se posent via les `.env.example` (section Configuration). Pour valider
ou exécuter un notebook, ne pas écrire de script ad-hoc : le dépôt fournit une CLI dédiée
(section Scripts et validation).

### Installation par série

La plupart des séries sont autonomes et s'ouvrent sur un **notebook de mise en route**
(Setup / Environment) qui installe les dépendances de la série et vérifie la chaîne d'outils :
c'est le point de départ recommandé. Pour les kernels, WSL et toolchains spécifiques, des
scripts de préparation dédiés accompagnent ces notebooks. Les séries sans notebook de setup
s'installent directement via leur `requirements.txt`.

| Série | Notebook de mise en route | Préparation dédiée |
|-------|---------------------------|--------------------|
| GenAI | `GenAI/00-GenAI-Environment/` (Environment-Setup, Docker-Services, API-Endpoints, Validation) | `requirements.txt` (+ `-audio` / `-video`) ; `00-GenAI-Environment/validate_auth.py` |
| GameTheory | `GameTheory/GameTheory-1-Setup.ipynb` | `scripts/setup_wsl_openspiel.sh`, `setup_wsl_lean4.sh`, `setup_lean4_kernel.ps1` |
| Sudoku | `Sudoku/Sudoku-0-Environment-Csharp.ipynb` | kernel .NET Interactive |
| Probas | `Probas/Infer/Infer-1-Setup.ipynb`, `Probas/PyMC/PyMC-1-Setup.ipynb` | `Infer/scripts/setup_environment.ps1` |
| QuantConnect | `QuantConnect/Python/QC-Py-01-Setup.ipynb` | `requirements.txt` |
| Lean | `SymbolicAI/Lean/Lean-1-Setup.ipynb` | `Lean/scripts/setup_wsl_python.sh`, `validate_lean_setup.py` |
| Planners | `SymbolicAI/Planners/00-Environment/Planners-0-Setup.ipynb` | `requirements.txt` ; `SymbolicAI/scripts/install_clingo.py` |
| SemanticWeb | `SymbolicAI/SemanticWeb/SW-1-CSharp-Setup.ipynb` | kernel .NET Interactive |
| SmartContracts | `SymbolicAI/SmartContracts/00-Foundations/SC-1-Setup-Foundry.ipynb`, `SC-2-Setup-Web3py.ipynb` | `setup_env.py`, `scripts/setup_wsl_smartcontracts.sh` |
| Tweety | `SymbolicAI/Tweety/Tweety-1-Setup.ipynb` | `tweety_init.py` (JDK auto-télécharge) |
| Argument Analysis | `SymbolicAI/Argument_Analysis/Argument_Analysis_UI_configuration.ipynb` | `install_jdk_portable.py` |
| IIT | `requirements.txt` | `scripts/setup_pyphi_env.ps1` |
| Search / RL / CaseStudies | `requirements.txt` | -- |
| cross-series | `requirements.txt` | `cross-series/matching-cv/scripts/install_deps.sh` |

Pour les séries qui exposent un `requirements.txt`, l'installation directe reste possible :

```bash
pip install -r MyIA.AI.Notebooks/<Serie>/requirements.txt
```

Les notebooks C# (ML.NET, Sudoku, SemanticWeb, Probas/Infer.NET) ne passent pas par pip :
ils s'appuient sur le kernel .NET Interactive et `dotnet restore` (section Mise en route).

---

## Configuration

Les séries Search, Sudoku, ML.Net, Probas (Infer.NET), Tweety, SemanticWeb et Planners fonctionnent sans aucune clé API. Les séries suivantes nécessitent une configuration :

| Série | Fichier | Variables requises |
|-------|---------|-------------------|
| GenAI | `GenAI/.env` | `OPENAI_API_KEY`, `ANTHROPIC_API_KEY` |
| Lean | `SymbolicAI/Lean/.env` | `OPENAI_API_KEY`, `GITHUB_TOKEN` |
| Argument Analysis | `SymbolicAI/Argument_Analysis/.env` | `OPENAI_API_KEY` |
| QuantConnect | `QuantConnect/.env` | `QC_USER_ID`, `QC_API_TOKEN` |
| C# Notebooks | `Config/settings.json` | `apikey`, `model` |
| Docker ComfyUI | `comfyui-qwen/.env` | `CIVITAI_TOKEN`, `HF_TOKEN` |

Chaque dossier contient un `.env.example` documentant les variables. Copier et éditer :

```bash
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
# Éditer le fichier .env avec vos clés
```

---

## Kernels Jupyter

| Kernel | Séries | Installation |
|--------|--------|--------------|
| `python3` | Tous les notebooks Python | `pip install ipykernel` |
| `.net-csharp` | Sudoku, Search, Probas, ML | `dotnet tool install -g Microsoft.dotnet-interactive` |
| `lean4` / `lean4-wsl` | Lean, GameTheory (notebooks Lean) | Via `elan` + wrapper WSL |

Limitations connues : les notebooks C# avec `#!import` nécessitent une exécution cellule par cellule (incompatible Papermill). Lean 4 requiert WSL sous Windows.

---

## Infrastructure Docker

Pour les notebooks GenAI avancés utilisant des modèles locaux (Qwen Image Edit, ComfyUI Video, etc.), une infrastructure Docker avec support GPU est fournie.

Services disponibles : Qwen Image Edit (~29 Go VRAM), ComfyUI Video (~12 Go), Stable Diffusion Forge (~10 Go), Whisper, MusicGen, Kokoro TTS, Demucs.

La pile s'orchestre via le CLI `genai.py` plutôt que des commandes `docker` lancées à la main :

```bash
cp docker-configurations/services/comfyui-qwen/.env.example docker-configurations/services/comfyui-qwen/.env
python scripts/genai-stack/genai.py docker status      # état des services
python scripts/genai-stack/genai.py docker start all   # démarrer
python scripts/genai-stack/genai.py docker stop all    # arrêter
python scripts/genai-stack/genai.py gpu                # vérifier la VRAM disponible
```

Configuration détaillée dans `docker-configurations/`.

---

## Scripts et validation

Règle de base : **toujours passer par ces scripts pour valider ou exécuter un notebook,
jamais par un script écrit pour l'occasion**. La CLI détecte le kernel depuis les métadonnées
du notebook (Python, .NET Interactive, Lean sous WSL).

| Script | Usage |
|--------|-------|
| `scripts/notebook_tools/notebook_tools.py` | CLI multi-series : `validate`, `execute`, `analyze`, `skeleton`, `check-env` |
| `scripts/notebook_tools/notebook_helpers.py` | Manipulation de notebooks, itération cellule par cellule |
| `scripts/genai-stack/genai.py` | Pile GenAI : `docker`, `validate`, `notebooks`, `gpu` |
| `scripts/smartcontracts/validate_sc_notebooks.py` | Validation dédiée Smart Contracts (`--quick`, `--execute --anvil`) |

```bash
# Validation de structure
python scripts/notebook_tools/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku

# Exécution (Papermill ; --cell-by-cell pour les notebooks .NET / Lean)
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/Search --cell-by-cell

# Vérification de l'environnement d'une famille
python scripts/notebook_tools/notebook_tools.py check-env GenAI

# Validation complète de la pile GenAI
python scripts/genai-stack/genai.py validate --full
```

Un workflow GitHub Actions valide automatiquement les notebooks à chaque pull request (format, syntaxe, exécution de base).

---

## Outils Claude Code

Le dépôt inclut une configuration Claude Code avec des agents spécialisés et des commandes slash pour la maintenance des notebooks.

**Commandes principales** : `/verify-notebooks`, `/enrich-notebooks`, `/cleanup-notebooks`, `/build-notebook`, `/execute-notebook`, `/validate-genai`, `/qc-iterative-improve`

**Agents spécialisés** : notebook-enricher, notebook-validator, notebook-executor, qc-strategy-analyzer, qc-strategy-improver, readme-updater, et d'autres.

Configuration dans `.claude/agents/` et `.claude/skills/`.

---

## Outils et dépendances externes

Les dépendances principales par série :

| Outil | Séries | Provenance |
|-------|--------|-----------|
| Z3 SMT Solver | Sudoku, Search, SymbolicAI | `requirements.txt` de la série |
| OR-Tools | Sudoku, Search, Planners | `requirements.txt` de la série |
| Tweety + JDK | Tweety, Argument_Analysis | JDK auto-télécharge ; reste dans `requirements.txt` |
| Lean 4 + Mathlib | Lean, GameTheory | `elan` (WSL) ; diagnostic via `validate_lean_setup.py` |
| OpenSpiel | GameTheory | `requirements.txt` GameTheory |
| Infer.NET | Probas | NuGet (kernel .NET Interactive) |
| PyPhi | IIT | `requirements.txt` IIT |

---

## Contribution

1. Fork le dépôt
2. Créer une branche (`git checkout -b feature/nouveau-notebook`)
3. Commit (`git commit -m 'Add: notebook sur les Transformers'`)
4. Push et ouvrir une Pull Request

Conventions : PEP 8 pour Python, conventions standard pour C#, pas d'emojis dans le code, documentation en français. Chaque famille de notebooks doit inclure un `.env.example` documentant les variables requises.

## Licence

Ce projet est sous licence MIT - voir [LICENSE](LICENSE).

---

Repository : [github.com/jsboige/CoursIA](https://github.com/jsboige/CoursIA)
