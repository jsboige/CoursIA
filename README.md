# CoursIA

**Apprendre l'intelligence artificielle par la pratique, des fondements théoriques aux applications avancées.**

CoursIA est un curriculum de notebooks Jupyter interactifs pour apprendre l'IA en la mettant en œuvre. On y part des algorithmes de recherche et des contraintes, puis on aborde le raisonnement formel, l'incertitude, la théorie des jeux, le machine learning, l'apprentissage par renforcement, l'IA générative et le trading algorithmique. Certaines séries vont jusqu'à la recherche : preuve mécanisée de théorèmes, évaluation rigoureuse de modèles et mesure de l'émergence causale dans leurs représentations internes.

Les notebooks utilisent Python, C# avec .NET Interactive et Lean 4. De nombreux concepts existent en **jumeaux C#/Python** : même problème et même progression, dans deux écosystèmes, afin de distinguer les idées de leur implémentation. Les parcours locaux sans clé ni GPU offrent une entrée immédiate ; les séries qui requièrent une API, le cloud, WSL ou une infrastructure GPU documentent leur environnement dès la mise en route.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

---

> **Catalogue vivant** -- Pour l'inventaire exhaustif (comptes par série, statut READY/DEMO, maturité PRODUCTION/BETA), consultez **[`COURSE_CATALOG.generated.md`](COURSE_CATALOG.generated.md)**. Généré par l'automatisation, ce catalogue porte les chiffres et les statuts ; ce README en donne la vue d'ensemble pédagogique.

## Commencer ici

Trois chemins permettent d'entrer dans le dépôt sans parcourir tout le catalogue :

1. **Suivre un parcours guidé** : [PARCOURS.md](PARCOURS.md) relie les notebooks en cinq itinéraires thématiques et indique leur maturité.
2. **Choisir une série** : chaque README de série présente son objectif, son ordre de lecture, ses prérequis et ses notebooks.
3. **Préparer l'environnement** : pour exécuter immédiatement, commencer par [Mise en route](#mise-en-route), puis ouvrir le notebook `Setup` ou `Environment` de la série choisie.

Le répertoire [docs/](docs/README.md) rassemble ensuite les références d'infrastructure, de validation et de contribution.

## Cartographie rapide du dépôt

```
MyIA.AI.Notebooks/
  Search/          -> Algorithmes de recherche (BFS, A*, Métaheuristiques, CSPs) -- point d'entrée idéal pour débutants
  Sudoku/          -> Résolution multi-paradigme -- plusieurs approches pour un seul problème (C#, Python)
  ML/              -> Machine Learning (ML.NET, agents ADK)
  RL/              -> Reinforcement Learning (du bandit au post-training des LLMs : DQN, PPO, SAC, GRPO, DPO)
  Probas/          -> Programmation probabiliste (Infer.NET, PyMC, Pyro) + théorie de la décision
  GameTheory/      -> Théorie des jeux, équilibres de Nash, mechanism design, social choice
  IIT/             -> Information intégrée (Tononi, PyPhi) + banc ICT : trajectoires causales, du tri au LLM
  CaseStudies/     -> Études de cas interdisciplinaires
  SymbolicAI/      -> Raisonnement formel (Lean 4, Tweety, Semantic Web, Smart Contracts, Planners, SMT, Argument Analysis, Symbolic Learning) -- la plus vaste série du dépôt
  GenAI/           -> IA générative (Image, Audio, Video, Texte, Semantic Kernel, Aspire, Vibe Coding) -- l'une des plus vastes séries
  QuantConnect/    -> Trading algorithmique (notebooks pédagogiques + stratégies backtestées + pipeline ML)
  cross-series/    -> Applications transverses (matching-cv, socle métadonnées, i18n)
```

Le dépôt rassemble les notebooks pédagogiques, leurs projets Lean 4 compagnons et un corpus de traduction structuré sous `MyIA.AI.Notebooks/`. Le [catalogue généré](COURSE_CATALOG.generated.md) fait foi sur les comptes et statuts par série ; les références Lean et de traduction documentent leurs propres mesures à jour.

---

## Parcours recommandés

**Démarrer sans service externe** -- Search introduit l'exploration et les heuristiques ; Sudoku permet ensuite de comparer plusieurs paradigmes sur un problème constant ; ML.NET transforme ces bases en pipeline d'apprentissage supervisé. Ce parcours fonctionne localement, sans clé API.

**Raisonner sous incertitude et en interaction** -- Probas apprend à représenter l'incertitude et à décider ; GameTheory ajoute des agents dont les choix dépendent les uns des autres ; RL montre comment ces stratégies peuvent être apprises par l'expérience.

**Construire une IA vérifiable** -- SymbolicAI relie logique, graphes de connaissances, planification, solveurs SMT et preuves Lean. Les études de cas réemploient ensuite ces briques dans des systèmes hybrides complets.

**Déployer des modèles et des agents** -- ML, GenAI et QuantConnect passent de l'entraînement à l'orchestration, au backtest et au déploiement. Selon le volet, une clé API, Docker, un GPU ou le cloud QuantConnect peut être nécessaire.

**Explorer les frontières de recherche** -- Les preuves formelles, le pipeline ML multi-seed, le post-training des LLMs et IIT/ICT proposent des résultats falsifiables, y compris des résultats négatifs documentés.

Pour les itinéraires notebook par notebook, leur maturité et leurs prérequis, voir [PARCOURS.md](PARCOURS.md).

---

## Ce qui distingue le curriculum

Le dépôt ne juxtapose pas seulement des technologies : il organise des comparaisons et des passages d'un paradigme à l'autre.

- **Plusieurs langages pour séparer le concept de l'outil** : Python porte le machine learning et l'IA générative ; C# ouvre ML.NET, Infer.NET et Semantic Kernel ; Lean 4 vérifie formellement des résultats. Les notebooks jumeaux rendent leurs différences observables sur un même problème.
- **Des garanties comparées, pas confondues** : une simulation illustre, un test cherche un contre-exemple, un solveur tranche dans son domaine et une preuve Lean est vérifiée par le noyau. Les séries Search, Sudoku, SymbolicAI et GameTheory montrent où chaque niveau de garantie devient pertinent.
- **Une évaluation qui accepte les résultats négatifs** : QuantConnect et le pipeline ML imposent validation hors échantillon, walk-forward et répétition multi-seed ; GenAI distingue l'appel de démonstration du service réellement déployable ; IIT/ICT publie aussi les expériences qui ne confirment pas l'hypothèse.
- **Des sujets de recherche reliés au cours** : théorèmes mécanisés, agents de preuve, neuro-symbolique, post-training et émergence causale prolongent directement les notions introduites dans les séries fondamentales.
- **Des systèmes complets** : études de cas et projets transverses recomposent recherche, contraintes, probabilités, apprentissage et explication dans un même livrable.
- **Le dépôt lui-même comme terrain d'ingénierie agentique** : exécution des notebooks, validation, catalogue et revues croisées sont assistés par une flotte d'agents sous revue humaine ([détail](MyIA.AI.Notebooks/README.md#un-dépôt-vivant--maintenu-par-une-flotte-dagents)).

Cette cohérence permet de lire le dépôt horizontalement — suivre une technique — ou verticalement — reprendre un même problème avec plusieurs familles d'outils.

---

## Philosophie pédagogique

Chaque série fournit son propre point d'entrée : un README donne l'ordre de lecture et le notebook de mise en route prépare l'environnement. Les notebooks introduisent leurs prérequis au moment où ils deviennent utiles, plutôt que de supposer un long cours préalable.

Les approches **multi-paradigmes** sont privilégiées. Le Sudoku est résolu par backtracking, contraintes, métaheuristiques et réseaux de neurones ; les jeux sont simulés en Python puis formalisés en Lean 4. Garder le problème fixe rend visibles les compromis entre garantie, performance, interprétabilité et généralisation.

La progression alterne **exemple guidé et exercice** : une notion est d'abord expliquée et observée sur une sortie réelle, puis reprise dans une tâche à compléter. Les cellules d'exercice restent exécutables même avant leur résolution, afin que le lecteur puisse parcourir tout le notebook, comparer les résultats et revenir ensuite sur le code manquant.

Enfin, le dépôt privilégie le chemin d'exécution le plus direct. Search, Sudoku et plusieurs séries ML ou symboliques fonctionnent en local ; les besoins supplémentaires — clé API, WSL, Docker, GPU ou cloud QuantConnect — sont annoncés dans le README et le notebook de mise en route de la série concernée.

---

## Séries de notebooks

### Search -- Algorithmes de recherche et optimisation

Comment un ordinateur trouve-t-il son chemin dans un labyrinthe, ordonne-t-il un atelier, ou bat-il un humain au Puissance 4 ? Tout problème d'IA, du jeu de plateau à la planification logistique, se ramène à un même défi : explorer un espace de solutions possibles pour trouver la meilleure. Le fil conducteur de la série n'est pas l'accumulation d'algorithmes mais une seule compétence -- savoir **quand explorer, quand contraindre, et quand combiner les deux** -- construite autour de l'idée de **réduction de l'espace de recherche** : comment passer d'une énumération aveugle exponentielle à une résolution intelligemment guidée.

**[Fondements](MyIA.AI.Notebooks/Search/Part1-Foundations/README.md)** -- La progression part de la formalisation d'un problème en espace d'états (S, A, T, G), puis déroule les grands paradigmes : recherche non informée (BFS, DFS), recherche guidée par heuristique (A*), optimisation locale, évolution, recherche adversariale et Monte Carlo Tree Search jusqu'à l'architecture AlphaGo. La théorie des graphes complète ce socle en jumeaux NetworkX/QuikGraph -- plus courts chemins, centralités, flots -- avant les extensions de pointe : Dancing Links de Knuth, programmation linéaire, automates symboliques à prédicats Z3 et banc d'essai de métaheuristiques. La garantie d'A* n'est pas seulement observée : le lake compagnon [`search_lean`](MyIA.AI.Notebooks/Search/search_lean/) prouve en Lean 4 que l'admissibilité entraîne l'optimalité et que la consistance autorise l'arrêt au premier but extrait.

**[Programmation par contraintes](MyIA.AI.Notebooks/Search/Part2-CSP/README.md)** -- Un changement de paradigme : au lieu de concevoir un algorithme d'exploration, on déclare les contraintes du problème et le solveur trouve les solutions. On y apprend la propagation (AC-3, Forward Checking, MAC) qui élague l'espace avant même de chercher, les contraintes globales d'OR-Tools CP-SAT (AllDifferent, Cumulative), puis les usages industriels -- ordonnancement d'atelier, planification de projet, optimisation combinatoire (sac à dos, bin packing) -- et les frontières du domaine : contraintes souples, raisonnement temporel par algèbre d'Allen, CSP distribués entre agents, et surtout l'hybridation (CP+SAT, CP+ML, et génération de contraintes par LLM). C'est le pont vers SymbolicAI.

**[Recherche heuristique avancée](MyIA.AI.Notebooks/Search/Part3-Advanced/README.md)** -- La montée en gamme sur la recherche informée : bases de données de motifs, recherche à divergence limitée et A* pondéré, mesurés en jumeaux Python/C# sur le taquin et le Rubik's cube. La discrépance combinatoire ouvre ensuite une frontière théorique vivante : colorer en ±1 sans déséquilibrer, comparer un oracle exact CP-SAT aux bornes de Beck-Fiala et Komlós, puis porter ces bornes dans le lake [`discrepancy_lean`](MyIA.AI.Notebooks/Search/discrepancy_lean/).

**[Métaheuristiques composables](MyIA.AI.Notebooks/Search/Part4-Metaheuristics/README.md)** -- Un side-track .NET 9 (GeneticSharp) qui **reconstruit et compose** les métaheuristiques plutôt que d'importer une boîte noire : moteur, grammaire de composition, paysages en dimension N≥5, robustesse aux translations et rotations, synergie d'îles, contrôle de paramètres et No-Free-Lunch. Après avoir isolé l'opérateur de Metropolis, la série confronte ses reconstructions aux implémentations de référence de `mealpy`, puis referme l'expérience par une sélection empirique d'algorithme et une synthèse croisée. On apprend ainsi non seulement à programmer un optimiseur, mais à établir sur quelles familles de problèmes il mérite d'être choisi.

**[Applications](MyIA.AI.Notebooks/Search/Applications/README.md)** -- Chaque concept se mesure sur un problème réel, souvent adapté d'un projet étudiant : N-Queens, plannings, démineur hybride, Wordle par théorie de l'information, nonogrammes, Wave Function Collapse, Puissance 4, tournées de véhicules, portefeuille ou réglage d'hyperparamètres. Une veine récente pousse les solveurs jusqu'à leur certificat : coloration d'arêtes et conjecture de Tutte, cryptanalyse différentielle par SAT, planification multi-agents sans collision, enchères combinatoires et covering arrays. L'audit de la garantie devient alors l'exercice : distinguer résultat trouvé, optimum prouvé et approximation honnêtement bornée.

Cette série est aussi un carrefour : ses algorithmes irriguent Sudoku (DLX, automates), SymbolicAI (Z3, planification PDDL), GameTheory (Minimax, MCTS) et RL (MCTS et DQN), et ses métaheuristiques reviennent régler les hyperparamètres du Machine Learning.

Python et C# | [README détaillé](MyIA.AI.Notebooks/Search/README.md)

### Sudoku -- Résolution multi-paradigme

Et si l'on prenait un seul problème -- une grille de Sudoku -- pour le résoudre d'une dizaine de manières radicalement différentes ? L'objectif n'est pas de remplir des grilles (un solveur industriel le fait en quelques millisecondes) mais de transformer ce casse-tête en **banc d'essai contrôlé** : parce que le problème reste constant, on isole la seule variable qui change d'un notebook à l'autre -- le paradigme algorithmique -- et l'on rend visible l'arbitrage qui traverse toute l'IA, **garantie de solution contre performance contre généralisation**. Le Sudoku généralisé est NP-complet, de la même famille que SAT ou le voyageur de commerce. Et chaque technique existe en miroir C# et Python, pour comparer un paradigme sans changer de langage.

**Les méthodes exactes -- la garantie pour boussole** -- La première moitié de la série réunit les approches qui trouvent toujours la solution si elle existe. On part du backtracking, l'exploration récursive fondamentale, accéléré par l'heuristique MRV (choisir d'abord la case la plus contrainte) ; puis la couverture exacte de Knuth (Dancing Links), où une représentation de données astucieuse -- des listes doublement chaînées -- transforme les performances sans changer l'algorithme. Vient ensuite le grand basculement vers le déclaratif : au lieu de programmer l'exploration, on déclare les contraintes et le solveur cherche. C'est la programmation par contraintes -- propagation de Norvig (l'élagage seul suffit déjà à résoudre les grilles simples), CSP académique à la AIMA, coloration de graphe, et les solveurs industriels OR-Tools CP-SAT et Choco -- prolongée par l'IA symbolique : le solveur SMT Z3, les automates symboliques à prédicats, les diagrammes de décision binaires. Une étape singulière code treize techniques de déduction humaine (paires nues, candidats cachés, pointing) : le pont entre le raisonnement de la machine et celui du joueur.

**Les méthodes approchées -- échanger la garantie contre autre chose** -- L'autre moitié renonce délibérément à la garantie. Les métaheuristiques inspirées de la nature -- algorithme génétique, recuit simulé, essaim particulaire -- explorent l'espace intelligemment sans jamais promettre d'aboutir, mais souvent très vite. Puis le data-driven inverse la logique : au lieu de programmer la résolution, on l'apprend. Un modèle probabiliste (Infer.NET, NumPyro) place une distribution à posteriori sur les cases ; un réseau de neurones apprend, sur un très grand nombre de grilles résolues, les régularités qui mènent à une solution ; un LLM tente de raisonner sans algorithme explicite. Chacun illustre une limite autant qu'une force : le réseau a besoin d'énormément de données, le LLM trébuche sur le raisonnement logique pur.

**Le banc d'essai comparatif** -- Le notebook de synthèse confronte toutes les approches sur une échelle de difficulté croissante, du facile à l'expert, et c'est là que l'arbitrage paie. Deux enseignements ressortent, contre-intuitifs. D'abord, sur les modèles appris, le volume de données pèse plus lourd que la taille du modèle : un petit réseau bien nourri devance un gros réseau affamé. Ensuite -- et c'est le cœur de la série -- même entraîné jusqu'à une précision quasi parfaite, le réseau de neurones reste un **approximateur** : il peut se tromper, là où les solveurs exacts (Norvig, OR-Tools, Z3) garantissent la solution et sont souvent plus rapides en inference. La leçon n'est pas qu'une approche l'emporte, mais que le bon choix dépend du contexte -- garantie, vitesse, ou capacité à généraliser.

Sudoku est ainsi une coupe verticale du dépôt : un seul problème traverse **Search** (backtracking, métaheuristiques, DLX et CSP), **SymbolicAI** (Z3), **Probas** (inférence bayésienne) et **ML** (solveur neuronal et LLM). Les solveurs CP-SAT et MaxSMT y passent aussi de la satisfaction à l'optimisation, tandis qu'un companion statistique soumet leurs benchmarks aux intervalles bootstrap et aux tests de significativité. Enfin, le lake [`sudoku_lean`](MyIA.AI.Notebooks/Sudoku/sudoku_lean/) prouve la correction des règles de propagation : la technique centrale des méthodes exactes est rejouée puis certifiée par le noyau Lean.

C# et Python (OR-Tools, Z3, PyTorch) | [README détaillé](MyIA.AI.Notebooks/Sudoku/README.md)

### SymbolicAI -- Raisonnement formel

Une machine peut-elle raisonner -- non pas approximer une réponse plausible, mais déduire, prouver, justifier ? C'est le pari de l'IA symbolique, l'autre grande tradition de l'intelligence artificielle : représenter la connaissance sous forme de propositions, de règles et de structures logiques, puis en dériver mécaniquement de nouvelles conclusions. La plus vaste série du dépôt l'explore — des systèmes experts des années 80 jusqu'aux assistants de preuve et aux agents LLM d'aujourd'hui. Le fil conducteur n'est pas une technologie mais une promesse : ce raisonnement est **explicite, vérifiable et explicable** -- exactement ce que l'apprentissage statistique seul ne garantit pas. Et là où les deux paradigmes se rencontrent se trouve le front actif de la recherche : le symbolique devient la couche de contrôle du neuronal -- détecter les incohérences d'un LLM, l'ancrer sur des faits, certifier la robustesse d'un réseau.

La progression suit cette logique : formaliser le raisonnement (Tweety), représenter la connaissance (Semantic Web), la prouver mécaniquement (Lean) ou la vérifier automatiquement par solveurs SMT, l'appliquer à des problèmes concrets (Planners, Smart Contracts), puis la ponter vers le neuronal (Argument Analysis, Symbolic Learning). Chaque sous-série est autonome, mais ensemble elles dessinent une vision cohérente de l'IA symbolique moderne.

**[Tweety](MyIA.AI.Notebooks/SymbolicAI/Tweety/README.md) -- logiques formelles et argumentation computationnelle** -- Construite sur TweetyProject, cette sous-série réunit sous un même toit logiques propositionnelle, du premier ordre, modale, de description et conditionnelle, révision de croyances AGM et surtout argumentation computationnelle. Les bibliothèques Java sont pilotées depuis Python via JPype et, dans leurs jumeaux C#, via IKVM ou des implémentations .NET explicites : on expérimente d'un formalisme et d'un écosystème à l'autre sans masquer le solveur. Des cadres abstraits de Dung, on passe à ASPIC+, DeLP, ABA et Clingo, puis aux frameworks étendus, pondérés et probabilistes, aux dialogues et au vote. Le lake compagnon [`argumentation_lean`](MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean/) referme la boucle en prouvant l'acceptabilité grounded comme point fixe de Knaster-Tarski ; les certificats s'exécutent dans le notebook par le kernel Lean. Les applications vont du raisonnement juridique et médical au contrôle des incohérences d'un LLM.

**[Semantic Web](MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/README.md) -- de RDF aux graphes de connaissances qui ancrent les LLMs** -- Le Web Sémantique est la promesse d'un Web où les machines comprennent le sens des données, pas seulement leur syntaxe. La sous-série en couvre le spectre complet, et la raison de cette complétude est que les briques s'articulent en couches : RDF définit les données (le triplet sujet-prédicat-objet, un fait élémentaire), SPARQL les interroge, RDFS et OWL ajoutent le raisonnement (hiérarchies de classes, restrictions, inférence automatique), SHACL valide leur qualité, JSON-LD ponte vers le Web des développeurs, RDF-Star ajoute la provenance, et les graphes de connaissances couplés aux LLMs ferment la boucle. C'est ce dernier maillon qui a relancé le domaine après des années de désillusion : GraphRAG a montré qu'un graphe RDF pouvait ancrer un LLM sur des faits vérifiables -- le Web Sémantique comme garde-fou de l'IA générative. Le parcours est délibérément bilingue : fondations en .NET avec dotNetRDF, standards modernes et IA en Python (rdflib, pySHACL, GraphRAG), chaque notebook C# disposant d'un miroir Python pour qui préfère un seul écosystème.

**[Lean](MyIA.AI.Notebooks/SymbolicAI/Lean/README.md) -- la preuve mécanique, où le noyau a toujours le dernier mot** -- Lean 4 est à la fois un langage fonctionnel et un assistant de preuve : une proposition devient un type, une preuve un terme, et le noyau vérifie chaque étape. Le parcours part de Curry-Howard, du mode tactique et de Mathlib, puis introduit l'assistance par LLM. LeanCopilot, LeanDojo et les agents de preuve peuvent proposer ou explorer ; ils ne remplacent jamais le verdict du noyau. Les applications relient cette garantie à la robustesse des réseaux et à des formalisations inspirées de Grothendieck et Conway, puis à des résultats vivants : conjecture de Sendov, théorie de l'analyse de Tao, méthode entropique pour PFR, détection MIMO et problème inverse de Galois. Les notebooks companions importent les lakes et rejouent leurs certificats -- `#check`, `decide`, `#print axioms` -- afin que la preuve soit exécutée, pas seulement citée. Sous Windows, cette série nécessite WSL.

**[Planners](MyIA.AI.Notebooks/SymbolicAI/Planners/README.md) -- non pas "que prédire ?" mais "que faire ?"** -- La planification automatique répond à une question que l'apprentissage ne pose pas : étant donné un état initial, un ensemble d'actions décrites par leurs préconditions et leurs effets, et un but, quelle séquence d'actions y mène ? C'est une technologie éprouvée -- elle pilote des robots, optimise la logistique, et a dirigé des engins spatiaux autonomes (le Remote Agent de Deep Space, les rovers martiens) -- standardisée par le langage PDDL, qui a fait naître tout un écosystème de solveurs comparables. La sous-série suit la montée en puissance habituelle : des fondations STRIPS et de l'explosion combinatoire de l'espace d'états -- celle qui rend les heuristiques indispensables -- on passe à la planification classique avec Fast-Downward, vainqueur des compétitions IPC, et ses heuristiques admissibles ; puis aux approches avancées -- programmation par contraintes avec OR-Tools, planification temporelle, réseaux de tâches hiérarchiques (HTN). La dernière étape ponte vers le neuro-symbolique : faire générer des plans par un LLM, comparer les solveurs derrière une interface unifiée, apprendre les heuristiques par réseaux de neurones. Le fil rouge rejoint celui de la série -- donner à un modèle de langage une capacité d'action vérifiable et orientée vers un but, plutôt qu'une suite d'actions plausible mais non garantie.

**[SMT](MyIA.AI.Notebooks/SymbolicAI/SMT/README.md) -- la vérification automatique par solveurs SMT** -- Là où Lean accompagne un humain pas à pas dans une preuve, les solveurs SMT (Satisfiability Modulo Theories) automatisent la vérification de propriétés sur des formules logiques riches -- arithmétique, tableaux, chaînes de caractères, types inductifs. La sous-série couvre l'écosystème Z3 dans ses deux déclinaisons : [Z3-API](MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/README.md) (bindings Python et C#/.NET, du Sudoku aux tactiques de preuve en passant par les solveurs de quantificateurs et les expressions régulières) et [Z3-Linq2Z3](MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-Linq2Z3/README.md) (Linq-to-Z3, où les requêtes Z3 s'écrivent comme des expressions Linq familières du monde .NET). On y voit aussi la théorie des tableaux et des tableaux imbriqués (nested arrays, 2D/3D), la synthèse de programmes par Resharp, et les automates finis comme contre-exemples. L'enjeu pédagogique est de montrer qu'un solveur SMT peut prendre le relais quand Lean devient trop interactif, et qu'en pratique industrielle (audit de smart contracts, vérification de pipelines, test de propriétés logicielles) ces deux familles de vérification sont complémentaires.

**[Smart Contracts](MyIA.AI.Notebooks/SymbolicAI/SmartContracts/README.md) -- quand le code fait foi, le rendre digne de confiance** -- Un contrat déployé transfère de la valeur sans laisser la possibilité d'un correctif immédiat : sécurité et développement doivent donc avancer ensemble. Le parcours remonte des primitives cryptographiques à Solidity et aux standards applicatifs, puis ajoute tests, fuzzing, invariants et vérification formelle avec Foundry. Il aborde aussi la confidentialité sur une chaîne transparente, la gouvernance et plusieurs écosystèmes non-EVM avant le déploiement. Le lien avec Lean et SMT est direct : dans les trois cas, il s'agit de transformer une confiance intuitive dans le programme en propriétés que la machine peut vérifier.

**[Argument Analysis](MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/README.md) -- où s'arrête le LLM, où commence le vérificateur** -- Distinguer un argument valide d'un sophisme devient un acte critique dans une société saturée de discours générés à la chaîne : quand un LLM produit à la demande un texte plausible, la frontière entre persuasion légitime et manipulation rhétorique se brouille. Cette sous-série, la plus fournie de SymbolicAI, pose une question concrète : peut-on prendre un texte argumentatif en entrée et en restituer une carte logique formelle, vérifiée par un solveur, avec détection systématique des sophismes connus ?

L'arc principal est un **pipeline agentique en six temps** (`0-init` → `1-informal` → `2-formal` → `3-orchestration` → `4-capstone` → `5-jtms`), chaque étape existant en version pédagogique et en version *agent* exécutable. Un agent LLM orchestré par Semantic Kernel extrait le tissu informel -- prémisses, conclusions, transitions ; un solveur logique (TweetyProject, via le même pont JPype que la sous-série Tweety) vérifie la cohérence des formalisations propositionnelles ; la dernière étape ajoute un **JTMS** (*justification-based truth maintenance system*), qui garde trace de *pourquoi* chaque croyance tient et sait la rétracter quand son support tombe -- exactement ce qui manque à un LLM qui change d'avis sans savoir qu'il l'a fait.

Autour de cet arc, une douzaine de notebooks explorent les **axes formels** de l'argumentation, chacun sur un angle que le pipeline seul n'atteint pas : sémantiques de Dung (quels arguments survivent aux attaques), sémantiques de *ranking* (les classer plutôt que les accepter ou les rejeter en bloc), *Value-Based AF* (une attaque ne l'emporte que si la valeur qu'elle défend prime, ce qui explique deux désaccords rationnels sur les mêmes faits), modèle de Toulmin (données, garantie, réfutation), et une **matrice de richesse formelle** qui met ces cadres en regard. Trois notebooks d'ontologies (AIF, liens croisés, **vertus** argumentatives) donnent au corpus sa colonne vertébrale sémantique ; un routage multi-backend compare les moteurs derrière une interface unique ; la *restitution en trois actes* et l'*ArgumentProfile* traitent la question aval, souvent négligée : une fois l'analyse faite, comment la rendre lisible à un humain. Trois bibliothèques C# compagnes (adaptateur OWL, synchronisation de jeux de données, gestion de prompts) sortent le tout du notebook.

Cette sous-série est le point d'atterrissage de **deux projets vivants**, dont le travail se distille progressivement ici et dont l'état d'avancement dépasse aujourd'hui ce que les notebooks en montrent.

Le plus mûr des deux est [2025-Epita-Intelligence-Symbolique](https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique), le *moteur* : plusieurs dizaines d'agents spécialistes -- chacun tenant un axe d'analyse, un formalisme ou une étape de vérification -- répartis sur plusieurs systèmes d'orchestration concurrents et protégés par une vaste suite d'intégration. La difficulté propre à ce projet n'est pas d'ajouter un agent de plus : c'est de **consolider en vol** cette diversité d'orchestrateurs sans perdre ce que chacun sait faire -- un problème d'architecture agentique à part entière. C'est de là que vient `argumentation_lib`.

L'autre est [Argumentum](https://www.argumentum.games), le *corpus et le produit* : un jeu de cartes dont la taxonomie compte **1 408 sophismes et 223 vertus** argumentatives, déjà traduite en **huit langues** (français, anglais, russe, arabe, farsi, chinois, espagnol, portugais), avec sa chaîne d'impression et son site. À la taxonomie s'ajoutent **167 cartes Scénarii** -- des situations de discours -- et c'est leur produit cartésien avec les sophismes qui ouvre la voie la plus prometteuse : un corpus d'entraînement *synthétique* de grande taille, engendré par construction plutôt que collecté. Le dépôt CoursIA est ce qui relie les deux -- le notebook [Argumentum Cards](MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Argumentum_Cards.ipynb) travaille directement cette taxonomie, et le sous-module `Argumentum` en embarque la source.

Tout l'enjeu pédagogique tient dans la jointure -- où le LLM, fiable pour extraire mais faible pour prouver, passe la main au vérificateur formel, et comment une boucle informel/formel converge vers un verdict. C'est l'incarnation appliquée du fil de la série : le symbolique comme garde-fou du neuronal, mis au service de la pensée critique, du fact-checking et de l'audit de contenus générés par IA.

**[Symbolic Learning](MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/README.md) -- apprendre de la connaissance, pas seulement des données** -- Cette sous-série demande comment apprendre avec peu d'exemples, produire des règles lisibles et réutiliser une théorie du domaine déjà connue. Elle part des espaces de versions et de l'apprentissage par explication, passe par la programmation logique inductive et l'apprentissage actif d'automates, puis rejoint le neuro-symbolique : logiques différentiables, fouille de règles sur graphes et boucles où un LLM propose ce qu'un vérificateur symbolique contrôle. L'apprentissage statistique apporte la généralisation numérique ; l'apprentissage symbolique apporte structure, parcimonie et interprétabilité.

Vue d'ensemble, la série raconte une seule idée déclinée d'une sous-série à l'autre : reformuler une affirmation dans un cadre où elle devient vérifiable. Tweety formalise un débat en sémantiques d'acceptabilité, le Web Sémantique ancre des faits dans un graphe interrogeable, Lean réduit une preuve à ce que son noyau accepte ligne à ligne, les contrats se relisent à l'aune de leur vérification formelle, le planificateur confronte une intention dite en mots à un solveur qui tranche, l'argumentation et l'apprentissage symbolique rebouclent un LLM sur un vérificateur. Ce geste -- changer de représentation jusqu'à ce que la garantie devienne possible -- déborde SymbolicAI : on le retrouve dans les portages Lean de la théorie des jeux (existence de Nash, impossibilité d'Arrow, valeur de Shapley) et dans la théorie de la décision de Probas, partout où le dépôt fait passer un résultat du plausible au contrôlable. C'est la grille que propose [La mer qui monte](docs/grothendieckian-lens.md) : à mesure que l'IA bascule vers les grands modèles, la rendre digne de confiance, ce sera trouver le cadre où son affirmation se vérifie.

Python, Lean 4 et C# | [README détaillé](MyIA.AI.Notebooks/SymbolicAI/README.md)

### Probas -- Programmation probabiliste

Comment raisonner -- et surtout décider -- quand rien n'est certain ? Un diagnostic médical n'est jamais sûr à cent pour cent, un classement de joueurs dépend de performances variables, et les données arrivent toujours bruitées ou incomplètes. La programmation probabiliste refuse de répondre par un seul chiffre : elle calcule une *distribution* qui dit à quel point on croit à chaque issue possible. Mais une croyance ne sert à rien tant qu'on n'agit pas dessus -- et c'est là le fil conducteur de la série : passer d'une réponse unique à une distribution, puis d'une distribution à une décision. La théorie de la décision bayésienne, qui occupe toute la seconde moitié du parcours, est la charnière de ce mouvement, et le socle dont la théorie des jeux a besoin pour modéliser des agents rationnels.

**Deux écosystèmes, les mêmes modèles** -- La série repose sur une juxtaposition délibérée : chaque modèle est traité dans deux écosystèmes complémentaires qui couvrent, à eux deux, plusieurs familles d'algorithmes d'inférence. [Infer.NET](MyIA.AI.Notebooks/Probas/Infer/README.md) (Microsoft, C#) compile le modèle en graphe de facteurs et laisse choisir son moteur -- passage de messages (Expectation Propagation, Variational Message Passing) ou échantillonnage de Gibbs -- avec des résultats exacts sur les modèles conjugués et approchés ailleurs, le tout rapide et dont la structure se visualise. [PyMC](MyIA.AI.Notebooks/Probas/PyMC/README.md) (Python) reprend l'intégralité de ces modèles avec le MCMC moderne à base de gradient (le sampler NUTS), qui s'applique à presque tout modèle au prix d'un diagnostic de convergence outillé par ArviZ (R-hat, taille d'échantillon effective, divergences, trace plots). L'enjeu n'est donc pas de trancher entre exact et approché, ni même entre déterministe et aléatoire -- chaque famille a sa place -- mais d'apprendre, en voyant un même modèle résolu de plusieurs façons, quel moteur convient à quelle structure. Les modèles viennent d'applications réelles : réseaux bayésiens pour le diagnostic médical et l'explaining away, Item Response Theory (le moteur des tests adaptatifs comme le GMAT), TrueSkill (le classement bayésien des joueurs sur Xbox Live), LDA pour la découverte de thèmes, modèles de Markov cachés pour les régimes, agrégation de foules d'annotateurs bruités, recommandation assortie d'une barre d'incertitude.

**[Théorie de la décision](MyIA.AI.Notebooks/Probas/DecisionTheory/README.md)** -- Une troisième sous-série porte l'arc décision en miroir dans [DecInfer](MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/README.md) et [PyMC](MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/README.md), prolongé par le lake Lean 4 [`decision_theory_lean`](MyIA.AI.Notebooks/Probas/decision_theory_lean/) et par deux notebooks-ponts de causalité : [do-calculus](MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/Do-Calculus-Bridge.ipynb) quand l'intervention est identifiable, méthodes quasi-expérimentales quand `do()` est impossible. Le versant actuariel traite crédibilité, prime pure et chargement, ruine de Lundberg, valeur de l'information en souscription et fréquence-sévérité hiérarchique. Un banc cross-engine soumet en outre le même contrat JSON à Infer.NET et PyMC, pour comparer des décisions plutôt que juxtaposer des syntaxes. Le lake prouve dans `Discount.lean` les identités d'escompte qui fondent l'indice de Gittins ; la frontière restante du théorème d'optimalité est documentée plutôt que masquée. Il mécanise aussi la cohérence tarifaire : un barème non additif expose un Dutch Book exploitable.

**De l'inférence à la décision -- la théorie de l'utilité** -- À quoi bon une distribution si elle ne dicte aucune action ? La seconde moitié de la série franchit ce pas, et c'est son cœur. On part des axiomes de Von Neumann-Morgenstern qui fondent l'utilité espérée comme critère rationnel, on modélise l'aversion au risque (utilités CARA et CRRA, paradoxe de Saint-Petersbourg), on décide sur plusieurs critères à la fois (utilité multi-attributs, MAUT), on branche la décision sur l'inférence par les diagrammes d'influence, on chiffre la valeur d'une information avant de payer pour l'acquérir (EVPI, EVSI -- quand un test complémentaire est-il rentable ?), on se protège contre l'incertitude radicale (Minimax Regret), et l'on débouche sur la décision *séquentielle* : processus de décision markoviens, bandits, POMDP. Ce dernier maillon est une double passerelle -- vers le reinforcement learning d'un côté, et de l'autre vers la théorie des jeux, qui suppose précisément des agents maximisant leur utilité espérée. C'est pourquoi cette série précède GameTheory : l'utilité en est le prérequis.

**Jusqu'à la preuve formelle -- l'indice de Gittins en Lean** -- Le problème du bandit -- explorer pour apprendre, ou exploiter ce qu'on croit savoir ? -- admet une solution remarquable : l'indice de Gittins, qui ramène un problème séquentiel intimidant à un simple classement de bras. La série ne se contente pas de l'implémenter ; un volet en Lean 4 (avec Mathlib) cherche à le *prouver*. Les identités d'escompte géométrique qui fondent le calcul d'une valeur actualisée -- la somme escomptée d'une récompense constante -- y sont démontrées rigoureusement, vérifiées ligne à ligne par le noyau. Le théorème d'optimalité de Gittins lui-même, en revanche, est *énoncé* mais laissé à la frontière : sa preuve complète exigerait une formalisation des MDP et de l'équation de Bellman qui manque encore à Mathlib, et le notebook le documente comme tel. Cette distinction entre ce qui est prouvé et ce qui ne l'est pas encore est l'enseignement -- elle relie Probas à la série Lean de SymbolicAI, où le noyau a toujours le dernier mot. Le même mouvement ancre le début du parcours : les axiomes de Von Neumann-Morgenstern et leur théorème de représentation par l'utilité espérée sont eux aussi portés en Lean 4 (`decision_theory_lean`), et l'arc décision se clôt sur le Thompson Sampling -- la réponse bayésienne moderne au même dilemme exploration-exploitation, doublée comme le reste en Infer.NET et PyMC.

Probas est un carrefour discret du dépôt. Sa théorie de la décision est le socle de **GameTheory** (jeux bayésiens, agents à utilité espérée) et la passerelle vers **RL** (ses MDP et ses bandits y deviennent apprentissage par renforcement) ; son inférence bayésienne nourrit le TP de régression de **ML** et la gestion du risque de **QuantConnect** (où un modèle de Markov caché génère des signaux de trading) ; ses fondements probabilistes sous-tendent le phi de l'**IIT** et le raisonnement incertain des ontologies de **SemanticWeb** ; et son pont vers Lean prolonge le fil de vérification formelle de **SymbolicAI**. Partout la même exigence : ne pas confondre une croyance avec une certitude, ni une prédiction avec une décision.

C# (Infer.NET), Python (PyMC, Pyro) et Lean 4 | [README détaillé](MyIA.AI.Notebooks/Probas/README.md)

### GameTheory -- Théorie des jeux

Comment des agents rationnels interagissent-ils quand le résultat de chacun dépend des choix de tous les autres ? Enchère, négociation, élection, partie de poker, guerre commerciale : partout des décideurs anticipent les décisions d'autrui avant d'arrêter les leurs. La théorie des jeux est le langage mathématique de cette interdépendance, et elle suppose d'emblée des agents qui maximisent une utilité espérée -- c'est pourquoi elle vient ici juste après Probas, dont la théorie de la décision lui sert de socle. Le fil conducteur de la série n'est pas un thème mais une *méthode* : tout résultat y est abordé deux fois, simulé en Python pour le *voir* à l'œuvre, puis prouvé en Lean 4 pour le *certifier*. Le notebook Python montre qu'un équilibre est plausible ; le notebook Lean montre qu'il est inévitable.

**Des jeux statiques aux frontières -- une montée en stratégie** -- Le fil principal suit la maturation historique de la discipline. On part des jeux statiques, du minimax, de Nash et du tournoi d'Axelrod ; le processus de Moran ajoute ensuite la fixation stochastique dans une population finie. Le temps et l'incertitude introduisent formes extensives, jeux combinatoires, induction, réputation et jeux bayésiens. L'information asymétrique devient un arc propre -- citrons d'Akerlof, signal de Spence, screening de Rothschild-Stiglitz et équilibres Wilson-Miyazaki -- avant les frontières contemporaines : CFR au poker, Stackelberg, coopération, mécanismes VCG et apprentissage multi-agent.

Une strate plus récente étend le vocabulaire stratégique lui-même : les **jeux ouverts et les lentilles** rendent les jeux composables ; la dette d'abstraction et les méta-actions tarifées font de la transformation des règles une décision ; les chemins de swaps, chambres et murs explorent la géométrie ordinale des jeux 2×2 ; Poincaré-Bendixson étudie leurs ensembles limites. Les applications rejoignent les marchés réels par l'échange de reins, les jeux de sécurité Stackelberg, l'affectation de Kuhn-Munkres et le design automatisé de mécanismes.

**Simuler, puis prouver -- la dualité Python/Lean** -- Les grands résultats ne sont pas seulement illustrés : les lakes Lean 4 en rejouent les certificats. Points fixes pour Nash, PGame pour les jeux combinatoires, axiomes de Shapley, condition de Bondareva-Shapley par la route de Farkas et treillis des mariages stables de Knuth forment le socle. Les companions plus récents certifient le seuil du marché des citrons, l'optimalité de Kuhn-Munkres par dualité à gap nul, l'enchère de Vickrey et le grim-trigger. La direction difficile du théorème Folk escompté reste explicitement à la frontière : le dépôt distingue ce qui est vérifié par le noyau de ce qui demeure un programme de preuve.

**L'agrégation des préférences -- choix social et impossibilités** -- Une sous-série dédiée, [SocialChoice](MyIA.AI.Notebooks/GameTheory/SocialChoice/README.md), prolonge le bloc sur l'agrégation collective et l'éclaire sous trois angles à la fois. Le théorème d'impossibilité d'Arrow y apparaît contre-intuitif quand on le simule, inévitable quand on le prouve en Lean, et franchement insatisfiable quand on l'encode en problème SAT résolu par Z3 -- trois façons de saisir un même résultat. S'y ajoutent le paradoxe libéral de Sen, les méthodes de vote classiques (Condorcet, Borda, Copeland) et le modèle spatial de Downs. C'est le pont le plus direct vers la gouvernance on-chain étudiée dans SmartContracts, où un vote de DAO n'est qu'une règle d'agrégation soumise aux mêmes impossibilités.

Au-delà du tableau noir, ces résultats structurent l'économie numérique : les enchères VCG fondent la publicité en ligne de Google et Meta à l'échelle de milliards de transactions par jour, l'algorithme de Gale-Shapley affecte étudiants aux écoles et internes aux hôpitaux -- un mécanisme couronné par le prix Nobel d'économie 2012 -- et la Counterfactual Regret Minimization a permis aux machines de battre les meilleurs joueurs de poker. GameTheory est ainsi un carrefour : elle prolonge la théorie de la décision de **Probas** vers l'interaction stratégique, alimente le **RL** par son volet multi-agent, irrigue **SmartContracts** par le vote vérifiable et la gouvernance, et partage avec **SymbolicAI** l'exigence de la preuve vérifiée par la machine.

Python (Nashpy, OpenSpiel, Z3), C# et Lean 4 | [README détaillé](MyIA.AI.Notebooks/GameTheory/README.md)

### ML -- Machine Learning

Comment passe-t-on d'un tableur rempli de données à un modèle qui prédit, recommande ou anticipe ? Et ce savoir-faire change-t-il selon qu'on code en C# ou en Python ? La série répond par la négative : les concepts du Machine Learning -- features, entraînement, évaluation, généralisation -- sont **invariants**, seuls les outils et le degré d'automatisation diffèrent. Le fil conducteur est justement ce déplacement : *qui* tient le pipeline ? Vous à la main, puis l'AutoML, puis un agent LLM autonome -- la constante étant, à chaque étage, une évaluation qui distingue un modèle qui marche d'un modèle qu'on comprend.

**[ML.NET](MyIA.AI.Notebooks/ML/ML.Net/README.md) -- le Machine Learning sans quitter l'écosystème .NET** -- Le premier volet construit le pipeline complet en C# : `MLContext`, `IDataView`, feature engineering, entraînement, AutoML, validation croisée et explication par importance de permutation, puis prévision SSA, interopérabilité ONNX et recommandation. Chaque étape a son jumeau scikit-learn : la parité rend visibles les invariants du pipeline jusque dans le non-supervisé, avec clustering RFM et détection d'anomalies. Le capstone marie ML.NET à la régression bayésienne d'Infer.NET pour prédire une valeur et sa plage de confiance -- pont direct vers Probas.

**[Data Science avec agents](MyIA.AI.Notebooks/ML/DataScienceWithAgents/README.md) (Python)** -- Entre les fondations et les agents, deux cursus ont grandi. Le cours canonique couvre régressions, ensembles, biais-variance et PAC, puis l'évaluation responsable : calibration des probabilités, équité par sous-groupe, données déséquilibrées et analyse d'erreurs. Le lake [`learning_theory_lean`](MyIA.AI.Notebooks/ML/learning_theory_lean/) certifie la convergence de Novikoff et la complexité d'échantillon PAC. Le parcours deep learning ouvre ensuite la boîte noire couche par couche : rétropropagation écrite à la main et vérifiée par différence finie, optimiseurs, régularisation, attention, transformer, modèles génératifs et distillation, chaque mécanisme étant construit *from scratch* avant son équivalent PyTorch.

Le dernier volet change enfin qui tient le pipeline : au lieu d'écrire seul le code d'analyse, on orchestre des agents LLM qui le produisent et l'exécutent. LangChain construit l'agent outillé ; Google ADK monte vers les boucles planner-coder, DS-STAR, MLE-STAR et le déploiement BigQuery/BQML. Le support multi-provider -- Gemini, OpenAI ou vLLM local -- permet surtout d'étudier quand un agent accélère réellement l'analyse et comment le juger contre le référent manuel construit auparavant.

Cette série irrigue le reste du dépôt par sa démarche d'évaluation : on la retrouve dans QuantConnect (modèles prédictifs de trading), RL (mêmes gradients, mêmes réseaux, même méfiance du surapprentissage) et Probas (l'inférence bayésienne du TP) ; son réglage d'hyperparamètres rejoint les métaheuristiques de Search ; et ses agents LLM reposent sur les modèles couverts par GenAI -- où les modèles ONNX de ML.NET servent justement à déployer BERT et Whisper.

C# et Python | [README détaillé](MyIA.AI.Notebooks/ML/README.md)

### GenAI -- IA générative

Comment générer une image à partir d'une phrase, faire parler une machine, composer un fond musical, animer une vidéo, ou brancher un LLM sur ses propres outils ? L'une des plus vastes séries du dépôt explore l'IA générative dans toutes ses modalités. Son fil conducteur n'est pas l'accumulation d'APIs : c'est apprendre à **choisir** entre un modèle cloud (gpt-image-1, GPT-5, Whisper) et un modèle open-source auto-hébergé (FLUX, Stable Diffusion, Qwen, MusicGen) selon le coût, le contrôle, le débit et la sensibilité des données, puis à **combiner** ces briques dans des pipelines qui tiennent en production. Tout commence par [`00-GenAI-Environment`](MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/README.md), le passage obligé qui configure clés API, services Docker et validation.

Chaque modalité (Image, Audio, Video) suit la même montée en quatre niveaux -- Foundation (premiers appels d'API), Advanced (modèles locaux sur GPU, édition fine), Orchestration (workflows multi-modèles) et Applications (cas d'usage concrets) -- et chacune se structure autour d'un fil rouge concret à construire de bout en bout.

**[Image](MyIA.AI.Notebooks/GenAI/Image/README.md)** -- De gpt-image-1 et GPT-5 en cloud jusqu'aux modèles auto-hébergés (FLUX, Stable Diffusion 3.5, Qwen Image Edit, Z-Image/Lumina) orchestrés via ComfyUI. On y apprend à éditer plutôt que régénérer (inpainting, ControlNet), à composer des graphes de nœuds reproductibles, et à gérer la VRAM (quantizations INT4/FP8). Fil rouge : un générateur de visuels pédagogiques.

**[Audio](MyIA.AI.Notebooks/GenAI/Audio/README.md)** -- La chaîne vocale complète : transcription (Whisper), synthèse (OpenAI TTS, Kokoro, Chatterbox), clonage de voix (XTTS), génération musicale (MusicGen, YuE, ACE-Step), séparation de sources (Demucs) et TTS expressif à tags prosodiques. Fil rouge : un podcast entièrement généré, voix clonée et fond musical compris.

**[Video](MyIA.AI.Notebooks/GenAI/Video/README.md)** -- La modalité la plus exigeante : compréhension de séquences (GPT-5, Qwen-VL), génération de mouvement (HunyuanVideo, LTX-Video puis LTX-2 pour l'audiovisuel joint, Wan, Stable Video Diffusion), super-résolution et interpolation (Real-ESRGAN, RIFE). Fil rouge : transformer un script texte en vidéo pédagogique animée.

**[Texte](MyIA.AI.Notebooks/GenAI/Texte/README.md)** -- Le socle de tout le reste : prompt engineering, sorties structurées, function calling, RAG, code interpreter, modèles de raisonnement et déploiement local. L'arc agentique ajoute orchestration, mémoire persistante, Tree-of-Thoughts et scaling du calcul à l'inférence. Autour de ce socle, les garde-fous sont devenus un parcours à part entière : red-team de prompts, mécanique d'inférence, stratégies de long contexte, évaluation systématique des textes et des agents, plus une veine d'inférence .NET avec LLamaSharp et TensorSharp.

**[Semantic Kernel](MyIA.AI.Notebooks/GenAI/SemanticKernel/README.md)** -- Le SDK d'orchestration agentique de Microsoft, en Python et en C#/.NET Interactive : plugins, agents, filtres, vector stores, Process Framework, multimodalité et MCP. Démonstrateur phare : un NotebookMaker à trois agents (Admin, Coder, Reviewer) qui génère lui-même des notebooks pédagogiques.

**[FineTuning](MyIA.AI.Notebooks/GenAI/FineTuning/README.md) -- adapter sans tout ré-entraîner** -- La boîte à outils pratique de la spécialisation : LoRA et QLoRA pour n'entraîner qu'une poignée de paramètres, SFT pour apprendre un format de réponse, DPO pour aligner sur des préférences et *model merging* pour combiner plusieurs spécialisations. Le parcours va désormais jusqu'au LoRA vision-langage et reste orienté vers une question concrète : qu'est-ce qui tient réellement sur le GPU disponible ?

**[PostTraining](MyIA.AI.Notebooks/GenAI/PostTraining/README.md) -- la chaîne complète, du SFT au RL à récompense vérifiable** -- C'est ici que se fabrique concrètement un assistant, et c'est l'une des séries les plus denses du dépôt. Elle remonte toute la chaîne -- SFT, puis RLHF, puis DPO, puis GRPO, puis RLVR -- en expliquant à chaque étape *la formule du loss avant le code*, parce que le point pédagogique n'est pas qu'un `trainer.train()` converge, mais qu'on sache pourquoi DPO se passe d'un reward model et pourquoi GRPO se passe d'un critique. Trois notebooks réimplémentent la famille « sans critique » **depuis zéro** sur un environnement jouet CPU -- GRPO, RLOO et GAE côte à côte, où l'on voit l'arbitrage biais-variance à l'œuvre et où le « collapse » observé à un pas se révèle une propriété du banc d'essai plutôt que de l'algorithme, une fois le crédit rendu véritablement différé. Les corrections DAPO et Dr.GRPO montrent ensuite comment l'objectif GRPO originel se répare quand sa normalisation introduit ses propres biais. Deux autres sortent du jouet et entraînent un **vrai modèle** (Qwen3.5-0.8B en QLoRA 4-bit, sur un GPU de 8 Go) contre des récompenses *vérifiées par un solveur* -- Z3 sur des contraintes arithmétiques, SymPy et un N-reines -- avec un détecteur de *reward hacking* branché en ligne pendant l'entraînement, et une validation multi-seed. La discipline d'évaluation du dépôt s'y applique à la lettre : un gain se déclare sur plusieurs graines ou ne se déclare pas.

**[Plateformes conversationnelles](MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/README.md) -- quand la GenAI devient un produit que quelqu'un utilise** -- Un modèle qui répond n'est pas encore un service : il lui faut une interface, des comptes, une mémoire, des outils et une responsabilité d'exploitation. La sous-série est nommée par sa **fonction** plutôt que par un produit, car elle compare deux terrains complémentaires et fait de leur choix une décision d'architecture.

*Open WebUI*, d'abord : la plateforme auto-hébergée, avec un tour guidé fonctionnalité par fonctionnalité, puis une série d'**assurance qualité automatisée** avec Playwright -- authentification, streaming de réponses, RAG, outils MCP, multi-tenant et intégration continue. *AI-Engine*, ensuite : l'extension GenAI d'un site **WordPress** existant, terrain radicalement différent où l'IA doit s'insérer dans un CMS déjà en production, avec son contenu, ses formulaires et ses visiteurs. Les notebooks explorent la plateforme **par son API** contre une **instance jetable** de WordPress, montée puis détruite : ils restent reproductibles sans risquer un site réel. Le parcours couvre le socle, la présentation, les chatbots, les formulaires, les visiteurs anonymes, les environnements multi-fournisseurs et l'exposition d'un serveur MCP. Il aborde ainsi les questions propres au déploiement : ingérer un corpus long en RAG, **séparer les espaces vectoriels** de recette et de production, mesurer la dérive d'un copilot, tester un formulaire conditionnel et vérifier un rendu. Le MCP est traité dans les deux sens -- consommer un serveur d'outils et exposer WordPress lui-même comme serveur -- avant une comparaison centrée non sur « la meilleure plateforme », mais sur le terrain auquel chacune convient.

Côté **mémoire des agents**, la sous-série [RAG et Mémoire Sémantique](MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/README.md) est devenue un cursus complet : retrieval avancé, embeddings et tokenisation reconstruits depuis zéro, stockage vectoriel, puis Kernel Memory en processus, en Python, en recherche hybride et multimodale. Qdrant en est le backend opérationnel pour ancrer les agents de codage dans l'historique des conversations et le code des dépôts.

**[Aspire](MyIA.AI.Notebooks/GenAI/Aspire/README.md) -- la pile IA inattendue : C#/.NET** -- Une sous-série à contre-courant : décrire modèles, bases vectorielles, services, secrets, santé et télémétrie dans un **AppHost** compilé et typé plutôt que dans un assemblage de Compose et de scripts. Partie de l'orchestration GPU et multi-machines, elle couvre désormais observabilité OpenTelemetry, streaming d'agents par Channels, tests d'intégration avec conteneurs éphémères, garde-fous Roslyn exécutés dans le build et flotte sémantique multi-connecteurs. Deux axes vivent en sous-séries propres : [EF Core](MyIA.AI.Notebooks/GenAI/EFCore/) fait du compilateur un garde-fou jusque dans les requêtes et le [SDK GitHub Copilot](MyIA.AI.Notebooks/GenAI/CopilotSDK/) pilote depuis C# un agent en streaming avec des endpoints typés.

**[Vibe-Coding](MyIA.AI.Notebooks/GenAI/Vibe-Coding/README.md)** -- Le développement assisté par agents IA : ateliers progressifs sur Claude Code et Roo Code, compétences, sous-agents, MCP et hooks, complétés par les agents conteneurisés Claw-Systems et le proxy multi-provider Claudish. La question directrice est celle qui suit naturellement l'écriture assistée : *si un agent produit le code, qui le relit et quelles garanties restent indépendantes de lui ?* L'analyseur Roslyn **MyIA.AgentSafetyAnalyzer** compile ces garde-fous dans le build : règles de sécurité, correction automatique des secrets codés en dur, registre de suppressions et tests. Il est distinct d'**AgentGuard.Analyzers**, le volet Roslyn de la sous-série Aspire. Un second chantier branche un REPL C# sur un processus .NET vivant pour l'observer et le corriger sans l'arrêter.

**Projets étudiants de bout en bout** -- La sous-série [GenAI/CaseStudies](MyIA.AI.Notebooks/GenAI/CaseStudies/README.md) réunit quatre projets complets, adaptés de réalisations étudiantes : duel verbal multi-agent avec génération d'images, générateur de recettes orchestré par agents, chatbot médical multi-agent avec plugins, et jeu interactif inspiré de Fort Boyard. Quatre systèmes complets — où placer la logique métier, comment empêcher deux agents de tourner en rond, quand arrêter une conversation — ce qu'aucun tutoriel ciblé ne montre.

Tout converge dans un fil rouge transverse : le **Texte** structure un script, l'**Image** l'illustre, l'**Audio** le narre, la **Vidéo** l'assemble, et **Semantic Kernel** orchestre l'ensemble en agents autonomes -- c'est ce parcours d'intégration qui distingue une démonstration d'un produit déployable.

Python | [README détaillé](MyIA.AI.Notebooks/GenAI/README.md)

**[FallacyDetection](MyIA.AI.Notebooks/GenAI/FallacyDetection/README.md) -- reconnaître un sophisme, et savoir pourquoi le modèle l'a reconnu** -- Une série jeune, et volontairement exposée : elle prend un problème que le reste du dépôt aborde par le formalisme -- la détection de sophismes -- et l'attaque cette fois par le modèle de langage, en s'imposant de rendre compte de sa décision. La question directrice n'est pas « le modèle classe-t-il bien ? » mais **« qu'a-t-il appris au juste ? »** : distinguer ce qu'un *fine-tuning* mémorise (le motif de raisonnement « du général au particulier ») de ce qu'un *post-training* sait réemployer sur des cas inédits. Le verdict est arbitré par des autoencodeurs parcimonieux entraînés sur le modèle lui-même -- ce qui fait de cette série le prolongement appliqué de la strate 6 du banc **ICT**, et son critère de succès déclaré : sans SAE disponibles sur au moins trois tailles de modèle, le pivot interprétabilité n'est pas tenu, et l'EPIC l'écrit noir sur blanc plutôt que de reformuler le succès après coup. La vraie difficulté est celle des **données**, et la série la traite en premier plutôt qu'en note de bas de page : un petit corpus d'amorçage, puis deux sources d'une autre échelle -- les corpus académiques annotés et surtout un corpus **synthétique** engendré par le produit cartésien des cartes **Argumentum** (167 scénarios de discours croisés avec 1 408 sophismes). Les deux notebooks en ligne publient un résultat négatif : le [paysage des jeux de données](MyIA.AI.Notebooks/GenAI/FallacyDetection/02_fallacy_datasets_landscape.ipynb) confronte les corpus académiques disponibles en accès réel, l'[écart de couverture taxonomique](MyIA.AI.Notebooks/GenAI/FallacyDetection/03_taxonomy_coverage_gap.ipynb) mesure ce qu'ils couvrent effectivement de la taxonomie Argumentum -- et la réponse est : une petite part, très inégalement répartie. Sous-série de GenAI depuis la tranche 1 de #13581 (2026-08-30) -- voir `docs/notebook-metadata/production-scope.md` pour le périmètre in-scope.

### QuantConnect -- Trading algorithmique

Peut-on appliquer l'IA aux marchés financiers -- et comment savoir si une stratégie *marche* vraiment, plutôt que d'avoir simplement eu de la chance sur un historique ? Le trading algorithmique génère aujourd'hui plus de la moitié des volumes échangés, et cette série apprend à construire, backtester et déployer ses propres stratégies sur le framework open-source **LEAN** de QuantConnect, utilisé par des milliers de quants professionnels. Son fil conducteur n'est pas la course au rendement : c'est la **discipline d'évaluation** qui sépare un edge réel d'un mirage de backtest -- validation hors échantillon, walk-forward, répétition multi-graine, coûts de transaction réels, tests de significativité. Le cours et les stratégies s'exécutent en backtest et paper trading sur le cloud QuantConnect (free tier), sans capital ; un laboratoire standalone permet en parallèle d'éprouver localement les idées sur des données publiques avant de les porter vers LEAN. Le livre de référence est *Hands-On AI Trading*, de Jared Broad, fondateur de QuantConnect.

**[Le cours](MyIA.AI.Notebooks/QuantConnect/Python/README.md) -- des fondations LEAN à l'IA de pointe** -- Le parcours pédagogique monte en huit phases et impose de maîtriser l'écosystème avant tout modèle : architecture LEAN et cycle de vie d'un algorithme, gestion des données, sélection d'univers, classes d'actifs (actions, options, futures, forex), types d'ordres et risk management, puis l'Algorithm Framework modulaire (Alpha, Portfolio Construction, Execution, Risk) qui rend les stratégies scalables. Vient seulement ensuite l'IA : données alternatives et analyse de sentiment, machine learning classique (Random Forest, XGBoost), deep learning pour séries temporelles (LSTM, Transformers, autoencodeurs), et enfin reinforcement learning, LLMs employés comme générateurs de signaux, détection de régime de marché et déploiement live. Chaque notebook s'exécute sur le cloud, avec des contournements documentés pour rester dans le free tier.

**[Les stratégies](MyIA.AI.Notebooks/QuantConnect/projects/README.md) -- ce qui survit au backtest réaliste** -- Un large catalogue de stratégies prêtes à backtester accompagne le cours, du momentum multi-actifs et des facteurs Fama-French jusqu'aux options couvertes, au mean reversion et aux approches ML/DL/RL. Leur singularité pédagogique tient en un point : les performances varient *volontairement*. Quelques stratégies dominent durablement, beaucoup ne battent leur indice que dans certains régimes, quelques-unes perdent -- et c'est précisément l'enseignement. Le suivi de tendance survit aux longues périodes ; un croisement de moyennes brillant sur backtest court s'effondre en hors-échantillon, démonstration concrète du danger du surapprentissage ; des composites censés cumuler les défenses font parfois moins bien que leurs briques isolées. Chaque stratégie vient avec son code source, son notebook de recherche standalone (yfinance/pandas) et ses métriques vérifiées sur le cloud.

**[La recherche standalone](MyIA.AI.Notebooks/QuantConnect/research/README.md) -- l'idéation avant le cloud** -- Ce laboratoire regroupe des notebooks autonomes en yfinance, pandas et scikit-learn, exécutables localement sans compte QuantConnect : facteurs, allocation, volatilité réalisée, prototypes RL. Une idée y est réfutée ou affinée sur données publiques avant le backtest haute fidélité sur LEAN. Les verdicts négatifs y ont la même valeur que les succès, du test de Diebold-Mariano sur la fréquence d'échantillonnage aux leçons de reward shaping.

**[Le pipeline d'entraînement ML](MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/README.md) -- séparer l'edge du hasard** -- Un pipeline complet entraîne et évalue des modèles de forecasting financier : LSTM, Transformer, PatchTST, iTransformer, Mamba, réseaux de neurones sur graphes, Decision Transformer et mélanges d'experts, plus l'évaluation zero-shot de modèles foundation (Chronos-Bolt, Kronos) et une série systématique de modèles de volatilité (HAR, GARCH, HEAVY, Markov-switching). Mais l'architecture n'est pas le coeur du sujet : la valeur tient au protocole de validation, intentionnellement sévère -- walk-forward expansif à plusieurs plis, répétition sur plusieurs graines, test de Diebold-Mariano pour la significativité statistique, univers expurgé des mégacaps technologiques pour éviter le biais de survie, coûts de transaction appliqués. Le verdict est tranché -- BEATS, NO BEATS ou INCONCLUSIVE -- et la majorité des étages testés sont rejetés, résultats négatifs documentés au même titre que les succès. Un résultat marquant en ressort : les modèles qui *classent une action* (acheter, tenir, vendre) battent ceux qui *prédisent un rendement*, parce que la traduction d'une prévision en position détruit le signal via les coûts et la discrétisation. L'entraînement GPU y est thermalement protégé pour tourner sur du matériel réel.

**Fondations formelles du sizing** -- La sous-série [kelly_lean](MyIA.AI.Notebooks/QuantConnect/kelly_lean/README.md) prouve en Lean 4 avec Mathlib l'optimalité du critère de Kelly pour le *position sizing* — fraction risquée `f* = (b·p − q) / b` qui maximise la log-croissance asymptotique du capital sur un pari de Bernoulli. Petit module, mais essentiel : relier le backtest à un théorème d'optimalité formellement vérifié, plutôt qu'à une heuristique empirique.

**[Le cours partenaire](MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/README.md) -- de l'exercice au déploiement** -- Un volet dédié, sponsorisé par Jared Broad (fondateur de QuantConnect) via le palier Trading Firm, propose une progression opérationnelle : des templates gradués (débutant : croisement EMA sur crypto ; intermédiaire : ranking momentum avec Algorithm Framework ; avancé : RandomForest sur BTC avec ré-entraînement mensuel), des exemples d'instructeur validés par des backtests réels, et des notebooks de recherche QuantBook qui matérialisent le workflow canonique du quant -- *idée, recherche, backtest, déploiement*. Plusieurs stratégies déployées sur le cloud sont directement issues des modèles retenus par le pipeline ML, bouclant la chaîne de la recherche à la production.

Cette série est le terrain où convergent les autres : les modèles prédictifs de **ML** s'y appliquent à des données de marché réelles, **RL** y prolonge ses mêmes gradients et sa même méfiance du surapprentissage, **Probas** y nourrit la gestion bayésienne du risque, **Search** y rejoint l'optimisation d'hyperparamètres, et **GenAI** y branche ses LLMs sur l'analyse de sentiment. Surtout, la discipline d'évaluation qu'elle exige -- préférer un "NO BEATS" vérifié à un "prometteur" sans preuve -- est exactement celle que réclame la série ML : ici, elle a le marché pour juge.

Python | [README détaillé](MyIA.AI.Notebooks/QuantConnect/README.md) | [Strategies](MyIA.AI.Notebooks/QuantConnect/projects/README.md)

### RL -- Apprentissage par renforcement

Comment apprendre à décider quand personne ne fournit la bonne réponse ? Là où l'apprentissage supervisé prédit à partir d'exemples étiquetés et l'apprentissage non supervisé dégage des structures, le renforcement **agit** : un agent choisit une action, observe la récompense ou la pénalité que lui renvoie son environnement, et corrige sa stratégie à l'essai et à l'erreur. C'est le paradigme derrière AlphaGo, la marche des robots et les moteurs de recommandation. Le fil conducteur de la série est un pari pédagogique assumé -- *agir d'abord, comprendre ensuite* : on entraîne un agent fonctionnel en quelques lignes avec un framework industriel, puis on réimplémente les mêmes algorithmes à la main pour voir ce qui tourne sous le capot.

**Le framework d'abord -- un agent qui marche en quelques lignes** -- Le point d'entrée est **Stable Baselines3** : on entraîne un agent PPO à équilibrer un bâton (CartPole) et on visualise sa progression avant d'avoir écrit la moindre équation. La prise en main s'enrichit ensuite des outils de production -- wrappers pour reconfigurer un environnement, callbacks pour monitorer et sauvegarder, multiprocessing pour accélérer -- puis franchit un saut qualitatif avec les tâches à objectif (goal-conditioned RL) et l'astuce HER, qui réinterprète les échecs comme des succès : on passe d'équilibrer un bâton à garer une voiture. L'intuition concrète précède la théorie, jamais l'inverse.

**Les maths sous le capot -- réimplémenter pour comprendre** -- Le second temps quitte le framework et reconstruit tout depuis zéro. On commence par la question fondatrice -- explorer de nouvelles options ou exploiter ce qui marche déjà -- sur les bandits manchots (epsilon-greedy, Thompson Sampling, regret cumulé). Vient ensuite la formalisation : processus de décision markovien, équation de Bellman, value et policy iteration, Q-Learning tabulaire. Puis le passage à l'échelle par les réseaux de neurones, en PyTorch pur et par paliers : DQN et REINFORCE, l'architecture acteur-critique (A2C), PPO et son surrogate clippé avec GAE, SAC et le cadre maximum d'entropie pour les actions continues, enfin GRPO -- la variante critic-free popularisée par DeepSeek-R1, appliquée ici à une allocation de portefeuille synthétique, pont direct vers le RLHF. Chaque algorithme éclaire un compromis -- on-policy contre off-policy, value-based contre policy-based, biais contre variance.

**Plusieurs agents qui apprennent -- du jeu solitaire à l'interaction** -- Vient ensuite le multi-agent : plusieurs agents qui apprennent simultanément, coopèrent ou s'affrontent. Avec PettingZoo et l'Independent Q-Learning, un agent affronte sa propre copie en self-play sur un jeu à somme nulle -- la même situation que la théorie des jeux, mais où l'équilibre est *appris* plutôt que calculé.

**Ce que le manuel escamote -- les impasses traitées de front** -- La série ne s'arrête pas au socle. Dyna-Q apprend un modèle du monde ; le RL offline affronte l'erreur d'extrapolation ; reward shaping et curriculum montrent comment une récompense mal formée enseigne autre chose ; POMDP, C51 et curiosité retirent tour à tour l'état vrai, l'espérance unique et la récompense externe. Le RL hiérarchique ajoute l'abstraction temporelle par le framework des options, tandis que le Climbing Game montre l'échec de coordination multi-agent : une excellente action conjointe peut être sous-évaluée par chaque apprenant indépendant.

**Post-training des LLMs -- le RL là où il compte aujourd'hui** -- L'arc `rlpt_*` branche ces mécanismes sur l'alignement des modèles de langage : PPO façon RLHF, GRPO à récompense vérifiable, anatomie du reward hacking et comparaison DPO hors ligne/RL en ligne. Les notebooks partent de boucles transparentes, puis exécutent GRPO sur un vrai modèle local compact avec récompenses vérifiables. GRPO passe aussi au banc face à PPO sur plusieurs graines avec Wilcoxon et bootstrap ; un verdict INCONCLUSIVE est conservé tel quel. Le pont atterrit dans [GenAI / PostTraining](MyIA.AI.Notebooks/GenAI/PostTraining/README.md), qui reprend les mêmes techniques à l'échelle GPU avec solveurs et contrôles de reward hacking.

Ce dernier pas ouvre la porte des séries voisines. Le multi-agent prolonge directement **GameTheory** -- équilibre de Nash appris au lieu d'être démontré -- tandis que les MDP généralisent les processus décisionnels bayésiens de **Probas**, dont la théorie de l'utilité fournit le socle. Le renforcement partage avec **ML** ses outils (PyTorch, gradients) et avec **Search** sa parenté entre value iteration et exploration d'un espace d'états ; il s'incarne enfin sur données réelles en **QuantConnect**, où acheter et vendre deviennent des actions et le profit une récompense. L'arc post-training rejoint frontalement **GenAI/PostTraining**, qui aborde le même sujet par l'ingénierie des modèles plutôt que par l'algorithmique du renforcement -- les deux séries se lisent en vis-à-vis. Le contraste feed-forward contre récurrent qui structure ses architectures rejoint enfin la question soulevée par **IIT**.

Python | [README détaillé](MyIA.AI.Notebooks/RL/README.md)

### IIT -- Théorie de l'Information Intégrée

La conscience est-elle mesurable ? La théorie de l'information intégrée, proposée par Giulio Tononi, répond oui : un système est conscient dans la mesure où il intègre de l'information de manière irréductible, et cette quantité porte un nom et une valeur calculable -- **Phi**. C'est la série la plus spéculative du dépôt, et l'une de celles qui ont le plus grandi : partie d'un noyau PyPhi (la bibliothèque de référence du laboratoire Tononi), elle s'est prolongée en un véritable programme de recherche interne, la série **ICT**. Son fil conducteur reste le même : calculer rigoureusement des mesures candidates de l'intégration et de l'émergence, tout en gardant un esprit critique sur ce qu'elles signifient vraiment.

**Calculer Phi -- du réseau causal à la géométrie de l'information** -- On part de circuits binaires élémentaires : une matrice de transition décrit les règles d'évolution du système, et le calcul de Phi sur un petit réseau XOR rend concrète la notion d'intégration irréductible. Partition d'information minimale, répertoires cause-effet et mécanismes maximalement irréductibles déconstruisent ensuite la mesure, avant que l'explosion combinatoire n'impose le coarse-graining. Le noyau récent rend aussi le **problème de frontière** mesurable : plusieurs découpages d'un même substrat sont comparés, Phi et information efficace peuvent se dissocier, et le complexe majeur opérationnalise le postulat d'exclusion.

**De la mesure aux débats -- ce que Phi engage** -- L'IIT a inspiré le Perturbational Complexity Index clinique et fournit un cas d'école sur les critères de scientificité d'une théorie de l'esprit. Plutôt qu'un duel IIT contre Global Workspace, le parcours confronte désormais six lentilles -- Global Workspace, Global Neuronal Workspace, traitement prédictif, théories d'ordre supérieur, Attention Schema et modèle de soi transparent -- sur des bancs de dissociation exécutés. Une théorie n'y est admise que par le contraste qu'elle rend effectivement mesurable. La question touche directement l'IA : une inférence purement feed-forward peut calculer sans boucle causale intégrée, mais le notebook demande précisément quelles observations permettraient de distinguer cette affirmation d'une simple métaphore.

**ICT -- des états aux trajectoires, jusqu'au LLM** -- L'extension [ICT](MyIA.AI.Notebooks/IIT/ICT-Series/README.md) (*Integrated Causal Trajectories*), développée dans le dépôt même, déplace la question : au lieu de mesurer l'intégration d'un *état*, elle mesure ce qu'une **trajectoire** de système fait émerger causalement au fil du temps. Sa batterie réunit trois gains complémentaires -- émergence causale (le niveau macro prédit-il mieux que le micro, à la Hoel), surprise transitionnelle (énergie libre) et compression (MDL) -- chacun crédité seulement s'il dépasse à la fois un mélange aléatoire et un modèle-contrôle.

Avec une cinquantaine de notebooks, la série a cessé de tenir sur une seule échelle et se lit désormais sur **deux axes**, ce que le [cadrage](MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Framing.md) explicite. Un **axe vertical** empile sept strates de substrats, du plus transparent au plus opaque : le tri auto-organisé, la morphogenèse dynamique (Gray-Scott, paysages d'attracteurs, signaux d'alerte précoce), les agents -- réactifs, inhibés au sens de Laborit, puis stratégiques à la Axelrod --, les trois scalaires fondateurs sur substrats non-LLM (identité MDL, ε-machine, flèche du temps, budget de réversibilité), puis les représentations internes d'un **transformer réel** lues à travers un autoencodeur parcimonieux (SAE), le **discours** lui-même comme substrat, et enfin les *freebits d'ordre 2* -- ces degrés de liberté qu'aucune histoire causale antérieure ne détermine. La charnière entre les deux moitiés est le **grokking** : l'instant où un représentant interne cesse d'anticiper un comportement pour devenir un état de représentation apprise. Un **axe transverse** tresse par-dessus des expériences qui éclairent un même substrat sous plusieurs angles -- prégnance thomienne, morphogenèse rhétorique, obstruction de Čech, invention de symboles et adoption collective, inoculation. Ce sont *des pattes, pas des barreaux* : en ajouter une ne renumérote aucune strate.

Les claims de ce laboratoire sont suivis dans une [matrice des dissociations](docs/ict/dissociations-matrix.md) : proxy, contrôle, réplicas, verdict sobre et portée explicite. Le package Python `ict/`, installable et couvert par ses suites pytest, transforme les mesures récurrentes en code de recherche validé plutôt qu'en cellules isolées. Un capstone RL relie enfin ICT au post-training : dérive de persona sous récompense hackable, bras inoculé contre non inoculé, GRPO et contrôles falsifiables. Un résultat négatif -- dissociation entre lentilles, échec de recouvrement SAE, absence d'effet -- y vaut autant qu'une convergence : c'est un laboratoire, pas une démonstration.

Cette série dialogue avec **Probas** et **GameTheory**, dont elle partage les concepts de causalité et d'interaction, et avec **RL** : la distinction feed-forward contre récurrent, qui annule ou non Phi, éclaire le choix d'architecture d'un agent. L'ICT rejoint le fil rouge **causalité** du dépôt -- le même opérateur `do(·)` de Pearl s'instancie dans Tweety (symbolique), Infer.NET (message passing), PyMC (MCMC) et ICT (théorie de l'information). Le constat qu'un modèle de langage feed-forward a un Phi nul prolonge enfin les discussions sur la conscience artificielle qui traversent **GenAI** -- que l'ICT reprend désormais par la mesure plutôt que par le débat.

Python | [README détaillé](MyIA.AI.Notebooks/IIT/README.md)

### CaseStudies -- Études de cas interdisciplinaires

Que se passe-t-il quand on cesse d'étudier les techniques en silos ? L'IA réelle ne fonctionne presque jamais avec un seul paradigme : un assistant de diagnostic combine des règles symboliques, des modèles probabilistes, de la recherche heuristique et des contraintes formelles. Cette série, conçue comme un devoir intégrateur de fin de cycle, prend trois problèmes métier -- un diagnostic médical, une planification oncologique et un dispatch énergétique -- et y compose plusieurs solveurs en un seul système décisionnel cohérent. Son fil conducteur est l'architecture hybride en couches, et l'idée que l'**ordre de composition** importe autant que les briques elles-mêmes.

**Composer les paradigmes en cascade -- l'architecture hybride** -- Chaque projet empile cinq couches : des connaissances métier (ontologies OWL, règles), un filtre de contraintes dures (CSP, SMT, OR-Tools), une modélisation de l'incertitude (bayésien, Pyro, Infer.NET), une optimisation (recherche A-star, algorithme génétique, et au-delà le renforcement) et une décision finale expliquée. On filtre avant d'optimiser, on modélise l'aléatoire avant de valider sous contraintes : le [Diagnostic Medical](MyIA.AI.Notebooks/CaseStudies/Diagnostic-Medical/README.md) articule recherche informée, algorithme génétique et validation par solveur Z3 ; l'[Oncology Planning](MyIA.AI.Notebooks/CaseStudies/Oncology-Planning/README.md) marie ontologie, planification CP-SAT et inférence probabiliste ; le [SmartGrid Energy](MyIA.AI.Notebooks/CaseStudies/SmartGrid-Energy/README.md) traite l'*unit commitment / dispatch* (CC3 EPF) en combinant optimisation CP-SAT (centrales pilotables, mix renouvelable incertain), raisonnement bayésien (risque de défaillance) et arbitrage multi-objectif (coût vs émissions). Aucune couche ne suffit seule, et c'est tout l'enseignement.

**Le jumeau numérique -- un patient simulé pour décider sans risque** -- Les deux projets reposent sur un modèle de patient simulé : un objet logiciel qui représente un état clinique et réagit aux interventions proposées. Ce pattern de jumeau numérique, devenu central en santé numérique comme en industrie, permet de tester des scénarios de traitement sans toucher au patient réel. La pédagogie privilégie l'autonomie : chaque projet fournit un template étudiant exécutable de bout en bout -- y compris lorsque les exercices ne sont pas complétés -- et une solution de référence pour s'autoévaluer.

Le choix du médical est pédagogique, pas exclusif : la même architecture en couches se transpose telle quelle à la finance (jumeau de marché, contraintes réglementaires, signaux probabilistes), à la logistique ou à la maintenance prédictive. C'est le devoir qui ferme la boucle du cursus, en convoquant simultanément **Search**, **SymbolicAI**, **Probas**, **Planners**, **SemanticWeb** et **RL** autour d'une seule question réelle.

Python | [README détaillé](MyIA.AI.Notebooks/CaseStudies/README.md)

### cross-series -- Applications transverses

Et après le notebook ? Le répertoire `cross-series/` rassemble ce qui ne tient dans aucune série parce que cela les traverse toutes -- applications complètes, socle partagé, outillage de la collection elle-même.

**[`matching-cv`](MyIA.AI.Notebooks/cross-series/matching-cv/README.md) -- un problème, trois lectures** -- Une application web Flask qui confronte trois façons d'apparier un CV à une offre d'emploi : le comptage de mots-clés comme référence transparente, la similarité sémantique par plongements avec cache vectoriel (issue de **GenAI**), et l'appariement stable de Gale-Shapley (rencontré en **GameTheory** et prouvé en Lean dans `game_theory_lean`). La leçon n'est pas qu'un algorithme gagne : c'est que **le « meilleur » appariement dépend du critère**, le meilleur score individuel n'étant pas l'affectation globalement stable -- la différence, rendue visible sur les mêmes données, entre optimum local et stabilité collective. La même démarche que le banc d'essai du **Sudoku**, transposée à une application déployable avec ses tests et son interface.

**[`socle-metadata-driven`](MyIA.AI.Notebooks/cross-series/socle-metadata-driven/Socle-MetadataDriven-Csharp.ipynb) -- ce que toutes les familles .NET partagent** -- Là où `matching-cv` *combine* des séries, ce notebook C# expose ce qu'elles ont en *commun* : la bibliothèque [`MyIA.AI.Shared`](MyIA.AI.Shared/), qui factorise trois besoins qu'autrement chaque série réécrirait -- découverte de types par décoration (des attributs suffisent, aucun enregistrement explicite), sérialisation JSON/XML aller-retour d'un graphe d'entités, et surtout la règle métier *low-code* : un prédicat qui arrive sous forme de chaîne -- d'un fichier, d'un CSV, d'un utilisateur non-développeur -- compilé une fois puis appliqué à N instances. C'est la différence entre coder N branches conditionnelles et piloter la logique par les données.

**`i18n` -- traduire une collection sans la casser** -- Un pilote du mécanisme de traduction appliqué à la documentation : un README découpé en segments repérés par clé stable, colonne source française remplie, colonne cible vide, et le rendu qui reconstruit le document à l'identique. C'est le pendant markdown du corpus `translations/` (33 CSV, 24 470 cellules de notebooks) ; l'un et l'autre attendent le même feu vert éditorial avant de lancer les huit langues. Le mécanisme, lui, est déjà là et vérifiable -- ce qui manque est une décision, pas une technique.

[README détaillé](MyIA.AI.Notebooks/cross-series/README.md)

---

## Structure du dépôt

```text
CoursIA/
  MyIA.AI.Notebooks/          Notebooks interactifs, organisés par série
    Search/                    Algorithmes de recherche (Python, C#)
    Sudoku/                    Résolution multi-paradigme (Python, C#)
    SymbolicAI/                IA symbolique (Python, Lean 4, C#)
      Tweety/ SemanticWeb/ Lean/ SMT/ Planners/ SmartContracts/ Argument_Analysis/ SymbolicLearning/
    Probas/                    Programmation probabiliste (C#, Python)
    GameTheory/                Théorie des jeux (Python, Lean 4)
    ML/                        Machine Learning (C#, Python)
    RL/                        Reinforcement Learning (Python)
    GenAI/                     IA générative (Python, C#)
      00-GenAI-Environment/ Image/ Audio/ Video/ Texte/ SemanticKernel/ FineTuning/ PostTraining/
      Plateformes-Conversationnelles/ Vibe-Coding/ RAG-et-Memoire-Semantique/ CaseStudies/ tutorials/
      Aspire/                  Pile GenAI orchestrée en C#/.NET (AppHost Aspire)
      CopilotSDK/              Agents programmables avec le SDK GitHub Copilot
      EFCore/                  Accès aux données .NET vérifié à la compilation
    QuantConnect/              Trading algorithmique (Python)
      Python/                  Notebooks pédagogiques
      research/                Recherche standalone locale (yfinance/pandas)
      projects/                Stratégies backtestées
      ML-Training-Pipeline/    Pipeline DL forecasting
      partner-course-quant-trading/ Projets étudiants
    CaseStudies/               Études de cas interdisciplinaires (Python)
    cross-series/              Applications transverses multi-domaines (Python)
      matching-cv/ socle-metadata-driven/ i18n/
    IIT/                       Information intégrée + série ICT (Python)
    Config/                    Configuration API

  scripts/                     Validation, exécution, analyse
  docs/                        Documentation pérenne (procédures, inventaires, leçons consolidées)
  translations/                Corpus de traduction des notebooks (inventaire et statut dans son README)
  slides/                      Présentations pédagogiques
  docker-configurations/       Infrastructure Docker GPU
  GradeBookApp/                Notation étudiants
  GradeBookApp.Tests/          Tests du moteur de notation
  MyIA.AI.Shared/              Bibliothèque C# partagée
  MyIA.AI.Shared.Tests/        Tests de la bibliothèque partagée
  MyIA.Trading.Converter/      Conversion de formats de données de trading
  THIRD_PARTY_NOTICES.md       Attributions des sources et composants tiers
```

---

## Mise en route

### Prérequis

- Python 3.10+ avec pip
- .NET 9.0+ SDK (pour notebooks C# — .NET 10 LTS validé en local)
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
# Préciser --version : le dernier build publié casse #!import (15 notebooks C#).
# Version vérifiée compatible : cf docs/reference/kernels-runtime.md
dotnet tool install --global Microsoft.dotnet-interactive --version 1.0.617701
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
| GenAI | `GenAI/00-GenAI-Environment/` (6 notebooks : environment, services Docker, endpoints API, validation, test ComfyUI local, déploiement Docker local) | `requirements.txt` (+ `-audio` / `-video`) ; `00-GenAI-Environment/validate_auth.py` |
| GameTheory | `GameTheory/GameTheory-01-Setup.ipynb` | `GameTheory/scripts/setup_wsl_openspiel.sh`, `GameTheory/scripts/setup_wsl_lean4.sh`, `GameTheory/scripts/setup_lean4_kernel.ps1` |
| Sudoku | `Sudoku/Sudoku-00-Environment-Csharp.ipynb` | kernel .NET Interactive |
| Probas | `Probas/Infer/Infer-1-Setup.ipynb`, `Probas/PyMC/PyMC-01-Setup.ipynb` | `Probas/Infer/scripts/setup_environment.ps1` |
| QuantConnect | `QuantConnect/Python/QC-Py-01-Setup.ipynb` | `requirements.txt` |
| Lean | `SymbolicAI/Lean/Lean-1-Setup.ipynb` | `SymbolicAI/Lean/scripts/setup_wsl_python.sh`, `SymbolicAI/Lean/scripts/validate_lean_setup.py` |
| Planners | `SymbolicAI/Planners/00-Environment/Planners-0-Setup.ipynb` | `requirements.txt` ; `SymbolicAI/scripts/install_clingo.py` |
| SemanticWeb | `SymbolicAI/SemanticWeb/SW-1-CSharp-Setup.ipynb` | kernel .NET Interactive |
| SmartContracts | `SymbolicAI/SmartContracts/00-Foundations/SC-1-Setup-Foundry.ipynb`, `SC-2-Setup-Web3py.ipynb` | `SymbolicAI/SmartContracts/setup_env.py`, `SymbolicAI/SmartContracts/scripts/setup_wsl_smartcontracts.sh` |
| Tweety | `SymbolicAI/Tweety/Tweety-1-Setup.ipynb` | `tweety_init.py` (JDK auto-télécharge) |
| Argument Analysis | `SymbolicAI/Argument_Analysis/Argument_Analysis_UI_configuration.ipynb` | `install_jdk_portable.py` |
| IIT | `requirements.txt` | `IIT/scripts/setup_pyphi_env.ps1` |
| GenAI / Aspire | `GenAI/Aspire/01-Aspire-Orchestration-GenAi.ipynb` | SDK .NET 10 + CLI Aspire (`dotnet tool install -g Aspire.Cli`) ; Docker démarré |
| GenAI / FallacyDetection | -- (kernel Python de base) | `scripts/fallacy_detection/extract_jessynoo_fallacy.py` (stdlib seule) |
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
| GameTheory (optionnel) | `GameTheory/.env` | fournisseurs LLM et paramètres d'exécution documentés dans `.env.example` |
| Lean | `SymbolicAI/Lean/.env` | `OPENAI_API_KEY`, `GITHUB_TOKEN` |
| Argument Analysis | `SymbolicAI/Argument_Analysis/.env` | `OPENAI_API_KEY` |
| QuantConnect | `QuantConnect/.env` | `QC_API_USER_ID`, `QC_API_ACCESS_TOKEN` |
| C# Notebooks | `Config/settings.json` (exemples : `settings.json.openai-example`, `settings.json.azure-example`) | `apikey`, `model` |
| Docker ComfyUI | `docker-configurations/services/comfyui-qwen/.env` | `CIVITAI_TOKEN`, `HF_TOKEN` |

Chaque dossier contient un fichier d'exemple documentant les variables (`.env.example`, ou `settings.json.openai-example` / `.azure-example` pour `Config/`). Copier et éditer :

```bash
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
# Éditer le fichier .env avec vos clés
```

---

## Kernels Jupyter

**Critère d'inclusion** : un kernel figure ici s'il est **requis par au moins un notebook du dépôt** (`metadata.kernelspec`). Une partie est **créée par un script de mise en route du dépôt** (`python3-wsl` via `SymbolicAI/Lean/scripts/setup_wsl_python.sh`, `pyphi` via `IIT/scripts/setup_pyphi_env.ps1`, `smartcontracts` via `SymbolicAI/SmartContracts/scripts/setup.sh`, kernel `python3` de base), les autres sont **consommés sans script dédié** (`mcp-jupyter`, `mcp-jupyter-py310`, `coursia-ml-training`, `coursia-sae`, `epita_symbolic_ai`). La colonne « Installation canonique » nomme le script de setup quand il existe, sinon renvoie à `docs/reference/kernels-runtime.md`. Les artefacts d'environnement local (`conda-torch`, `miniconda3-base`, `pymc18-jsboi`, etc.) ne sont pas des prérequis de projet : ils relèvent de `jupyter kernelspec list` sur la machine de développement.

| Famille | Kernels requis par le dépôt | Séries principales | Installation canonique |
|---------|-------------------------------|-------------------|----------------------|
| **Python** | `python3`, `python3-wsl`, `mcp-jupyter`, `mcp-jupyter-py310`, `coursia-ml-training`, `coursia-sae`, `epita_symbolic_ai`, `pyphi`, `smartcontracts` | GenAI, QuantConnect, Search, ML, IIT | `pip install ipykernel` + `python -m ipykernel install --user --name=<kernel>` (kernel de base) ; voir `docs/reference/kernels-runtime.md` pour les envs conda dédiés |
| **.NET Interactive** | `.net-csharp`, `.net-fsharp`, `.net-powershell` | Sudoku, Search, Probas, ML.NET, SemanticWeb | `dotnet tool install --global Microsoft.dotnet-interactive --version 1.0.617701` puis `dotnet interactive jupyter install` |
| **Lean 4** | `lean4`, `lean4-wsl` | Lean, GameTheory (notebooks Lean) | `MyIA.AI.Notebooks/GameTheory/scripts/setup_wsl_kernel.ps1` + `setup_lean4_native.sh` (elan) |

Pour la **liste exhaustive et à jour** (versions épinglées, historique, dépendances conda), consulter [`docs/reference/kernels-runtime.md`](docs/reference/kernels-runtime.md), qui prime sur tout inventaire figé. Pour vérifier l'état local à tout moment : `jupyter kernelspec list`.

Limitations connues : les notebooks C# avec `#!import` nécessitent une exécution cellule par cellule (incompatible Papermill). Lean 4 requiert WSL sous Windows. Le détail des versions compatibles (dotnet-interactive, Lean/elan) et leur historique figure dans [docs/reference/kernels-runtime.md](docs/reference/kernels-runtime.md).

---

## Infrastructure Docker

Pour les notebooks GenAI avancés utilisant des modèles locaux (Qwen Image Edit, ComfyUI Video, etc.), une infrastructure Docker avec support GPU est fournie.

Services disponibles (sous `docker-configurations/services/`, 19 dossiers) : Qwen Image Edit (~29 Go VRAM), ComfyUI Video (~12 Go), Stable Diffusion Forge (~10 Go), Whisper (STT, 2 services), MusicGen, TTS (multi-engine : Kokoro, FishAudio, autres, via `tts-api`), Demucs.

La pile s'orchestre via le CLI `genai.py` plutôt que des commandes `docker` lancées à la main :

```bash
cp docker-configurations/services/comfyui-qwen/.env.example docker-configurations/services/comfyui-qwen/.env
python scripts/genai-stack/genai.py docker status [--remote]  # état des services
python scripts/genai-stack/genai.py docker start all [--build] # démarrer (+rebuild images si demandé)
python scripts/genai-stack/genai.py docker stop all           # arrêter
python scripts/genai-stack/genai.py docker restart <service>  # redémarrer un service
python scripts/genai-stack/genai.py gpu [--detailed]          # vérifier la VRAM disponible
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

Le dépôt embarque une configuration Claude Code complète pour la maintenance et l'enrichissement des notebooks : sous-agents spécialisés (notebooks, QuantConnect, Lean/preuves, GenAI, README/slides, training ML, coordination multi-machines) et commandes slash dédiées (`/verify-notebooks`, `/enrich-notebooks`, `/build-notebook`, `/coordinate`, `/review-student-prs`…).

L'inventaire des agents, compétences et scripts dédiés, ainsi que leurs usages recommandés, est tenu à jour dans [`docs/reference/subagents-reference.md`](docs/reference/subagents-reference.md). Cette référence prime sur une liste figée qui se périmerait à chaque ajout ; les définitions se trouvent dans `.claude/agents/` et `.claude/skills/`.

---

## Outils et dépendances externes

Les dépendances principales par série (vérifiées contre les `requirements.txt` par série — voir `MyIA.AI.Notebooks/<famille>/requirements.txt`) :

| Outil | Séries | Provenance |
|-------|--------|-----------|
| Z3 SMT Solver | Sudoku, Search, SymbolicAI (Tweety, Z3-API, SMT), GameTheory | `z3-solver>=4.13` dans `requirements.txt` |
| OR-Tools (CP-SAT) | Sudoku, Search, Planners | `ortools>=9.8` dans `requirements.txt` |
| Unified Planning | Planners | `unified-planning>=1.1` ; Fast-Downward via WSL/Docker |
| Tweety + JDK | Tweety, Argument_Analysis | `jpype1>=1.4` ; JARs auto-téléchargés via `download_tweety_tools.py` |
| Lean 4 + Mathlib | Lean, GameTheory (`game_theory_lean/`) | `elan` (WSL) ; diagnostic via `validate_lean_setup.py` |
| Lean 7-9 multi-agent (Semantic Kernel + LLM) | Lean | `semantic-kernel>=1.39.0`, `openai>=1.0.0`, `anthropic>=0.20.0` |
| OpenSpiel | GameTheory | `open_spiel>=1.4` dans `requirements.txt` GameTheory |
| Nash equilibrium (nashpy) | GameTheory | `nashpy>=0.0.40` |
| Axelrod (IPD tournaments + Moran) | GameTheory | `axelrod>=4.0.0` (GameTheory-6) |
| PySAT | GameTheory, Tweety | `python-sat>=0.1.8` (Glucose3, Minisat22, Cadical103) |
| Metaheuristics (DEAP, PyGAD, Mealpy) | Search, Sudoku | `deap>=1.4`, `pygad>=3.3`, `mealpy>=3.0` ; `simanneal>=0.5` (Sudoku) |
| Infer.NET | Probas | NuGet via le kernel .NET Interactive ; parcours détaillé dans `Probas/Infer/README.md` |
| Pyro-PPL + PyTorch | Probas | `pyro-ppl>=1.8`, `torch>=2.0` (Pyro_RSA_Hyperbole + backends Pyro) |
| PyMC + ArviZ | Probas | `pymc>=5.0`, `arviz>=0.14` (PyMC/ series + HMM Trading Alpha) |
| scikit-learn, hmmlearn, yfinance | Probas (PyMC-HMM-Trading-Alpha), QuantConnect | `scikit-learn>=1.2`, `hmmlearn>=0.3`, `yfinance>=0.2` |
| Probabilistic programming (JAX, NumPyro) | Sudoku (Sudoku-15) | `jax>=0.4`, `numpyro>=0.12` |
| RL (Stable-Baselines3, Gymnasium, PettingZoo) | RL | `stable-baselines3[extra]>=2.0`, `gymnasium>=0.29`, `pettingzoo[classic]>=1.24`, `highway-env>=1.8` |
| QuantConnect LEAN | QuantConnect | `quantconnect-lean>=2.5.14000` + MCP `qc-mcp` |
| ComfyUI + Stack GenAI (Qwen Image Edit, SD Forge, Video) | GenAI/Image, GenAI/Video | Stack Docker dans `docker-configurations/services/` (Qwen ~29 Go VRAM, ComfyUI Video ~12 Go, SD Forge ~10 Go) |
| Audio GenAI (Whisper, TTS multi-engine, MusicGen, Demucs) | GenAI/Audio | `TTS>=0.22`, `faster-whisper>=0.10`, `librosa>=0.10`, `transformers>=4.35`, `diffusers>=0.24` ; services `whisper-api` + `tts-api` (Kokoro, FishAudio, autres) |
| PyPhi | IIT | `pyphi==1.2.0` (épinglé Python ≤3.9 + NumPy<2) dans `requirements.txt` IIT |

---

## Contribution

1. Fork le dépôt
2. Créer une branche (`git checkout -b feature/nouveau-notebook`)
3. Commit (`git commit -m 'Add: notebook sur les Transformers'`)
4. Push et ouvrir une Pull Request

Conventions : PEP 8 pour Python, conventions standard pour C#, pas d'emojis dans le code, documentation en français. Chaque famille de notebooks doit inclure un `.env.example` documentant les variables requises.

## Licence

Ce projet est sous licence MIT - voir [LICENSE](LICENSE).

## Confidentialité

Le dépôt public ne contient **ni copies ou rendus privés, ni notes ou appréciations,
ni données personnelles issues des processus privés d'enseignement ou de notation**
(listes de classe, adresses e-mail, identifiants scolaires).

Les pipelines et données de notation vivent sur un stockage privé hors dépôt ; seul le
[moteur de notation générique](GradeBookApp/) est public, vide de données. Détails et
posture PII : [PRIVACY.md](PRIVACY.md).

---

Repository : [github.com/jsboige/CoursIA](https://github.com/jsboige/CoursIA)

<!-- README-DATE: 2026-08-31 -->
