# CoursIA

**Apprendre l'intelligence artificielle par la pratique, des fondements theoriques aux applications avancees.**

CoursIA est une collection de notebooks Jupyter interactifs couvrant l'ensemble du spectre de l'IA : algorithmes de recherche, resolution par contraintes, raisonnement formel, theorie des jeux, programmation probabiliste, machine learning, IA generative multimodale et trading algorithmique.

Les notebooks sont disponibles en Python, C# (.NET Interactive) et Lean 4. Chaque serie suit une progression pedagogique, des concepts fondamentaux vers les applications avancees. La plupart fonctionnent en local sans configuration ; seules les series GenAI et QuantConnect necessitent des cles API.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

---

> **Catalogue vivant** -- Pour l'inventaire exhaustif et a jour (comptes exacts par serie, statut READY/DEMO, maturite PRODUCTION/BETA), consultez **[`COURSE_CATALOG.generated.md`](COURSE_CATALOG.generated.md)**. Ce catalogue est regenere automatiquement chaque jour : il fait foi sur les chiffres et les statuts, ce README en donne la vue d'ensemble pedagogique. Le depot couvre une douzaine de grandes series, de l'IA symbolique au trading algorithmique en passant par l'IA generative et l'apprentissage automatique.

## Commencer ici

Vous avez clone le depot et vous ne savez pas par ou commencer ?

1. **Choisissez votre niveau** : voyez les parcours recommandes plus bas pour un plan d'apprentissage guide
2. **Explorez par serie** : chaque serie a son propre README detaille avec une vue d'ensemble, la liste des notebooks, les prerequis et la duree estimee
3. **Documentation projet** : le repertoire [docs/](docs/README.md) centralise les regles de travail, l'infrastructure, les procedes recurrents et les guides d'apprentissage

## Cartographie rapide du depot

```
MyIA.AI.Notebooks/
  Search/          -> Algorithmes de recherche (BFS, A*, CSP) -- point d'entree ideal pour debutants
  Sudoku/          -> Resolution multi-paradigme -- 10 approches pour 1 probleme
  ML/              -> Machine Learning (ML.NET, agents ADK)
  RL/              -> Reinforcement Learning (PPO, DQN, Stable Baselines3)
  Probas/          -> Programmation probabiliste (Infer.NET, Pyro)
  GameTheory/      -> Theorie des jeux, equilibres de Nash, mechanism design
  IIT/             -> Theorie de l'information integree (Tononi, PyPhi)
  CaseStudies/     -> Etudes de cas interdisciplinaires
  SymbolicAI/      -> Raisonnement formel (Lean 4, Tweety, Semantic Web, Smart Contracts, Planners, Symbolic Learning)
  GenAI/           -> IA generative (Image, Audio, Video, Texte, Semantic Kernel) -- la plus grande serie
  QuantConnect/    -> Trading algorithmique (notebooks pedagogiques + strategies backtestees + pipeline ML)
  cross-series/    -> Applications transverses (matching-cv : data science multi-domaines)
```

Pour un guide complet des parcours d'apprentissage, voir [docs/parcours/](docs/parcours/).

---

## Parcours recommandes

**Debutant** -- Commencer par Search (Part 1), Sudoku, puis ML.Net. Ces series ne necessitent aucune cle API et introduisent les concepts fondamentaux.

**Intermediaire** -- Explorer GameTheory, Probas, puis la partie Foundations de GenAI (Image, Texte). Ajoutez les techniques probabilistes et generatives a votre boite a outils.

**Avance** -- SymbolicAI (Lean, SmartContracts), QuantConnect (strategies ML/DL), GenAI Video/Audio. Pour les etudiants a l'aise avec les fondamentaux qui veulent aller plus loin.

**Recherche** -- ML Training Pipeline (forecasting, GNN), SymbolicAI (preuves formelles Lean 4), Infer.NET (programmation probabiliste avancee).

---

## Ce qu'on y trouve

Le depot couvre un spectre large de l'IA, des algorithmes classiques aux modeles generatifs les plus recents, avec un parti pris constant : confronter plusieurs paradigmes sur les memes problemes plutot que d'en privilegier un seul. Quelques points notables :

- **Multi-langages, multi-ecosystemes** : Python pour le machine learning et l'IA generative, C# pour l'ecosysteme Microsoft (ML.NET, Infer.NET, Semantic Kernel), Lean 4 pour la verification formelle. Chaque langage est employe la ou il excelle, pas par defaut.
- **Du fondamental a la recherche** : les series partent des algorithmes de base (BFS, A*, backtracking) et vont jusqu'a des sujets de pointe -- transformers pour le forecasting financier, agents de preuve autonomes, integration neuro-symbolique, deep learning multimodal.
- **Preuves formelles ambitieuses** : au-dela des exercices, les series Lean et GameTheory mecanisent des theoremes phares en Lean 4 -- theoreme de sensibilite, theoreme de Kochen-Specker, theoreme du libre arbitre de Conway-Kochen, formalisations des theoremes d'Arrow et de Sen -- avec des hommages aux mathematiques de Grothendieck et de Conway.
- **Donnees et marches reels** : les notebooks QuantConnect s'appuient sur des donnees de marche reelles (yfinance, framework LEAN) ; le pipeline d'entrainement ML valide ses modeles par walk-forward strict et multi-seed sur un panier de cryptomonnaies.
- **IA generative deployable** : les notebooks GenAI fonctionnent au choix sur des APIs cloud (OpenAI, Anthropic) ou sur des modeles locaux servis par une infrastructure Docker GPU (Qwen, FLUX, ComfyUI, Whisper, MusicGen).
- **Agents et LLMs transverses** : assistants de preuve, agents de data science autonomes, planification pilotee par LLM, GraphRAG et boucles LLM-verification symbolique tissent un fil rouge entre les series.
- **Etudes de cas integratrices** : des projets interdisciplinaires (diagnostic medical, planification oncologique) et des applications transverses combinent les techniques apprises en silos en livrables complets.

---

## Philosophie pedagogique

Chaque serie est concue pour etre **self-contained** : un etudiant peut ouvrir n'importe quel notebook et suivre la progression sans prerequis externes, les explications etant integrees au fil des cellules.

Les approches **multi-paradigmes** sont privilegiees : le Sudoku est resolu par backtracking, CSP, metaheuristiques et reseaux de neurones pour comparer les compromis. Les jeux sont formalises en Python et en Lean 4. Cette diversite d'approches sur un meme probleme est au coeur de la demarche.

Les notebooks combinent **theorie et implementation** : les concepts sont introduits progressivement, puis mis en pratique dans des cellules executables. La structure **exemple puis exercice** est systematique -- chaque notion est d'abord demontree par un exemple resolu, puis reprise dans un exercice a completer ; corriges et squelettes cohabitent, et le notebook s'execute de bout en bout meme lorsque les exercices ne sont pas faits.

Enfin, **la priorite au local** : la majorite des series tournent apres un simple clone, sans cle API ni GPU. Seules GenAI (modeles generatifs) et QuantConnect (donnees de marche) demandent une configuration -- de sorte que rien ne fasse barrage a la prise en main.

---

## Series de notebooks

### Search -- Algorithmes de recherche et optimisation

Comment un ordinateur trouve-t-il son chemin dans un labyrinthe, ordonne-t-il un atelier, ou bat-il un humain au Puissance 4 ? Tout probleme d'IA, du jeu de plateau a la planification logistique, se ramene a un meme defi : explorer un espace de solutions possibles pour trouver la meilleure. Le fil conducteur de la serie n'est pas l'accumulation d'algorithmes mais une seule competence -- savoir **quand explorer, quand contraindre, et quand combiner les deux** -- construite autour de l'idee de **reduction de l'espace de recherche** : comment passer d'une enumeration aveugle exponentielle a une resolution intelligemment guidee.

**Fondements** -- La progression part de la formalisation d'un probleme en espace d'etats (S, A, T, G), puis deroule les grands paradigmes : recherche non informee (BFS, DFS), recherche guidee par heuristique (A*, avec la garantie d'optimalite lorsque l'heuristique est admissible), optimisation locale (Hill Climbing, recuit simule, Tabu), evolution (algorithmes genetiques), recherche adversariale dans les jeux (Minimax, Alpha-Beta) et enfin Monte Carlo Tree Search jusqu'a l'architecture AlphaGo (MCTS couple a un DQN). S'y greffent des extensions de pointe : Dancing Links de Knuth pour la couverture exacte, programmation lineaire, automates symboliques a predicats Z3, et un banc d'essai de metaheuristiques (essaim particulaire, colonies, recuit).

**Programmation par contraintes** -- Un changement de paradigme : au lieu de concevoir un algorithme d'exploration, on declare les contraintes du probleme et le solveur trouve les solutions. On y apprend la propagation (AC-3, Forward Checking, MAC) qui elague l'espace avant meme de chercher, les contraintes globales d'OR-Tools CP-SAT (AllDifferent, Cumulative), puis les usages industriels -- ordonnancement d'atelier, planification de projet, optimisation combinatoire (sac a dos, bin packing) -- et les frontieres du domaine : contraintes souples, raisonnement temporel par algebre d'Allen, CSP distribues entre agents, et surtout l'hybridation (CP+SAT, CP+ML, et generation de contraintes par LLM). C'est le pont vers SymbolicAI.

**Applications** -- Chaque concept se mesure sur un probleme reel, la plupart adaptes de projets etudiants : N-Queens, coloration de cartes, planning d'infirmiers, emploi du temps, demineur (CSP, probabilites et LLM combines), solveur Wordle par theorie de l'information, nonogrammes, generation procedurale par Wave Function Collapse, Puissance 4 oppose a une batterie d'IA, voyageur de commerce et tournees de vehicules, optimisation de portefeuille et detection de bords par algorithmes genetiques (avec leurs pendants C# sur GeneticSharp), reglage d'hyperparametres pour le Machine Learning. C'est le terrain ou l'on compare, sur une meme instance, methode exacte et methode approchee.

Cette serie est aussi un carrefour : ses algorithmes irriguent Sudoku (DLX, automates), SymbolicAI (Z3, planification PDDL), GameTheory (Minimax, MCTS) et RL (MCTS et DQN), et ses metaheuristiques reviennent regler les hyperparametres du Machine Learning.

Python et C# | [README detaille](MyIA.AI.Notebooks/Search/README.md)

### Sudoku -- Resolution multi-paradigme

Et si l'on prenait un seul probleme -- une grille de Sudoku -- pour le resoudre d'une dizaine de manieres radicalement differentes ? L'objectif n'est pas de remplir des grilles (un solveur industriel le fait en quelques millisecondes) mais de transformer ce casse-tete en **banc d'essai controle** : parce que le probleme reste constant, on isole la seule variable qui change d'un notebook a l'autre -- le paradigme algorithmique -- et l'on rend visible l'arbitrage qui traverse toute l'IA, **garantie de solution contre performance contre generalisation**. Le Sudoku generalise est NP-complet, de la meme famille que SAT ou le voyageur de commerce : c'est un terrain legitime, pas un jouet. Et chaque technique existe en miroir C# et Python, pour comparer un paradigme sans changer de langage.

**Les methodes exactes -- la garantie pour boussole** -- La premiere moitie de la serie reunit les approches qui trouvent toujours la solution si elle existe. On part du backtracking, l'exploration recursive fondamentale, accelere par l'heuristique MRV (choisir d'abord la case la plus contrainte) ; puis la couverture exacte de Knuth (Dancing Links), ou une representation de donnees astucieuse -- des listes doublement chainees -- transforme les performances sans changer l'algorithme. Vient ensuite le grand basculement vers le declaratif : au lieu de programmer l'exploration, on declare les contraintes et le solveur cherche. C'est la programmation par contraintes -- propagation de Norvig (qui elague l'espace avant meme de chercher et offre des gains spectaculaires), CSP academique a la AIMA, coloration de graphe, et les solveurs industriels OR-Tools CP-SAT et Choco -- prolongee par l'IA symbolique : le solveur SMT Z3, les automates symboliques a predicats, les diagrammes de decision binaires. Une etape singuliere code treize techniques de deduction humaine (paires nues, candidats caches, pointing) : le pont entre le raisonnement de la machine et celui du joueur.

**Les methodes approchees -- echanger la garantie contre autre chose** -- L'autre moitie renonce deliberement a la garantie. Les metaheuristiques inspirees de la nature -- algorithme genetique, recuit simule, essaim particulaire -- explorent l'espace intelligemment sans jamais promettre d'aboutir, mais souvent tres vite. Puis le data-driven inverse la logique : au lieu de programmer la resolution, on l'apprend. Un modele probabiliste (Infer.NET, NumPyro) place une distribution a posteriori sur les cases ; un reseau de neurones apprend, sur un tres grand nombre de grilles resolues, les regularites qui menent a une solution ; un LLM tente de raisonner sans algorithme explicite. Chacun illustre une limite autant qu'une force : le reseau a besoin d'enormement de donnees, le LLM trebuche sur le raisonnement logique pur.

**Le banc d'essai comparatif -- la lecon honnete** -- Le notebook de synthese confronte toutes les approches sur une echelle de difficulte croissante, du facile a l'expert, et c'est la que l'arbitrage paie. Deux enseignements ressortent, contre-intuitifs et assumes. D'abord, sur les modeles appris, le volume de donnees pese plus lourd que la taille du modele : un petit reseau bien nourri devance un gros reseau affame. Ensuite -- et c'est le coeur de la serie -- meme entraine jusqu'a une precision quasi parfaite, le reseau de neurones reste un **approximateur** : il peut se tromper, la ou les solveurs exacts (Norvig, OR-Tools, Z3) garantissent la solution et sont souvent plus rapides en inference. La lecon n'est pas qu'une approche l'emporte, mais que le bon choix depend du contexte -- garantie, vitesse, ou capacite a generaliser.

Sudoku est ainsi une coupe verticale du depot : un seul probleme qui traverse **Search** (dont il instancie le backtracking, les metaheuristiques, DLX et le CSP), **SymbolicAI** (par le solveur SMT Z3), **Probas** (par l'inference bayesienne) et **ML** (par le solveur neuronal et l'evaluation des LLM) -- et qui permet, fait rare, de comparer toutes ces familles sur un pied d'egalite.

C# et Python (OR-Tools, Z3, PyTorch) | [README detaille](MyIA.AI.Notebooks/Sudoku/README.md)

### SymbolicAI -- Raisonnement formel

Une machine peut-elle raisonner -- non pas approximer une reponse plausible, mais deduire, prouver, justifier ? C'est le pari de l'IA symbolique, l'autre grande tradition de l'intelligence artificielle : representer la connaissance sous forme de propositions, de regles et de structures logiques, puis en deriver mecaniquement de nouvelles conclusions. La plus vaste serie du depot l'explore des systemes experts des annees 80 jusqu'aux assistants de preuve et aux agents LLM d'aujourd'hui. Le fil conducteur n'est pas une technologie mais une promesse : ce raisonnement est **explicite, verifiable et explicable** -- exactement ce que l'apprentissage statistique seul ne garantit pas. Et la ou les deux paradigmes se rencontrent se trouve le front actif de la recherche : le symbolique devient la couche de controle du neuronal -- detecter les incoherences d'un LLM, l'ancrer sur des faits, certifier la robustesse d'un reseau.

La progression suit cette logique : formaliser le raisonnement (Tweety), representer la connaissance (Semantic Web), la prouver mecaniquement (Lean), l'appliquer a des problemes concrets (Planners, Smart Contracts), puis la ponter vers le neuronal (Argument Analysis, Symbolic Learning). Chaque sous-serie est autonome, mais ensemble elles dessinent une vision coherente de l'IA symbolique moderne.

**Tweety -- logiques formelles et argumentation computationnelle** -- Construite sur TweetyProject (une collection de bibliotheques Java pilotees depuis Python via JPype), cette sous-serie reunit une dizaine de formalismes sous un meme toit : logiques propositionnelle, du premier ordre, modale, de description et conditionnelle ; revision de croyances AGM -- comment un agent rationnel met a jour ses connaissances face a une information contradictoire ; et surtout l'argumentation computationnelle, son coeur. On y passe des cadres abstraits de Dung -- des arguments qui s'attaquent sans qu'on regarde leur contenu, et des semantiques qui decident lesquels sont acceptables -- a l'argumentation structuree (ASPIC+, DeLP, ABA, ASP via Clingo), ou les arguments ont une structure interne de premisses et de regles defeasibles, jusqu'aux frameworks etendus, ponderes et probabilistes. La serie se conclut sur les dialogues entre agents et la theorie du vote, passerelle directe vers la theorie des jeux. Tout reunir sous un meme toit a un interet pedagogique precis : on experimente d'une logique a l'autre sans reimplementer chaque solveur. Les applications sont concretes -- raisonnement juridique, aide a la decision medicale, negociation multi-agents -- et de plus en plus, controle des LLMs (detecter une incoherence, structurer un debat).

**Semantic Web -- de RDF aux graphes de connaissances qui ancrent les LLMs** -- Le Web Semantique est la promesse d'un Web ou les machines comprennent le sens des donnees, pas seulement leur syntaxe. La sous-serie en couvre le spectre complet, et la raison de cette completude est que les briques s'articulent en couches : RDF definit les donnees (le triplet sujet-predicat-objet, un fait elementaire), SPARQL les interroge, RDFS et OWL ajoutent le raisonnement (hierarchies de classes, restrictions, inference automatique), SHACL valide leur qualite, JSON-LD ponte vers le Web des developpeurs, RDF-Star ajoute la provenance, et les graphes de connaissances couples aux LLMs ferment la boucle. C'est ce dernier maillon qui a relance le domaine apres des annees de desillusion : GraphRAG a montre qu'un graphe RDF pouvait ancrer un LLM sur des faits verifiables -- le Web Semantique comme garde-fou de l'IA generative. Le parcours est deliberement bilingue : fondations en .NET avec dotNetRDF, standards modernes et IA en Python (rdflib, pySHACL, GraphRAG), chaque notebook C# disposant d'un miroir Python pour qui prefere un seul ecosysteme.

**Lean -- la preuve mecanique, ou le noyau a toujours le dernier mot** -- Lean 4 est a la fois un langage de programmation fonctionnel et un assistant de preuve fonde sur la theorie des types dependants. Son principe est radical : une preuve n'est acceptee que si le noyau du systeme la verifie pas a pas -- pas de "ca semble correct", pas d'argument d'autorite. C'est exactement la garantie que cherche l'IA symbolique, poussee a son extreme. La progression part des fondations -- types dependants, isomorphisme de Curry-Howard ou une proposition EST un type et sa preuve un terme, mode tactique avec les briques de Mathlib -- puis bascule vers le front actif : l'assistance par LLM. LeanCopilot et AlphaProof suggerent des tactiques, des agents autonomes explorent l'espace des preuves (APOLLO, attaques de problemes d'Erdos), LeanDojo trace des bibliotheques entieres pour entrainer ces modeles ; mais le partage des roles ne change jamais -- le LLM propose, le noyau dispose. C'est l'illustration la plus pure du symbolique comme garde-fou du neuronal. La serie applique enfin Lean a des cibles ambitieuses : verifier formellement la robustesse d'un reseau de neurones (IBP, CROWN), porter des theoremes de recherche recents (theoreme de sensibilite de Huang, theoreme de Kochen-Specker sur la contextualite quantique), et rendre hommage aux mathematiciens en formalisant leur oeuvre -- le langage grothendieckien dans Mathlib, le jeu de la vie et le theoreme du libre arbitre de Conway-Kochen. Necessite WSL sous Windows.

**Planners -- non pas "que predire ?" mais "que faire ?"** -- La planification automatique repond a une question que l'apprentissage ne pose pas : etant donne un etat initial, un ensemble d'actions decrites par leurs preconditions et leurs effets, et un but, quelle sequence d'actions y mene ? C'est une technologie eprouvee -- elle pilote des robots, optimise la logistique, et a dirige des engins spatiaux autonomes (le Remote Agent de Deep Space, les rovers martiens) -- standardisee par le langage PDDL, qui a fait naitre tout un ecosysteme de solveurs comparables. La sous-serie suit la montee en puissance habituelle : des fondations STRIPS et de l'explosion combinatoire de l'espace d'etats -- celle qui rend les heuristiques indispensables -- on passe a la planification classique avec Fast-Downward, vainqueur des competitions IPC, et ses heuristiques admissibles ; puis aux approches avancees -- programmation par contraintes avec OR-Tools, planification temporelle, reseaux de taches hierarchiques (HTN). La derniere etape ponte vers le neuro-symbolique : faire generer des plans par un LLM, comparer les solveurs derriere une interface unifiee, apprendre les heuristiques par reseaux de neurones. Le fil rouge rejoint celui de la serie -- donner a un modele de langage une capacite d'action verifiable et orientee vers un but, plutot qu'une suite d'actions plausible mais non garantie.

**Smart Contracts -- quand le code fait foi, le rendre digne de confiance** -- Un smart contract est un programme qui s'execute tout seul sur une blockchain : une fois deploye, son code fait loi, transfere de la valeur et applique ses regles sans intermediaire ni retour en arriere. C'est sa force -- des ecosystemes entiers (DeFi, NFT, DAO) reposent dessus -- et son danger : un bug n'est pas un correctif a pousser le lendemain, c'est une faille immuable qui peut couter des millions, comme l'a montre le hack de The DAO ou les exploits de ponts cross-chain. D'ou le poids egal accorde ici au developpement ET a la preuve qu'on peut s'y fier : tests, fuzzing, invariants, verification formelle. Le parcours suit le fil de son titre -- on remonte aux primitives cryptographiques des cypherpunks (hachage, arbres de Merkle, preuve de travail, signatures) pour comprendre pourquoi une blockchain tient, on construit en Solidity (types, heritage, standards ERC, DeFi, gouvernance), on securise avec Foundry jusqu'a la verification formelle, on apprend a proteger la vie privee sur une chaine pourtant transparente (preuves a connaissance nulle, chiffrement homomorphe, vote verifiable de bout en bout), avant d'elargir aux chaines non-EVM (Vyper, XRP, Bitcoin Script, Move/Sui, Solana) et au deploiement reel sur testnet puis mainnet. Le point de contact avec le reste de la serie est direct : la verification formelle d'un contrat par solveur SMT et la preuve d'un theoreme en Lean sont deux facettes de la meme verite -- la correction mathematique d'un programme.

**Argument Analysis -- ou s'arrete le LLM, ou commence le verificateur** -- Distinguer un argument valide d'un sophisme devient un acte critique dans une societe saturee de discours generes a la chaine : quand un LLM produit a la demande un texte plausible, la frontiere entre persuasion legitime et manipulation rhetorique se brouille. Cette sous-serie pose une question concrete -- peut-on prendre un texte argumentatif en entree et en restituer une carte logique formelle, validee par un solveur SAT, avec detection systematique des sophismes connus ? La reponse assemble trois competences : un agent LLM (orchestre par Semantic Kernel) extrait le tissu informel -- premisses, conclusions, transitions ; un solveur logique (TweetyProject, via le meme pont JPype que la sous-serie Tweety) verifie la coherence des formalisations propositionnelles ; une couche agentique transforme la chaine en pipeline reproductible. Tout l'enjeu pedagogique tient dans la jointure -- ou le LLM, fiable pour extraire mais faible pour prouver, passe la main au verificateur formel, et comment une boucle informel/formel converge vers un verdict. C'est l'incarnation appliquee du fil de la serie : le symbolique comme garde-fou du neuronal, mis au service de la pensee critique, du fact-checking et de l'audit de contenus generes par IA.

**Symbolic Learning -- apprendre de la connaissance, pas seulement des donnees** -- Comment un agent apprend-il a partir de ce qu'il sait deja, et non d'un deluge d'exemples ? Cette sous-serie, dans la lignee du chapitre 19 d'AIMA, est la contrepartie symbolique du machine learning statistique -- et elle adresse trois limites que ce dernier ne sait pas traiter : apprendre quand les donnees sont rares (l'apprentissage base sur les explications, EBL, generalise depuis un seul exemple prouve), produire des regles interpretables par un humain (une clause "SI fievre ET toux ALORS infection" se lit, un reseau de cent millions de parametres non), et exploiter une theorie du domaine deja connue. Le parcours part de l'induction pure -- espaces de versions, elimination de candidats -- vers l'apprentissage guide par la connaissance (EBL, apprentissage par la pertinence et treillis des determinations) puis la programmation logique inductive (FOIL, resolution inverse, regles apprises sur des graphes de connaissances). Sa phase finale est le point de jonction de toute la serie SymbolicAI : T-norms differentiables et Logic Tensor Networks qui rendent la logique compatible avec la descente de gradient, fouille de regles sur graphes reels, boucles ou un LLM extrait des regles que la verification symbolique valide. Apprentissage symbolique et apprentissage statistique n'y sont pas rivaux mais complementaires.

Vue d'ensemble, la serie raconte une seule idee declinee d'une sous-serie a l'autre : reformuler une affirmation dans un cadre ou elle devient verifiable. Tweety formalise un debat en semantiques d'acceptabilite, le Web Semantique ancre des faits dans un graphe interrogeable, Lean reduit une preuve a ce que son noyau accepte ligne a ligne, les contrats se relisent a l'aune de leur verification formelle, le planificateur confronte une intention dite en mots a un solveur qui tranche, l'argumentation et l'apprentissage symbolique rebouclent un LLM sur un verificateur. Ce geste -- changer de representation jusqu'a ce que la garantie devienne possible -- deborde SymbolicAI : on le retrouve dans les portages Lean de la theorie des jeux (existence de Nash, impossibilite d'Arrow, valeur de Shapley) et dans la theorie de la decision de Probas, partout ou le depot fait passer un resultat du plausible au controlable. C'est la grille que propose [La mer qui monte](docs/grothendieckian-lens.md) : a mesure que l'IA bascule vers les grands modeles, la rendre digne de confiance, ce sera trouver le cadre ou son affirmation se verifie.

Python, Lean 4 et C# | [README detaille](MyIA.AI.Notebooks/SymbolicAI/README.md)

### Probas -- Programmation probabiliste

Comment raisonner -- et surtout decider -- quand rien n'est certain ? Un diagnostic medical n'est jamais sur a cent pour cent, un classement de joueurs depend de performances variables, et les donnees arrivent toujours bruitees ou incompletes. La programmation probabiliste refuse de repondre par un seul chiffre : elle calcule une *distribution* qui dit a quel point on croit a chaque issue possible. Mais une croyance ne sert a rien tant qu'on n'agit pas dessus -- et c'est la le fil conducteur de la serie : passer d'une reponse unique a une distribution, puis d'une distribution a une decision. La theorie de la decision bayesienne, qui occupe toute la seconde moitie du parcours, est la charniere de ce mouvement, et le socle dont la theorie des jeux a besoin pour modeliser des agents rationnels.

**Deux ecosystemes, les memes modeles** -- La serie repose sur une juxtaposition deliberee : chaque modele est traite dans deux ecosystemes complementaires qui couvrent, a eux deux, plusieurs familles d'algorithmes d'inference. Infer.NET (Microsoft, C#) compile le modele en graphe de facteurs et laisse choisir son moteur -- passage de messages (Expectation Propagation, Variational Message Passing) ou echantillonnage de Gibbs -- avec des resultats exacts sur les modeles conjugues et approches ailleurs, le tout rapide et dont la structure se visualise. PyMC (Python) reprend l'integralite de ces modeles avec le MCMC moderne a base de gradient (le sampler NUTS), qui s'applique a presque tout modele au prix d'un diagnostic de convergence outille par ArviZ (R-hat, taille d'echantillon effective, divergences, trace plots). L'enjeu n'est donc pas de trancher entre exact et approche, ni meme entre deterministe et aleatoire -- chaque famille a sa place -- mais d'apprendre, en voyant un meme modele resolu de plusieurs facons, quel moteur convient a quelle structure. Et les modeles ne sont pas des jouets : reseaux bayesiens pour le diagnostic medical et l'explaining away, Item Response Theory (le moteur des tests adaptatifs comme le GMAT), TrueSkill (le classement bayesien des joueurs sur Xbox Live), LDA pour la decouverte de themes, modeles de Markov caches pour les regimes, agregation de foules d'annotateurs bruites, recommandation assortie d'une barre d'incertitude.

**De l'inference a la decision -- la theorie de l'utilite** -- A quoi bon une distribution si elle ne dicte aucune action ? La seconde moitie de la serie franchit ce pas, et c'est son coeur. On part des axiomes de Von Neumann-Morgenstern qui fondent l'utilite esperee comme critere rationnel, on modelise l'aversion au risque (utilites CARA et CRRA, paradoxe de Saint-Petersbourg), on decide sur plusieurs criteres a la fois (utilite multi-attributs, MAUT), on branche la decision sur l'inference par les diagrammes d'influence, on chiffre la valeur d'une information avant de payer pour l'acquerir (EVPI, EVSI -- quand un test complementaire est-il rentable ?), on se protege contre l'incertitude radicale (Minimax Regret), et l'on debouche sur la decision *sequentielle* : processus de decision markoviens, bandits, POMDP. Ce dernier maillon est une double passerelle -- vers le reinforcement learning d'un cote, et de l'autre vers la theorie des jeux, qui suppose precisement des agents maximisant leur utilite esperee. C'est pourquoi cette serie precede desormais GameTheory : l'utilite en est le prerequis.

**Jusqu'a la preuve formelle -- l'indice de Gittins en Lean** -- Le probleme du bandit -- explorer pour apprendre, ou exploiter ce qu'on croit savoir ? -- admet une solution remarquable : l'indice de Gittins, qui ramene un probleme sequentiel intimidant a un simple classement de bras. La serie ne se contente pas de l'implementer ; un volet en Lean 4 (avec Mathlib) cherche a le *prouver*. Les identites d'escompte geometrique qui fondent le calcul d'une valeur actualisee -- la somme escomptee d'une recompense constante -- y sont demontrees rigoureusement, verifiees ligne a ligne par le noyau. Le theoreme d'optimalite de Gittins lui-meme, en revanche, est *enonce* mais laisse a la frontiere : sa preuve complete exigerait une formalisation des MDP et de l'equation de Bellman qui manque encore a Mathlib, et le notebook le documente honnetement comme tel. Cette lucidite sur ce qui est prouve et ce qui ne l'est pas encore est l'enseignement -- elle relie Probas a la serie Lean de SymbolicAI, ou le noyau a toujours le dernier mot.

Probas est un carrefour discret du depot. Sa theorie de la decision est le socle de **GameTheory** (jeux bayesiens, agents a utilite esperee) et la passerelle vers **RL** (ses MDP et ses bandits y deviennent apprentissage par renforcement) ; son inference bayesienne nourrit le TP de regression de **ML** et la gestion du risque de **QuantConnect** (ou un modele de Markov cache genere des signaux de trading) ; ses fondements probabilistes sous-tendent le phi de l'**IIT** et le raisonnement incertain des ontologies de **SemanticWeb** ; et son pont vers Lean prolonge le fil de verification formelle de **SymbolicAI**. Partout la meme exigence : ne pas confondre une croyance avec une certitude, ni une prediction avec une decision.

C# (Infer.NET), Python (PyMC, Pyro) et Lean 4 | [README detaille](MyIA.AI.Notebooks/Probas/README.md)

### GameTheory -- Theorie des jeux

Comment des agents rationnels interagissent-ils quand le resultat de chacun depend des choix de tous les autres ? Enchere, negociation, election, partie de poker, guerre commerciale : partout des decideurs anticipent les decisions d'autrui avant d'arreter les leurs. La theorie des jeux est le langage mathematique de cette interdependance, et elle suppose d'emblee des agents qui maximisent une utilite esperee -- c'est pourquoi elle vient ici juste apres Probas, dont la theorie de la decision lui sert de socle. Le fil conducteur de la serie n'est pas un theme mais une *methode* : tout resultat y est aborde deux fois, simule en Python pour le *voir* a l'oeuvre, puis prouve en Lean 4 pour le *certifier*. Le notebook Python montre qu'un equilibre est plausible ; le notebook Lean montre qu'il est inevitable.

**Des jeux statiques aux frontieres -- une montee en strategie** -- Le fil principal suit la maturation historique de la discipline, en trois phases. On part des jeux statiques : matrices de gains et dominance, classification geometrique des jeux deux-contre-deux (la table periodique de Robinson-Goforth), equilibre de Nash pur et mixte par l'algorithme de Lemke-Howson, theoreme minimax et sa dualite avec la programmation lineaire, et le tournoi d'Axelrod ou la cooperation finit par emerger de l'egoisme repete. La deuxieme phase introduit le temps et l'incertitude : formes extensives et arbres de jeu, jeux combinatoires (Nim, theoreme de Sprague-Grundy), induction arriere et avant, menaces credibles et equilibre parfait en sous-jeux, puis jeux bayesiens et jeux de reputation, ou l'on raisonne sur les croyances et le signaling. La troisieme ouvre les frontieres contemporaines : la Counterfactual Regret Minimization -- le moteur des IA de poker Libratus et Pluribus -- les jeux differentiels a la Stackelberg, la theorie cooperative (valeur de Shapley, Core), le design de mecanismes (principe de revelation, encheres VCG), et enfin l'apprentissage multi-agent (NFSP, PSRO, AlphaZero) qui referme la boucle vers le reinforcement learning.

**Simuler, puis prouver -- la dualite Python/Lean** -- A cote du fil principal court un fil de formalisation : les grands theoremes ne sont pas seulement illustres, ils sont demontres dans l'assistant de preuve Lean 4. L'existence d'un equilibre de Nash y est etablie via les points fixes de Brouwer et Kakutani ; les jeux combinatoires reposent sur la structure PGame de Mathlib ; la valeur de Shapley est reconstruite a partir de ses axiomes. Plusieurs projets Lake independants portent ce travail, et la serie reste honnete sur sa frontiere : la valeur de Shapley comme le theoreme d'Arrow sont prouves sans aucun `sorry`, tandis que des resultats tels que la condition de Bondareva-Shapley ou le treillis de Gale-Shapley sont *enonces* mais laisses ouverts, leur preuve complete excedant ce que Mathlib offre aujourd'hui. Cette lucidite sur ce qui est certifie et ce qui ne l'est pas encore est exactement le fil rouge de verification formelle partage avec la serie Lean de SymbolicAI.

**L'agregation des preferences -- choix social et impossibilites** -- Une sous-serie dediee, SocialChoice, prolonge le bloc sur l'agregation collective et l'eclaire sous trois angles a la fois. Le theoreme d'impossibilite d'Arrow y apparait contre-intuitif quand on le simule, inevitable quand on le prouve en Lean, et franchement insatisfiable quand on l'encode en probleme SAT resolu par Z3 -- trois facons de saisir un meme resultat. S'y ajoutent le paradoxe liberal de Sen, les methodes de vote classiques (Condorcet, Borda, Copeland) et le modele spatial de Downs. C'est le pont le plus direct vers la gouvernance on-chain etudiee dans SmartContracts, ou un vote de DAO n'est qu'une regle d'agregation soumise aux memes impossibilites.

Au-dela du tableau noir, ces resultats structurent l'economie numerique : les encheres VCG fondent la publicite en ligne de Google et Meta a l'echelle de milliards de transactions par jour, l'algorithme de Gale-Shapley affecte etudiants aux ecoles et internes aux hopitaux -- un mecanisme couronne par le prix Nobel d'economie 2012 -- et la Counterfactual Regret Minimization a permis aux machines de battre les meilleurs joueurs de poker. GameTheory est ainsi un carrefour : elle prolonge la theorie de la decision de **Probas** vers l'interaction strategique, alimente le **RL** par son volet multi-agent, irrigue **SmartContracts** par le vote verifiable et la gouvernance, et partage avec **SymbolicAI** l'exigence de la preuve verifiee par la machine.

Python (Nashpy, OpenSpiel, Z3) et Lean 4 | [README detaille](MyIA.AI.Notebooks/GameTheory/README.md)

### ML -- Machine Learning

Comment passe-t-on d'un tableur rempli de donnees a un modele qui predit, recommande ou anticipe ? Et ce savoir-faire change-t-il selon qu'on code en C# ou en Python ? La serie repond par la negative : les concepts du Machine Learning -- features, entrainement, evaluation, generalisation -- sont **invariants**, seuls les outils et le degre d'automatisation different. Le fil conducteur est justement ce deplacement : *qui* tient le pipeline ? Vous a la main, puis l'AutoML, puis un agent LLM autonome -- la constante etant, a chaque etage, une evaluation honnete qui distingue un modele qui marche d'un modele qu'on comprend.

**ML.NET -- le Machine Learning sans quitter l'ecosysteme .NET** -- Le premier volet construit le pipeline complet en C# : point d'entree `MLContext`, structure colonnaire `IDataView`, feature engineering (encodage, normalisation, concatenation), puis l'entrainement (SDCA, LightGBM, et l'AutoML qui cherche seul l'algorithme et ses hyperparametres). Vient ensuite l'etape la plus importante -- l'evaluation rigoureuse par validation croisee et l'explication des predictions (Permutation Feature Importance) -- avant les sujets de production : prevision de series temporelles par analyse spectrale (SSA), interoperabilite ONNX qui sert des modeles entraines ailleurs (scikit-learn, PyTorch, jusqu'a BERT ou Whisper) directement dans une application .NET, et systemes de recommandation par factorisation matricielle. Le TP capstone marie ML.NET et la regression bayesienne d'Infer.NET pour predire non plus seulement une valeur, mais sa plage de confiance -- pont direct vers Probas.

**Data Science avec agents (Python)** -- Le second volet part des fondations (NumPy, Pandas, scikit-learn) puis bascule vers un changement de paradigme : non plus *ecrire* le code d'analyse, mais *orchestrer* des agents LLM qui le produisent et l'executent. Le sous-track LangChain construit l'agent unique outille -- interroger un DataFrame, nettoyer un jeu de donnees, parser des appels d'offres, scorer des candidatures. Le sous-track Google ADK monte en puissance vers les systemes multi-agents : boucles planner-coder, framework DS-STAR pour une data science autonome, MLE-STAR jusqu'a concourir sur Kaggle, et le deploiement cloud (BigQuery, BQML). Tout est multi-provider -- Gemini, OpenAI ou un vLLM local au choix -- pour ne dependre d'aucun fournisseur unique. L'enjeu pedagogique depasse la technique : comprendre *quand* un agent accelere reellement l'analyse, et *comment* l'encadrer.

Cette serie irrigue le reste du depot par sa rigueur d'evaluation : on la retrouve dans QuantConnect (modeles predictifs de trading), RL (memes gradients, memes reseaux, meme mefiance du surapprentissage) et Probas (l'inference bayesienne du TP) ; son reglage d'hyperparametres rejoint les metaheuristiques de Search ; et ses agents LLM reposent sur les modeles couverts par GenAI -- ou les modeles ONNX de ML.NET servent justement a deployer BERT et Whisper.

C# et Python | [README detaille](MyIA.AI.Notebooks/ML/README.md)

### GenAI -- IA Generative

Comment generer une image a partir d'une phrase, faire parler une machine, composer un fond musical, animer une video, ou brancher un LLM sur ses propres outils ? La plus grande serie du depot explore l'IA generative dans toutes ses modalites. Son fil conducteur n'est pas l'accumulation d'APIs : c'est apprendre a **choisir** entre un modele cloud (DALL-E, GPT-5, Whisper) et un modele open-source auto-heberge (FLUX, Stable Diffusion, Qwen, MusicGen) selon le cout, le controle, le debit et la sensibilite des donnees, puis a **combiner** ces briques dans des pipelines qui tiennent en production. Tout commence par `00-GenAI-Environment`, le passage oblige qui configure cles API, services Docker et validation.

Chaque modalite (Image, Audio, Video) suit la meme montee en quatre niveaux -- Foundation (premiers appels d'API), Advanced (modeles locaux sur GPU, edition fine), Orchestration (workflows multi-modeles) et Applications (cas d'usage concrets) -- et chacune se structure autour d'un fil rouge concret a construire de bout en bout.

**Image** -- De DALL-E 3 et GPT-5 en cloud jusqu'aux modeles auto-heberges (FLUX, Stable Diffusion 3.5, Qwen Image Edit, Z-Image/Lumina) orchestres via ComfyUI. On y apprend a editer plutot que regenerer (inpainting, ControlNet), a composer des graphes de noeuds reproductibles, et a gerer la VRAM (quantizations INT4/FP8). Fil rouge : un generateur de visuels pedagogiques.

**Audio** -- La chaine vocale complete : transcription (Whisper), synthese (OpenAI TTS, Kokoro, Chatterbox), clonage de voix (XTTS), generation musicale (MusicGen, YuE, ACE-Step), separation de sources (Demucs) et TTS expressif a tags prosodiques. Fil rouge : un podcast entierement genere, voix clonee et fond musical compris.

**Video** -- La modalite la plus exigeante : comprehension de sequences (GPT-5, Qwen-VL), generation de mouvement (HunyuanVideo, LTX-Video, Wan, Stable Video Diffusion), super-resolution et interpolation (Real-ESRGAN, RIFE). Fil rouge : transformer un script texte en video pedagogique animee.

**Texte** -- Le socle de tout le reste : prompt engineering, structured outputs (JSON Schema, Pydantic), function calling, RAG moderne, code interpreter, modeles de raisonnement (o-series, GPT-5 thinking), patterns de production, et deploiement de LLMs locaux (vLLM, quantization AWQ/GPTQ).

**Semantic Kernel** -- Le SDK d'orchestration agentique de Microsoft, en Python et en C#/.NET Interactive : plugins, agents, filtres, vector stores, Process Framework, multimodalite et MCP. Demonstrateur phare : un NotebookMaker a trois agents (Admin, Coder, Reviewer) qui genere lui-meme des notebooks pedagogiques.

**Specialisation des modeles** -- Au-dela de l'usage, on entraine : FineTuning (LoRA, QLoRA, SFT, DPO) pour adapter un modele sans tout re-entrainer, et PostTraining pour les techniques d'alignement de pointe (RLHF, DPO, GRPO, RLVR).

**Industrialisation** -- Les applications GenAI se testent : la serie Playwright-OWUI ecrit des tests de bout en bout sur Open WebUI (navigation, streaming, RAG, outils MCP, CI/CD), pour passer de la demonstration jouet au produit deployable.

**Vibe-Coding** -- Le developpement assiste par agents IA, devenu competence centrale : ateliers progressifs sur Claude Code et Roo Code, plus une introduction aux agents autonomes (Claw-Systems), de la decouverte a l'automatisation avancee (skills, sous-agents, MCP, hooks).

Tout converge dans un fil rouge transverse : le **Texte** structure un script, l'**Image** l'illustre, l'**Audio** le narre, la **Video** l'assemble, et **Semantic Kernel** orchestre l'ensemble en agents autonomes -- c'est ce parcours d'integration qui distingue une demo d'un produit deployable.

Python | [README detaille](MyIA.AI.Notebooks/GenAI/README.md)

### QuantConnect -- Trading algorithmique

Peut-on appliquer l'IA aux marches financiers -- et comment savoir si une strategie *marche* vraiment, plutot que d'avoir simplement eu de la chance sur un historique ? Le trading algorithmique genere aujourd'hui plus de la moitie des volumes echanges, et cette serie -- l'une des plus vastes du depot -- apprend a construire, backtester et deployer ses propres strategies sur le framework open-source **LEAN** de QuantConnect, utilise par des milliers de quants professionnels. Son fil conducteur n'est pas la course au rendement : c'est la **discipline d'evaluation** qui separe un edge reel d'un mirage de backtest -- validation hors echantillon, walk-forward, repetition multi-graine, couts de transaction reels, tests de significativite. Tout se passe en backtest et paper trading, sur le cloud QuantConnect (free tier), sans capital ni installation locale. Le livre de reference est *Hands-On AI Trading*, de Jared Broad, fondateur de QuantConnect.

**Le cours -- des fondations LEAN a l'IA de pointe** -- Le parcours pedagogique monte en huit phases et impose de maitriser l'ecosysteme avant tout modele : architecture LEAN et cycle de vie d'un algorithme, gestion des donnees, selection d'univers, classes d'actifs (actions, options, futures, forex), types d'ordres et risk management, puis l'Algorithm Framework modulaire (Alpha, Portfolio Construction, Execution, Risk) qui rend les strategies scalables. Vient seulement ensuite l'IA : donnees alternatives et analyse de sentiment, machine learning classique (Random Forest, XGBoost), deep learning pour series temporelles (LSTM, Transformers, autoencodeurs), et enfin reinforcement learning, LLMs employes comme generateurs de signaux, detection de regime de marche et deploiement live. Chaque notebook s'execute sur le cloud, avec des contournements documentes pour rester dans le free tier.

**Les strategies -- ce qui survit au backtest realiste** -- Un large catalogue de strategies pretes a backtester accompagne le cours, du momentum multi-actifs et des facteurs Fama-French jusqu'aux options couvertes, au mean reversion et aux approches ML/DL/RL. Leur singularite pedagogique est assumee : les performances varient *volontairement*. Quelques strategies dominent durablement, beaucoup ne battent leur indice que dans certains regimes, quelques-unes perdent -- et c'est precisement l'enseignement. Le suivi de tendance survit aux longues periodes ; un croisement de moyennes brillant sur backtest court s'effondre en hors-echantillon, demonstration concrete du danger du surapprentissage ; des composites censes cumuler les defenses font parfois moins bien que leurs briques isolees. Chaque strategie vient avec son code source, son notebook de recherche standalone (yfinance/pandas) et ses metriques verifiees sur le cloud.

**Le pipeline d'entrainement ML -- la rigueur qui separe l'edge du hasard** -- Un pipeline complet entraine et evalue des modeles de forecasting financier : LSTM, Transformer, PatchTST, iTransformer, Mamba, reseaux de neurones sur graphes, Decision Transformer et melanges d'experts, plus l'evaluation zero-shot de modeles foundation (Chronos-Bolt, Kronos) et une serie systematique de modeles de volatilite (HAR, GARCH, HEAVY, Markov-switching). Mais l'architecture n'est pas le coeur du sujet : la valeur tient au protocole de validation, intentionnellement severe -- walk-forward expansif a plusieurs plis, repetition sur plusieurs graines, test de Diebold-Mariano pour la significativite statistique, univers expurge des megacaps technologiques pour eviter le biais de survie, couts de transaction appliques. Le verdict est binaire et honnete : BEATS, NO BEATS ou INCONCLUSIVE -- la majorite des etages testes sont rejetes, et c'est documente comme tel. Un resultat marquant en ressort : les modeles qui *classent une action* (acheter, tenir, vendre) battent ceux qui *predisent un rendement*, parce que la traduction d'une prevision en position detruit le signal via les couts et la discretisation. L'entrainement GPU y est thermalement protege pour tourner sur du materiel reel.

**Le cours partenaire -- de l'exercice au deploiement** -- Un volet dedie, sponsorise par Jared Broad (fondateur de QuantConnect) via le palier Trading Firm, propose une progression operationnelle : des templates gradues (debutant : croisement EMA sur crypto ; intermediaire : ranking momentum avec Algorithm Framework ; avance : RandomForest sur BTC avec re-entrainement mensuel), des exemples d'instructeur valides par des backtests reels, et des notebooks de recherche QuantBook qui materialisent le workflow canonique du quant -- *idee, recherche, backtest, deploiement*. Plusieurs strategies deployees sur le cloud sont directement issues des modeles retenus par le pipeline ML, bouclant la chaine de la recherche a la production.

Cette serie est le terrain ou convergent les autres : les modeles predictifs de **ML** s'y appliquent a des donnees de marche reelles, **RL** y prolonge ses memes gradients et sa meme mefiance du surapprentissage, **Probas** y nourrit la gestion bayesienne du risque, **Search** y rejoint l'optimisation d'hyperparametres, et **GenAI** y branche ses LLMs sur l'analyse de sentiment. Surtout, la discipline d'evaluation honnete qu'elle exige -- preferer un "NO BEATS" verifie a un "prometteur" complaisant -- est exactement celle que reclame la serie ML : ici, elle a le marche pour juge.

Python | [README detaille](MyIA.AI.Notebooks/QuantConnect/README.md) | [Strategies](MyIA.AI.Notebooks/QuantConnect/projects/README.md)

### RL -- Apprentissage par renforcement

Comment apprendre a decider quand personne ne fournit la bonne reponse ? La ou l'apprentissage supervise predit a partir d'exemples etiquetes et l'apprentissage non supervise degage des structures, le renforcement **agit** : un agent choisit une action, observe la recompense ou la penalite que lui renvoie son environnement, et corrige sa strategie a l'essai et a l'erreur. C'est le paradigme derriere AlphaGo, la marche des robots et les moteurs de recommandation. Le fil conducteur de la serie est un pari pedagogique assume -- *agir d'abord, comprendre ensuite* : on entraine un agent fonctionnel en quelques lignes avec un framework industriel, puis on reimplemente les memes algorithmes a la main pour voir ce qui tourne sous le capot.

**Le framework d'abord -- un agent qui marche en quelques lignes** -- Le point d'entree est **Stable Baselines3** : on entraine un agent PPO a equilibrer un baton (CartPole) et on visualise sa progression avant d'avoir ecrit la moindre equation. La prise en main s'enrichit ensuite des outils de production -- wrappers pour reconfigurer un environnement, callbacks pour monitorer et sauvegarder, multiprocessing pour accelerer -- puis franchit un saut qualitatif avec les taches a objectif (goal-conditioned RL) et l'astuce HER, qui reinterprete les echecs comme des succes : on passe d'equilibrer un baton a garer une voiture. L'intuition concrete precede la theorie, jamais l'inverse.

**Les maths sous le capot -- reimplementer pour comprendre** -- Le second temps quitte le framework et reconstruit tout depuis zero. On commence par la question fondatrice -- explorer de nouvelles options ou exploiter ce qui marche deja -- sur les bandits manchots (epsilon-greedy, Thompson Sampling, regret cumule). Vient ensuite la formalisation : processus de decision markovien, equation de Bellman, value et policy iteration, Q-Learning tabulaire. Puis le passage a l'echelle par les reseaux de neurones, en PyTorch pur et par paliers : DQN et REINFORCE, l'architecture acteur-critique (A2C), PPO et son surrogate clippe avec GAE, enfin SAC et le cadre maximum d'entropie pour les actions continues. Chaque algorithme eclaire un compromis -- on-policy contre off-policy, value-based contre policy-based, biais contre variance.

**Plusieurs agents qui apprennent -- du jeu solitaire a l'interaction** -- La serie se clot sur le multi-agent : plusieurs agents qui apprennent simultanement, cooperent ou s'affrontent. Avec PettingZoo et l'Independent Q-Learning, un agent affronte sa propre copie en self-play sur un jeu a somme nulle -- la meme situation que la theorie des jeux, mais ou l'equilibre est *appris* plutot que calcule.

Ce dernier pas ouvre la porte des series voisines. Le multi-agent prolonge directement **GameTheory** -- equilibre de Nash appris au lieu d'etre demontre -- tandis que les MDP generalisent les processus decisionnels bayesiens de **Probas**, dont la theorie de l'utilite fournit le socle. Le renforcement partage avec **ML** ses outils (PyTorch, gradients) et avec **Search** sa parente entre value iteration et exploration d'un espace d'etats ; il s'incarne enfin sur donnees reelles en **QuantConnect**, ou acheter et vendre deviennent des actions et le profit une recompense. Le contraste feed-forward contre recurrent qui structure ses architectures rejoint meme la question soulevee par **IIT**.

Python | [README detaille](MyIA.AI.Notebooks/RL/README.md)

### IIT -- Theorie de l'Information Integree

La conscience est-elle mesurable ? La theorie de l'information integree, proposee par Giulio Tononi, repond oui : un systeme est conscient dans la mesure ou il integre de l'information de maniere irreductible, et cette quantite porte un nom et une valeur calculable -- **Phi**. C'est une serie courte mais singuliere : on y manipule un formalisme precis, calculable avec **PyPhi** (la bibliotheque de reference du laboratoire Tononi), pour une grandeur que l'on croit d'ordinaire reservee a la philosophie. Son fil conducteur est exactement cette tension : calculer rigoureusement une mesure de la conscience tout en gardant un esprit critique sur ce qu'elle signifie vraiment.

**Calculer Phi -- du reseau causal a la geometrie de l'information** -- On part de circuits binaires elementaires : une matrice de transition decrit les regles d'evolution du systeme, et le calcul de Phi sur un petit reseau XOR rend concrete la notion d'integration irreductible. La structure cause-effet revele comment un systeme specifie sa propre geometrie informationnelle. Un second temps deconstruit le calcul : partition d'information minimale (MIP) pour localiser le maillon faible, repertoires cause-effet, mecanismes maximalement irreductibles (MICE), et distinction entre le Phi du systeme entier et le phi d'un mecanisme isole. L'extension a des reseaux plus grands fait surgir une explosion combinatoire qui rend le calcul exact intractable des qu'on depasse une poignee de noeuds -- d'ou le coarse-graining comme strategie d'approximation, et un apercu des evolutions recentes vers IIT 4.0.

**De la mesure aux debats -- ce que Phi engage** -- L'IIT n'est pas qu'une speculation : ses principes ont inspire le Perturbational Complexity Index, une mesure clinique (stimulation magnetique transcranienne plus EEG) qui distingue empiriquement les etats conscients des etats inconscients chez des patients non communicants. Elle s'oppose frontalement aux theories du Global Workspace dans des tests adversariaux sur donnees reelles. Et elle touche directement l'IA : un reseau purement feed-forward -- comme l'inference d'un grand modele de langage classique -- a un Phi nul, car l'information y transite sans boucle causale integree ; il calcule sans "etre". Une critique publique retentissante (une lettre ouverte la qualifiant de pseudoscience) fait de l'IIT un cas d'ecole pour interroger les criteres de scientificite d'une theorie de l'esprit.

Cette serie dialogue avec **Probas** et **GameTheory**, dont elle partage les concepts de causalite et d'interaction, et avec **RL** : la distinction feed-forward contre recurrent, qui annule ou non Phi, eclaire le choix d'architecture d'un agent. Le constat qu'un modele de langage feed-forward a un Phi nul prolonge enfin les discussions sur la conscience artificielle qui traversent **GenAI**.

Python | [README detaille](MyIA.AI.Notebooks/IIT/README.md)

### CaseStudies -- Etudes de cas interdisciplinaires

Que se passe-t-il quand on cesse d'etudier les techniques en silos ? L'IA reelle ne fonctionne presque jamais avec un seul paradigme : un assistant de diagnostic combine des regles symboliques, des modeles probabilistes, de la recherche heuristique et des contraintes formelles. Cette serie, concue comme un devoir integrateur de fin de cycle, prend deux problemes metier -- un diagnostic medical, une planification oncologique -- et y compose plusieurs solveurs en un seul systeme decisionnel coherent. Son fil conducteur est l'architecture hybride en couches, et l'idee que l'**ordre de composition** importe autant que les briques elles-memes.

**Composer les paradigmes en cascade -- l'architecture hybride** -- Chaque projet empile cinq couches : des connaissances metier (ontologies OWL, regles), un filtre de contraintes dures (CSP, SMT, OR-Tools), une modelisation de l'incertitude (bayesien, Pyro, Infer.NET), une optimisation (recherche A-star, algorithme genetique, et au-dela le renforcement) et une decision finale expliquee. On filtre avant d'optimiser, on modelise l'aleatoire avant de valider sous contraintes : le Diagnostic Medical articule recherche informee, algorithme genetique et validation par solveur Z3 ; l'Oncology Planning marie ontologie, planification CP-SAT et inference probabiliste. Aucune couche ne suffit seule, et c'est tout l'enseignement.

**Le jumeau numerique -- un patient simule pour decider sans risque** -- Les deux projets reposent sur un modele de patient simule : un objet logiciel qui represente un etat clinique et reagit aux interventions proposees. Ce pattern de jumeau numerique, devenu central en sante numerique comme en industrie, permet de tester des scenarios de traitement sans toucher au patient reel. La pedagogie privilegie l'autonomie : chaque projet fournit un template etudiant executable de bout en bout (stubs conformes, jamais d'erreur volontaire) et une solution de reference pour s'autoevaluer.

Le choix du medical est pedagogique, pas exclusif : la meme architecture en couches se transpose telle quelle a la finance (jumeau de marche, contraintes reglementaires, signaux probabilistes), a la logistique ou a la maintenance predictive. C'est le devoir qui ferme la boucle du cursus, en convoquant simultanement **Search**, **SymbolicAI**, **Probas**, **Planners**, **SemanticWeb** et **RL** autour d'une seule question reelle.

Python | [README detaille](MyIA.AI.Notebooks/CaseStudies/README.md)

### cross-series -- Applications transverses

La derniere etape franchit la frontiere du notebook. Le repertoire `cross-series/` rassemble des applications completes -- code structure, tests, interface -- ou les techniques vues separement se rejoignent dans un livrable autonome et deployable. L'exemple de reference, `matching-cv`, est une application web Flask qui confronte trois facons d'apparier un CV a une offre d'emploi : l'appariement stable de Gale-Shapley (rencontre en **GameTheory** et **SymbolicAI**), la similarite semantique par plongements et le RAG hybride (issus de **GenAI**), avec la recherche en arriere-plan. Comparer ces approches sur le meme probleme, c'est mesurer ce que chaque paradigme apporte vraiment -- la meme demarche que le banc d'essai du **Sudoku**, transposee a une application reelle. C'est ici que le depot tient sa promesse : non pas une collection d'outils juxtaposes, mais des manieres complementaires de resoudre, faites pour se combiner.

[README detaille](MyIA.AI.Notebooks/cross-series/README.md)

---

## Structure du depot

```text
CoursIA/
  MyIA.AI.Notebooks/          Notebooks interactifs, organises par serie
    Search/                    Algorithmes de recherche (Python, C#)
    Sudoku/                    Resolution multi-paradigme (Python, C#)
    SymbolicAI/                IA symbolique (Python, Lean 4, C#)
      Tweety/ SemanticWeb/ Lean/ Planners/ SmartContracts/ Argument_Analysis/ SymbolicLearning/
    GameTheory/                Theorie des jeux (Python, Lean 4)
    Probas/                    Programmation probabiliste (C#, Python)
    ML/                        Machine Learning (C#, Python)
    RL/                        Reinforcement Learning (Python)
    GenAI/                     IA Generative (Python)
      Image/ Audio/ Video/ Texte/ SemanticKernel/ Vibe-Coding/
    QuantConnect/              Trading algorithmique (Python)
      Python/                  Notebooks pedagogiques
      projects/                Strategies backtestees
      ML-Training-Pipeline/    Pipeline DL forecasting
      partner-course-quant-trading/ Projets etudiants
    CaseStudies/               Etudes de cas interdisciplinaires (Python)
    cross-series/              Applications transverses multi-domaines (Python)
    IIT/                       Information integree (Python)
    Config/                    Configuration API

  scripts/                     Validation, execution, analyse
  docker-configurations/       Infrastructure Docker GPU
  GradeBookApp/                Notation etudiants
  MyIA.AI.Shared/              Bibliotheque C# partagee
  notebook-infrastructure/     Papermill + MCP maintenance
```

---

## Mise en route

### Prerequis

- Python 3.10+ avec pip
- .NET 9.0 SDK (pour notebooks C#)
- VS Code avec extensions Python, Jupyter, .NET Interactive
- WSL (pour Lean et certains outils SymbolicAI)
- Docker + GPU (optionnel, pour GenAI avance)

### Installation rapide

```bash
# 1. Cloner
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA

# 2. Environnement Python (un venv suffit pour la majorite des series)
python -m venv venv
venv\Scripts\activate          # Windows ; sous Linux/WSL : source venv/bin/activate
pip install jupyter ipykernel python-dotenv

# 3. Kernel Jupyter Python
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"

# 4. Kernel .NET Interactive (notebooks C#)
dotnet tool install --global Microsoft.dotnet-interactive
dotnet interactive jupyter install
dotnet restore MyIA.CoursIA.sln

# 5. Dependances de la serie visee (chaque serie porte son requirements.txt)
pip install -r MyIA.AI.Notebooks/<Serie>/requirements.txt
```

Les cles API eventuelles se posent via les `.env.example` (section Configuration). Pour valider
ou executer un notebook, ne pas ecrire de script ad-hoc : le depot fournit une CLI dediee
(section Scripts et validation).

### Installation par serie

La plupart des series sont autonomes et s'ouvrent sur un **notebook de mise en route**
(Setup / Environment) qui installe les dependances de la serie et verifie la chaine d'outils :
c'est le point de depart recommande. Pour les kernels, WSL et toolchains specifiques, des
scripts de preparation dedies accompagnent ces notebooks. Les series sans notebook de setup
s'installent directement via leur `requirements.txt`.

| Serie | Notebook de mise en route | Preparation dediee |
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
| Tweety | `SymbolicAI/Tweety/Tweety-1-Setup.ipynb` | `tweety_init.py` (JDK auto-telecharge) |
| Argument Analysis | `SymbolicAI/Argument_Analysis/Argument_Analysis_UI_configuration.ipynb` | `install_jdk_portable.py` |
| IIT | `requirements.txt` | `scripts/setup_pyphi_env.ps1` |
| Search / RL / CaseStudies | `requirements.txt` | -- |
| cross-series | `requirements.txt` | `cross-series/matching-cv/scripts/install_deps.sh` |

Pour les series qui exposent un `requirements.txt`, l'installation directe reste possible :

```bash
pip install -r MyIA.AI.Notebooks/<Serie>/requirements.txt
```

Les notebooks C# (ML.NET, Sudoku, SemanticWeb, Probas/Infer.NET) ne passent pas par pip :
ils s'appuient sur le kernel .NET Interactive et `dotnet restore` (section Mise en route).

---

## Configuration

Les series Search, Sudoku, ML.Net, Probas (Infer.NET), Tweety, SemanticWeb et Planners fonctionnent sans aucune cle API. Les series suivantes necessitent une configuration :

| Serie | Fichier | Variables requises |
|-------|---------|-------------------|
| GenAI | `GenAI/.env` | `OPENAI_API_KEY`, `ANTHROPIC_API_KEY` |
| Lean | `SymbolicAI/Lean/.env` | `OPENAI_API_KEY`, `GITHUB_TOKEN` |
| Argument Analysis | `SymbolicAI/Argument_Analysis/.env` | `OPENAI_API_KEY` |
| QuantConnect | `QuantConnect/.env` | `QC_USER_ID`, `QC_API_TOKEN` |
| C# Notebooks | `Config/settings.json` | `apikey`, `model` |
| Docker ComfyUI | `comfyui-qwen/.env` | `CIVITAI_TOKEN`, `HF_TOKEN` |

Chaque dossier contient un `.env.example` documentant les variables. Copier et editer :

```bash
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
# Editer le fichier .env avec vos cles
```

---

## Kernels Jupyter

| Kernel | Series | Installation |
|--------|--------|--------------|
| `python3` | Tous les notebooks Python | `pip install ipykernel` |
| `.net-csharp` | Sudoku, Search, Probas, ML | `dotnet tool install -g Microsoft.dotnet-interactive` |
| `lean4_jupyter` | Lean, GameTheory (b) | Via `elan` (WSL uniquement) |

Limitations connues : les notebooks C# avec `#!import` necessitent une execution cellule par cellule (incompatible Papermill). Lean 4 requiert WSL sous Windows.

---

## Infrastructure Docker

Pour les notebooks GenAI avances utilisant des modeles locaux (Qwen Image Edit, ComfyUI Video, etc.), une infrastructure Docker avec support GPU est fournie.

Services disponibles : Qwen Image Edit (~29 Go VRAM), ComfyUI Video (~12 Go), Stable Diffusion Forge (~10 Go), Whisper, MusicGen, Kokoro TTS, Demucs.

La pile s'orchestre via le CLI `genai.py` plutot que des commandes `docker` lancees a la main :

```bash
cp docker-configurations/services/comfyui-qwen/.env.example docker-configurations/services/comfyui-qwen/.env
python scripts/genai-stack/genai.py docker status      # etat des services
python scripts/genai-stack/genai.py docker start all   # demarrer
python scripts/genai-stack/genai.py docker stop all    # arreter
python scripts/genai-stack/genai.py gpu                # verifier la VRAM disponible
```

Configuration detaillee dans `docker-configurations/`.

---

## Scripts et validation

Regle de base : **toujours passer par ces scripts pour valider ou executer un notebook,
jamais par un script ecrit pour l'occasion**. La CLI detecte le kernel depuis les metadonnees
du notebook (Python, .NET Interactive, Lean sous WSL).

| Script | Usage |
|--------|-------|
| `scripts/notebook_tools/notebook_tools.py` | CLI multi-series : `validate`, `execute`, `analyze`, `skeleton`, `check-env` |
| `scripts/notebook_tools/notebook_helpers.py` | Manipulation de notebooks, iteration cellule par cellule |
| `scripts/genai-stack/genai.py` | Pile GenAI : `docker`, `validate`, `notebooks`, `gpu` |
| `scripts/smartcontracts/validate_sc_notebooks.py` | Validation dediee Smart Contracts (`--quick`, `--execute --anvil`) |

```bash
# Validation de structure
python scripts/notebook_tools/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku

# Execution (Papermill ; --cell-by-cell pour les notebooks .NET / Lean)
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/Search --cell-by-cell

# Verification de l'environnement d'une famille
python scripts/notebook_tools/notebook_tools.py check-env GenAI

# Validation complete de la pile GenAI
python scripts/genai-stack/genai.py validate --full
```

Un workflow GitHub Actions valide automatiquement les notebooks a chaque pull request (format, syntaxe, execution de base).

---

## Outils Claude Code

Le depot inclut une configuration Claude Code avec des agents specialises et des commandes slash pour la maintenance des notebooks.

**Commandes principales** : `/verify-notebooks`, `/enrich-notebooks`, `/cleanup-notebooks`, `/build-notebook`, `/execute-notebook`, `/validate-genai`, `/qc-iterative-improve`

**Agents specialises** : notebook-enricher, notebook-validator, notebook-executor, qc-strategy-analyzer, qc-strategy-improver, readme-updater, et d'autres.

Configuration dans `.claude/agents/` et `.claude/skills/`.

---

## Outils et dependances externes

Les dependances principales par serie :

| Outil | Series | Provenance |
|-------|--------|-----------|
| Z3 SMT Solver | Sudoku, Search, SymbolicAI | `requirements.txt` de la serie |
| OR-Tools | Sudoku, Search, Planners | `requirements.txt` de la serie |
| Tweety + JDK | Tweety, Argument_Analysis | JDK auto-telecharge ; reste dans `requirements.txt` |
| Lean 4 + Mathlib | Lean, GameTheory | `elan` (WSL) ; diagnostic via `validate_lean_setup.py` |
| OpenSpiel | GameTheory | `requirements.txt` GameTheory |
| Infer.NET | Probas | NuGet (kernel .NET Interactive) |
| PyPhi | IIT | `requirements.txt` IIT |

---

## Contribution

1. Fork le depot
2. Creer une branche (`git checkout -b feature/nouveau-notebook`)
3. Commit (`git commit -m 'Add: notebook sur les Transformers'`)
4. Push et ouvrir une Pull Request

Conventions : PEP 8 pour Python, conventions standard pour C#, pas d'emojis dans le code, documentation en francais. Chaque famille de notebooks doit inclure un `.env.example` documentant les variables requises.

## Licence

Ce projet est sous licence MIT - voir [LICENSE](LICENSE).

---

Repository : [github.com/jsboige/CoursIA](https://github.com/jsboige/CoursIA)
