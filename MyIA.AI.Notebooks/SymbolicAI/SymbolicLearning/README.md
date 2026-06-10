# SymbolicLearning - Apprentissage Symbolique

<!-- CATALOG-STATUS
series: SymbolicAI-SymbolicLearning
pedagogical_count: 7
breakdown: SymbolicLearning=7
maturity: PRODUCTION=7
-->

Comment un agent peut-il apprendre a partir de connaissances existantes plutot que de donnees brutes ? Cette serie explore l'apprentissage symbolique tel que decrit dans le chapitre 19 d'AIMA (Russell & Norvig), depuis l'apprentissage inductif pur (CBH, Version Space) jusqu'aux methodes guidees par la connaissance (EBL, RBL).

Le premier notebook pose les bases : representation d'hypotheses comme conjonctions de contraintes, algorithmes Current-Best-Hypothesis et Candidate Elimination (Version Space), et leurs limites face au bruit et aux concepts disjonctifs. Le second notebook montre comment la connaissance du domaine accelere l'apprentissage : l'apprentissage base sur les explications (EBL) compile les theories en heuristiques operationnelles, et l'apprentissage base sur la pertinence (RBL) identifie les attributs determinant via les determinations. Le troisieme notebook approfondit le RBL avec le treillis des determinations, l'algorithme MINIMAL-CONSISTENT-DET et une comparaison avec sklearn. Le quatrieme notebook couvre la programmation logique inductive (ILP) : l'algorithme FOIL (top-down), la resolution inverse (bottom-up) et la connexion avec les knowledge graphs. Les trois derniers notebooks ouvrent vers des methodes contemporaines : SL-5 introduit le neuro-symbolique (T-norms differentiables, Logic Tensor Networks, DeepProbLog) ; SL-6 outille la decouverte de regles sur knowledge graphs reels avec rdflib et AMIE rule mining ; SL-7 boucle LLM et verification symbolique pour fiabiliser le raisonnement formel guide par modeles de langage. Trois notebooks etendent la serie : SL-8 change de paradigme avec l'apprentissage *actif* (l'algorithme L* d'Angluin interroge un oracle au lieu de subir un echantillon, et apprend des automates finis avec garanties de minimalite) ; SL-9 complete l'ILP de SL-4 par la voie bottom-up aboutie (LGG de Plotkin, theta-subsomption, clause bottom et recherche a la Progol) ; SL-10 est le capstone qui assemble toute la serie en un pipeline neuro-symbolique de bout en bout — du texte brut aux faits decouverts, avec un LLM reel (Gemini 3.5 Flash) aux deux extremites et le symbolique comme colonne vertebrale.

**A qui s'adresse cette serie** : etudiants en IA, informaticiens interesses par le raisonnement symbolique, et chercheurs en apprentissage automatique souhaitant comprendre les approches non-statistiques. Les notebooks (~9h30 total) ne necessitent que Python 3.10+ standard library, sauf SL-3 (scikit-learn + numpy pour la comparaison RBL / information mutuelle) et SL-6 (rdflib pour les knowledge graphs) ; SL-7 et SL-10 acceptent une cle OpenRouter optionnelle (fichier `.env`) pour des appels LLM reels, avec un simulateur deterministe en repli. Une familiarite avec la logique propositionnelle suffit pour SL-1 a SL-4, SL-8 et SL-9 ; SL-5, SL-7 et SL-10 supposent une intuition des reseaux de neurones et des LLMs. Ils constituent un complement theorique aux series [Tweety](../Tweety/README.md) (argumentation computationnelle), [SemanticWeb](../SemanticWeb/README.md) (representation de connaissances) et [ML](../../ML/README.md) (apprentissage statistique - contraste avec l'inductif symbolique).

## Pourquoi cette serie

L'apprentissage symbolique represente la contrepartie theorique du machine learning statistique. Tandis que les methodes modernes (deep learning, ensembles d'arbres) excellent a extraire des patterns de grandes masses de donnees, elles souffrent de trois limites fondamentales que l'approche symbolique adresse directement :

- **Peu de donnees disponibles** : les methodes symboliques comme Candidate Elimination ou FOIL apprennent a partir de quelques exemples,voire d'un seul (EBL). Quand la collecte de donnees est couteuse ou impossible (diagnostic medical rare, validation formelle), l'induction pure ne fonctionne pas.
- **Interpretabilité requise** : une regle logique `IF temperature > 38 AND toux THEN infection` est comprehensible par un humain. Un reseau de neurones de 100M de parametres ne l'est pas. Pour les applications critique ou reglementees (medecine, finance, justice), l'interpretabilité n'est pas un luxe — c'est une exigence.
- **Integration avec la connaissance existante** : les methodes symboliques combinent examples ET theorie du domaine. EBL compile un exemple prouve en une regle operationnelle generale ; RBL identifie les attributs determinant via des contraintes formelles. Aucune methode statistique ne peut exploiter cette connaissance a priori de la meme facon.

Cette serie montre que les deux approches ne s'opposent pas — elles se **complementent**. La phase finale (SL-5 a SL-7) explore explicitement cette integration : T-norms differentiables pour rendre la logique compatible avec l'entrainement neuronal, rule mining sur knowledge graphs reels, et boucles de verification symbolique pour fiabiliser les sorties LLM.

## Objectifs d'apprentissage

A l'issue de cette serie, vous serez capable de :

1. **Implémenter** les algorithmes d'apprentissage inductif de base (CBH, Candidate Elimination, Version Space)
2. **Compiler** des preuves en heuristiques operationnelles via EBL, et **identifier** les attributs pertinents via RBL et les determinations
3. **Construire** le treillis des determinations et appliquer MINIMAL-CONSISTENT-DET pour la selection guidee d'attributs
4. **Apprendre** des regles logiques ( clauses Horn ) a partir d'exemples avec FOIL et la resolution inverse
5. **Intégrer** logique et apprentissage neuronal via T-norms, Logique Tensorielle, et DeepProbLog
6. **Extraire** des regles de knowledge graphs reels avec rdflib et AMIE, et **effectuer** la completion de graphes
7. **Concevoir** une boucle LLM-symbolique : extraction de regles IF-THEN depuis du texte, verification de coherence formelle, feedback pour l'amelioration
8. **Implémenter** l'algorithme L* d'Angluin : table d'observation, requetes d'appartenance et d'equivalence, apprentissage actif d'automates minimaux
9. **Construire** la chaine bottom-up de l'ILP : LGG de Plotkin, theta-subsomption, clause bottom et recherche de clause a la Progol
10. **Assembler** un pipeline neuro-symbolique complet : extraction LLM, oracle de validation type, mining de regles, chainage avant avec provenance, et confrontation LLM vs KG

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 10 |
| Exercices (table de pioche) | 40 |
| Kernel | Python 3 |
| Duree estimee | ~570 min |
| prerequis | Python 3.10+ (standard library + sklearn pour SL-3/SL-4, rdflib pour SL-6, cle OpenRouter optionnelle pour SL-7/SL-10) |

## Parcours d'apprentissage

### Phase 1 : Fondations inductives (SL-1, ~50 min)

Le parcours commence par l'apprentissage inductif pur : un agent doit decouvrir une regle cachee a partir d'exemples. SL-1 presente les algorithmes fondamentaux — Current-Best-Hypothesis (ajuste une seule hypothese incrementalement) et Candidate Elimination (maintient l'ensemble complet des hypotheses consistantes, le "Version Space"). Vous experimentez leurs limites face au bruit et aux concepts disjonctifs, ce qui motive naturellement les approches plus riches introduites ensuite.

### Phase 2 : Apprentissage base sur la connaissance (SL-2 a SL-3, ~95 min)

La deuxieme phase introduit l'idee centrale que **la connaissance accelere l'apprentissage**. EBL (SL-2) montre comment compiler un exemple prouve en une regle operationnelle generale, en quatre etapes : expliquer, variabiliser, extraire, simplifier. RBL (introduit en SL-2, approfondi en SL-3) explore une autre facette : identifier les attributs qui determinant vraiment la cible via le formalisme des determinations et le treillis des sous-ensembles d'attributs. La comparaison avec sklearn (information mutuelle) montre quand la connaissance du domaine bat la statistique brute.

### Phase 3 : Programmation logique inductive (SL-4, ~55 min)

SL-4 fait le pont entre apprentissage automatique et intelligence artificielle symbolique classique en couvrant l'ILP : apprentissage de programmes logiques (clauses Horn) a partir d'exemples. L'algorithme FOIL (top-down) et la resolution inverse (bottom-up) sont implémentes de zero, puis appliques aux knowledge graphs — avec extraction de regles AMIE et requetes SPARQL CONSTRUCT. La section finale confronte le FOIL artisanal a l'ILP moderne : **Popper** (Learning From Failures) retrouve le programme recursif `ancestor` optimal sur les memes donnees, demontre l'apport de la recursion par ablation, et le programme appris est verifie independamment en SWI-Prolog.

### Phase 4 : Integration neuro-symbolique (SL-5 a SL-7, ~160 min)

La phase finale explore les methodes contemporaines a l'intersection du symbolique et du connexionniste. SL-5 introduit les T-norms differentiables, les predicats neuronaux et les Logics Tensor Networks qui rendent la logique operationnelle dans un gradient descent. SL-6 passe a l'echelle avec le rule mining reel sur des knowledge graphs construits avec rdflib (AMIE, completion de graphes). SL-7 ferme la boucle avec LLMs : extraction de regles depuis du texte naturel, verification symbolique des sorties, et boucles de retroaction pour fiabiliser le raisonnement.

### Phase 5 : Apprentissage actif, ILP bottom-up et capstone (SL-8 a SL-10, ~210 min)

Trois extensions concluent la serie. SL-8 inverse le rapport de l'apprenant aux donnees : au lieu de subir un echantillon, L* d'Angluin *choisit* ses questions (requetes d'appartenance et d'equivalence a un oracle MAT) et apprend des automates finis deterministes prouvablement minimaux — le cadre theorique (Myhill-Nerode, fermeture et coherence de la table d'observation) est implemente et verifie de zero. SL-9 reprend la promesse bottom-up esquissee en SL-4 et la mene a terme : LGG de Plotkin, theta-subsomption, clause bottom par entailment inverse, et recherche de clause a la Progol qui retrouve la definition de `grandfather/2` parmi 56 candidats. SL-10 est le capstone : un pipeline neuro-symbolique en 6 etages (extraction LLM -> oracle de validation -> knowledge graph -> mining de regles -> chainage avant avec provenance -> confrontation LLM vs KG) execute avec de vrais appels Gemini 3.5 Flash, ou chaque etage mobilise un notebook anterieur de la serie — y compris une lecon d'architecture decouverte dans les sorties reelles : le chainage avant peut violer les contraintes que l'oracle impose en amont.

### Parcours alternatives

#### Parcours rapide (SL-1 + SL-5 + SL-7 + SL-10, ~4h)

Pour ceux qui veulent saisir l'essence sans suivre toute la progression : les fondements inductifs (SL-1), l'integration neuro-symbolique (SL-5), la verification LLM (SL-7) et le capstone qui assemble le tout (SL-10). Donne une vue d'ensemble du spectre, de l'inductif pur au pipeline neuro-symbolique complet.

#### Parcours ILP approfondi (SL-1 a SL-4 + SL-9, ~325 min)

Pour les etudiants en logique et IA symbolique : suivre les quatre premiers notebooks dans l'ordre, puis SL-9 qui mene le bottom-up a terme — de Candidate Elimination a FOIL, puis LGG, theta-subsomption, clause bottom et Progol.

#### Parcours theorie des langages (SL-1 + SL-8, ~110 min)

Pour les etudiants en informatique theorique : le cadre inductif general (SL-1), puis l'apprentissage actif d'automates avec ses garanties formelles (SL-8) — requetes, Myhill-Nerode, minimalite, bornes PAC de l'oracle d'equivalence echantillonne.

#### Parcours knowledge graphs (SL-2, SL-3, SL-4, SL-6, ~220 min)

Pour les professionnels du web semantique et des donnees structurees : EBL, RBL, FOIL sur clauses Horn, puis application directe sur des knowledge graphs reels avec rdflib et AMIE. Presuppose une familiarite avec RDF/SPARQL.

## Seance de restitution : la table de pioche (40 exercices)

Modalite de la seance : chaque groupe choisit **un exercice** dans la table ci-dessous, le prepare, et le presente en seance. Resoudre l'exercice est le minimum attendu ; chaque exercice est assorti d'une **question-twist** (detaillee dans la cellule « Defi presentation » du notebook correspondant) qui fait partie integrante de la presentation. Premier arrive, premier servi : annoncez votre choix pour eviter les doublons.

| # | Notebook | Exercice | Question-twist (en bref) |
|---|----------|----------|--------------------------|
| 1 | [SL-1](SL-1-LogicalLearning.ipynb) | Ex. 1 — CBH avec ordre personnalise | Deux ordres d'exemples, deux hypotheses finales : pourquoi, a accuracy egale ? |
| 2 | [SL-1](SL-1-LogicalLearning.ipynb) | Ex. 2 — Version Space sur sous-ensemble | Qu'est-ce qui rend un exemple *informatif* (frontieres S et G) ? |
| 3 | [SL-1](SL-1-LogicalLearning.ipynb) | Ex. 3 — Regles avec couverture | Compacite vs hypothese AIMA : quel biais (rasoir d'Occam) prefere l'une a l'autre ? |
| 4 | [SL-1](SL-1-LogicalLearning.ipynb) | Ex. 4 — Reflexion sur le biais conjonctif | Un domaine ou ce biais est ideal, un ou il est catastrophique (no free lunch) |
| 5 | [SL-1](SL-1-LogicalLearning.ipynb) | Ex. 5 — La consistance sans Occam (aima) | Echantillonner les graines ne prouve pas la minimalite : quel algorithme exact le ferait ? |
| 6 | [SL-2](SL-2-KnowledgeBasedLearning.ipynb) | Ex. 1 — EBL differentiation symbolique | Exhiber une variabilisation trop agressive qui produit une regle compilee fausse |
| 7 | [SL-2](SL-2-KnowledgeBasedLearning.ipynb) | Ex. 2 — Filtrage des regles (operationnalite) | Deux distributions de requetes qui inversent le classement d'utilite des regles |
| 8 | [SL-2](SL-2-KnowledgeBasedLearning.ipynb) | Ex. 3 — Speedup EBL | Le *utility problem* (Minton 1990) : pourquoi apprendre plus finit par ralentir |
| 9 | [SL-3](SL-3-RelevanceLearning.ipynb) | Ex. 1 — Determinations meteo | Une observation bruitee : quelle determination minimale survit ? |
| 10 | [SL-3](SL-3-RelevanceLearning.ipynb) | Ex. 2 — RBL vs selection aleatoire | Trouver le point de croisement ou la selection statistique bat le RBL |
| 11 | [SL-3](SL-3-RelevanceLearning.ipynb) | Ex. 3 — Selecteur hybride | Quelles garanties votre hybride herite-t-il vraiment ? Contre-exemple construit |
| 12 | [SL-4](SL-4-InductiveLogicProgramming.ipynb) | Ex. 1 — `sibling` avec FOIL | Le role du biais de langage : que se passe-t-il sans le litteral `X != Y` ? |
| 13 | [SL-4](SL-4-InductiveLogicProgramming.ipynb) | Ex. 2 — Operateur W | Generalisation consistante mais fausse : pourquoi le bottom-up y est expose |
| 14 | [SL-4](SL-4-InductiveLogicProgramming.ipynb) | Ex. 3 — Regles sur mini-KG | Monde clos vs PCA (cf SL-6) : quelle confiance est la bonne pour VOTRE KG ? |
| 15 | [SL-4](SL-4-InductiveLogicProgramming.ipynb) | Ex. 4 — `grandparent` avec Popper | Sans negatif arriere-grand-parent, quel programme plus court devient consistant ? |
| 16 | [SL-5](SL-5-NeuroSymbolic.ipynb) | Ex. 2 — LTN frere/oncle | Retirer les axiomes negatifs : pourquoi une LTN a besoin de negatifs explicites |
| 17 | [SL-5](SL-5-NeuroSymbolic.ipynb) | Ex. 3 — Regle transitive `ancestor` | Le modele trivial « vrai partout » sature la regle : qu'est-ce qui l'evite ? |
| 18 | [SL-5](SL-5-NeuroSymbolic.ipynb) | Ex. 4 — T-norm de Lukasiewicz | Gradients exactement nuls : qu'est-ce qu'une semantique floue *apprenable* ? |
| 19 | [SL-5](SL-5-NeuroSymbolic.ipynb) | Ex. 5 — Ablation de l'axiome 4 (LTNtorch) | Le negatif difficile (Marie, Pierre) est-il indispensable ? Contraste avec clingo (SL-6) |
| 20 | [SL-6](SL-6-KnowledgeGraphs-ILP.ipynb) | Ex. 1 — Nouvelle relation au KG | Regles redondantes (meme extension, syntaxe differente) : comment AMIE les evite |
| 21 | [SL-6](SL-6-KnowledgeGraphs-ILP.ipynb) | Ex. 2 — PCA confidence | Construire un mini-KG ou la PCA confidence est trompeuse |
| 22 | [SL-6](SL-6-KnowledgeGraphs-ILP.ipynb) | Ex. 3 — Regles a 3 atomes | Explosion combinatoire : pourquoi AMIE impose des regles fermees, a quel prix |
| 23 | [SL-6](SL-6-KnowledgeGraphs-ILP.ipynb) | Ex. 4 — Reparation minimale (clingo) | Les reparations optimales sont ex-aequo : departager par des poids de confiance |
| 24 | [SL-7](SL-7-LLM-SymbolicLearning.ipynb) | Ex. 1 — Prompt personnalise | Changer de modele LLM : que garantit vraiment l'oracle symbolique ? |
| 25 | [SL-7](SL-7-LLM-SymbolicLearning.ipynb) | Ex. 2 — Prompt direct vs CoT | Validation oracle vs plausibilite du texte : les deux metriques peuvent diverger |
| 26 | [SL-7](SL-7-LLM-SymbolicLearning.ipynb) | Ex. 3 — Detection d'hallucinations | Le detecteur suppose un monde clos : que devient-il en monde ouvert (cf SL-6) ? |
| 27 | [SL-7](SL-7-LLM-SymbolicLearning.ipynb) | Ex. 4 — Taux d'hallucination du vrai LLM | Maximiser le taux de validation ou le nombre de regles validees par appel ? |
| 28 | [SL-8](SL-8-ActiveAutomataLearning.ipynb) | Ex. 1 — Le langage « contient abb » | Certificat de minimalite : un suffixe distinguant pour chaque paire d'etats (Myhill-Nerode) |
| 29 | [SL-8](SL-8-ActiveAutomataLearning.ipynb) | Ex. 2 — Fiabilite de l'EQ echantillonnee | Relier le taux de reussite empirique a la borne PAC ; construire une distribution adverse |
| 30 | [SL-8](SL-8-ActiveAutomataLearning.ipynb) | Ex. 3 — Contre-exemples : prefixes vs suffixes | Le pire cas qui fait exploser la table d'observation (Rivest-Schapire) |
| 31 | [SL-8](SL-8-ActiveAutomataLearning.ipynb) | Ex. 4 — Oracle bruite | Reparer L* par vote majoritaire : surcout en requetes et probabilite residuelle d'erreur |
| 32 | [SL-9](SL-9-InverseResolution.ipynb) | Ex. 1 — Apprendre `grandmother/2` | Pourquoi `grandparent/2` (sans sexe) est *plus facile* — role des negatifs |
| 33 | [SL-9](SL-9-InverseResolution.ipynb) | Ex. 2 — Profondeur de la clause bottom | Croissance de la clause bottom avec la profondeur ; la cible reste-t-elle dans le treillis ? |
| 34 | [SL-9](SL-9-InverseResolution.ipynb) | Ex. 3 — Tolerance au bruit | Le score `p - n - L` comme argument MDL : quand prefere-t-il une clause imparfaite ? |
| 35 | [SL-9](SL-9-InverseResolution.ipynb) | Ex. 4 — Reduction de Plotkin | Subsomption vs implication : le cas des clauses recursives ou elles divergent |
| 36 | [SL-9](SL-9-InverseResolution.ipynb) | Ex. 5 — Aleph face au bruit | Memoriser l'exception, sur-generaliser ou payer L dans f : trois frontieres face au meme bruit |
| 37 | [SL-10](SL-10-Capstone-NeuroSymbolic.ipynb) | Ex. 1 — Etendre le schema (`marie_avec`) | Le mineur redecouvre la symetrie injectee par l'oracle : regle ou tautologie ? |
| 38 | [SL-10](SL-10-Capstone-NeuroSymbolic.ipynb) | Ex. 2 — Politique de conflit a sources | *Truth discovery* : estimer la fiabilite des sources en meme temps que les faits |
| 39 | [SL-10](SL-10-Capstone-NeuroSymbolic.ipynb) | Ex. 3 — Le bon seuil n'existe pas | Vraie et fausse regle a confiance egale (0.67) : quel signal au-dela du seuil ? |
| 40 | [SL-10](SL-10-Capstone-NeuroSymbolic.ipynb) | Ex. 4 — Empoisonnement bout-en-bout | Classer les defenses par etage du pipeline ; ou s'arrete la provenance ? |

Note : dans SL-5, le premier exercice de la numerotation interne est un exemple guide ; les exercices a piocher sont Ex. 2 a Ex. 5.

## Notebooks

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 1 | [SL-1 - Apprentissage Logique](SL-1-LogicalLearning.ipynb) | CBH, Version Space, Candidate Elimination | 50 min |
| 2 | [SL-2 - Apprentissage et Connaissance](SL-2-KnowledgeBasedLearning.ipynb) | EBL, introduction au RBL (determinations) | 45 min |
| 3 | [SL-3 - Apprentissage Base sur la Pertinence](SL-3-RelevanceLearning.ipynb) | Treillis des determinations, MINIMAL-CONSISTENT-DET, RBL vs sklearn | 50 min |
| 4 | [SL-4 - Programmation Logique Inductive](SL-4-InductiveLogicProgramming.ipynb) | FOIL, resolution inverse, clauses Horn, knowledge graphs, Popper (LFF) | 55 min |
| 5 | [SL-5 - Integration Neuro-Symbolique](SL-5-NeuroSymbolic.ipynb) | T-norms, predicats neuronaux, LTN, DeepProbLog | 55 min |
| 6 | [SL-6 - ILP Moderne et Knowledge Graphs](SL-6-KnowledgeGraphs-ILP.ipynb) | rdflib, AMIE rule mining, completion KG, ASP avec clingo | 55 min |
| 7 | [SL-7 - LLMs et Apprentissage Symbolique](SL-7-LLM-SymbolicLearning.ipynb) | Prompting, extraction de regles, verification symbolique (Gemini 3.5 Flash optionnel) | 50 min |
| 8 | [SL-8 - Apprentissage Actif d'Automates](SL-8-ActiveAutomataLearning.ipynb) | L* d'Angluin, table d'observation, requetes MQ/EQ, Myhill-Nerode | 60 min |
| 9 | [SL-9 - Resolution Inverse et Progol](SL-9-InverseResolution.ipynb) | LGG de Plotkin, theta-subsomption, clause bottom, recherche Progol | 60 min |
| 10 | [SL-10 - Capstone Neuro-Symbolique](SL-10-Capstone-NeuroSymbolic.ipynb) | Pipeline 6 etages : extraction LLM, oracle, KG, mining, inference avec provenance, QA | 90 min |

## Contenu detaille

### SL-1-LogicalLearning.ipynb

| Section | Contenu |
|---------|---------|
| Domaine restaurant | Attributs, exemples AIMA, hypotheses comme conjonctions |
| Consistance | Faux positifs/negatifs, verification d'hypotheses |
| Generalisation/Specialisation | Operations fondamentales, hierarchie de generalite |
| CBH | Algorithme Current-Best-Hypothesis (AIMA Fig 19.2) |
| Version Space | Candidate Elimination, G-set et S-set (AIMA Fig 19.3) |
| Prediction | Strategies unanime, conservateur, majority |
| Limites | Sensibilite au bruit, incapacite a representer les disjonctions |

### SL-2-KnowledgeBasedLearning.ipynb

| Section | Contenu |
|---------|---------|
| Cadre general | Contrainte d'entrainement, EBL vs RBL vs KBIL |
| EBL - Principe | Exemple de Zog, 4 etapes (expliquer, variabiliser, extraire, simplifier) |
| EBL - Arithmetique | Simplification d'expressions, arbre de preuve |
| EBL - Implementation | Classe ArithmeticEBL complete |
| EBL - Efficacite | Operationalite vs generalite, proliferation de regles |
| RBL - Introduction | Determinations, verification fonctionnelle, reduction d'espace (approfondi dans SL-3) |

### SL-3-RelevanceLearning.ipynb

| Section | Contenu |
|---------|---------|
| Determinations | Formalisme, monotonie, minimalite, `check_determination()` |
| Treillis des determinations | `build_determination_lattice()`, visualisation ASCII, up-set |
| MINIMAL-CONSISTENT-DET | Implementation detaillee, donnees moleculaires, cas d'echec disjonctif (restaurant) |
| Selection guidee | RBL vs sklearn (information mutuelle), comparaison |
| Analyse PAC | Reduction exponentielle, bornes d'echantillonnage |
| Web Semantique | Parallel RBL <-> OWL (FunctionalProperty, hasKey) |

### SL-4-InductiveLogicProgramming.ipynb

| Section | Contenu |
|---------|---------|
| Clauses Horn | Representation, `Literal`, `HornClause`, unification |
| FOIL | Algorithme top-down, gain FOIL, litteraux candidats |
| FOIL pas-a-pas | Trace detaillee sur le probleme ancestor |
| Resolution inverse | Operateurs V (absorption) et W (identification) |
| Knowledge Graphs | Regles AMIE, triples RDF, SPARQL CONSTRUCT |
| Popper (Learning From Failures) | Programme recursif optimal, ablation sans recursion, verification SWI-Prolog (kernel Linux/WSL) |
| Exercices | sibling, operateur W, regles sur KG |

### SL-5-NeuroSymbolic.ipynb

| Section | Contenu |
|---------|---------|
| T-norms / T-conorms | Operateurs logiques differentiables |
| Predicats neuronaux | Fonctions P(x) -> [0,1] apprises |
| LTN | Logique Tensorielle simplifiee |
| Raisonnement guide | Regles logiques guidant l'entrainement neuronal |
| DeepProbLog | Programmation logique probabiliste + predicats neuronaux |

### SL-6-KnowledgeGraphs-ILP.ipynb

| Section | Contenu |
|---------|---------|
| Knowledge Graphs | Construction avec rdflib |
| AMIE rule mining | Decouverte de regles de Horn sur KG |
| Completion | Inference de nouveaux triples |
| ASP avec clingo | Validation croisee de la completion, recursion (`ancestorOf`), contraintes d'integrite (pont serie Tweety) |

### SL-7-LLM-SymbolicLearning.ipynb

| Section | Contenu |
|---------|---------|
| LLMs et raisonnement | Forces et limites pour le raisonnement symbolique |
| Parseur de regles | Extraction de regles IF-THEN depuis du texte |
| Verification symbolique | Coherence formelle des sorties LLM |
| Boucle LLM-Symbolique | Generation + verification + feedback |

### SL-8-ActiveAutomataLearning.ipynb

| Section | Contenu |
|---------|---------|
| Apprentissage actif | Passif vs actif, le cadre MAT (Minimally Adequate Teacher) |
| DFA | Representation, execution, langage du mot « se termine par a » |
| Table d'observation | Prefixes S, suffixes E, fermeture et coherence |
| L* | Algorithme complet d'Angluin (1987), construction de l'hypothese |
| Contre-exemples | Traitement, raffinement, convergence vers le DFA minimal |
| Oracle echantillonne | Equivalence approchee par tirage, lien PAC |
| Theorie | Myhill-Nerode, minimalite, bornes sur le nombre de requetes |

### SL-9-InverseResolution.ipynb

| Section | Contenu |
|---------|---------|
| Clauses et couverture | `covers()` par backtracking, validation de la cible `grandfather/2` |
| LGG de Plotkin | Anti-unification, generalisation la moins generale, sur-specialisation |
| Theta-subsomption | `subsumes()` par skolemisation, le treillis de generalite |
| Clause bottom | Saturation bornee, entailment inverse, variabilisation |
| Recherche Progol | Sous-ensembles connectes du corps de bottom, score `f = p - L`, consistance dure |
| Cover-set | Boucle d'apprentissage de theorie complete |

### SL-10-Capstone-NeuroSymbolic.ipynb

| Section | Contenu |
|---------|---------|
| Corpus | Saga « Atelier Verne » : 13 enonces, 2 pieges factuels |
| Etage 1 - Extraction | LLM (Gemini 3.5 Flash) ou simulateur : texte -> triples candidats |
| Etage 2 - Oracle | Validation typee + contraintes fonctionnelles (cf SL-7) |
| Etage 3 - KG | Knowledge graph valide (cf SL-6) |
| Etage 4 - Mining | AMIE-lite : decouverte de regles avec confiance standard (cf SL-4/SL-6) |
| Etage 5 - Inference | Chainage avant avec provenance ; le derive peut violer l'oracle (lecon d'architecture) |
| Etage 6 - QA | Question 2 sauts : reponse KG (derivation citee) vs reponse LLM seule |

## Concepts cles

| Concept | Explication | Notebook |
|---------|-------------|----------|
| **Hypothese FOL** | Conjonction de contraintes sur les attributs | SL-1 |
| **Version Space** | Ensemble de toutes les hypotheses consistantes | SL-1 |
| **CBH** | Maintient une seule hypothese ajustee incrementalement | SL-1 |
| **EBL** | Extrait une regle generale d'un seul exemple par deduction | SL-2 |
| **RBL** | Identifie les attributs pertinents via les determinations | SL-2 |
| **Determination** | Relation fonctionnelle entre attributs | SL-2, SL-3 |
| **KBIL** | Apprentissage inductif guide par la connaissance | SL-2 |
| **Treillis des determinations** | Ensemble partiellement ordonne des sous-ensembles d'attributs | SL-3 |
| **MINIMAL-CONSISTENT-DET** | Trouve la determination minimale par taille croissante | SL-3 |
| **FOIL** | Apprentissage top-down de clauses Horn | SL-4 |
| **Resolution inverse** | Apprentissage bottom-up par operateurs V et W | SL-4 |
| **Clause Horn** | Regle logique avec au plus un litteral positif | SL-4 |
| **Unification** | Trouve une substitution rendant deux termes egaux | SL-4 |
| **ILP** | Apprentissage de programmes logiques a partir d'exemples | SL-4 |
| **Learning From Failures (Popper)** | ILP moderne : recherche de programme optimal par contraintes (clingo + Prolog) | SL-4 |
| **T-norm** | Generalisation differentiable de AND | SL-5 |
| **DeepProbLog** | Programmation logique probabiliste + predicats neuronaux | SL-5 |
| **Knowledge Graph** | Graphe oriente de triples (sujet, predicat, objet) | SL-6 |
| **AMIE** | Rule mining sur knowledge graphs incomplets | SL-6 |
| **LLM-Symbolique** | Boucle de retroaction LLM + verification formelle | SL-7 |
| **Apprentissage actif** | L'apprenant choisit ses questions au lieu de subir un echantillon | SL-8 |
| **MAT** | Minimally Adequate Teacher : oracle d'appartenance + equivalence | SL-8 |
| **Table d'observation** | Structure (S, E, T) fermee et coherente dont on lit un DFA | SL-8 |
| **Myhill-Nerode** | Classes d'equivalence de suffixes = etats du DFA minimal | SL-8 |
| **LGG** | Generalisation la moins generale de deux clauses (Plotkin) | SL-9 |
| **Theta-subsomption** | Ordre de generalite decidable entre clauses (∃θ : Cθ ⊆ D) | SL-9 |
| **Clause bottom** | Clause la plus specifique couvrant un exemple (entailment inverse) | SL-9 |
| **Progol** | Recherche de clause guidee par la clause bottom | SL-9 |
| **Provenance** | Trace de derivation attachee a chaque fait infere | SL-10 |
| **Pipeline neuro-symbolique** | LLM aux extremites, validation et inference symboliques au centre | SL-10 |

## prerequis

### Connaissances requises

- Python de base (fonctions, classes, tuples, dictionnaires)
- Logique propositionnelle (conjonctions, predicats)
- Notions d'apprentissage supervisé (classification binaire)

### Environnement Python

Aucune dependance externe pour SL-1, SL-2, SL-5, SL-8 et SL-9 (bibliotheque standard Python 3.10+ uniquement). SL-3 utilise `scikit-learn` et `numpy` pour la comparaison avec la selection statistique. SL-6 utilise `rdflib` et `clingo` (module Python officiel Potassco, installe silencieusement par le notebook — meme moteur ASP que le binaire utilise par la serie Tweety via `scripts/install_clingo.py`). SL-7 et SL-10 utilisent `python-dotenv` et `openai` pour les appels LLM optionnels via OpenRouter (Gemini 3.5 Flash) : copiez `.env.example` vers `.env` et renseignez `OPENROUTER_API_KEY` ; sans cle, un simulateur deterministe prend le relais et le notebook s'execute integralement.

SL-4 est en bibliotheque standard pour l'essentiel, mais sa section finale **Popper** requiert un environnement Unix : Popper utilise `signal.SIGALRM`, absent de Windows — le notebook s'execute donc sur un kernel Python **Linux** (kernel `python3-wsl` via WSL sous Windows, kernel natif sous Linux/macOS). Dependances de la section (installees silencieusement par le notebook) : SWI-Prolog >= 9.1.12 (`ppa:swi-prolog/stable`), `popper-ilp` epingle a **v4.4.0** (la 5.0 exige Python >= 3.14), `janus_swi`, `clingo`, `setuptools < 81`. Si Popper est indisponible, les cellules de la section l'indiquent et se sautent proprement — le reste du notebook tourne sur n'importe quel kernel Python.

## FAQ / Troubleshooting

### `rdflib` ne s'installe pas ou plantage a l'execution

SL-6 depend de `rdflib` pour manipuler les knowledge graphs RDF. Si l'installation echoue :

```bash
pip install rdflib
```

Si rdflib plante avec une erreur de compilateur C sur les parsers RDF/XML : installez `lxml` comme fallback `pip install lxml`, ou utilisez un environnement conda (`conda install -c conda-forge rdflib`).

### JPype / Java : erreurs courantes avec les bindings

Certains algorithmes de cette serie (surtout SL-5 pour les Logics Tensor Networks et SL-6 pour certains benchmarks AMIE) peuvent necessiter JPype pour interagir avec du code Java. Erreurs frequentes :

- **`java.lang.NoClassDefFoundError`** : `JAVA_HOME` n'est pas defini. Verifiez `echo $JAVA_HOME` (PowerShell: `$env:JAVA_HOME`) et ajoutez-le au PATH.
- **`UnsatisfiedLinkError`** : version Java incompatible. JPype necessite Java 8 ou 11. Evitez Java 17+ pour les anciennes versions de JPype.
- **`ModuleNotFoundError: jpype1`** : `pip install jpype1` ou `pip install jpype1-python` (version moderne).

### `scikit-learn` : version incompatible avec Python 3.10+

SL-3 utilise `scikit-learn` pour la comparaison information mutuelle vs determinations. Si vous avez une erreur lors de l'import :

```bash
pip install -U scikit-learn numpy
```

Les versions >= 1.3 de scikit-learn sont compatibles avec Python 3.10-3.12.

### `MemoryError` sur le treillis des determinations (SL-3)

Le treillis des determinations croit exponentiellement avec le nombre d'attributs. Si vous travaillez avec des datasets > 50 attributs :

- Limitez l'analyse aux 20-30 attributs les plus informatifs en premier
- Utilisez `check_determination()` pour filtrer avant de construire le treillis complet
- Le notebook inclut un parametre `max_attributes` pour controler cette taille

### Erreurs de compilation Lean dans les preuves references

Bien que cette serie soit en Python, certaines fonctions sont comparees avec des preuves Lean dans les notes de reference. Si `lake build` echoue :

- Verifiez la version de Lean 4 : `lake --version` (minimum 4.9.0)
- Si les imports Mathlib échouent : `lake exe cache get` pour rafraichir les dependances

### Jupyter / kernels Python

- Si le kernel Python n'apparait pas : `python -m ipykernel install --user --name python3 --display-name "Python 3"`
- Si Papermill ne tourne pas les notebooks : `pip install papermill`
- En cas de conflit de sortie entre cellules : redemarrez le kernel avant execution complete

## Ressources

### References

- Russell & Norvig, *Artificial Intelligence: A Modern Approach*, 3e/4e ed., Chapitre 19
- Tom Mitchell, *Machine Learning*, Chapitres 2 (Concept Learning) et 11 (EBL)
- [AIMA Python Code](https://github.com/aimacode/aima-python) - Implementations de reference

## Structure des fichiers

```
SymbolicLearning/
├── SL-1-LogicalLearning.ipynb              # CBH, Version Space
├── SL-2-KnowledgeBasedLearning.ipynb        # EBL, RBL
├── SL-3-RelevanceLearning.ipynb             # Treillis, MINIMAL-CONSISTENT-DET, RBL vs sklearn
├── SL-4-InductiveLogicProgramming.ipynb     # FOIL, resolution inverse, knowledge graphs
├── SL-5-NeuroSymbolic.ipynb                 # T-norms, LTN, DeepProbLog
├── SL-6-KnowledgeGraphs-ILP.ipynb           # rdflib, AMIE rule mining
├── SL-7-LLM-SymbolicLearning.ipynb          # LLMs + verification symbolique (Gemini 3.5 Flash optionnel)
├── SL-8-ActiveAutomataLearning.ipynb        # L* d'Angluin, apprentissage actif d'automates
├── SL-9-InverseResolution.ipynb             # LGG, theta-subsomption, clause bottom, Progol
├── SL-10-Capstone-NeuroSymbolic.ipynb       # Capstone : pipeline neuro-symbolique 6 etages
├── .env.example                             # Modele de configuration LLM (OpenRouter)
├── requirements.txt                         # Dependances optionnelles
├── reference/
│   └── AIMA_Ch19_Knowledge_in_Learning.md   # Notes de reference
└── README.md                                # Cette documentation
```

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|-------------|
| [Tweety](../Tweety/README.md) | Argumentation | Les logiques formelles de Tweety (propositionnelle, FOL) sont le fondement des hypotheses symboliques |
| [SemanticWeb](../SemanticWeb/README.md) | Representation de connaissances | RDFS/OWL formalisent les determinations et les hierarchies de generalite |
| [Planners](../Planners/README.md) | Planification | EBL compile les theories en regles operationnelles, similaire aux heuristiques de planification |
| [Lean](../Lean/README.md) | Preuves formelles | L'arbre de preuve EBL est analogue aux arbres de preuve Lean 4 |
| Lecture transversale | [La mer qui monte](../../../docs/grothendieckian-lens.md) | Grille de lecture grothendieckienne du depot : changement de representation, certification A/B/C |
