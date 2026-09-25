# Argument_Analysis - Analyse Argumentative avec Agents IA

<!-- CATALOG-STATUS
series: SymbolicAI-Argument_Analysis
pedagogical_count: 33
breakdown: Argument_Analysis=33
maturity: BETA=31, ALPHA=1, DRAFT=1
-->

[← SmartContracts](../SmartContracts/README.md) | [↑ SymbolicAI](../README.md) | [SymbolicLearning →](../SymbolicLearning/README.md)

Pipeline complet d'analyse argumentative combinant Semantic Kernel, TweetyProject et programmation logique pour l'identification et l'évaluation d'arguments dans des textes.

## Pourquoi cette série

Distinguer un argument valide d'un sophisme est un acte essentiel dans une société saturée de discours générés à la chaîne. Lorsque les LLMs produisent des textes plausibles à la demande, la frontière entre persuasion légitime et manipulation rhétorique se brouille : raisonnements circulaires, faux dilemmes, appels à l'autorité mal calibrés deviennent indétectables par simple lecture rapide. La vérification formelle, autrefois réservée aux logiciens, devient un service de masse : modération de plateformes, journalisme assisté, éducation critique, audit de contenus pédagogiques générés par IA.

Cette série pose une question concrète : peut-on construire un pipeline qui prend un texte argumentatif en entrée et qui en restitue une carte logique formelle, validée par un solveur SAT, avec détection systématique des sophismes connus ? La réponse passe par un assemblage soigné de trois compétences distinctes : un LLM pour extraire le tissu argumentatif informel (prémisses, conclusions, transitions), un solveur logique (TweetyProject, Java via JPype) pour vérifier la cohérence des formalisations propositionnelles obtenues, et une couche d'orchestration agentique (Semantic Kernel) qui transforme cette chaîne en pipeline reproductible. Le travail pédagogique consiste à maîtriser chacune de ces briques *et* leur composition : où s'arrête le LLM, où commence le vérificateur formel, comment une boucle informel/formel converge vers un verdict.

Le contexte de recherche actuel rend cette compétence particulièrement pertinente. Les frameworks de raisonnement structuré (ASPIC+, ABA, DeLP) sont implémentés en JVM et accessibles via les mêmes ponts JPype que ceux utilisés ici. Les LLMs de 2025-2026 sont assez fiables pour la phase d'extraction informelle mais restent faibles sur la vérification formelle, ce qui motive précisément le pattern hybride documenté dans la série. Les ponts vers [Tweety](../Tweety/) (sémantiques de Dung, révision de croyances AGM, préférences de Tweety-9) et [Lean](../Lean/) (preuves formelles, tactiques) permettent d'aller plus loin pour qui veut dépasser la simple vérification SAT.

**À qui s'adresse cette série** : enseignants en pensée critique, équipes éditoriales construisant des outils de fact-checking, étudiants en philosophie computationnelle ou en linguistique formelle, et ingénieurs explorant les architectures hybrides LLM + solveur. La maîtrise préalable supposée est modérée : Python intermediate, intuition logique propositionnelle, familiarité minimale avec les LLMs et l'OpenAI API. Les notebooks (~4-5h total) s'enchaînent dans l'ordre des numéros (00 → 08), avec l'`Executor` (`08b`) comme point d'entrée pour une exécution batch reproductible (Papermill / MCP).

## Domaines d'application

L'analyse argumentative outillée s'inscrit dans plusieurs cas concrets où la distinction "argument valide / sophisme" doit être rendue automatique ou semi-automatique :

- **Modération de discussions en ligne** : détection des sophismes récurrents (homme de paille, faux dilemmes, glissement, ad hominem) dans des fils de commentaires longs, avec un rapport agrégé par utilisateur ou par fil. Le pattern LLM-extracteur + vérificateur formel est calibré précisément pour cet usage.
- **Fact-checking et journalisme assisté** : décomposition d'un éditorial ou d'un discours politique en chaîne de prémisses et conclusions, marquage des transitions logiquement faibles, identification des affirmations factuelles à vérifier externellement. La phase "formalisation" crée un livrable inspectable, contrairement aux jugements opaques d'un LLM seul.
- **Éducation à la pensée critique** : production d'exercices d'analyse à partir de textes réels (discours, essais, posts), avec correction automatisée partielle. L'enseignant valide la décomposition, l'élève apprend à justifier chaque étape.
- **Audit de contenus IA** : vérification de la cohérence interne des réponses LLM longues sur sujets sensibles (médical, juridique, financier). Un LLM peut produire un raisonnement plausible mais incohérent ; le solveur formel détecte les contradictions internes.
- **Recherche en argumentation structurée** : terrain expérimental pour les frameworks Dung, ASPIC+, ABA, accessibles via les ponts Tweety. La série sert de support à des explorations académiques (mémoires, thèses) sur les sémantiques d'acceptabilité, la révision de croyances AGM, ou les préférences entre arguments.

## Objectifs d'apprentissage

À l'issue de cette série, vous serez capable de :

1. **Extraire le tissu argumentatif** d'un texte en identifiant prémisses, conclusions et transitions à l'aide d'un agent LLM (Semantic Kernel)
2. **Formaliser des arguments** en logique propositionnelle et vérifier leur cohérence avec un solveur SAT (TweetyProject)
3. **Détecter les sophismes** courants (homme de paille, faux dilemme, ad hominem, appel à l'autorité) de manière systématique
4. **Orchestrer un pipeline multi-agents** combinant extraction informelle, formalisation logique et validation formelle
5. **Comparer les approches** LLM-only vs hybride (LLM + solveur formel) et comprendre les limites de chaque couche

## Quel parcours choisir ?

| Profil | Parcours recommandé | Notebooks |
|--------|-------------------|-----------|
| **Découvreur de l'analyse argumentative** | Pipeline complet en ordre | 00 → 02 → 05 → 07 (~3h) |
| **Enseignant en pensée critique** | Extraction + détection sophismes | 00 → 02 → 08c (~1h30) |
| **Ingénieur ML/LLM** | Architecture multi-agents | 00 → 07 → 08b (~1h30) |
| **Chercheur en logique formelle** | Formalisation + vérification SAT | 00 → 05 (~1h) |

---

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Kernel | Python 3 |
| Durée estimée | ~4-5h |
| API requise | OpenAI |

## Notebooks

| # | Notebook | Contenu | Rôle |
|---|----------|---------|------|
| 00 | [Argumentation-00-Setup-Tweety-Python](Argumentation-00-Setup-Tweety-Python.ipynb) | Configuration env : JPype + JDK 17 + 76 jars Tweety, démarrage JVM fail-loud + smoke test | Setup |
| 01 | [Argumentation-01-Toulmin-Model-Python](Argumentation-01-Toulmin-Model-Python.ipynb) | Modèle structurel informel de Toulmin (1958) : 6 composants (claim/data/warrant/backing/qualifier/rebuttal), audit de complétude, et pont computationnel vers Dung (rebuttals → attaques, le grounded tranche le débat) — pur stdlib Python | Argumentation informelle structurée |
| 01b | [Argumentation-01b-Schemes-Walton-Python](Argumentation-01b-Schemes-Walton-Python.ipynb) | Les 10 schémas d'argumentation de Walton (table verbatim du moteur étudiant EPITA, distillation Triple Distillation) et leur classifieur lexical déterministe : paire de mots-clés accentués exigée, ordre canonique qui départage (`modus_ponens` en dernier, « donc » armant aussi `cause_effect`), questions critiques canoniques, échec bruyant (`None` honnête, jamais d'étiquette fabriquée) — pur stdlib | Argumentation informelle schématique |
| 02 | [Argumentation-02-Fallacies-Detection-Python](Argumentation-02-Fallacies-Detection-Python.ipynb) | Détection de sophismes par taxonomie (CSV 1406 nœuds) | Détection d'arguments |
| 02b | [Argumentation-02b-Argumentum-Cards-Python](Argumentation-02b-Argumentum-Cards-Python.ipynb) | Deck imprimable du jeu Argumentum (176 cartes depuis la taxonomie) | Production |
| 03 | [Argumentation-03-Dung-AF-Semantics-Python](Argumentation-03-Dung-AF-Semantics-Python.ipynb) | Sémantiques grounded / preferred / stable reconstruites de zéro en pur Python (cas canonique où les trois divergent) | Fondation argumentation abstraite |
| 03b | [Argumentation-03b-Value-Based-AF-Python](Argumentation-03b-Value-Based-AF-Python.ipynb) | Argumentation basée sur les valeurs (Bench-Capon 2003) : chaque argument promeut une valeur, chaque audience ordonne les valeurs ; une attaque ne défait sa cible que si la valeur de l'attaquant est préférée — un même graphe produit des conclusions différentes selon l'audience — pur stdlib Python | Argumentation + préférences |
| 03c | [Argumentation-03c-Ranking-Semantics-Python](Argumentation-03c-Ranking-Semantics-Python.ipynb) | Sémantiques de classement (h-Categoriser, fardeau) en pur Python : force numérique départageant des arguments de même statut Dung | Argumentation graduée |
| 04 | [Argumentation-04-Dialogues-Protocolises-Python](Argumentation-04-Dialogues-Protocolises-Python.ipynb) | Protocoles de dialogue Walton–Krabbe (inquiry/persuasion) comme machines à états sur 9 actes de parole : tables de transitions, terminaison par condition testable (compréhension mutuelle, capitulation, boucle), validation sur fixture partagée (9 transitions + 7 historiques, `data/dialogue_protocols_examples.json`), jonction classifieur Walton (01b) → `FormalArgument.scheme` (04b), propriétés mesurées du moteur dont une condition de terminaison inatteignable (`_term_double_retract`) — pur stdlib Python | Protocoles d'échange / pragmatique |
| 04b | [Argumentation-04b-Knowledge-Base-Python](Argumentation-04b-Knowledge-Base-Python.ipynb) | La mémoire d'un débat (distillation Triple Distillation du moteur étudiant EPITA) : population transitive (`add_argument` porte prémisses et conclusion), support/attaque par convention lexicale `¬`, cohérence = conflit ouvert P/`¬P`, `entails` = appartenance documentée (pas d'inférence — non-explosion mesurée, `¬¬P` distinct de `P`, écrasement par contenu) — pur stdlib Python | Mémoire de débat |
| 05 | [Argumentation-05-Formal-Verification-Python](Argumentation-05-Formal-Verification-Python.ipynb) | Logique formelle réelle (PL + FOL + Modal + Dung via Tweety) | Formalisation |
| 05b | [Argumentation-05b-Multi-Backend-Routing-Python](Argumentation-05b-Multi-Backend-Routing-Python.ipynb) | Routage multi-backend « décider ou échouer bruyamment » : PL/Modal/Dung/FOL décidés par Tweety embarqué + sentinelle de contrat de livraison gardant les prouveurs externes (EProver/Mace4) — doctrine anti-théâtre / fail-loud | Raisonnement robuste |
| 05c | [Argumentation-05c-Formal-Richness-Matrix-Python](Argumentation-05c-Formal-Richness-Matrix-Python.ipynb) | Matrice de richesse formelle (FP-5) : classifier ce qu'un solveur *décide réellement* (principe *wiring* ≠ *output*), 4 classes de verdict (substantive / honest-absent / unavailable / théâtre), sentinelle anti-théâtre `fabricated_true` + diagnostic laggards — pur stdlib | Évaluation honnête / anti-théâtre |
| 06 | [Argumentation-06-JTMS-Python](Argumentation-06-JTMS-Python.ipynb) | Truth Maintenance System déterministe (Doyle 1979) : étiquetage IN/OUT, cascade de rétractation, détection d'odd loops — pur stdlib Python | Raisonnement non-monotone |
| 07 | [Argumentation-07-Orchestration-Python](Argumentation-07-Orchestration-Python.ipynb) | Orchestration : mini-DAG déterministe vs conversationnel (state-driven) | Coordination |
| 07b | [Argumentation-07b-Communication-Channels-Python](Argumentation-07b-Communication-Channels-Python.ipynb) | Bus de communication multi-agents (distillation Triple Distillation du tronc EPITA) : format message à priorité inversée, contrat de canal fail-loud (#2161), routage sans routes mortes (#1571), corrélation requête-réponse — pur stdlib Python, déterministe | Communication multi-agents |
| 07c | [Argumentation-07c-Orchestration-Modes-Python](Argumentation-07c-Orchestration-Modes-Python.ipynb) | Comparer 7 modes d'orchestration par le budget (distillation Triple Distillation de l'instrument EPITA #1735) : 3 registres d'arrêt (filet du harnais / déclaration du mode / réalité des phases), asymétrie d'axes largeur-délégation-dialogue, budget calibré dérivé de la mesure — mesures committées, pur stdlib | Arbitrage d'architectures multi-agents |
| 08 | [Argumentation-08-Capstone-Python](Argumentation-08-Capstone-Python.ipynb) | Capstone : baseline 0-shot vs pipeline intégral, verdicts convergents + value-gates VG-1..VG-4 | Intégration |
| 08b | [Argumentation-08b-Executor-Python](Argumentation-08b-Executor-Python.ipynb) | Orchestrateur principal | Exécution |
| 08c | [Argumentation-08c-UI-Configuration-Python](Argumentation-08c-UI-Configuration-Python.ipynb) | Interface utilisateur widgets | Interaction |
| 08d | [Argumentation-08d-Restitution-3-Actes-Python](Argumentation-08d-Restitution-3-Actes-Python.ipynb) | Restitution honnête en 3 actes : scaffold déterministe pur stdlib (evidence réel-en-état, bande de verdict *gated*, gate de lisibilité §4, renderer *fail-loud*) + narration LLM **réelle** (SDK OpenAI, clé via `GenAI/.env`) *gated* — prompts conduits, callable injectable, fail-loud sans clé | Restitution / honnêteté |
| 08e | [Argumentation-08e-Argument-Profile-Python](Argumentation-08e-Argument-Profile-Python.ipynb) | Vue agrégée par argument (`ArgumentProfile`) : réunit les 5 dimensions (sophismes, qualité, contre-arguments, JTMS, formel) en une fiche exploitable, et trie un débat par force (arguments faibles / fallacieux). Démontre l'**indépendance des dimensions** (valide formellement ≠ non fallacieux). Auto-contenu, déterministe, sans LLM | Vue agrégée / multidimensionnelle |
| 0* | [Agentic-0-init_agent](Argument_Analysis_Agentic-0-init_agent.ipynb) | *(legacy)* Configuration LLM/OpenAI (semantic_kernel) | Setup |
| 1* | [Agentic-1-informal_agent](Argument_Analysis_Agentic-1-informal_agent.ipynb) | *(legacy)* Agent analyse informelle | Détection d'arguments |
| 2* | [Agentic-2-pl_agent](Argument_Analysis_Agentic-2-pl_agent.ipynb) | *(legacy)* Agent logique propositionnelle | Formalisation |
| 3* | [Agentic-3-orchestration_agent](Argument_Analysis_Agentic-3-orchestration_agent.ipynb) | *(legacy)* Orchestration multi-agents (semantic_kernel) | Coordination |
| Dated | [Dated_Graphs](Argument_Analysis_Dated_Graphs.ipynb) | Instrument $G_t^{arg} \to G_{t+1}^{arg}$ (Epic #13303, issue #13310) : corpus daté → graphe AIF conforme (critère d'inclusion C1–C3 écrit, exclusions publiées) → projection Dung ; deux mesures d'écart de familles différentes (Jaccard structurelle nœuds/attaques + Jaccard sémantique sur extensions grounded), **contrôle négatif** (plancher de bruit par split de la même période) publié à côté de tout écart, **contrôle positif** à magnitude attendue écrite avant mesure (attaque de racine : sortie directe + réhabilitation paradoxale de la victime + cascade) — pur Python + rdflib, validation synthétique uniquement ; **hypothèse monotone** posée, vérifiée par inclusion et violée délibérément (retrait d'un déchu vs d'un accepté : ce que voient les deux mesures) | Argumentation temporelle / mesure |
| Obs | [Observatoire-1-Initiation](Argument_Analysis_Observatoire-1-Initiation.ipynb) | Cas 1 de l'Observatoire (Epic #13303, livré #16431) : Bumble « Opening Moves » (mars–avril 2024), DiD imparfait sur avis datés — instrument Dated_Graphs **rebranché, pas réécrit** (module `_dated_graphs_mod.py`), corpus Arctic Shift 4 bras × 2 fenêtres stratifiés mensuellement, extraction LLM Ollama (qwen2.5:7b-instruct-q4_K_M, température 0, échantillon complet), agrégats public-safe, plancher de bruit split-half chronologique — verdict sur quatre observations conjointes, plafond de preuve déclaré | Étude de cas / mesure empirique |
| Recol | [Recollement_Lectures](Argument_Analysis_Recollement_Lectures.ipynb) | Lectures croisées de la série (récollement) | Consolidation |
| Recol6 | [Recollement_Strate6](Argument_Analysis_Recollement_Strate6.ipynb) | Strate 6 du récollement | Consolidation |
| Ontology_AIF | [Ontology_AIF](Argument_Analysis_Ontology_AIF.ipynb) | Socle ontologique Argumentum (`argumentum_fallacies.owl`, 4,7 MB OWL2/XML) : parseur regex tolérant (37 axiom `ExactCardinality` mal formés bloquent rdflib), inventaire 10 976 NamedIndividual + 1 305 ClassAssertion (skos:Concept dominant) + 4 183 ObjectPropertyAssertion, recherche des schemes Walton dans les labels, sous-graphe autour de l'Equivoque — lien entre la série et l'ontologie upstream Argumentum | Socle ontologique |
| CrossLinks | [Ontology_CrossLinks](Argument_Analysis_Ontology_CrossLinks.ipynb) | Complément CSV canonique Argumentum (`Cards/Fallacies/Argumentum Fallacies - Taxonomy.csv`, 1 408 lignes × 102 colonnes) : 8 colonnes `crossLink_*` (PredatesOn, Denounces, Leverages, Allows, Opposes, Inverts, Mirrors, IsRelatedTo — quasi-vides, 22 relations totales, 1,5% des sophismes ont ≥1 crossLink) + 70 mappings AIF (skos:broadMatch/closeMatch/narrowMatch, absents OWL) + 60 schemes Walton uniques (top : OppositeConsequences_Conflict 5 occurrences). Compare le gap OWL (10 976 NI) vs CSV (1 408 sophismes × 8 langues = 11 264 descriptions) — finding méthodologique : l'effort de curation upstream est porté sur la **taxonomie** (8 langues, 8 familles, 9 niveaux), pas sur les **liens transverses** | CSV canonique |
| Ontology_Virtues | [Ontology_Virtues](Argument_Analysis_Ontology_Virtues.ipynb) | Pôle **positif** de l'axe argumentatif (`argumentum_virtues.owl`, 863 KB OWL2/XML) : thésaurus SKOS des **vertus** argumentatives, miroir des sophismes (`aif:goodTenorOf` vs `badTenorOf`). Pont regex→rdflib chargeant 2 639 triplets SKOS (rdflib et owlready2 échouent sur l'OWL/XML fonctionnel), 224 `skos:Concept` bilingues (prefLabel fr 223 / en 223), racine `validArgument`, 14 schemes de Walton rattachés — contraste ABox (sophismes = NamedIndividual + ObjectPropertyAssertion) vs thésaurus d'annotations SKOS (vertus) | Pôle vertus / SKOS |
| I2 | [I2_Contre_arguments_ASPIC](groupe-I2-contre-arguments-aspic/I2_Contre_arguments_ASPIC.ipynb) | Travail de groupe : contre-arguments ASPIC (sous-répertoire `groupe-I2-contre-arguments-aspic/`, production autonome) | Travail de groupe |

## Ce que chaque notebook apporte

| Notebook | Compétence clé | Temps |
|----------|----------------|-------|
| **00** | Configurer l'environnement Python + Java, charger les clés API, vérifier la connexion Tweety/JVM | 30 min |
| **02** | Charger la taxonomie des sophismes (CSV 1406 nœuds, 7 familles), descendre d'un niveau (depth=2) et construire un détecteur déterministe par mots-clés sur un texte synthétique | 30 min |
| **1-informal_agent** *(legacy)* | Construire un agent LLM qui identifie et annote les arguments dans un texte naturel | 60 min |
| **05** | Vérifier des arguments en logique propositionnelle, du premier ordre et modale avec le solveur réel Tweety (JVM/JPype), apéru Dung — mode fail-loud, jamais simulé | 45 min |
| **2-pl_agent** *(legacy)* | Convertir les arguments informels en formules propositionnelles et les vérifier via SAT | 60 min |
| **07** | Composer les agents précédents en pipeline coordonné avec rapport de sortie structuré | 50 min |
| **06** | Construire un moteur de croyances non-monotones (étiquetage IN/OUT, cascade de rétractation, détection d'odd loops) en pur stdlib Python, sans LLM ni solveur externe | 40 min |
| **03** | Reconstruire les sémantiques grounded, preferred et stable de l'argumentation abstraite de Dung de zéro en pur Python (sans JVM) sur un cas où les trois divergent | 35 min |
| **03b** | Étendre Dung par des valeurs et une audience (Bench-Capon 2003) : une attaque ne réussit que si la valeur de l'attaquant est préférée ; montrer qu'un même graphe en cycle produit trois conclusions distinctes selon l'audience — pur stdlib Python | 35 min |
| **01** | Déployer un argument en ses 6 composants Toulmin (claim/data/warrant/backing/qualifier/rebuttal), auditer sa complétude, et traduire un débat en cadre de Dung (rebuttals → attaques) pour voir quel claim survit — pur stdlib Python | 30 min |
| **01b** | Reconnaître la forme stéréotypée d'un argument (autorité, analogie, cause à effet...) par un matcher lexical déterministe, prédire son départage par l'ordre canonique, et auditer un texte classé avec les questions critiques de Walton — pur stdlib Python | 30 min |
| **04** | Lire deux protocoles de dialogue Walton–Krabbe comme des machines à états : neuf actes de parole, tables de transitions inquiry vs persuasion, terminaison par condition testable (compréhension mutuelle, capitulation, boucle), et une condition de terminaison inatteignable découverte dans le source — pur stdlib Python | 35 min |
| **04b** | Construire et interroger la mémoire d'un débat : population transitive (un argument porte ses prémisses et sa conclusion), requêtes support/attaque par convention lexicale `¬`, détection du conflit ouvert, et les limites mesurées (pas d'inférence depuis une contradiction, `¬¬P` distinct de `P`, écrasement des propositions homonymes) — pur stdlib Python | 30 min |
| **03c** | Calculer la *force* numérique d'un argument (h-Categoriser par point fixe, fardeau par comparaison lexicographique) et départager des arguments que Dung déclare indistinctement rejetés — pur stdlib Python | 35 min |
| **07c** | Reconstruire les tableaux sous-budget/calibré d'un comparatif de 7 modes d'orchestration, nommer les 3 registres d'arrêt, et dériver un budget calibré — avec la limite mesurée de la projection linéaire (1081 s naïfs vs 600 s réels) | 30 min |
| **Dated_Graphs** | Construire l'instrument de comparaison temporelle des graphes d'argumentation : critère d'inclusion écrit d'un énoncé, graphe AIF conforme sérialisé en RDF, projection Dung, deux mesures d'écart de familles différentes, plancher de bruit (contrôle négatif) publié avec chaque mesure, et contrôle positif dont la magnitude attendue est dérivée à la main avant l'exécution | 45 min |
| **Observatoire-1-Initiation** | Conduire un cas empirique pré-inscrit de bout en bout : reprise de l'instrument Dated_Graphs sans réécriture (module dédié, garde anti-repli), corpus daté stratifié mensuellement, extraction LLM épinglée (modèle, température 0, schéma JSON), mesure via l'instrument avec plancher de bruit split-half chronologique, et plafond de preuve déclaré (DiD imparfait) | — |
| **08d** | Séparer la *lisibilité* (confiée au LLM) de l'*honnêteté* (gardée par un scaffold déterministe) : extraction d'evidence, bande de verdict *gated* sur la couverture, gate de tissage anti-énumération (§4), renderer qui *nomme* les actes manquants, et narration LLM injectable *fail-loud* | 45 min |
| **07b** | Construire un bus de communication multi-agents : messages à priorité inversée, filtres fail-loud, routage sans routes mortes, corrélation requête-réponse — pur stdlib Python | 30 min |
| **08e** | Construire la fiche agrégée d'un argument réunissant les 5 dimensions d'analyse (sophismes, qualité, contre-arguments, JTMS, formel), puis trier un débat entier par force — démontre l'indépendance des dimensions | 35 min |
| **Ontology_AIF** | Charger l'ontologie Argumentum (OWL2/XML, 4,7 MB) via un parseur regex tolérant (rdflib échoue sur 37 axiom `ExactCardinality` mal formés), inventorier les 10 976 NamedIndividual + 4 183 ObjectPropertyAssertion, retrouver les schemes Walton dans les labels multilingues (Sign, Rule), et construire le sous-graphe du sophisme Equivoque (`semanticAmbiguity` + variantes) | 35 min |
| **Ontology_CrossLinks** | Compléter la vue OWL par le CSV canonique Argumentum (1 408 lignes × 102 colonnes, 8 langues × 8 familles × 9 niveaux) : quantifier les 8 colonnes `crossLink_*` (PredatesOn 9, Denounces 1, Leverages 4, Allows 1, Opposes 2, Inverts 1, Mirrors 2, IsRelatedTo 2 — total 22, soit 1,5% de couverture par sophisme) et les 70 mappings AIF/Walton (`skos:broadMatch` 57, `skos:closeMatch` 10, `skos:narrowMatch` 3) ; démontrer empiriquement le gap OWL↔CSV (×7,8 en NamedIndividual par label multilingue) et la **sparsity structurelle** des relations transverses vs la richesse de l'arbre taxonomique | 30 min |
| **Ontology_Virtues** | Charger le pôle **positif** de la taxonomie Argumentum (`argumentum_virtues.owl`, thésaurus SKOS) via un pont regex→rdflib (rdflib et owlready2 échouent sur l'OWL/XML fonctionnel) : construire 2 639 triplets SKOS sur 224 concepts, inventorier les prédicats SKOS (prefLabel / definition / broader / topConceptOf), contraster le paradigme ABox des sophismes (NamedIndividual + ObjectPropertyAssertion) avec le thésaurus d'annotations des vertus, extraire les libellés bilingues FR/EN et relier chaque vertu à ses schemes de Walton via `aif:goodTenorOf` | 35 min |
| **08c** | Créer une interface interactive (ipywidgets) pour piloter le pipeline en mode exploratoire | 30 min |
| **08b** | Exécuter le pipeline complet en mode batch (Papermill/MCP) avec configuration .env | 20 min |

## Architecture

```mermaid
flowchart TD
    EX(["<b>Executor</b><br/>point d'entrée batch<br/>Papermill / MCP"])
    IA["<b>Informal Agent</b><br/>extraction du tissu argumentatif<br/>+ détection de sophismes — couche LLM"]
    PL["<b>PL Agent</b><br/>formalisation en<br/>logique propositionnelle"]
    OR["<b>Orchestration Agent</b><br/>coordination déterministe<br/>ou conversationnelle"]
    TW[("<b>Tweety</b><br/>solveur formel unique<br/>Java / JPype")]
    EX --> IA
    EX --> PL
    EX --> OR
    IA --> TW
    PL --> TW
    OR --> TW
```

L'`Executor` est le seul point d'entrée (exécution batch via Papermill/MCP) : il déclenche la chaîne et agrège le rapport final. Le travail se *fan-out* vers trois agents spécialisés — **Informal** (extraction du tissu argumentatif et détection de sophismes, couche LLM), **PL** (formalisation en logique propositionnelle) et **Orchestration** (coordination déterministe ou conversationnelle) — puis *converge* vers **Tweety**, le solveur formel unique (Java via JPype).

Cette topologie en entonnoir n'est pas accidentelle : la cohérence logique est la seule propriété qu'aucun agent ne peut auto-certifier, elle doit donc être déléguée à un vérificateur externe et partagé. Le LLM se charge de tout ce qui est flou et contextuel (lire un texte, repérer un sophisme) ; le solveur se charge de tout ce qui est tranchant et décisif (une formule est-elle satisfaisable ? un argument est-il défendable ?). La frontière informel/formel passe exactement au point de convergence.

## Pipeline d'analyse

1. **Extraction** - Identification des arguments dans le texte
2. **Formalisation** - Conversion en logique propositionnelle
3. **Validation** - Vérification cohérence via Tweety
4. **Évaluation** - Détection de sophismes et faiblesses
5. **Rapport** - Génération conclusion structurée

```mermaid
flowchart LR
    TXT(["Texte<br/>argumentatif"]) --> E1["1 · Extraction<br/>prémisses, conclusions"]
    E1 --> E2["2 · Formalisation<br/>logique propositionnelle"]
    E2 --> E3["3 · Validation<br/>cohérence (SAT)"]
    E3 --> E4["4 · Évaluation<br/>sophismes, faiblesses"]
    E4 --> RAP["5 · Rapport<br/>synthèse groundée"]
    E3 -. "requêtes SAT" .-> TW[("Tweety<br/>Java / JPype")]
```

## Exemple de trace du pipeline

Pour rendre ce déroulement concret, voici ce que produit le pipeline sur le **terrain commun** du capstone ([Argumentation-08-Capstone-Python](Argumentation-08-Capstone-Python.ipynb)) : un texte argumentatif neutre — un comité abstrait, sans entité réelle — délibérément chargé de cinq sophismes détectables (appel à l'autorité, attaque *ad hominem*, généralisation hâtive, appel à la peur, appel à la conformité). Il sert de terrain commun à la baseline et au pipeline complet.

1. **Extraction informelle** — l'agent parcourt le texte et isole le tissu argumentatif : prémisses, conclusions, transitions rhétoriques. Chaque passage suspect est confronté à la taxonomie des sophismes (1406 nœuds, 7 familles).
2. **Détection** — les sophismes présents sont étiquetés et rattachés à leur famille (Obstruction pour *ad hominem*, Erreur de raisonnement pour le faux dilemme, etc.), avec le déclencheur textuel qui les a signalés.
3. **Formalisation** — les arguments retenus sont traduits en formules de logique propositionnelle et ajoutés au *belief set*.
4. **Validation formelle** — Tweety, via le pont JPype, interroge ce belief set (une dizaine de requêtes SAT) pour confirmer la cohérence interne : pas de contradiction masquée, pas de conclusion tirée sans prémisse. Mode *fail-loud* : si la JVM manque, le pipeline échoue bruyamment plutôt que de simuler un verdict.
5. **Synthèse groundée** — le rapport final cite explicitement chaque artefact qu'il invoque (`[artifact:champ:id]`), ce que les *value-gates* vérifient déterministiquement : VG-1 (densité de citations), VG-2 (état substantiel peuplé), VG-3 (non-boilerplate), VG-4 (vrai paragraphe de synthèse citant ≥ 2 champs distincts).

Le verdict attendu sur l'`Executor` (mode batch) est `COMPLETE_VALIDATED` : 1 argument identifié, 4 sophismes étiquetés, 1 belief set formel, ~10 requêtes au solveur, et les quatre value-gates au vert. La même exécution en mode baseline (LLM seul, 0-shot) sert de contre-point : sans la couche formelle, la cohérence interne n'est garantie par rien, et c'est précisément cet écart que la série cherche à mesurer.

## Concepts clés

Le pipeline mobilise un vocabulaire issu de trois traditions — la rhétorique classique, la logique formelle et l'argumentation computationnelle. Le tableau ci-dessous reprend les notions effectivement manipulées dans les notebooks, avec un pointeur vers celui qui les met en œuvre.

| Concept | Description | Notebook |
|---------|-------------|----------|
| **Argument** | Suite de *prémisses* soutenant une *conclusion* ; c'est le tissu que le pipeline extrait d'un texte naturel. | 02 |
| **Prémisse / Conclusion** | Brique atomique de l'argument : la prémisse est l'énoncé admis, la conclusion celle que l'on dérive. Leur identification est la sortie de l'agent informel. | 02 |
| **Sophisme** | Raisonnement fallacieux mais plausible. La série s'appuie sur une taxonomie de 1406 nœuds en 7 familles (Obstruction, Erreur de raisonnement, …) organisée en arbre jusqu'à 10 niveaux. | 02 |
| **Formalisation** | Traduction d'un argument naturel en formule logique inspectable. C'est le point de bascule où le texte cesse d'être du langage naturel pour devenir un objet qu'un solveur peut interroger. | 05 |
| **Logique propositionnelle (PL)** | Logique des connecteurs (∧, ∨, →, ¬) sans quantificateurs ; vérifiée via un modus ponens dans Tweety. | 05 §3 |
| **Logique du premier ordre (FOL)** | PL étendue des quantificateurs (∀, ∃) et prédicats. Exige une *signature* déclarée (constantes, prédicats) avant toute requête. | 05 §4 |
| **Logique modale** | Logique du *possible* (◇) et du *nécessaire* (□), utile pour les arguments portant sur la contingence ou l'obligation. | 05 §5 |
| **Argumentation de Dung** | Cadre abstrait où les arguments s'attaquent mutuellement ; la sémantique *grounded* calcule l'ensemble des arguments défendables. Les sémantiques *preferred* et *stable* étendent ce verdict sous différentes attitudes (crédule, auto-suffisante). | 03, 05 §6 |
| **Sémantique de classement** | Approche *graduée* : au lieu d'un verdict tout-ou-rien, chaque argument reçoit une *force* numérique (h-Categoriser, fardeau) qui induit un ordre — départageant des arguments de même statut Dung. | 03c |
| **Belief set** | Ensemble de formules formalisant l'état de croyance déduit du texte ; c'est ce que le solveur manipule et interroge. | 05 |
| **SAT** | Problème de satisfaisabilité : existe-t-il une valuation rendant un ensemble de formules cohérent ? Cœur de la validation Tweety. | 05 |
| **Fail-loud** | Principe de conception : le pipeline échoue bruyamment plutôt que de *simuler* un verdict (jamais de sortie fictive si la JVM ou le solveur manque). | 05 |
| **Value-gates (VG-1..VG-4)** | Quatre gardes déterministes qui notent si la synthèse finale est *groundée* (elle cite ses artefacts via `[artifact:champ:id]`) ou *boilerplate* (template vide). | 08 |
| **Pipeline hybride LLM + solveur** | Architecture où le LLM gère l'extraction informelle (floue, contextuelle) et le solveur formel garantit la cohérence ; aucune des deux couches ne suffit seule. | 07 |
| **Ontologie OWL2 (Argumentum)** | Représentation formelle de la taxonomie Argumentum (10 976 `NamedIndividual`, 4 183 `ObjectPropertyAssertion`). En raison de 37 axiom `ExactCardinality` structurellement invalides dans l'export upstream, le parseur regex tolérant est obligatoire — `rdflib` échoue, `owlready2` charge en silence mais n'expose pas les concepts via API. | Ontology_AIF |
| **SKOS (Simple Knowledge Organization System)** | Famille de propriétés W3C (`skos:broader`, `skos:narrower`, `skos:inScheme`, `skos:Concept`) qui dominent l'ontologie Argumentum (1 304/1 305 `ClassAssertion`). La navigation dans la taxonomie s'appuie sur ces relations plutôt que sur AIF. | Ontology_AIF |
| **Schemes d'argumentation (Walton)** | Patterns d'inférence (Position to Know, Sign, Rule, Cause to Effect) servant de taxonomie pour présomption : la reconnaissance d'un scheme active les *critiques* associées. Argumentum expose `Sign` (11 labels) et `Rule` (2 labels) ; `Position to Know` et `Cause to Effect` sont absents du label parsing. | Ontology_AIF, 02 |
| **CrossLinks `crossLink_*` (Argumentum CSV)** | Huit relations transverses (PredatesOn, Denounces, Leverages, Allows, Opposes, Inverts, Mirrors, IsRelatedTo) qui créeraient un **graphe** au-dessus de l'arbre taxonomique. Sur 1 408 sophismes, seulement 22 relations sont renseignées (1,5% de couverture), avec une forte dominance de `PredatesOn` (9/22, 41%). Ces colonnes sont **uniquement dans le CSV upstream** — absentes de l'OWL `argumentum_fallacies.owl`. **Finding méthodologique** : la taxonomie Argumentum est **structurellement plate** en transverses ; l'effort de curation upstream est porté sur la **profondeur taxonomique** (9 niveaux, 8 langues), pas sur les **liens inter-noeuds**. | Ontology_CrossLinks |
| **Mappings AIF/Walton (Argumentum CSV)** | Trois colonnes `AIF_skosDirectRef` / `AIF_skosExceptionRef` / `AIF_skosMappingType` (colonnes 70-72 du CSV) relient chaque sophisme aux schemes Walton via les types SKOS `broadMatch` (57, majorité), `closeMatch` (10) et `narrowMatch` (3). 70 mappings couvrent 5,0% des sophismes (1 408) ; 60 schemes Walton uniques sont référencés, top : `OppositeConsequences_Conflict` (5 occurrences). **Comme `crossLink_*`, ces mappings sont absents de l'OWL** — présents uniquement dans le CSV canonique, ce qui en fait la **source de vérité** pour l'alignement sophisme→scheme. | Ontology_CrossLinks, 02 |
| **Gap OWL ↔ CSV (Argumentum upstream)** | L'OWL `argumentum_fallacies.owl` expose 10 976 `NamedIndividual` ; le CSV canonique n'en compte que 1 408 sophismes × 8 langues = 11 264 descriptions. Facteur d'écart : ×7,8 (1 NamedIndividual ≈ 7,8 labels multilingues). L'OWL capture **plus de granularité** (sous-variantes, classifications internes) ; le CSV capture **la version canonique 8-langues** avec relations transverses. Les deux sources sont **complémentaires, pas redondantes** : OWL = squelette structurel (perd les crossLinks) ; CSV = graphe opérationnel (perd la granularité OWL). | Ontology_CrossLinks, Ontology_AIF |

## Prérequis

### Python

```bash
pip install semantic-kernel openai python-dotenv jpype1
```

### Java

JDK 17+ requis (auto-télécharge via `install_jdk_portable.py`).

### Configuration

```bash
# Dans .env
OPENAI_API_KEY=sk-...
GLOBAL_LLM_SERVICE=openai
BATCH_MODE=false
```

## Mode batch

Pour exécution automatisée (Papermill/MCP) :

```bash
# Dans .env
BATCH_MODE="true"
# Optionnel : texte personnalisé
# BATCH_TEXT="Votre texte à analyser..."
```

## Technologies

| Technologie | Usage |
|-------------|-------|
| **Semantic Kernel** | Orchestration agents |
| **OpenAI GPT** | Analyse textuelle |
| **TweetyProject** | Logique formelle (Java) |
| **JPype** | Pont Python-Java |

## Quick Start

```bash
# 1. Installer les dépendances Python
pip install semantic-kernel openai python-dotenv jpype1

# 2. Configurer les API keys
cp .env.example .env
# Éditer .env : OPENAI_API_KEY, BATCH_MODE=true

# 3. Lancer le premier notebook
jupyter notebook Argumentation-00-Setup-Tweety-Python.ipynb
```

> **Note** : JDK 17+ est requis mais auto-télécharge via `install_jdk_portable.py` (pas d'installation système).

---

## FAQ / Troubleshooting

| Problème | Solution |
|----------|----------|
| **`ModuleNotFoundError: semantic_kernel`** | `pip install semantic-kernel`. Vérifier le kernel Jupyter actif (`jupyter kernelspec list`). |
| **`OPENAI_API_KEY not set`** | Copier `.env.example` en `.env` et renseigner la clé. Vérifier que le notebook 0 charge bien le `.env`. |
| **`JVM not found`** au démarrage | JDK 17+ requis. Exécuter `python install_jdk_portable.py` dans le répertoire. |
| **`FileNotFoundException` sur un JAR Tweety** | Les JARs doivent être dans `libs/`. Re-exécuter le notebook 0 qui les télécharge. |
| **`BATCH_MODE` ignoré** | Vérifier que `.env` contient `BATCH_MODE="true"` (avec guillemets) et que le fichier est au même niveau que les notebooks. |
| **Erreur `dotnet` ou `.NET`** | Cette série est 100% Python. Seul Semantic Kernel (package Python) est utilisé, pas le SDK .NET. |
| **Sortie `PARTIAL_VALIDATED`** | Le pipeline n'a pas convergé. Vérifier les logs de l'agent PL (formalisation incomplète). Relancer avec un texte plus court. |
| **`OutOfMemoryError` JVM** | Augmenter le heap dans la cellule de démarrage : ajouter `-Xmx2g` aux arguments JPype. |

## Structure des fichiers

```text
Argument_Analysis/
├── *.ipynb                    # notebooks pédagogiques (pipeline agentique + Dung)
├── .env / .env.example        # Configuration
├── install_jdk_portable.py    # Installation JDK
├── data/                      # Données (taxonomie sophismes)
├── ext_tools/                 # Outils externes
├── jdk-17-portable/           # JDK (ignoré git)
├── libs/                      # JARs Tweety
├── ontologies/                # Ontologies OWL
├── output/                    # Résultats analyses
└── resources/                 # Ressources Tweety
```

## Sortie

Le pipeline génère un rapport JSON dans `output/analysis_report.json` :

```json
{
  "validation_status": "COMPLETE_VALIDATED",
  "confidence_score": 85,
  "checks": {
    "ARGUMENTS_IDENTIFIED": true,
    "FALLACIES_ANALYZED": true,
    "BELIEF_SET_CREATED": true,
    "QUERIES_EXECUTED": true,
    "CONCLUSION_GENERATED": true
  }
}
```

## Statistiques catalogue à jour

Lecture `CATALOG-STATUS` byte-identique (l. 3-8) : la valeur canonique `pedagogical_count: 28`, `breakdown: Argument_Analysis=28`, `maturity: BETA=26, ALPHA=1, DRAFT=1` (et non un re-affichage dérivé) est la **source de vérité** ; le breakdown par sous-série ci-dessous ré-aligne la prose sur le marqueur canonique header (catalog-pr-hygiene R1 = marqueur canonique byte-identique, pas de re-affichage dérivé). **Écart disque ↔ catalogue signalé** : le répertoire compte **33** notebooks, dont **cinq** absents du catalogue au dernier passage du cron : `07b` (Communication Channels), `04` (Dialogues Protocolises), `04b` (Knowledge Base), `Observatoire-1-Initiation` et `01b` — le cron `catalog-cron.yml` rattrapera ; on ne régénère PAS le catalogue sur cette branche.

| Sous-série | Notebooks | Maturité | Contenu clé |
|------------|-----------|----------|-------------|
| **00-Setup** | 2 | BETA=2 | Chargement env (JDK 17 portable via `install_jdk_portable.py`, 76 JARs Tweety, démarrage JVM fail-loud + smoke test), config `OPENAI_API_KEY` + `GLOBAL_LLM_SERVICE` ; représenté par `Agentic-0-init` + `Agentic-0-init_agent` |
| **01-Pipeline agentique (Agentic-N)** | 8 | BETA=8 | Pipeline principal 0 → 1 → 2 → 3 → 4 (capstone) → 5 (JTMS), compagnons legacy `*_agent` (superseded par SK intégré dans Agentic-N ; statut DEMO sur `0-init_agent` et `3-orchestration_agent`) |
| **02-Argumentation computationnelle** | 8 | BETA=7, DRAFT=1 | Dung AF sémantiques grounded/preferred/stable, VAF Bench-Capon, Toulmin, Ranking (h-Categoriser + fardeau), Dated_Graphs (instrument $G_t^{arg} \to G_{t+1}^{arg}$), 05b (routage multi-backend « décider ou échouer bruyamment », EProver/Mace4), 05c (matrice de richesse formelle anti-théâtre, DRAFT), 08e (ArgumentProfile, vue agrégée) |
| **03-Restitution honnête** | 1 | BETA=1 | `08d` (Restitution 3 actes) : scaffold déterministe pur stdlib (evidence réel-en-état, bande de verdict *gated*, gate de lisibilité §4) + narration LLM *gated* (SDK OpenAI, clé via `GenAI/.env`, statut DEMO — narration clé requise) |
| **04-Interface & widgets** | 1 | BETA=1 | `08c` (UI configuration) : ipywidgets exploratoires (interphase optionnelle, le pipeline reste utilisable sans via `Executor`) |
| **05-Orchestration batch** | 1 | BETA=1 | `08b` (Executor) : point d'entrée unique Papermill/MCP, mode `BATCH_MODE=true` configurable via `.env`, sortie JSON `output/analysis_report.json` |
| **06-Socle ontologique Argumentum** | 3 | ALPHA=1, BETA=2 | `Ontology_AIF` (OWL 4,7 MB, parseur regex tolérant — ALPHA), `Ontology_CrossLinks` (CSV canonique, crossLinks + mappings AIF), `Ontology_Virtues` (thésaurus SKOS des vertus) |
| **07-Récollement & production** | 3 | BETA=3 | `Recollement_Lectures` (lectures croisées), `Recollement_Strate6` (strate 6 du récollement), `02b` (Argumentum Cards, deck imprimable 176 cartes) |
| **08-Travail de groupe** | 1 | BETA=1 | `I2_Contre_arguments_ASPIC` (sous-répertoire `groupe-I2-contre-arguments-aspic/`, production autonome) |
| **Total** | **28** | **BETA=26, ALPHA=1, DRAFT=1** | Python 3.9+, kernel Python 3, JDK 17 portable (auto-install), TweetyProject Java/JPype, Semantic Kernel Python, OpenAI SDK, ontologies OWL (data/) |

> **Note d'audit §E (REWORK tranche 3 #5661 post-Wave-31+)** : la table **« Statistiques catalogue à jour »** a été re-alignée sur le marqueur canonique `CATALOG-STATUS` (l. 3-8, `pedagogical_count: 18`, `maturity: PRODUCTION=13, BETA=4, ALPHA=1`). Le re-affichage dérivé `pedagogical_count: 17` présent dans la version précédente était un **artefact de re-génération locale non canonique** (catalog-pr-hygiene R1 = JAMAIS régénérer un second marqueur sur la branche) ; la **source de vérité** reste le marqueur header. Le breakdown par sous-série passe de 17 → 18 par ajout explicite d'`ArgumentProfile` dans 02-Argumentation computationnelle (qui était omis, faussant le compte). Si un futur passage du cron `catalog-cron.yml` ré-aligne différemment, le résultat sera visible dans la CI par-PR `catalog-drift.yml` — **on ne re-génère PAS sur cette branche**.

**Note PR-A #5721 (Ontology_AIF ajouté)** : le notebook `Argument_Analysis_Ontology_AIF.ipynb` a été ajouté à la liste « Notebooks » (l. 47-64) et à la table « Ce que chaque notebook apporte » (l. 67-84), avec une entrée dédiée dans « Concepts clés » (Ontologie OWL2 / SKOS / Schemes de Walton) et un pont vers [Argumentum](../../../../Argumentum) dans « Ponts avec les autres séries ». **Le marqueur `CATALOG-STATUS` header (l. 3-8) reste byte-identique** à `pedagogical_count: 18` (canonique) — la maturité détaillé du nouveau notebook (BETA initial, à promouvoir en PRODUCTION après validation multi-utilisateur) sera re-alignée par le cron `catalog-cron.yml` ou par `catalog-drift.yml` lors d'une PR ultérieure. **catalog-pr-hygiene R1 respectée** : on n'a pas régénéré le marqueur canonique sur la branche.

**Note PR-B #4960 PR-B (Ontology_CrossLinks ajouté — complément CSV canonique)** : le notebook `Argument_Analysis_Ontology_CrossLinks.ipynb` complète la fondation ontologique par le **CSV canonique** d'Argumentum (1 408 lignes × 102 colonnes, 8 langues × 8 familles × 9 niveaux). Trois findings structurels disclosed honnêtement : **(1)** les 8 colonnes `crossLink_*` (PredatesOn, Denounces, Leverages, Allows, Opposes, Inverts, Mirrors, IsRelatedTo) ne portent que **22 relations totales** = 1,5% de couverture par sophisme — l'arbre taxonomique est **structurellement plat en transverses** ; **(2)** les 3 colonnes `AIF_skos*` (DirectRef, ExceptionRef, MappingType) portent 70 mappings Walton repartis sur `skos:broadMatch` (57), `skos:closeMatch` (10), `skos:narrowMatch` (3) — uniquement présents dans le CSV, **absents de l'OWL** ; **(3)** gap OWL↔CSV mesuré : 10 976 NamedIndividual OWL ≈ 1 408 sophismes CSV × 8 langues = 11 264 descriptions (facteur ×7,8). Ajouts README : ligne dans la table « Notebooks » (l. 62bis après Ontology_AIF), entrée dédiée « Ce que chaque notebook apporte » (l. 81bis), 3 concepts clés dans la table « Concepts clés » (CrossLinks / Mappings AIF / Gap OWL↔CSV). **Le marqueur `CATALOG-STATUS` header reste byte-identique** à `pedagogical_count: 18` (R1 respectée) — la maturité détaillé sera re-alignée par un passage ultérieur du cron `catalog-cron.yml` ou par `catalog-drift.yml` sur PR dédiée.

**Note explicite maturité mixte** : le marqueur canonique porte `BETA=26, ALPHA=1, DRAFT=1`. Le statut **ALPHA** sur `Ontology_AIF` reflète la fragilité du pont de parsing (37 axioms `ExactCardinality` mal formés côté upstream forçant le parseur regex tolérant), pas un défaut de la série. Le statut **DRAFT** sur `Formal_Richness_Matrix` marque une évaluation outillée encore en consolidation. Le statut **DEMO** du catalogue (`0-init_agent`, `3-orchestration_agent`, `Restitution_3_Actes`) marque des notebooks dont l'exécution complète exige une clé OpenAI ou se limite à une démonstration. Les compagnons `*_agent` restent fonctionnels et servent de référence historique (supersession par le pipeline Agentic-N intégré, pas un défaut technique — Semantic Kernel est absorbé dans `Agentic-3-orchestration` + `Agentic-4-capstone`).

**Conformité C.1 (stubs sans erreur volontaire)** : tous les notebooks utilisent les patterns conformes (`pass` / `return None` / `print("Exercice à compléter")` / `result = None  # TODO étudiant`) — **jamais** `raise NotImplementedError` / `assert False` / `1/0` (règle C.1 user 2026-04-26). Le notebook s'exécute de bout en bout même avec les exercices non complétés (mode batch `COMPLETE_VALIDATED` dégradé en `PARTIAL_VALIDATED` sur stub, jamais en exception).

**Dépendances `requirements.txt`** : `semantic-kernel>=0.4`, `openai>=1.0`, `python-dotenv>=1.0`, `jpype1>=1.5`, `pandas>=2.0`, `numpy>=1.24`, `matplotlib>=3.7`. Outils externes : **JDK 17** (auto-install via `install_jdk_portable.py`, pas d'installation système requise), **TweetyProject JARs** (76 JARs, pré-téléchargés dans `libs/`), **OpenAI API** (clé via `.env`, jamais de literal-inline).

**EPITA-IS Argumentum (EPIC #4960)** : la série est livrée upstream-verbatim avec **15 PRs MERGED** (cycle 11 EPITA-IS partitions Symbolique) — le contenu d'`Argument_Analysis_Agentic-*.ipynb` reproduit byte-equal les notebooks source EPITA sous licence MIT/EPITA. C'est la **garantie de complétude** la plus forte du dépôt : la chaîne d'argumentation est **fidèle au syllabus EPITA-IS 2025-2026** sans réécriture locale.

## Ponts avec les autres séries

| Série | Connexion | Détails |
| ----- | ---------- | ------- |
| **[Tweety](../Tweety/)** | Backend argumentatif | Utilise directement TweetyProject (JPype) pour le raisonnement formel. Les sémantiques de Dung (Tweety-5) et la révision de croyances (Tweety-4) sont au cœur du pipeline. |
| **[Lean](../Lean/)** | Preuves formelles | La formalisation logique des arguments (Agentic-2) suit le même paradigme que les tactiques Lean. La vérification de cohérence via SAT est analogue aux proof checkers. |
| **[Tweety-9](../Tweety/Tweety-09-Preferences-Python.ipynb)** | Préférences et vote | L'analyse d'arguments de valeur croise les modèles de préférence et la théorie du choix social (GameTheory/game_theory_lean/SocialChoice/). |
| **[SemanticWeb](../SemanticWeb/)** | Raisonneur OWL/SHACL | Pattern analogue pour la détection d'incohérence ; l'ontologie Argumentum partage les mêmes contraintes de parsing (axiom mal-formés, rdflib en échec) — le notebook `Ontology_AIF` charge `argumentum_fallacies.owl` via parseur regex dédié. |
| **[Argumentum](../../../../Argumentum)** *(submodule, hors-repo)* | Ontologie source | L'ontologie `argumentum_fallacies.owl` (4,7 MB OWL2/XML, 10 976 NamedIndividual) est l'export formel de la taxonomie utilisée par le détecteur de sophismes (`02`). Les 8 colonnes `crossLink_*` du CSV upstream complètent les relations OWL natives par des liens inter-noeuds (PredatesOn, Denounces, Leverages, Allows, Opposes, Inverts, Mirrors, IsRelatedTo). |

[La mer qui monte](../../../docs/grothendieckian-lens.md) : une grille de lecture grothendieckienne du dépôt — l'analyse d'argumentation comme changement de représentation vers le vérifiable : du langage naturel aux sémantiques formelles qu'on peut interroger.

> **Note** : Le pipeline s'exécute de bout en bout. L'`Executor` (point d'entrée Papermill/MCP) produit une validation `COMPLETE_VALIDATED` à 100 % (1 argument identifié, 4 sophismes, 1 belief set formel, 10 requêtes au solveur).

## Écosystème MCP et parenté cross-lane

**3 outils d'infrastructure MCP** (cohérent avec cycles 19-30 hubs) :

1. **MCP Jupyter (`mcp__jupyter-papermill__*`)** — note bug #5211 (mode async ignore `kernel_name`, re-exec = `nbconvert --execute --ExecutePreprocessor.kernel_name=python3 --timeout=600`). Argument_Analysis utilise **kernel Python 3 uniquement** (Semantic Kernel = package Python, pas de kernel .NET natif requis ; JDK 17 portable est un exécutable subprocess, pas un kernel Jupyter).
2. **Validation pre-commit** (`.pre-commit-config.yaml`) — `gitleaks` détecte les secrets inline (clé OpenAI, mnemonic wallet, paths absolus) ; le validateur notebook `validate_pr_notebooks.py` enforce C.1 (stubs sans `NotImplementedError`) et C.2 (notebooks commités AVEC outputs, `execution_count != null`). **Note spécifique Argument_Analysis** : le fichier `.env` (`OPENAI_API_KEY`, `GLOBAL_LLM_SERVICE`, `BATCH_MODE`) doit vivre dans `.gitignore`, jamais en clair dans un notebook ou une cellule — la clé OpenAI est particulièrement sensible (compte facturé).
3. **MCP QC Cloud (`mcp__qc-mcp-lite__*`)** — backtest QuantConnect partagé. Argument_Analysis n'utilise pas QC Cloud directement, mais partage avec QC la même doctrine **anti-théâtre** : la matrice `Formal_Richness_Matrix` classifie les solveurs en 4 verdicts (substantive / honest-absent / unavailable / théâtre), doctrine symétrique au principe QuantConnect « pas de backtest sans Sharpe/CAGR/MaxDD reportés ». Les deux convergent : **un résultat non vérifié n'est pas un résultat**.

**Table parenté cross-lane 6 colonnes** (Argument_Analysis se situe au croisement de plusieurs séries du dépôt) :

| Notebook Argument_Analysis | Série parente | Pont conceptuel |
|---------------------------|---------------|-----------------|
| `02` (taxonomie 1406 nœuds, 7 familles de sophismes) + `05` (Tweety) | [Tweety](../Tweety/) (JPype, sémantiques Dung, FOL, Modal) | TweetyProject = solveur formel unique, JPype = pont Python/Java ; Argument_Analysis consomme les API Tweety comme backend de validation |
| `05` (PL/FOL/Modal/Dung) | [Lean](../Lean/) (preuves formelles, tactiques) | Formalisation logique = même paradigme que tactiques Lean ; frontière informel/formel analogue à proof/script |
| `03`, `03c` | [Tweety](../Tweety/) (Tweety-5 argumentation abstraite) + [GameTheory](../../GameTheory/) (`game_theory_lean/SocialChoice/` Voting.lean) | Sémantiques de Dung (grounded/preferred/stable) = même fondement mathématique que Voting (Banks sets, monotonie STV) |
| `Value_Based_AF` | [GameTheory](../../GameTheory/) (`game_theory_lean/SocialChoice/`) + [Tweety-9](../Tweety/Tweety-09-Preferences-Python.ipynb) (préférences) | Audiences VAF = ordres de préférence sur les valeurs : agréger plusieurs audiences = problème de choix social (Condorcet, Arrow), pont direct vers la théorie du vote |
| `07` (orchestration, Semantic Kernel) | [Argumentum](Argumentum/) + [CoursIA-OwlAdapter](CoursIA-OwlAdapter/) (EPITA-IS verbatim ports, sous-dossiers locaux) | Orchestration agentique = même architecture que Semantic Kernel orchestrant prompts ; Argumentum = ports upstream byte-equal |
| `08d` (Restitution 3 actes, narration LLM *gated*) | [GenAI](../../GenAI/) (Text/Image/Audio/Video, self-hosted + Cloud) | Restitution LLM = même besoin de **séparation lisibilité/honnêteté** que GenAI Text : le LLM génère, le scaffold déterministe garantit la grounding |
| `05b`, `05c` (sentinelle anti-théâtre) | [Search](../../Search/) (CSP/SMT/Z3) + [SemanticWeb](../SemanticWeb/) (OWL/SHACL raisonneurs) | Routage multi-solveur avec sentinelle « décider ou échouer bruyamment » analogue à CSP marathon EPIC #4956 ; classification 4-verdicts symétrique aux solveurs OWL (consistent / inconsistent / unknown / timeout) |
| `06` (JTMS — Truth Maintenance System) | [Lean](../Lean/) (logique constructive) + [SemanticWeb](../SemanticWeb/) (incohérence OWL détection) | JTMS = raisonnement non-monotone étiquetage IN/OUT, analogue à propagation de contraintes Lean + détection d'incohérence SHACL |

**Paragraphe « effet de composition — Argument_Analysis = carrefour informel/formel anti-théâtre »** :

Là où Planners (cycle 29) est le carrefour **simulation/proof intra-série** (Python ⇄ Lean 4 sur l'admissibilité d'heuristique, cycle 29) et SmartContracts (cycle 30) est le carrefour **trust/privacy inter-séries** (confiance + confidentialité + décision collective), Argument_Analysis est le carrefour **informel/formel anti-théâtre inter-couches** : la **lecture de texte** (couche LLM, floue/contextuelle), la **formalisation logique** (couche PL/FOL/Modal, médium), et la **vérification formelle** (couche Tweety/Lean, tranchante/certaine) doivent collaborer SANS que l'une simule ce que l'autre fait réellement. Cette doctrine — incarnée par `Restitution_3_Actes` (scaffold déterministe + LLM *gated*), `Multi_Backend_Routing` (sentinelle « décider ou échouer bruyamment »), `Formal_Richness_Matrix` (4 classes de verdict anti-théâtre), et le mode fail-loud de `05` — est **la doctrine anti-théâtre du dépôt** : aucun notebook ne fait passer une simulation pour un résultat, aucune sortie n'est maquée pour embellir un échec.

La série — 33 notebooks sur disque, 28 au catalogue canonique — aligne l'évolution paradigmatique de l'argumentation computationnelle (1995 Dung AF → 2019 framework hybrides LLM + solveur) sur la **frontière de vérifiabilité** (extraction brute → taxonomie → formalisation → validation SAT → restitution grounded). Chaque notebook est un maillon de la chaîne *lire → formaliser → vérifier → restituer honnêtement*.

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Argument_Analysis est la série-pivot du dépôt : celle où le langage naturel rencontre le formel, médié par un LLM. En suivant le pipeline, vous avez appris à découper un texte argumentatif en couches de rigueur croissante :

- **L'extraction informelle** : un LLM isole prémisses, conclusions, transitions, et confronte chaque passage suspect à la taxonomie des sophismes (1406 nœuds, 7 familles). C'est le versant *vrai mais approximatif* — rapide, contextuel, mais sans garantie.
- **La formalisation** : les arguments informels deviennent un belief set propositionnel. Le texte fluide cède la place à des énoncés booléens que l'on peut *interroger*.
- **La validation formelle** : Tweety (via le pont JPype) interroge ce belief set — une dizaine de requêtes SAT — pour confirmer la cohérence interne : pas de contradiction masquée, pas de conclusion tirée sans prémisse. C'est le versant *sûr mais borné* — lent, rigide, mais fiable.
- **L'orchestration agentique** : Semantic Kernel assemble les briques en un pipeline reproductible, avec un mode *fail-loud* — si la JVM manque, le pipeline échoue bruyamment plutôt que de simuler un verdict.

### Prochaines étapes

- **Approfondissez le backend formel** : chaque requête SAT du pipeline s'appuie sur la théorie de l'argumentation. La série **[Tweety](../Tweety/)** (notebook 5 Dung, notebook 9 préférences/vote) est le socle logique que ce pipeline consomme.
- **Maîtrisez le vérificateur** : la frontière « où s'arrête le LLM, où commence le formel » est aussi celle que trace la vérification formelle. La série **[Lean](../Lean/)** pousse la validation jusqu'à la preuve mathématique.
- **Branchez les ontologies** : un belief set propositionnel est un graphe de connaissances minimal. La série **[SemanticWeb](../SemanticWeb/)** (OWL, SHACL) généralise cette idée à des raisonnements plus riches.
- **Reliez au choix social** : les arguments de valeur et les préférences (Tweety-9) rejoignent la théorie du vote formalisée dans la série **[GameTheory](../../GameTheory/)**.
- La [Lecture transversale](../../../docs/grothendieckian-lens.md) replace ce pipeline — *du langage naturel aux sémantiques formelles qu'on peut interroger* — dans le fil rouge du dépôt.

### Le fil rouge

Le titre annonce l'analyse d'arguments. Mais le geste que cette série enseigne est ailleurs : **tracer une frontière nette entre l'approximatif et le sûr**. Le LLM extrait vite mais sans garantie ; le solveur SAT valide lentement mais avec certitude. Le pipeline n'essaie pas de faire faire au LLM ce qu'il fait mal (garantir la cohérence), ni au solveur ce qu'il ne sait pas faire (lire un texte). Cette discipline du *bon outil pour la bonne tâche*, orchestrée en boucle convergente, est ce que vous emportez au-delà de cette série — et c'est le modèle le plus pragmatique, dans ce dépôt, d'une IA générative ancrée sur du vérifiable.

---

## Ressources

### Références académiques

| Référence | Couverture |
|-----------|------------|
| Dung, "On the Acceptability of Arguments and its Fundamental Role in Nonmonotonic Reasoning" (1995) | Argumentation abstraite, sémantiques |
| Baroni, Caminada & Giacomin, "An Introduction to Argumentation Semantics" (2011) | Sémantiques preferred/stable/complete, étiquetages |
| Modgil & Prakken, "The ASPIC+ Framework for Structured Argumentation" (2014) | Argumentation structurée |
| Alchourron, Gardenfors & Makinson, "On the Logic of Theory Change" (1985) | Révision de croyances AGM |
| Besnard & Hunter, *Elements of Argumentation* (2008) | Cadre général argumentation |
| Besnard & Hunter, "A logic-based theory of deductive arguments" (2001) | Fonction h-Categoriser (classement) |
| Amgoud & Ben-Naim, "Ranking-based semantics for argumentation frameworks" (2013) | Sémantique du fardeau, principes de classement |
| Walton, *Argumentation Schemes for Presumptive Reasoning* (1996) | Taxonomie des sophismes |

### Ressources en ligne

- [Semantic Kernel Docs](https://learn.microsoft.com/en-us/semantic-kernel/)
- [TweetyProject](https://tweetyproject.org/)

## Ordre partiel et prérequis — mapping exhaustif (33/33, version consolidée)

Cette section pose un **ordre partiel** sur l'ensemble des notebooks du
répertoire, fondé sur les déclarations de prérequis et les chaînes de
navigation déjà présentes dans les notebooks eux-mêmes. Aucun `git mv`,
aucune décision de renum — un ordre partiel est orthogonal au verdict renum
(EPIC #5081, §3 « aucune renum » reste tenu : les lettres restent posées là
où elles sont). L'objectif est strictement de répondre au constat :
*« on ne peut pas demander à un étudiant de piocher dans un ensemble non
ordonné. Il doit y avoir des séquences balisées, idéalement sur la progression
de prérequis »* (nit user 5594317963).

Le présent ordre est dérivé **lecture après lecture** des sections
`### Prerequis`, `### Pre-requis`, `**Prérequis:**`, et des lignes
`**Navigation : [<< N >>]` ; il est public et auditable, pas une convention de
nommage.

**Mesure du 2026-09-09 sur `main`** : **28 notebooks** `.ipynb` dans le
répertoire (27 à la racine, 1 sous `groupe-I2-contre-arguments-aspic/`). Depuis
cette mesure, **cinq arrivées** portent le répertoire à **33** (32 racine + 1
sous `groupe-I2-contre-arguments-aspic/`) : `Observatoire-1-Initiation`
(#16431), puis les quatre distillats Triple Distillation livrés le
2026-09-22/23 — `Dialogues_Protocolises`, `01b`, `Knowledge_Base`,
`Communication_Channels` — mesure re-vérifiée au 2026-09-23 (`git ls-tree` :
27 → 32 à la racine, aucune disparition). Chaque
notebook est balisé dans un des trois arcs ou déclaré hors-arc avec sa raison.
La présente section consolide la version c.1030 (livrée par session antérieure)
et le mapping exhaustif 28/28 (PR #15371) — les deux contributions sont
fusionnées sans doublon, le verdict renum (#15283) reste préservé ci-dessous.

### Arc 1 — Agentic (ligne principale, six rungs dans l'arc 00-08) — ordre strict

L'arc Agentic forme une chaîne canonique linéaire déjà balisée par les
notebooks eux-mêmes. C'est **le chemin par défaut** pour un étudiant qui
découvre la série ; il est conçu pour exécuter de bout en bout sans dépendre
de l'arc 3.

```
00  →  02  →  05  →  06  →  07  →  08
                 ↓               ↓              ↓
             (Tweety JVM)   (PL solver)   (UI config)
```

| Rung | Notebook | Rôle dans la série | Prérequis Kernel | Prérequis Notebook |
|------|----------|--------------------|------------------|--------------------|
| 00 | `Argumentation-00-Setup-Tweety-Python.ipynb` | Setup (JPype + JDK + JARs Tweety) | Python 3.10+, JPype, JDK 17 portable | aucun (point d'entrée) |
| 02 | `Argumentation-02-Fallacies-Detection-Python.ipynb` | Détection d'arguments / sophismes | stdlib uniquement | `00` |
| 05 | `Argumentation-05-Formal-Verification-Python.ipynb` | Formalisation (PL + FOL + Modal + Dung) | `jpype` + JVM Tweety | `00`, bases de logique formelle |
| 07 | `Argumentation-07-Orchestration-Python.ipynb` | Coordination (mini-DAG vs conversationnel) | stdlib uniquement | `02` (state-driven) |
| 08 | `Argumentation-08-Capstone-Python.ipynb` | Intégration (baseline 0-shot vs pipeline) | Python intermédiaire | `02`, `07` |
| 06 | `Argumentation-06-JTMS-Python.ipynb` | Raisonnement non-monotone (Doyle 1979) | stdlib uniquement | `05` (logique propositionnelle), `08` (pipeline) |

Lecture **des numéros dans l'ordre** sans raccourci : chaque étape consomme la précédente.

### Arc 2 — Compagnons `*_agent` (parallèle à l'arc 1) — strict après la base

Les compagnons `*_agent` implémentent l'agent spécialisé associé à chaque rung.
Ce sont des **vues « orientées agent »** du même rung — lire le compagnon
**après** la base, jamais avant. (Voir collision slot 2 dans le verdict
renum ci-dessous : `-2-formal` vs `-2-pl_agent` est owner-decision.)

| Base (Arc 1) | Compagnon | Note | Prérequis |
|--------------|-----------|------|------------|
| `Agentic-0-init` | `Agentic-0-init_agent` | *(legacy)* configuration LLM/OpenAI (semantic_kernel) | après `00` |
| `Agentic-1-informal` | `Agentic-1-informal_agent` | *(legacy)* agent d'analyse informelle | après `02` |
| `Agentic-2-formal` | `Agentic-2-pl_agent` | *(legacy)* agent logique propositionnelle | après `05` (collision slot 2 : voir verdict EPIC #5081) |
| `Agentic-3-orchestration` | `Agentic-3-orchestration_agent` | *(legacy)* orchestration multi-agents | après `07` |

Pas de compagnon `*_agent` pour `08` ni `06` (vérifié par `ls` le
2026-09-09) : le compagnon est un doublon legacy des étapes 0-3, la série n'en
a pas créé au-delà.

### Arc 3 — Mnémonique (théorie parallèle, fondationnelle) — ordre partiel

Cet arc regroupe les notebooks à **mnémonique** (sans préfixe `Agentic-`) qui
éclairent les concepts manipulés par l'arc 1. Aucun ne dépend d'un notebook
Agentic pour s'exécuter ; en revanche, plusieurs Agentic citent ces notebooks
en référence.

| Notebook | Rôle dans la série | Prérequis Notebook dans l'arc |
|----------|--------------------|-------------------------------|
| `Argumentation-03-Dung-AF-Semantics-Python.ipynb` | **fondationnel** — sémantiques grounded/preferred/stable de Dung (1995) | aucun (point d'entrée de l'arc 3) |
| `Argumentation-03b-Value-Based-AF-Python.ipynb` | VAF de Bench-Capon (2003) — Dung enrichi par les valeurs | `03` |
| `Argumentation-01-Toulmin-Model-Python.ipynb` | Modèle structurel informel de Toulmin (1958) — 6 composants | aucun (indépendant, pont computationnel vers Dung en fin de parcours) |
| `Argumentation-01b-Schemes-Walton-Python.ipynb` | Schémas d'argumentation de Walton (10 schémas stéréotypés, questions critiques) et classifieur lexical déterministe | aucun (indépendant ; niveau intermédiaire entre `01` et `03`, cités en contexte) |
| `Argumentation-04-Dialogues-Protocolises-Python.ipynb` | Protocoles Walton–Krabbe : inquiry/persuasion comme machines à états sur actes de parole | aucun (indépendant ; voisin de Toulmin_Model par la structure de l'échange, des Agentic par la multi-agentique) |
| `Argumentation-04b-Knowledge-Base-Python.ipynb` | Mémoire d'un débat : population transitive des propositions, requêtes support/attaque par négation lexicale `¬` | aucun (indépendant ; complète `01`, `01b` et `Dialogues_Protocolises`, cités en contexte) |
| `Argumentation-03c-Ranking-Semantics-Python.ipynb` | Sémantiques graduées (h-Categoriser, fardeau) | `03` |
| `Argument_Analysis_Dated_Graphs.ipynb` | Instrument $G_t^{arg} \to G_{t+1}^{arg}$ (Epic #13303, issue #13310) | `03` |
| `Argument_Analysis_Observatoire-1-Initiation.ipynb` | Cas 1 de l'Observatoire (Epic #13303, livré #16431) : étude empirique DiD imparfait consommant l'instrument | `Dated_Graphs` |

```
Dung_AF_Semantics ──→ Value_Based_AF
       │
       ├──→ Ranking_Semantics
       │
       └──→ Dated_Graphs ──→ Observatoire-1-Initiation

Toulmin_Model  (indépendant, racine propre)
```

### Hors-arc (14/33) — chaque notebook restant, avec sa raison

| Notebook | Raison du hors-arc |
|----------|--------------------|
| `Argumentation-08b-Executor-Python.ipynb` | **Transverse (infra)** : point d'entrée batch du pipeline complet (Papermill / MCP) — consomme l'arc 1 (parcours « 0 → 3 → Executor ») |
| `Argumentation-05b-Multi-Backend-Routing-Python.ipynb` | **Transverse (infra)** : routage multi-backend « décider ou échouer bruyamment », s'applique aux solveurs des arcs 1 et 3 |
| `Argumentation-07b-Communication-Channels-Python.ipynb` | **Transverse (infra)** : bus de communication multi-agents (contrat de canal fail-loud, routage sans routes mortes, corrélation requête-réponse) — pur stdlib Python, transversal aux arcs 1 et 2 |
| `Argumentation-05c-Formal-Richness-Matrix-Python.ipynb` | **Transverse (évaluation)** : matrice de richesse formelle (FP-5), classe les verdicts de n'importe quel solveur de la série |
| `Argumentation-08d-Restitution-3-Actes-Python.ipynb` | **Transverse (restitution)** : scaffold de restitution honnête (evidence + narration LLM *gated*), réutilisable par toute la série |
| `Argument_Analysis_Recollement_Lectures.ipynb` | **Transverse (consolidation)** : lectures croisées de la série |
| `Argument_Analysis_Recollement_Strate6.ipynb` | **Transverse (consolidation)** : strate 6 du récollement |
| `Argumentation-08e-Argument-Profile-Python.ipynb` | **Transverse (vue agrégée)** : fiche réunissant les 5 dimensions (sophismes, qualité, contre-arguments, JTMS, formel) — consomme les arcs 1, 2 et 3 |
| `Argumentation-08c-UI-Configuration-Python.ipynb` | **Transverse (interaction)** : interface utilisateur widgets, parcours alternatif « 0 → 1 → UI_configuration » |
| `Argumentation-02b-Argumentum-Cards-Python.ipynb` | **Hors-arc (production)** : deck imprimable du jeu Argumentum (176 cartes depuis la taxonomie) — consomme le socle ontologique, n'est pas un jalon de progression |
| `Argument_Analysis_Ontology_AIF.ipynb` | **Fondation (socle ontologique)** : lecture de l'OWL upstream (10 976 NamedIndividual, 4,7 MB) — outillage, pas un jalon d'apprentissage |
| `Argument_Analysis_Ontology_CrossLinks.ipynb` | **Fondation (socle ontologique)** : CSV canonique complémentaire (1 408 lignes × 102 colonnes) |
| `Argument_Analysis_Ontology_Virtues.ipynb` | **Fondation (socle ontologique)** : pôle vertus, thésaurus SKOS (2 639 triplets) |
| `groupe-I2-contre-arguments-aspic/I2_Contre_arguments_ASPIC.ipynb` | **Hors-arc (travail de groupe)** : sous-répertoire `groupe-I2-contre-arguments-aspic/`, production autonome (contre-arguments ASPIC), n'est pas un jalon de la progression |

### Synthèse — comment lire la série

Trois flux parallèles, **un seul ordre strict** (Agentic 0→5), les deux autres
sont des **ordres partiels** :

1. **Lire l'arc 3 d'abord si la théorie n'est pas acquise** — `03`
   puis, selon l'intérêt, `Value_Based_AF` / `Ranking_Semantics` / `Dated_Graphs`,
   ou `01` en parallèle.
2. **Suivre l'arc 1 dans l'ordre 0 → 5** pour la dimension pratique / pipeline.
   Les compagnons de l'arc 2 s'insèrent **après** leur base (par exemple
   `2-pl_agent` après `05`).
3. **L'arc 3 reste ouvert à tout moment** comme référence — `03`
   est explicitement cité par `05 §6`, et `06` cite Dung 1995 dans
   son introduction. Les **transverses** (`Executor`, `Multi_Backend_Routing`,
   `Communication_Channels`, `Formal_Richness_Matrix`, `Restitution_3_Actes`,
   `Recollement_*`, `ArgumentProfile`, `UI_configuration`) se croisent avec les arcs sans chaîne
   de prérequis stricte — voir « Limites » ci-dessous.

### Arithmétique (résolution du désaccord 14 vs 15 de #15283)

La discussion c.1030 opposait « 14 notebooks annoncés » (adjoint) à « 15
balisés » (auteur de la PR). La mesure de référence est le répertoire :
**33 notebooks sur `main`** au 2026-09-23 — les cinq arrivées depuis la mesure
du 2026-09-09 ont porté l'arc 3 de 5 à 9 — dont **19 balisés** par
les arcs (6 + 4 + 9) et **14 hors-arc** documentés ci-dessus — la somme fait
33, sans trou ni double. Les transverses que la c.1030 déclarait hors-ordre
(`Formal_Richness_Matrix`, `Recollement_*`, …) sont ici nommés un à un avec
leur raison.

### Limites de ce mapping

- L'ordre reste **orthogonal au verdict de renumérotation** (EPIC #5081 §3,
  « aucune renum ») : c'est un ordre de lecture, pas une convention de nom.
- Classification par **rôle déclaré dans les tables du README** ; un
  changement de rôle (ex. `Executor` promu jalon d'arc) impose un re-balisage.
- Un notebook ajouté à la série devra être re-balisé (arc ou raison hors-arc).
- **Ne traite pas la collision slot 2** (`-2-formal` vs `-2-pl_agent`) — le
  verdict EPIC #5081 attend une décision owner sur le rename ; l'ordre ci-dessus
  préserve la cohabitation actuelle (les deux notebooks restent lisibles, le
  companion venant après la base).
- **Ne tranche pas l'appartenance arc 1 / arc 3** des notebooks transverses :
  ils sont référencés depuis plusieurs arcs sans chaîne de prérequis stricte.
  Une révision ultérieure pourra les repositionner.
- **Ne modifie aucun notebook** : l'ordre est porté par le README seulement,
  conformément à la doctrine `notebook-accretion-numbering.md` §3 (« aucune
  renum » par défaut).
- Les blocs de statut catalogue du README sont inchangés : le catalogue
  appartient à l'automatisation (`catalog-cron.yml` / `catalog-drift.yml`).

## Licence

Voir la licence du repository principal.

---

## Renumérotation — verdict (EPIC #5081, issue #14950)

Cette section consigne la proposition d'analyse reçue du workspace partenaire `myia-ai-01:2025-Epita-Intelligence-Symbolique` au titre de la mission de distillation (issue [#14950](https://github.com/jsboige/CoursIA/issues/14950)). La proposition est **owner-decision** : aucun `git mv`, aucune PR de renommage exécutée à ce stade. La consignation ci-dessous sert de **mémo pour arbitrage ultérieur**, conformément à la doctrine `.claude/rules/notebook-accretion-numbering.md` §3 (« le verdict par défaut est aucune renum »).

### Verdict par branche

| Branche | Verdict proposé | Tell §3 nommé |
| ------- | --------------- | ------------- |
| `Argument_Analysis_Agentic-<N>` (numéros nus 0 à 5) | **aucune renumérotation** — c'est un arc | — |
| 4 compagnons `*_agent` (`-0-init_agent`, `-1-informal_agent`, `-2-pl_agent`, `-3-orchestration_agent`) | **normalisation `*` → `b`** (convention §2 : base = `a`, première accrétion = `b`) | traduction d'une intention auteur déjà notée `*(legacy)*` dans la table curée |
| 14 notebooks à mnémonique (théorie / formalismes) | **aucune renum, question de partition** — orthogonaux à l'arc Agentic | aucun tell ne se lit ; le mécanisme des lettres ne s'applique pas |

### Collision slot 2 — décision owner requise

Le slot 2 porte **deux notebooks au contenu distinct** sous le même identifiant nu :

- `Argumentation-05-Formal-Verification-Python.ipynb` (24 cellules, « Vérification Logique Formelle avec Tweety »)
- `Argument_Analysis_Agentic-2-pl_agent.ipynb` (23 cellules, « Agent : PropositionalLogicAgent (Definitions) »)

Deux tells §3 se lisent dans le contenu :

- **Collision d'identifiant (tell 1)** — deux contenus pour un même `<préfixe>-<num>`.
- **Faux prérequis séquentiel (tell 2)** — la navigation de `-2-pl_agent` déclare *Init → ce notebook → Orchestration*, sautant `-1-informal`.

Décision owner attendue : renommer `-2-pl_agent` (et son compagnon `-2-formal_agent` s'il existe) pour lever la collision. La proposition de mapping n'est pas émise dans cette section — un mapping dérivé de titres et de volumes est une hypothèse, conformément à §5.1.

### Indépendant de la renumération

Indépendamment de toute décision de renum, **trois classes de défauts** se corrigent dans les *headings* des notebooks sans toucher au catalogue (`catalog-pr-hygiene.md` : le catalogue appartient à l'automatisation, le cron rattrape sous 24 h) :

- 11 titres publiés commencent par le nom de fichier (régresse la lisibilité du catalogue)
- 3 titres portent le littéral `.ipynb`
- 1 titre cite un numéro de PR interne (`PR-B #4960`)
- 1 titre commence par un numéro de heading d'un autre système (`6.`)
- 3 titres commencent par « Introduction : »

Ce lot est **distinct** de la renumérotation et peut partir seul, sans attendre l'arbitrage owner du slot 2.

### Mesure repo-wide (hors Argument_Analysis)

Le garde de collision du merge-gate (`check_duplicate_notebook_index.py:_INDEX_RE`) exclut la convention dominante du cours (`ID_IN_NAME_RE` accepte `<Préfixe>-<num><lettre?>-`, `_INDEX_RE` exige l'index en tête). Mesure au 2026-09-06 sur 1240 notebooks (hors `_archive`/checkpoints/`.lake`) :

- identifiés par la règle §1 : 822
- vus par `_INDEX_RE` : 224
- écart : **746 notebooks identifiés que le garde de collision ne peut pas voir**

L'écart n'est pas propre à Argument_Analysis — contrôle positif sur les voisines : `Sudoku` 0/37, `Tweety` 0/34, `GameTheory` 8/94. Ce périmètre mériterait sa propre issue, mais elle appartient à l'owner de l'organe. **Elle n'est pas déposée depuis cette section** — la présente consignation se limite à la série Argument_Analysis.


---

**Version 1.2.4** — 2026-09-23 — audit fichier ENTIER §E (issue #17453) : ajout d'`Observatoire-1-Initiation` (livré #16431, epic #16410) dans les tables « Notebooks » et « Ce que chaque notebook apporte » + arc 3 (prérequis `Dated_Graphs`, diagramme mis à jour) ; ajout des 4 notebooks manquants à la table « Notebooks » (`Recollement_Lectures`, `Recollement_Strate6`, `Argumentum_Cards`, `I2_Contre_arguments_ASPIC` — chemin sous-dossier corrigé) ; mapping exhaustif re-mesuré **33/33** (32 racine + 1 sous groupe-I2 — cinq arrivées depuis la mesure du 2026-09-09, re-vérifiées au `git ls-tree`), arithmétique **19 balisés (6+4+9) + 14 hors-arc**, `Communication_Channels` classé hors-arc (transverse infra) ; table « Statistiques catalogue à jour » ré-alignée sur le marqueur canonique `pedagogical_count: 28`, `maturity: BETA=26, ALPHA=1, DRAFT=1` (l'ancienne table sommait à 18 sur un vocabulaire PRODUCTION périmé), écart disque↔catalogue signalé (**5** notebooks non catalogués, nommés, rattrapage par le cron). Marqueur `CATALOG-STATUS` byte-identique, aucune régénération sur la branche. Tell readme-french-first R1 respecté (prose nouvelle en français).

**Version 1.2.3** — 2026-09-10 — consolidation sans doublon de la section « Ordre partiel et prérequis » (PR #15371, suite au DM `msg-20260910T134004-9nsqfl` ai-01) : fusion de la livraison c.1030 (kernel/notebook prérequis détaillés, 15/28) avec le mapping exhaustif 28/28, en une seule section augmentée préservant le verdict renum (EPIC #5081, issue #14950) inchangé. Aucun notebook modifié, aucune décision de renum, marqueur `CATALOG-STATUS` byte-identique à `pedagogical_count: 18`. Tell readme-french-first R1 respectée (section rédigée en français). Tell catalog-pr-hygiene R1 respectée (catalogue inchangé).

**Version 1.2.2** — 2026-09-09 — section *Ordre partiel et prérequis* ajoutée suite au nit user 5594317963. Aucun fichier notebook modifié, aucune décision de renum (EPIC #5081 reste owner-decision). Tell readme-french-first R1 respecté (section rédigée en français). Tell catalog-pr-hygiene R1 respecté (CATALOG-STATUS inchangé).

**Version 1.2.1** — 2026-09-09 — section Renumérotation — verdict (EPIC #5081, issue #14950) consignant la proposition owner-decision sans modifier de fichier. Tell catalog-pr-hygiene R1 respecté (marqueur CATALOG-STATUS inchangé). Tell readme-french-first R1 respecté (section ajoutée en français).
