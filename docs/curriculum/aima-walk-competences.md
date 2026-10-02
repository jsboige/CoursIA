<!--
  FICHIER MANUEL — cartographie compétences du parcours pilote (issue #17982, étapes 1-2).
  Compagnon de docs/curriculum/aima-walk.md (EPIC #13844 Phase 2, #15807) : ce fichier
  n'est PAS régénéré automatiquement — ne pas l'inclure dans generate_parcours.py.
  Référentiels sources archivés (règle bibliography-hygiene, chemins cités en §Sources).
-->

# « Recherche et Corpus » au prisme des référentiels de compétences en IA — pilote #17982

Ce document répond à la question qu'un établissement se pose en premier devant un parcours :
**quelles compétences de mon programme ce parcours couvre-t-il, et lesquelles laisse-t-il de côté ?**
Il cartographie le parcours narratif [aima-walk.md](aima-walk.md) (25 étapes, 10 phases, ~25-30 h)
sur trois référentiels externes reconnus, puis mesure la couverture — les trous sont nommés
comme trous, pas lissés.

## Codification des référentiels

**RCA IA — Référentiel de compétences en IA pour les apprenants (UNESCO 2024)** :
4 aspects × 3 niveaux (Comprendre **C** / Appliquer **A** / Créer **K**) = 12 blocs, codés `RCA-<aspect><niveau>`.

| Code | Bloc (aspect × niveau) |
|---|---|
| RCA-1C/1A/1K | Perspective centrée sur l'humain : Agentivité humaine / Responsabilité humaine / Citoyenneté à l'ère de l'IA |
| RCA-2C/2A/2K | Éthique de l'IA : Intériorisation de l'éthique / Usage sécuritaire et responsable / Éthique dès la conception |
| RCA-3C/3A/3K | Techniques et applications de l'IA : Fondements de l'IA / Compétences pour l'application / Création d'outils d'IA |
| RCA-4C/4A/4K | Conception de systèmes d'IA : Délimitation des problèmes / Conception de l'architecture / Itérations et boucles de rétroaction |

**RCE IA — Référentiel de compétences en IA pour les enseignants (UNESCO 2024)** :
5 aspects × 3 niveaux (Acquérir **A** / Approfondir **P** / Créer **K**) = 15 blocs, codés `RCE-<aspect><niveau>`.
Un parcours d'apprenants ne développe les compétences enseignantes qu'indirectement : la
cartographie RCE ci-dessous porte donc sur ce qu'un **enseignant qui suivrait le parcours** en
retirerait, au niveau aspect uniquement — le niveau bloc serait de la sur-précision.

**AI4K12 — Five Big Ideas (AAAI/CSTA)** : 5 idées codées `AI4K12-1..5` — Perception ·
Représentation et raisonnement · Apprentissage · Interaction naturelle · Impact social.

## Cartographie étape par étape

Chaque justification cite **ce que le notebook fait faire**, jamais son titre. « P1 » à « P10 »
référencent les phases de [aima-walk.md](aima-walk.md).

| Étape | Notebook(s) | Compétences | Justification (ce que le notebook fait faire) |
|---|---|---|---|
| 1 (P1) | Search-01-StateSpace | RCA-4C, AI4K12-2 | L'apprenant formule un problème en triple état-initial/successeurs/but — le geste exact de la délimitation de problème — et acquiert le vocabulaire de représentation que tout le reste du parcours réutilise. |
| 2 (P1) | Search-02-Uninformed + 02b-NetworkX | RCA-3C, AI4K12-2 | Il implémente puis instrumente BFS/DFS/coût uniforme dans NetworkX, distinguant sur des traces d'exécution ce que chaque stratégie garantit (complétude, optimalité) — les fondements, exécutés. |
| 3 (P1) | Search-03-Informed + 03e-AStar-Optimality | RCA-3C, RCA-3A, AI4K12-2 | Il règle A* avec des heuristiques dont il vérifie l'admissibilité et la cohérence, puis le compagnon formel lui fait relire la preuve d'optimalité — comprendre le fondement, pas seulement appeler la fonction. |
| 4 (P2) | Search-04-LocalSearch | RCA-3C, RCA-3A | Il compare hill-climbing et recuit simulé sur des paysages où le premier se fige dans un optimum local : il applique une technique en observant ses conditions de défaillance. |
| 5 (P2) | Search-05-GeneticAlgorithms + MGS-01-Introduction | RCA-3A, RCA-4A, AI4K12-3 | Il fait tourner un algorithme génétique puis ouvre sur les métaheuristiques composées de la série MGS : assembler opérateurs et boucle évolutionnaire relève de la conception d'architecture de solveur. |
| 6 (P3) | Search-06-AdversarialSearch | RCA-3C, AI4K12-2 | Il développe l'arbre de jeu de minimax et l'élague en alpha-bêta : représenter un adversaire comme un arbre de décision séquentiel et raisonner dessus. |
| 7 (P3) | Search-07-MCTS-And-Beyond | RCA-3A, AI4K12-3 | Il fait échantillonner Monte-Carlo Tree Search par bandits sur des simulations répétées — appliquer une technique d'apprentissage par exploration à la décision séquentielle. |
| 8 (P4) | CSP-1-Fundamentals | RCA-4C, AI4K12-2 | Il modélise un problème en variables/domaines/contraintes puis le résout par backtracking : une seconde famille de délimitation formelle de problème. |
| 9 (P4) | CSP-2-Consistency | RCA-3A | Il propage la cohérence d'arc (AC-3) et ordonne les variables (MRV, forward-checking), mesurant l'effet de chaque heuristique sur l'arbre de recherche. |
| 10 (P5) | Tweety-2-Basic-Logics | RCA-3C, AI4K12-2 | Il représente des énoncés en logique propositionnelle et fait répondre un solveur Tweety : la représentation symbolique comme fondement vérifié par la machine. |
| 11 (P5) | Tweety-2c-FOL-Csharp | RCA-3A, AI4K12-2 | Il transpose les mêmes requêtes en logique du premier ordre sur le twin .NET : transférer une représentation d'un formalisme à une API sœur. |
| 12 (P5) | Tweety-3-Advanced-Logics | RCA-3C | Il exécute des inférences en logiques par défaut et modales : comprendre que « raisonner » se décline en sémantiques différentes selon ce qu'on veut capturer. |
| 13 (P6) | PyMC-04-Bayesian-Networks | RCA-3C, RCA-3A, AI4K12-2 | Il code un réseau bayésien, en lance l'inférence exacte puis MCMC, et voit la distribution posterieure se construire : raisonnement probabiliste représenté ET appliqué. |
| 14 (P6) | PyMC-05-Causal-Inference | RCA-3A, AI4K12-2 | Il intervient sur un graphe causal (`do`, contre-factuels) et compare à l'observation simple : appliquer la distinction corrélation/causalité sur des calculs qu'il exécute. |
| 15 (P7) | GameTheory-02-NormalForm | RCA-3C, AI4K12-2 | Il calcule des équilibres purs et mixtes de jeux sous forme normale : représenter une interaction stratégique et raisonner jusqu'à ses points fixes. |
| 16 (P7) | GameTheory-06-EvolutionTrust | RCA-3A, AI4K12-3 | Il programme des stratégies et les affronte dans un tournoi d'Axelrod où la coopération émerge des scores cumulés : appliquer l'apprentissage par répétition à la dynamique de confiance. |
| 17 (P7) | GameTheory-13-ImperfectInfo-CFR (+ 02b-Lean) | RCA-3A, RCA-4K | Il minimise le regret contrefactuel sur un poker à information imparfaite, boucle d'apprentissage itérative complète — et le compagnon Lean lui fait vérifier les définitions sous-jacentes. |
| 18 (P8) | Série Planners (PDDL/STRIPS) | RCA-4C, RCA-3A | Il décrit des domaines et problèmes en PDDL puis enchaîne les plans d'un solveur STRIPS : la planification comme CSP séquencé, délimitée puis résolue. |
| 19 (P9) | rl_1_intro_cartpole | RCA-3C, RCA-3A, AI4K12-3 | Il pose un MDP et entraîne un Q-learning sur Gymnasium jusqu'à stabiliser le pendule : le paradigme apprentissage-par-renforcement, des équations à la courbe de récompense. |
| 20 (P9) | rl_3_experience_replay_her | RCA-4K | Il stabilise l'entraînement par replay buffer et redéfinit les buts (HER), réglant la boucle de rétroaction expérience→mise à jour : itérer sur l'architecture d'apprentissage elle-même. |
| 21 (P9) | rl_15_grpo_group_relative_policy | RCA-3A, RCA-4K, AI4K12-3 | Il applique les policy gradients modernes (GRPO) — la même famille d'algorithmes qui aligne les LLM — et referme la boucle vers la phase 10. |
| 22 (P10) | 01_OpenAI_Intro + 02_PromptEngineering | RCA-3A, RCA-2A, RCA-2C, AI4K12-4 | Il appelle l'API, construit des prompts, et le notebook l'oblige explicitement à identifier les hallucinations et à situer les enjeux éthiques et de responsabilité (objectifs et section dédiés du carnet) : interaction naturelle doublée d'une première intériorisation de l'éthique. |
| 23 (P10) | 05_RAG_Modern | RCA-4A, RCA-2A, AI4K12-4 | Il assemble retriever et générateur — conception d'architecture de système IA — pour réduire les hallucinations via des sources vérifiables par l'utilisateur : usage sécuritaire comme critère de design. |
| 24 (P10) | 08_Reasoning_Models | RCA-3C, AI4K12-4 | Il fait raisonner des modèles en chaîne et en compare les échecs : comprendre ce que « raisonnement » veut dire pour un LLM, en le faisant interagir. |
| 25 (Épilogue) | IIT-01-IntroToPyPhi | RCA-3C | Il calcule des mesures d'information intégrée avec PyPhi : comprendre une théorie de la conscience artificielle propre au corpus, hors manuel — l'exercice même de lecture critique d'un cadre théorique. |

## Rapport de couverture mesuré

### RCA IA (apprenants) — les 12 blocs

| Aspect \ Niveau | Comprendre | Appliquer | Créer |
|---|---|---|---|
| 1. Perspective centrée sur l'humain | — | — | — |
| 2. Éthique de l'IA | partiel (ét. 22) | partiel (ét. 22, 23) | — |
| 3. Techniques et applications | **ét. 2, 3, 6, 10, 12, 13, 15, 19, 24, 25** | **ét. 3, 4, 7, 9, 11, 13, 14, 16, 17, 18, 19, 21, 22** | — |
| 4. Conception de systèmes d'IA | ét. 1, 8, 18 | ét. 5, 23 | ét. 17, 20, 21 |

Lecture : le parcours est **massivement un parcours « Techniques » (aspect 3) aux niveaux
Comprendre et Appliquer** — c'est cohérent avec sa nature de re-traversée d'AIMA. L'aspect 4
(conception) est représenté aux trois niveaux : délimitation (CSP, PDDL), architecture (GA
composés, pipeline RAG), boucles de rétroaction (HER, GRPO, CFR).

**Trous mesurés, pas supposés** :
- **Aspect 1 (perspective centrée sur l'humain) : 0 bloc sur 3 couvert.** Aucune étape ne fait
  réfléchir l'apprenant sur l'agentivité, la responsabilité humaine ou la citoyenneté à l'ère de
  l'IA. L'hypothèse de l'issue #17982 (« état d'esprit centré sur l'humain : trou probable »)
  est **confirmée par la mesure**.
- **Aspect 2 (éthique) : partiel et tardif.** Deux étapes sur 25 (22 et 23) touchent l'usage
  sécuritaire — parce que les carnets correspondants traitent nommément hallucinations et
  vérifiabilité des sources (vérifié dans leurs sources, cellules d'objectifs). Aucune étape ne
  pratique l'« éthique dès la conception » (niveau Créer) : nulle part l'apprenant ne conçoit un
  système en intégrant un critère éthique comme contrainte de conception.
- **Niveau Créer (vertical) : 3 blocs sur 12, tous côté aspect 4.** Le parcours fait exécuter et
  comprendre ; il ne fait presque jamais **cocréer** un outil d'IA. Seule exception réelle : la
  famille HER/GRPO/CFR, où l'apprenant règle la boucle d'apprentissage elle-même.

### RCE IA (enseignants) — niveau aspect, pour un enseignant qui suivrait le parcours

| Aspect | Contribution du parcours |
|---|---|
| 1. Perspective centrée sur l'humain | nulle — même trou que côté apprenants |
| 2. Éthique de l'IA | marginale (les encadrés hallucinations/vérifiabilité des ét. 22-23) |
| 3. Fondements et applications de l'IA | **substantielle aux niveaux Acquérir-Approfondir** : c'est le cœur du parcours — un enseignant qui le suit maîtrise les techniques fondamentales et leur mise en œuvre |
| 4. Pédagogie de l'IA | nulle en direct ; indirecte : le parcours est lui-même un exemple documenté de séquençage curriculaire spirale (phases 1→10), réutilisable comme patron |
| 5. IA pour le développement professionnel | nulle |

### AI4K12 — les cinq grandes idées

| Idée | Couverture |
|---|---|
| 1. Perception | **absente** — aucun carnet du parcours ne traite capteurs, vision ni parole |
| 2. Représentation et raisonnement | **ét. 1-3, 6, 8-15, 18, 24** — l'ossature du parcours |
| 3. Apprentissage | **ét. 5, 7, 16, 17, 19-21** — GA, MCTS, Axelrod, RL |
| 4. Interaction naturelle | **ét. 22-24** — LLM : prompting, RAG, modèles de raisonnement |
| 5. Impact social | **marginale** : uniquement la section enjeux éthiques de l'ét. 22 — un encadré, pas une pratique |

## Ce que le pilote dit à l'étape 3 (décision d'outillage)

La mesure donne un profil net et défendable : **« Recherche et Corpus » est un parcours
d'approfondissement technique (RCA-3 C/A, AI4K12-2/3) avec une porte étroite vers l'éthique
en usage (RCA-2A) et l'interaction LLM (AI4K12-4)**. Pour un établissement qui doit couvrir un
programme complet, ce parcours est une **brique spécialisée**, pas un tronc commun : les
aspects 1-2 du RCA et l'idée 5 d'AI4K12 s'acquièrent ailleurs (les séries XAI, IIT-éthique ou
GenAI/Semantic en sont les candidates naturelles du corpus).

Pour l'outillage (étape 3 de #17982) : cette cartographie a été produite à la main en croisant
les descriptions d'activité du parcours et les sources des carnets — le coût marginal par
parcours est faible mais non nul ; un champ `competences` généré par le catalogue ne se
justifiera que si les parcours narratifs se multiplient au-delà des trois pilotes. La
recommandation du pilote : **geler l'outillage tant que le nombre de parcours ne dépasse pas la
dizaine**, et réutiliser la codification ci-dessus (RCA-xN / RCE-xN / AI4K12-n) pour que les
futurs mappings restent comparables.

## Sources — référentiels archivés (règle bibliography-hygiene)

- `G:\Mon Drive\MyIA\IA\Bibliographie IA\Teaching Materials\2025 - UNESCO - Referentiel de competences en IA pour les apprenants - 392652fre.pdf` (RCA IA, éd. FR, 80 p.)
- `G:\Mon Drive\MyIA\IA\Bibliographie IA\Teaching Materials\2025 - UNESCO - Referentiel de competences en IA pour les enseignants - 392681fre.pdf` (RCE IA, éd. FR, 62 p.)
- `G:\Mon Drive\MyIA\IA\Bibliographie IA\Teaching Materials\2023 - AI4K12 AAAI-CSTA - Five Big Ideas in AI poster v2 EN.pdf`
- `G:\Mon Drive\MyIA\IA\Bibliographie IA\Teaching Materials\2020 - AI4K12 AAAI-CSTA - Cinq grandes idees en IA poster FR.pdf`
- Parcours cartographié : [aima-walk.md](aima-walk.md) (#15807, PR #15820) ; nomenclature des blocs RCA/RCE extraite des tableaux 1 de chaque référentiel UNESCO, vérifiée sur les PDF archivés.
- Ancrages de contenu vérifiés dans les sources des carnets : objectifs « hallucinations » et « enjeux éthiques » de `GenAI/Texte/01_OpenAI_Intro.ipynb` (cellules 2-3), « réduire les hallucinations » / « vérifiabilité » de `05_RAG_Modern.ipynb` (cellules 8, 33).
