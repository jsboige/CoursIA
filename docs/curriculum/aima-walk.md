<!--
  FICHIER MANUEL — parcours narratif pilote (EPIC #13844 Phase 2, issue #15807).
  Écrit à la main à partir de docs/transients/2026-09-02-curriculum-inventory.md : contrairement aux
  pages docs/curriculum/*.md générées chaque jour par catalog-cron.yml, ce fichier
  n'est PAS régénéré automatiquement — ne pas l'inclure dans generate_parcours.py.
-->

# Recherche et Corpus (AIMA-inspired) — lire le dépôt comme un corpus de recherche (~25-30 h)

Troisième des trois parcours narratifs pilotes de l'EPIC #13844 (avec l'accéléré GenAI et la
formalisation symbolique). Il s'adresse à **celui qui veut re-traverser l'IA classique avec un
manuel de référence — Russell & Norvig, *Artificial Intelligence: A Modern Approach* (AIMA) —
et vérifier chaque concept sur du code qui tourne**, plutôt qu'à celui qui cherche une
compétence applicative unique. C'est un parcours de **lecture exécutante** : chaque étape
s'accomplit en relisant le chapitre correspondant puis en exécutant le notebook cité.

## Prérequis vérifiables en ~10 min

| # | Prérequis | Test (doit réussir) |
|---|---|---|
| 1 | Python 3.10+ avec le `venv` du dépôt | `python -c "import networkx, pymc"` depuis `venv/` |
| 2 | .NET 9 + .NET Interactive (notebooks twins C#) | `jupyter kernelspec list` montre `.net-csharp` |
| 3 | Java 17+ (série Tweety) | `java -version` ≥ 17 |
| 4 | Clé API LLM (phase LLM uniquement) | variable d'env `OPENAI_API_KEY` définie |
| 5 | Lean 4 via elan **optionnel** (compagnons formels) | `elan show` — absent = parcours complet quand même |

Ce parcours suppose une **familiarité de premier cycle avec les structures d'algorithmes**
(graphe, file de priorité, complexité) et des bases de probabilités. Les notebooks twins C#
fournissent le même contenu pour lecteur .NET — ils sont des **alternatives**, pas des
prérequis ; les compagnons Lean sont des **approfondissements optionnels**, jamais des
prérequis (modèle de la clause de [`GameTheory/README.md`](../../MyIA.AI.Notebooks/GameTheory/README.md) §Parcours alternatifs).

## Durée estimée — base mesurée, pas une durée fantôme

Le **noyau mesure 21 h 15** : somme des `duree_estimee` du `COURSE_CATALOG.generated.json`
pour les 29 notebooks cités ci-dessous (le détail par phase porte la somme de ses étapes ;
seules les phases de **planification** (Phase 6) et de **théorie de la décision** (Phase 8),
qui renvoient au README de leur série, ne sont pas re-chiffrées). Les
**compagnons optionnels** (twins C# des mêmes étapes ≈ +7 h, side-tracks Lean ≈ +3 h)
portent la fourchette à **25-30 h** — fourchette assumée comme telle, conformément au
critère #13844 : l'estimation s'appuie sur le catalogue, pas sur une intuition.

## Sortie concrète

À la fin, vous avez **exécuté** : un A* avec heuristiques pondérées et pattern databases,
un solveur CSP avec propagation de cohérence, un solveur logique Tweety en FOL, un plan
PDDL/STRIPS, un réseau bayésien PyMC avec inférence causale, une décision sous incertitude
(utilité espérée, valeur de l'information, MDP), un équilibre de Nash calculé, un CFR sur
poker imparfait, un agent RL entraîné, et un pipeline LLM complet (prompting → RAG →
raisonnement). Vous savez surtout **où le corpus dépasse AIMA** (théorie des jeux formelle,
IIT, métaheuristiques composées) — l'épilogue le nomme.

***

## Le fil — AIMA comme ossature, chapitre par chapitre

Les phases suivent **la structure en parties du manuel**, et non l'ordre historique du dépôt :
Part II *Problem-solving* (recherche, chapitres 3-6) → Part III *Knowledge, reasoning, and
planning* (logique puis planification, chapitres 7-11) → Part IV *Uncertain knowledge and
reasoning* (modèles graphiques 12-15, **théorie de la décision 16-17**, décision multi-agents
18) → Part V *Machine Learning* (apprentissage par renforcement, chapitre 22) → Part VI
(langage, chapitres 23-24). C'est cet ordre — vérifié contre les tables des matières
archivées d'AIMA 3e et 4e — que le parcours re-traverse ; les écarts entre les deux éditions
sont nommés en **Angles morts** en fin de page.

### Phase 1 — Résoudre des problèmes par la recherche (AIMA ch. 3) — Search-01→03, ~3 h 45

1. **[`Search-01-StateSpace.ipynb`](../../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-01-StateSpace.ipynb)** (45 min) — espaces d'états,
   formulation problème/successeurs/but. *Suppose : bases de graphes. Apporte : le vocabulaire
   que toutes les étapes suivantes utilisent.*
2. **[`Search-02-Uninformed.ipynb`](../../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-02-Uninformed.ipynb)** (1 h) + **[`Search-02b-NetworkX.ipynb`](../../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-02b-NetworkX.ipynb)** (45 min) — BFS,
   DFS, coût uniforme, puis la mise en œuvre NetworkX. *Suppose : Phase 1.*
3. **[`Search-03-Informed.ipynb`](../../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03-Informed.ipynb)** (45 min) — A*, admissibilité, cohérence.
   **[`Search-03e-AStar-Optimality.ipynb`](../../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03e-AStar-Optimality.ipynb)** (30 min) — compagnon formel : l'optimalité d'A*
   relue sur le notebook (cf #13685).

### Phase 2 — Au-delà du classique : recherche locale (AIMA ch. 4) — Search-04→05, ~2 h 15

4. **[`Search-04-LocalSearch.ipynb`](../../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-04-LocalSearch.ipynb)** (45 min) — hill-climbing, simulated annealing.
5. **[`Search-05-GeneticAlgorithms.ipynb`](../../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-05-GeneticAlgorithms.ipynb)** (1 h) — algorithmes génétiques.
   **[`MGS-01-Introduction.ipynb`](../../MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-01-Introduction.ipynb)** (30 min) — ouverture du
   dépôt **au-delà d'AIMA** : métaheuristiques composées (série MetaGeneticSharp).

### Phase 3 — Recherche adversariale (AIMA ch. 5) — Search-06→07, ~1 h 30

6. **[`Search-06-AdversarialSearch.ipynb`](../../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-06-AdversarialSearch.ipynb)** (45 min) — minimax, alpha-bêta. *Suppose : arbres
   de jeu, Phase 1.*
7. **[`Search-07-MCTS-And-Beyond.ipynb`](../../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-07-MCTS-And-Beyond.ipynb)** (45 min) — Monte-Carlo Tree Search, pont vers le RL
   de la Phase 10.

### Phase 4 — Problèmes de satisfaction de contraintes (AIMA ch. 6) — CSP-1→2, ~1 h 45

8. **[`CSP-1-Fundamentals.ipynb`](../../MyIA.AI.Notebooks/Search/Part2-CSP/CSP-1-Fundamentals.ipynb)** (1 h) — modélisation CSP, backtracking.
9. **[`CSP-2-Consistency.ipynb`](../../MyIA.AI.Notebooks/Search/Part2-CSP/CSP-2-Consistency.ipynb)** (45 min) — AC-3, MRV, forward-checking. *La série continue
   jusqu'à CSP-9 (temporel, distribué) pour qui veut prolonger.*

### Phase 5 — Logique (AIMA ch. 7-9) — Tweety, ~2 h 15

10. **[`Tweety-02-Basic-Logics-Python.ipynb`](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-02-Basic-Logics-Python.ipynb)** (45 min) — logique propositionnelle
    avec la bibliothèque Tweety (Java). *Suppose : prérequis 3 (Java).*
11. **[`Tweety-02c-FOL-CSharp.ipynb`](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-02c-FOL-CSharp.ipynb)** (45 min) — logique du premier ordre, twin .NET.
12. **[`Tweety-03-Advanced-Logics-Python.ipynb`](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-03-Advanced-Logics-Python.ipynb)** (45 min) — logiques non classiques (défaut,
    modales). *Pont : [`Tweety-11-Causal-Python.ipynb`](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-11-Causal-Python.ipynb) pour la jonction avec la Phase 7.*

### Phase 6 — Planification (AIMA ch. 10-11) — série Planners (durée non chiffrée ici)

13. **[`SymbolicAI/Planners/`](../../MyIA.AI.Notebooks/SymbolicAI/Planners/)** — PDDL, STRIPS, planification temporelle et hiérarchique.
    Entrée par le README de la série, dont le parcours existe déjà (embryon #12 de
    [`2026-09-02-curriculum-inventory.md`](../transients/2026-09-02-curriculum-inventory.md) — il est `INTEGRATE`, donc cité, pas réécrit) ; sa durée se lit dans le
    README de la série, ce parcours ne la re-chiffre pas. *Suppose : Phase 4 (CSP) —
    la planification est un CSP séquencé.*

### Phase 7 — Raisonnement probabiliste et modèles graphiques (AIMA ch. 12-15) — PyMC, ~1 h

14. **[`PyMC-04-Bayesian-Networks.ipynb`](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-04-Bayesian-Networks.ipynb)** (30 min) — réseaux bayésiens, inférence
    exacte puis MCMC. *Suppose : bases de probabilités.*
15. **[`PyMC-05-Causal-Inference.ipynb`](../../MyIA.AI.Notebooks/Probas/PyMC/PyMC-05-Causal-Inference.ipynb)** (30 min) — do-calculus, contre-factuels — la
    jonction moderne d'AIMA ch. 16. *Annexe probabiliste : le [`README PyMC`](../../MyIA.AI.Notebooks/Probas/PyMC/README.md) (4 parcours,
    ~10 h) prolonge cette phase (embryon #5 de [`2026-09-02-curriculum-inventory.md`](../transients/2026-09-02-curriculum-inventory.md)).*

### Phase 8 — Théorie de la décision (AIMA ch. 16-17) — Probas/DecisionTheory (durée non chiffrée ici)

16. **[`Probas/DecisionTheory/`](../../MyIA.AI.Notebooks/Probas/DecisionTheory/README.md)** — l'arc de la décision sous incertitude : de
    l'utilité espérée et des axiomes de von Neumann–Morgenstern, aux diagrammes d'influence et
    à la valeur de l'information (ch. 16), puis au séquentiel — MDP, équation de Bellman,
    bandits (ch. 17). Entrée par le README de la série (38 carnets : les arcs
    [`DecInfer/`](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/README.md) C#+Lean et
    [`DecPyMC/`](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecPyMC/README.md) Python en miroir, la sous-série
    [`Actuariat/`](../../MyIA.AI.Notebooks/Probas/DecisionTheory/Actuariat/README.md), le capstone causal
    [`Causalite/`](../../MyIA.AI.Notebooks/Probas/Causalite/README.md) et le lake
    [`decision_theory_lean/`](../../MyIA.AI.Notebooks/Probas/DecisionTheory/decision_theory_lean/)) ; les deux
    entrées par lesquelles on aborde la série sont
    [`DecPyMC-01-Utility-Foundations`](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecPyMC/DecPyMC-01-Utility-Foundations.ipynb) et
    [`DecPyMC-07-Sequential`](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecPyMC/DecPyMC-07-Sequential.ipynb). Sa durée se lit dans le
    README de la série, ce parcours ne la re-chiffre pas. *Suppose : Phase 7 (modèles
    graphiques / posteriors) — un posterior est l'entrée d'une décision, pas sa fin.*

### Phase 9 — Décision multi-agents et théorie des jeux (AIMA ch. 18) — GameTheory, ~2 h 30

17. **[`GameTheory-02-NormalForm-Python.ipynb`](../../MyIA.AI.Notebooks/GameTheory/GameTheory-02-NormalForm-Python.ipynb)** (45 min) — formes normales, équilibres
    purs et mixtes. *Suppose : Phase 3 (minimax).*
18. **[`GameTheory-06-EvolutionTrust-Python.ipynb`](../../MyIA.AI.Notebooks/GameTheory/GameTheory-06-EvolutionTrust-Python.ipynb)** (45 min) — tournoi d'Axelrod, émergence de la
    coopération — la pause narrative du parcours.
19. **[`GameTheory-13-ImperfectInfo-CFR-Python.ipynb`](../../MyIA.AI.Notebooks/GameTheory/GameTheory-13-ImperfectInfo-CFR-Python.ipynb)** (1 h) — information imparfaite, counterfactual
    regret minimization (poker AI). *Companion formel optionnel :
    [`GameTheory-02b-Lean-Definitions-Lean.ipynb`](../../MyIA.AI.Notebooks/GameTheory/GameTheory-02b-Lean-Definitions-Lean.ipynb)* (45 min) — les mêmes définitions en Lean 4
    (embryon #7 : les lacs Lean comme compagnons formels).

### Phase 10 — Apprentissage par renforcement (AIMA ch. 22) — RL, ~2 h 15

20. **[`RL-01-Premiers-Pas-Stable-Baselines3-Python.ipynb`](../../MyIA.AI.Notebooks/RL/RL-01-Premiers-Pas-Stable-Baselines3-Python.ipynb)** (45 min) — MDP, Q-learning, Gymnasium. *Suppose :
    Phase 3 (arbres de décision séquentiels).*
21. **[`RL-03-Experience-Replay-HER-Python.ipynb`](../../MyIA.AI.Notebooks/RL/RL-03-Experience-Replay-HER-Python.ipynb)** (45 min) — replay, HER, stabilité.
22. **[`RL-15-GRPO-Comparatif-Multi-Graines-Python.ipynb`](../../MyIA.AI.Notebooks/RL/RL-15-GRPO-Comparatif-Multi-Graines-Python.ipynb)** (45 min) — policy gradients modernes
    (GRPO) — la jonction explicite avec les LLM de la Phase 11.

### Phase 11 — Langage et LLM (AIMA ch. 23-24, actualisés) — GenAI/Texte, ~2 h 30

23. **[`01_OpenAI_Intro.ipynb`](../../MyIA.AI.Notebooks/GenAI/Texte/01_OpenAI_Intro.ipynb)** (30 min) + **[`02_PromptEngineering.ipynb`](../../MyIA.AI.Notebooks/GenAI/Texte/02_PromptEngineering.ipynb)**
    (45 min) — API, prompting. *Suppose : prérequis 4 (clé API).*
24. **[`05_RAG_Modern.ipynb`](../../MyIA.AI.Notebooks/GenAI/Texte/05_RAG_Modern.ipynb)** (45 min) — retrieval-augmented generation.
25. **[`08_Reasoning_Models.ipynb`](../../MyIA.AI.Notebooks/GenAI/Texte/08_Reasoning_Models.ipynb)** (30 min) — modèles de raisonnement — ce qu'AIMA
    appelait « agents logiques », relu en 2026.

### Épilogue — Où le corpus dépasse AIMA, ~45 min

26. **[`IIT-01-IntroToPyPhi-Python.ipynb`](../../MyIA.AI.Notebooks/IIT/IIT-01-IntroToPyPhi-Python.ipynb)** (45 min) — théorie de l'information intégrée :
    hors AIMA, propre au dépôt. Prolongements nommés : [`Search-09e-Komlos-Lean.ipynb`](../../MyIA.AI.Notebooks/Search/Part1-Foundations/Search-09e-Komlos-Lean.ipynb)
    (recherche **formelle**, compagnon Lean de la phase 2), la série IIT complète (59
    notebooks de la famille la plus dense du dépôt, cf [`recherche.md`](recherche.md)).

***

## Angles morts — ce que ce parcours ne traverse pas

Le parcours est une **traversée à un carnet par étape**, pas un inventaire du dépôt : les
séries qu'il ne cite pas n'y sont pas absentes, elles ont leur propre parcours. Ce que cette
page ne traverse pas, nommément :

- **Le bloc symbolique au-delà de Tweety et Planners.** La Phase 5 (logique) porte trois
  carnets Tweety et la Phase 6 (planification) renvoie au dossier Planners ; les autres
  familles symboliques du dépôt — **Lean** (161 carnets de preuves formelles), **SMT/Z3**
  (52), **ArgumentAnalysis/Argumentum** (42), **SemanticWeb** (28), **SymbolicLearning**
  (31), **SmartContracts** (32) — ne figurent pas dans ce parcours : chacune a sa série et
  son README. Le bloc symbolique du manuel (AIMA ch. 7-11) est donc couvert ici par la
  logique et la planification seules.
- **La représentation des connaissances (AIMA ch. 10 en 4e)** n'a pas d'étape dédiée : elle
  est pliée dans le bloc logique/planification, pas traversée par un carnet.
- **L'arc de décision ne traverse que ses deux entrées.** La Phase 8 cite le README de la
  série DecisionTheory (38 carnets) et ses deux entrées Python ; la sous-série Actuariat, le
  capstone causal Causalité et la couche de certification Lean restent dans la série,
  pas dans le parcours.
- **L'écart 3e ↔ 4e que le parcours suit.** Le parcours suit la **4e** : en 4e la
  représentation des connaissances (ch. 10) précède la planification (ch. 11), et la décision
  multi-agents est un chapitre à part (ch. 18) placé **après** la théorie de la décision
  (ch. 16-17) ; en 3e, la planification (ch. 10-11) précède la représentation (ch. 12), et
  les jeux vivent dans le bloc recherche (ch. 5) — la décision multi-agents n'y est qu'une
  sous-section du ch. 17. La position de la **théorie de la décision** (après les modèles
  graphiques, avant le multi-agents) est en revanche **identique dans les deux éditions** —
  c'est elle que le réordonnacement de ce parcours vient rétablir.

## Ce que chaque étape suppose — règle de lecture

Chaque phase énonce ses **prérequis amont** (phases précédentes du parcours) ; le critère de
succès de l'EPIC — « un apprenant qui suit le parcours dans l'ordre peut compléter chacun des
notebooks référencés avec ses prérequis satisfaits » — se vérifie **notebook par notebook** :
si une étape exige un environnement absent de la table des prérequis vérifiables, c'est un
défaut de ce parcours, pas de l'apprenant.

## Sources — ce parcours recolle, il ne réinvente pas

La structure « Phase N — Titre (notebooks, durée) » généralise [`GameTheory/README.md`](../../MyIA.AI.Notebooks/GameTheory/README.md)
(embryon #1 de [`2026-09-02-curriculum-inventory.md`](../transients/2026-09-02-curriculum-inventory.md)) ; la clause de prérequis explicite reprend sa formulation
(embryon #7 pour les compagnons Lean) ; l'index multi-stack ML sert d'aiguillage (embryon
#3) ; [`Search/README.md`](../../MyIA.AI.Notebooks/Search/README.md) est la structure socle des phases 1-3 (embryon #15) ; l'annexe
probabiliste PyMC est l'embryon #5. Inventaire complet des embryons :
[`2026-09-02-curriculum-inventory.md`](../transients/2026-09-02-curriculum-inventory.md) (Phase 0 de l'EPIC #13844).

*Hors périmètre de ce fichier (cf #15807) : moteur Quarto (#10921), outillage de génération
de parcours (#14620), réécriture de [`PARCOURS.md`](../../PARCOURS.md) (Phase 3, après les trois pilotes).*
