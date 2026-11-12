# Inventaire de parité — séries parallèles hors DecisionTheory (tranche P2 de #12933)

> **État mesuré au 2026-10-28** sur `origin/main` `2cd7d14e1443e54a2612c01ddb4aa1eedae5dd31`.
> Méthode : énumération `find` des `.ipynb` hors `*_output.ipynb` dans `MyIA.AI.Notebooks/{Search,Sudoku,GameTheory,Probas,SymbolicAI/SemanticWeb,SymbolicAI/Planners}`, croisement avec le registre `scripts/notebook_tools/twin_pairs.d/*.yaml` sur les champs `python:`/`csharp:` (une mention en prose `known_differences` ne compte pas comme entrée — vérifié sur contre-exemples). Lecture Swift en volume, puis **recoupement lane sur les pivots** : cas de calibrage `App-9`/`App-10` (entrées registre lues), cinq trous registre (grep NONE re-vérifié).
> **Périmètre complet, en un endroit** : `.ipynb` hors `*_output.ipynb` — récursif dans `Search/` (Part1–Part5), `Sudoku/`, `GameTheory/` (racine + `Dynamics/` + `SocialChoice/`), `SymbolicAI/SemanticWeb/` et `SymbolicAI/Planners/` (**sous-dossiers compris** — la racine de Planners ne porte aucun carnet, contrairement aux autres familles énumérées au niveau racine) ; les familles sans paire (`Dynamics/`, `Search/Part4`, `Part5`) sont listées §4, les célibataires §4. Totaux **recomptés** depuis la table par paires : **110 paires mesurées** = 106 alignées + 0 compagnon-b + 2 décalées-numéro + 2 décalées-titre (classes disjointes, table §1) ; en canoniques au sens du scan (alignées + compagnon-b documentés) : **106**. *Etat mesuré au 2026-11-08 : les 14 compagnon-b de Search/Part3 (13 du relevé initial + App-34, paire enregistrée mais ratée par le relevé du 31/10) ont été alignées par renommage (#25341) ; les 6 restantes (SemanticWeb) sont alignées par le renommage #25325 intégré à la présente fusion (companions SW-0Nb vers SW-0N).*
> **Aucun renommage effectué.** Aucune édition du registre (tranche P0bis #22701 distincte). Cet inventaire est la mesure qui alimente l'arbitrage de mapping de l'EPIC — les recommandations de renommage sont **non livrées** (§6).
>
> Part of #12933. Périmètre : familles **sans fichier d'inventaire** — Search (Part1/Part2/Part3), Sudoku, GameTheory (racine + SocialChoice), SemanticWeb, Planners = **109 paires**. Probas Infer⇄PyMC et DecisionTheory ont leurs inventaires propres (§7).

> **Actualisation** : la paire Safe Subgame Solving est désormais enregistrée et ses deux variantes portent `13b`. Le tableau ci-dessous conserve la mesure historique.

## 1. Table de verdicts par famille

Vocabulaire aligné sur l'EPIC : `alignée` (même numéro complet et titre base, seuls les suffixes kernels varient) · `compagnon-b` (la seule différence d'identifiant est un `b`/`c` porté par un seul côté — forme documentée légitime par `_schema.yaml` `numbering_exception`, mais **décalée au sens strict de la doctrine**) · `décalée-numéro` (numéros divergents autrement) · `décalée-titre` (même numéro, titres base différents) · `extension unilatérale` (célibataires, §4). `fausse paire` : aucune détectée dans le périmètre.

| Famille | Paires | alignée | compagnon-b | décalée-numéro | décalée-titre | sans entrée registre |
|---|---|---|---|---|---|---|
| Search/Part1-Foundations | 15 | 15 | 0 | 0 | 0 | 0 |
| Search/Part2-CSP | 9 | 9 | 0 | 0 | 0 | 0 |
| Search/Part3-Cas-pratiques | 21 | 19 | 0 | 1 | 1 | 0 (membres de trios hors registre, nommés au §3) |
| Sudoku | 16 | 16 | 0 | 0 | 0 | 0 |
| GameTheory (racine) | 25 | 23 | 0 | 1 | 1 | 3 |
| GameTheory/SocialChoice | 4 | 4 | 0 | 0 | 0 | 0 |
| SymbolicAI/SemanticWeb | 11 | 11 | 0 | 0 | 0 | 0 |
| SymbolicAI/Planners | 9 | 9 | 0 | 0 | 0 | 0 |
| **Total (hors Probas/DT)** | **110** | **106** | **0** | **2** | **2** | **3** (+membres de trios) |

### Search/Part1-Foundations — 15 paires, toutes alignées, toutes enregistrées

`Search-01-StateSpace` ↔ `-CSharp` · `02-Uninformed` · `02b-NetworkX` (b des deux côtés) · `03-Informed` · `03b-PatternDatabases` · `03c-LimitedDiscrepancySearch` · `03d-WeightedAstar` · `04-LocalSearch` · `05-GeneticAlgorithms` · `06-AdversarialSearch` · `07-MCTS-And-Beyond` · `08-DancingLinks` · `09-LinearProgramming` · `10-SymbolicAutomata` · `11-Metaheuristics`.

Note registre : `03b`/`03c`/`03d` sont enregistrées sous les numéros historiques `search-12/13/14` (mapping par chemin vérifié, numéro de fichier ≠ numéro d'entrée).

### Search/Part2-CSP — 9 paires, toutes alignées, toutes enregistrées

`CSP-1-Fundamentals` à `CSP-9-Distributed`, chaque `CSP-N` ↔ `CSP-N-CSharp`.

### Search/Part3-Cas-pratiques — 21 paires, 19 alignées, 2 décalées, toutes enregistrées

| Paire | Verdict |
|---|---|
| `App-05-Timetabling-Python` ↔ `App-05-Timetabling-CSharp` | alignée |
| `App-06-Minesweeper-Python` ↔ `App-6-…-CSharp` | alignée |
| `App-08-MiniZinc-Python` ↔ `App-8-…-CSharp` | alignée |
| `App-16-Crossword-CSP-Python` ↔ `App-16-…-CSharp` | alignée |
| `App-19-ProceduralGeneration-WFC-Python` ↔ `App-19-…-CSharp` | alignée |
| `App-01-NQueens-Python` ↔ `App-1-…-CSharp` | alignée (ex-compagnon-b) |
| `App-02-GraphColoring-Python` ↔ `App-2-…-CSharp` | alignée (ex-compagnon-b) |
| `App-03-NurseScheduling-Python` ↔ `App-3-…-CSharp` | alignée (ex-compagnon-b) |
| `App-04-JobShopScheduling-Python` ↔ `App-4-…-CSharp` | alignée (ex-compagnon-b) |
| `App-07-Wordle-Python` ↔ `App-7-…-CSharp` | alignée (ex-compagnon-b) |
| `App-09-EdgeDetection-Python` ↔ `App-9-…-CSharp` | alignée (ex-compagnon-b ; cas de calibrage, entrée registre lue par la lane) |
| `App-10-Portfolio-Python` ↔ `App-10-…-CSharp` | alignée (ex-compagnon-b ; cas de calibrage) |
| `App-11-Picross-Python` ↔ `App-11-…-CSharp` | alignée (ex-compagnon-b) |
| `App-13-TSP-Metaheuristics-Python` ↔ `App-13-…-CSharp` | alignée (ex-compagnon-b) |
| `App-15-SportsScheduling-Python` ↔ `App-15-…-CSharp` | alignée (ex-compagnon-b) |
| `App-17-VRP-Logistics-Python` ↔ `App-17-…-CSharp` | alignée (ex-compagnon-b ; trio : `App-17-VRP-Logistics-Metaheuristiques-Python` hors registre, §3) |
| `App-20-SudokuBenchmark-Python` ↔ `App-20-…-CSharp` | alignée (ex-compagnon-b ; suffixes kernels explicites des deux côtés) |
| `App-12b-ConnectFour-Python` ↔ `App-12c-ConnectFour-CSharp` | décalée-numéro (12b↔12c, aucun suffixe kernel, pas de base App-12) |
| `App-14-ConnectFour-Adversarial-Python` ↔ `App-14-ConnectFour-CSharp` | décalée-titre (« Adversarial » côté Python seulement) |
| `App-18-HyperparameterTuning-Python` ↔ `App-18-…-CSharp` | alignée (ex-compagnon-b ; quatuor : `App-18-HyperparameterTuning-Implementation-Manuelle-Python` hors registre, §3) |
| `App-34-15Puzzle-Admissible-Astar-Python` ↔ `App-34-…-CSharp` | alignée (ex-compagnon-b ; Python ajouté le 2026-10-30 #21756, entrée registre `app-34` — **ratée par le relevé du 31/10**, qui la comptait célibataire §4) |

> Etat mesure au 2026-11-08 : les 14 compagnon-b ci-dessus (13 du relevé initial + App-34, ratée dudit relevé) sont devenues alignées par renommage **#25341** (le `b` d'accrétion est retiré du côté CSharp — trio App-17 et quatuor App-18 : retiré des **deux** membres, l'extension kernel-tierce `App-18c` restant inchangée). Historique complet : `docs/reference/rename-ledger.tsv`.

### Sudoku — 16 paires, toutes alignées, toutes enregistrées

`Sudoku-01-Backtracking` à `Sudoku-15-Infer` et `Sudoku-18-Comparison`, chaque `Sudoku-N-…-Python` ↔ `Sudoku-N-…-CSharp` (suffixe kernel explicite des deux côtés, convention la plus régulière du dépôt). Le n° 16 Python (`Sudoku-16-NeuralNetwork`) est célibataire (§4), le n° 17 aussi (LLM) ; `Sudoku-19` est Lean-only.

### GameTheory (racine) — 25 paires, 23 alignées, 1 décalée-numéro, 1 décalée-titre, 3 sans entrée registre

Paires alignées enregistrées : `02-NormalForm` (+ `02-NormalForm-Part2`, Part2 des deux côtés) · `02c-Travelers-Dilemma` (c des deux) · `03-Topology2x2` · `04-NashEquilibrium` · `04c-NashExistence` · `05-ZeroSum-Minimax` · `06-EvolutionTrust` · `06c-RepeatedGames-FolkTheorem` · `07-ExtensiveForm` · `08-CombinatorialGames` (+ `08c`, c des deux) · `09-BackwardInduction` · `10-ForwardInduction-SPE` · `11-BayesianGames` · `12-ReputationGames` · `13-ImperfectInfo-CFR` · `14-DifferentialGames` · `15-CooperativeGames` (+ `15c`, c des deux) · `16-MechanismDesign` · `17-MultiAgent-RL` — chaque paire `…-Python` ↔ `…-CSharp`.

| Paire | Verdict | Registre |
|---|---|---|
| `GameTheory-06f-Bounded-Agents-Python` ↔ `…-Lean` | alignée (suffixes Python/Lean) | **sans entrée** (grep NONE, re-vérifié) |
| `GameTheory-13b-Safe-Subgame-Solving-Python` ↔ `GameTheory-13c-Safe-Subgame-Solving-CSharp` | **décalée-numéro** (13b↔13c, même titre base, lettres d'accrétion différentes de part et d'autre — même forme que `App-12b`↔`App-12c`) | **sans entrée** (grep NONE des deux côtés, re-vérifié) |
| `GameTheory-16f-Lean-Assignment-Lean` ↔ `GameTheory-16f-Munkres-Assignment-Python` | **décalée-titre** (même 16f, titres Lean-Assignment vs Munkres-Assignment) | **sans entrée** (grep NONE, re-vérifié) |

Cas limite documenté : la quasi-paire `13b`↔`13c` ci-dessus — **deux célibataires de même titre base** dont les lettres d'accrétion diffèrent (`13b` côté Python, `13c` côté CSharp ; il n'existe ni `13c-Python` ni `13b-CSharp` dans l'arbre, mesuré). L'inventaire la mesure comme décalée-numéro ; la promouvoir en paire alignée (par renommage d'un côté) est une décision de mapping qui revient à l'EPIC (§6), l'inventaire ne la préjuge pas.

### GameTheory/SocialChoice — 4 paires, toutes alignées, toutes enregistrées

`01-Arrow-Impossibility-Theorem` · `02-Stable-Marriage-Gale-Shapley` · `03-Voting-Methods` · `04-Computational-Aggregation-SAT-Z3`, chaque `NN-…` ↔ `NN-…-Csharp`. **Note de graphie** : suffixe local `-Csharp` (casse différente du `-CSharp` canonique du reste du dépôt).

### SymbolicAI/SemanticWeb — 11 paires, 11 alignées, toutes enregistrées

> Alignées le 2026-11-08 (issue #25325, lane `myia-po-2023:CoursIA`) : les 6 compagnon-b `SW-0Nb` ont pris le numéro de leur jumeau C# avec suffixe kernel explicite (`SW-02b-RDFBasics-Python` → `SW-02-RDFBasics-Python`, etc.) — doctrine #12933, même concept ⇒ même numéro.

Convention locale : suffixe kernel en **position finale** pour les fondations (`SW-0N-<Titre>-CSharp` / `SW-0N-<Titre>-Python`, alignement #25325) ; exception SW-11, suffixe en position médiane (`SW-11-CSharp/Python-KnowledgeGraphs`).

| Paire | Verdict |
|---|---|
| `SW-02-RDFBasics-CSharp` ↔ `SW-02-RDFBasics-Python` | alignée |
| `SW-03-GraphOperations-CSharp` ↔ `SW-03-GraphOperations-Python` | compagnon-b |
| `SW-04-SPARQL-CSharp` ↔ `SW-04-SPARQL-Python` | alignée |
| `SW-05-LinkedData-CSharp` ↔ `SW-05-LinkedData-Python` | compagnon-b |
| `SW-06-RDFS-CSharp` ↔ `SW-06-RDFS-Python` | alignée |
| `SW-07-OWL-CSharp` ↔ `SW-07-OWL-Python` | alignée |
| `SW-08-SHACL-CSharp` ↔ `SW-08-SHACL-Python` | alignée |
| `SW-09-JSONLD-CSharp` ↔ `SW-09-JSONLD-Python` | alignée |
| `SW-10-RDFStar-CSharp` ↔ `SW-10-RDFStar-Python` | alignée |
| `SW-11-CSharp-KnowledgeGraphs` ↔ `SW-11-Python-…` | alignée |
| `SW-13-Reasoners-CSharp` ↔ `SW-13-Reasoners-Python` | alignée (suffixes en position **finale**, incohérence d'ordre de position annotée) |

### SymbolicAI/Planners — 9 paires, toutes alignées, toutes enregistrées (énumération **récursive** des sous-dossiers : la racine ne porte aucun `.ipynb`)

`Planners-01-Introduction-Python` à `Planners-09-HTN-Python`, chaque `Planners-N-…` ↔ `Planners-N-…-Csharp` (suffixe local `-Csharp`, même graphie que SocialChoice).

## 2. Cause structurelle — deux conventions de jumelage coexistent, toutes deux enregistrées

- **Convention suffixe-terminal** : même numéro, même titre, suffixe kernel en fin (`Search-01` ↔ `Search-01-CSharp`). Appliquée intégralement par Sudoku, GameTheory racine, SocialChoice, Planners, Search Part1/Part2, SW-8..13, et par 5 carnets de Part3.
- **Convention compagnon `b`** : le jumeau porte un `b`/`c` d'accrétion que la base n'a pas (`App-N` ↔ `App-Nb-CSharp`, `SW-N` ↔ `SW-Nb-Python`). Documentée **légitime** par `_schema.yaml` (`numbering_exception`) pour Part3 et SW-2..7, donc **attendue** — mais c'est une divergence au sens strict de la doctrine #12933 (« même préfixe, numéro, accrétion et titre ; seul le suffixe varie »), et elle n'est pas interne-cohérente : SW met le `b` côté **Python**, Part3 côté **CSharp**. **Etat au 2026-11-08** : Part3 est **éliminée** (13 paires renommées #25341, b retiré côté CSharp — trios/quatuor : des deux membres) ; SW-2..7 renommées de même (#25325, PR en cours de merge). La convention ne subsiste plus qu'à l'état de trace historique dans le ledger.
- **Trois graphies de suffixe** coexistent : `-CSharp` (canonique), `-Csharp` (SocialChoice, Planners), et la position médiane SW. Relevé, non jugé ici.

## 3. Trous du registre — paires réelles sans entrée `twin_pairs.d` (grep NONE re-vérifié par la lane)

1. `GameTheory-06f-Bounded-Agents` (Python ↔ Lean) — paire alignée, invisible à la garde NUMBERING-DRIFT.
2. `GameTheory-13b-Safe-Subgame-Solving-Python` ↔ `GameTheory-13c-Safe-Subgame-Solving-CSharp` — quasi-paire décalée-numéro (même titre, lettres 13b/13c), invisible à la garde.
3. `GameTheory-16f` (Lean-Assignment ↔ Munkres-Assignment) — quasi-paire même numéro, décalée-titre, invisible.
4. `App-17-VRP-Logistics-Metaheuristiques-Python.ipynb` (ex-`App-17b-…`) et `App-18-HyperparameterTuning-Implementation-Manuelle-Python.ipynb` (ex-`App-18b-…`) — membres Python de trios Part3 présents dans l'arbre, absents de toute entrée (les entrées `app-17`/`app-18` n'enregistrent que la paire Python-base ↔ CSharp-compagnon).

Hors périmètre nominal, même constat : `Probas/Applications/Percolation/Percolation-04-Sharpness-Python.ipynb` + `Percolation-04-Sharpness-Lean.ipynb` — paire même-numéro-même-titre sans entrée (grep NONE).

> **État mesuré au 2026-10-31** (myia-po-2028:CoursIA, #12933 tranche P2ter ; la liste ci-dessus est conservée telle que mesurée par P2 au 2026-10-28) :
>
> - **Trou 1 (GT-06f) — consommé par la consolidation #20316** : `GameTheory-06f-Bounded-Agents-{Python,Lean}.ipynb` ont été déplacés par #22177 (T3'a, descente du tier 06 dans `Dynamics/`) ; plus aucun fichier à ce chemin à `main` (`git log --diff-filter=D` mesuré). La paire relocalisée est Python ↔ Lean, hors schéma `python:`/`csharp:` du registre.
> - **Trou 3 (GT-16f) — consommé par la consolidation #20316** : les deux carnets `GameTheory-16f-*.ipynb` ont été supprimés par #22742 (T5a, sous-série Coalitions) ; le contenu Munkres vit désormais dans `Coalitions/Coalitions-04-Munkres-Affectation-Python.ipynb` + le lake `assignment_lean/Assignment/KuhnMunkres.lean`.
> - **Trou 2 (GT-13b↔13c) — enregistré à cette date** : entrée `twin_pairs.d/gametheory-13b-safe-subgame-solving.yaml` (+ audit file-per-audit), `parity_level: semantic`, divergence d'accrétion b/c portée par `numbering_exception` documentée — l'alignement des lettres reste une décision de mapping (§6).
> - **Trou 4 (App-17b/18b-Python) — HORS SCHÉMA DU REGISTRE, mesuré le 2026-10-31** : l'enregistrement d'une paire « 17b-Python ↔ 17b-CSharp » a été tenté puis **retiré** — le carnet CSharp `App-17b-VRP-Logistics-CSharp.ipynb` est déjà le membre `csharp:` de l'entrée `app-17` existante (idem `App-18b-…-CSharp` côté `app-18`), et le test d'intégrité `test_twin_registry_integrity.py::test_no_duplicate_notebook_paths` **rougit sur tout enregistrement qui duplique un carnet** (mesuré firsthand sur la PR). Le registre n'admet qu'une entrée par carnet : **le trio Part3 est structurellement inexprimable dans le schéma actuel** (une entrée = exactement 2 carnets `python:` + `csharp:`). Le membre Python de chaque trio reste documenté **en prose** — forme que l'entrée `app-17` pratique déjà (« App-17b-Python (vrai twin from-scratch) n'est PAS dans ce registre, gap pré-existant »). Étendre le schéma aux paires n-aires (trios) est une décision qui revient à l'arbitrage de l'EPIC (§6), jamais préjugée ici. Divergences mesurées pendant la tentative (conservées ici pour l'arbitrage) : côté 18b, CV **3-fold (Python)** vs **5-fold (CSharp)** et asymétrie de machinerie (Python from-scratch numpy, CSharp `Microsoft.ML` + `Microsoft.ML.AutoML` importé) ; côté 17b, import OR-Tools mesuré des deux côtés à côté des tranches from-scratch.
> - **Percolation-04 — hors schéma du registre** (paire Python ↔ Lean), le constat P2 demeure.

## 4. Extensions unilatérales (célibataires) — grep registre NONE sauf mention

- **Search/Part1** : `Search-02c-QuikGraph`, `03e-AStar-Optimality`, `03f-Reparer-Localement-Sous-Garantie-Python`, `05b-NaturalEvolutionStrategies`, `09b-SpuriousMinima`, `09c-CombinatorialDiscrepancy`, `09d-BeckFiala-Lean-Python`, `09e-Komlos-Lean`, `09f-ConvexOptimisation-Python`, `11b-Metaheuristiques-Deep` (+Part2/3/4), `11c`, `11d`, `12a-Composer-Regards`, `13a-Traverser-Murs-Certifies`.
- **Search/Part3** : `App-02-GraphColoring-Statistical-Validity-Python`, `App-17-VRP-Logistics-Metaheuristiques-Python` (ex-17b), `App-18-HyperparameterTuning-Implementation-Manuelle-Python` (ex-18b), `App-18c-HyperparameterTuning-Rustuna-vs-Optuna-Python`, `App-21-VoiceLeading-Python`, `App-22-AlgorithmSelection-Python`, `App-23-PRESENT-Differential-Cryptanalysis-SAT-Python`, `App-27-Sparse-Index-Tracking-Walk-Forward-Python`. *(Corrigé le 2026-11-08 : `App-34b-…-CSharp` n'est plus célibataire — le Python 34 ajouté le 2026-10-30 #21756 forme avec lui la paire enregistrée `app-34`, alignée par #25341.)*
- **Sudoku** : `Sudoku-00-Environment-CSharp` (setup, cité en prose dans `sudoku-02-dancinglinks.yaml`), `Sudoku-12b-Z3-Linq2Z3-CSharp`, `Sudoku-16-NeuralNetwork-Python`, `Sudoku-17-LLM-Python`, `Sudoku-18b-Statistical-Comparison-Python`, `Sudoku-19-Lean-Propagation-Lean`.
- **GameTheory racine** : `01-Setup-Python` ; compagnons Lean `02b-Lean-Definitions`, `04b`, `05b`, `06b/06d–06k`, `08b`, `08d`, `11b`, `15b`, `16b–16k` (hors `16f` pairé §1), `17c`, `17d` ; Python `02e`, `03b–03f`, `04d–04j`, `05c`, `06e`, `09b–09d`, `11d`, `13d–13h`, `15d–15g`, `17e/17f`, `18/18b/18c`, `19/19b`, `20/20b/20c`, `21` ; `02d` (cité en prose dans `gametheory-2-normalform.yaml`) ; `gateway/openspiel-cfr-service.ipynb`.
- **SocialChoice** : `01b-Lean-SocialChoice-Formal`, `05` à `10` (Python).
- **SemanticWeb** : `SW-01-Setup-CSharp`, `SW-12-GraphRAG-Python`, `SW-14-Coup-Ontologique-Python`, `SW-15-Coup-Argumentatif-Python`, `SW-16-ProofCarryingOntologies-Python` ; `RDF.Net-Legacy/RDF.Net.ipynb`.
- **Planners** : `Planners-00-Setup-Python`, `5b-Lean-Relaxation` et `10–12` (exclus explicitement dans `_schema.yaml`), `5c`, `Planners-13-Mesure-Qualite-Plans-Python` (cité en prose dans `planners-9-htn.yaml`).

Familles du périmètre **sans aucune paire** : `GameTheory/Dynamics/` (1 carnet Python), `Search/Part4-Metaheuristics` et `Part5-Frontieres` (séries MGS/Frontieres sans jumeaux inter-kernels).

## 5. Ce que la garde voit et ne voit pas

`check_twin_parity.py` ne couvre que les paires **enregistrées** : les 3 trous du §3 et les 2 célibataires de trios Part3 lui sont invisibles par construction. À l'inverse, les 19 compagnon-b et 2 décalées Part3 enregistrées ne sont pas des anomalies pour la garde (exception documentée) — c'est la doctrine #12933 qui les appelle décalées. Les deux lectures sont cohérentes : le registre décrit l'état, la doctrine décrit la cible.

## 6. Recommandations de mapping — NON LIVRÉES

Conformément au format P0, les recommandations de renommage (aligner les 19 compagnon-b, trancher App-12b/12c, App-14, GT-16f, GT-13b-vs-13c, compléter le registre sur les 3 trous + 2 trios, unifier les graphies de suffixe) sont **renvoyées à l'arbitrage de l'EPIC** : chaque renommage est un cycle atomique par famille (P2 : « une PR ne renumérote qu'une famille ») et doit être précédé d'une décision de mapping explicite.

## 7. Périmètres couverts par les inventaires existants

- **Probas Infer⇄PyMC** (19 paires mesurées) : `MyIA.AI.Notebooks/Probas/PARITY-INVENTORY.md` (tranche P1, PR #18795) — non recopié ici ; le scan P2 le reconfirme à l'identique (18 alignées, 1 décalée-titre `02b`, trou symétrique n° 6, extensions unilatérales `Infer-01b`, `Infer-08b`, `PyMC-Observabilite-OTel`).
- **DecisionTheory** : `MyIA.AI.Notebooks/Probas/DecisionTheory/PARITY-INVENTORY.md` (tranche P0) + enregistrement P0bis `dt-*` (PR #22701).
