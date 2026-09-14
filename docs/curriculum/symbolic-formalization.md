<!--
  FICHIER MANUEL — parcours narratif écrit à la main, PAS un artefact du
  catalogue. scripts/notebook_tools/generate_parcours.py n'écrit que les
  5 pages catalogue (genai.md, ia-classique.md, ia-symbolique.md,
  trading.md, recherche.md) ; ce fichier suit la convention des pages
  manuelles (comme _inventory.md, hors de la liste du générateur et du cron
  catalog-cron.yml — le nom n'est AUCUN des cinq ids) et n'est jamais
  régénéré. Cf EPIC #13844 Phase 2 (pilote 2) et #15806.
-->

# IA Symbolique et Formalisation (~20 h)

Deuxième des trois parcours narratifs pilotes de l'EPIC #13844 (Phase 2). Sa
matière première est l'inventaire des embryons livré en Phase 0
([_inventory.md](_inventory.md), entrées #8-14 et #35) ; sa forme généralise
les « Parcours alternatifs » de GameTheory
([README](../../MyIA.AI.Notebooks/GameTheory/README.md) : durée annoncée,
liste numérotée, clause de prérequis explicite) et sa rampe Lean reprend le
modèle le plus progressif du dépôt
([LEAN_PREREQUISITES.md](../../MyIA.AI.Notebooks/GameTheory/social_choice_lean/LEAN_PREREQUISITES.md),
trois niveaux nommés). La page catalogue
([ia-symbolique.md](ia-symbolique.md)) reste en place comme filet
alphabétique : elle dit *ce qui existe* (27 + 49 + 25 + … notebooks) ; ce
parcours dit *dans quel ordre le faire*.

**Le fil — « du symbole à la preuve ».** Un même objet (un argument, une
contrainte, un plan) est traversé **deux fois** : d'abord *résolu* par un
moteur (Tweety, Z3, Fast-Downward), puis *certifié* par une preuve formelle.
Les trois companions Lean du bloc final reprennent chacun un livrable d'un
bloc antérieur — l'argumentation de Dung de l'étape 5, la relaxation heuristique
de l'étape 22, la synthèse stable de l'étape 13 — et le prouvent : c'est
l'arc pédagogique du parcours, pas une collection de séries indépendantes.

**Public visé** — l'étudiant·e ou l'ingénieur·e qui connaît Python et un peu de
logique classique, et veut passer du symbolique « qui marche » à la
formalisation dont la correction est vérifiée par une machine.

## Prérequis vérifiables (~10 minutes)

| À vérifier | Comment | Succès attendu |
|---|---|---|
| Python 3.10+ | `python --version` | `Python 3.10` ou plus |
| Jupyter | `jupyter --version` (ou l'extension Jupyter de VS Code) | une version s'affiche, sans erreur |
| ~2 Go libres | — | JARs Tweety (42), fast-downward, toolchain Lean (bloc 4) |
| WSL2 + elan **(bloc 4 seulement)** | `wsl --status` puis, dans WSL, `elan show` | une toolchain `stable` s'affiche |
| Clé OpenAI **(aucune)** | — | ce parcours n'appelle AUCUNE API payante |

Les blocs 1-3 tournent sur Python seul (Tweety-1 télécharge et configure lui-même
le JDK Zulu et les JARs ; Z3 et fast-downward s'installent par pip). Le bloc 4
exige WSL2 + elan — vérifiable en 2 minutes, et TOUJOURS installable
(voir [kernels-runtime](../../docs/reference/kernels-runtime.md)).

Clause de prérequis — ce qui est supposé, et ce qui ne l'est pas :

> Ce parcours suppose une pratique élémentaire de Python (boucles, fonctions,
> dictionnaires) et la logique classique de première année (connecteurs,
> quantificateurs) — et **rien d'autre** : ni Lean, ni Java préinstallé, ni
> Docker, ni théorie des modèles. Chaque formalisme est introduit en route.
> Les jumeaux C# (`*-Csharp.ipynb`) des séries Tweety/Planners/SMT sont des
> **variantes**, pas des étapes : le parcours se fait intégralement côté
> Python. Seule la rampe NNG (bloc 4) se joue dans un navigateur.

## Durée estimée — et pourquoi elle est défendable

Chaque étape porte la `duree_estimee` du catalogue
(`COURSE_CATALOG.generated.json`). Somme sur les 29 étapes :

| Bloc | Étapes | Durée catalogue |
|---|---|---|
| 1 — Argumentation (Tweety) | 1-10 | 6 h 00 |
| 2 — Décision SMT (Z3) | 11-18 | 3 h 45 |
| 3 — Planification (Planners) | 19-25 | 4 h 45 |
| 4 — Le verrou de rigueur (Lean) | 26-29 | 1 h 45 |
| **Total colonne vertébrale** | | **16 h 15** |

Deux comptes plutôt qu'un chiffre flottant : (a) la colonne vertébrale totalise
**16 h 15** au catalogue ; (b) le bloc 4 suppose la rampe d'entrée du
« Parcours 1 — Débutant » de LEAN_PREREQUISITES, dont le
[Descriptif](../../MyIA.AI.Notebooks/GameTheory/social_choice_lean/LEAN_PREREQUISITES.md)
chiffre le minimum jouable — le *Natural Number Game* — à **3-4 h** (le parcours
débutant complet, lecture seule, est chiffré 18-22 h et reste une extension,
pas un prérequis). Colonne vertébrale + rampe NNG : **19 h 15 – 20 h 15**,
d'où la fenêtre **~20 h** du titre. Le rythme « ~6 mois » de l'inventaire
(_inventory.md:131) est un **espacement**, pas une durée : ~2 étapes par
semaine en travaillant sérieusement les exercices.

## Sortie concrète

À la fin du parcours, vous avez **exécuté** :

- quatre familles logiques en Tweety (propositionnelle/FOL, descriptions,
  révision AGM) et les sémantiques de Dung jusqu'à ASPIC+ (bloc 1) ;
- des problèmes SAT/SMT par Z3 — Sudoku, tactiques, quantificateurs, cœurs
  insatisfaisables — et un capstone d'optimisation (Meal Planner) (bloc 2) ;
- un plan PDDL exécuté par Fast-Downward, des heuristiques h-add, et le même
  problème en CP-SAT/OR-Tools (bloc 3) ;
- **trois preuves Lean 4 rejouées** : l'argumentation abstraite certifiée
  (Tweety-5b), la relaxation h-add formalisée (Planners-5b), la synthèse
  d'extensions stables Z3 → Lean (Tweety-5d) — la boucle « résolu puis prouvé »
  refermée sur vos propres livrables des blocs 1-3 (bloc 4).

## Colonne vertébrale — 29 étapes

Chaque ligne : **apporte** (ce que l'étape ajoute) → **suppose** (ce qui doit
être acquis avant). Les durées sont celles du catalogue.

### Bloc 1 — Argumentation (Tweety, étapes 1-10, 6 h)

Reprend le découpage en phases du
[README Tweety](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/README.md) (le cœur
est la Phase 3, argumentation).

| # | Notebook | Durée | Apporte → Suppose |
|---|---|---|---|
| 1 | [Tweety-1-Setup](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-1-Setup.ipynb) | 45 min | JDK + 42 JARs + solveurs externes auto-installés → rien |
| 2 | [Tweety-2-Basic-Logics](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-2-Basic-Logics.ipynb) | 45 min | PL, SAT (pySAT), FOL → étape 1 |
| 3 | [Tweety-3-Advanced-Logics](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-3-Advanced-Logics.ipynb) | 45 min | logiques de description, modale, QBF → étape 2 |
| 4 | [Tweety-4-Belief-Revision](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-4-Belief-Revision.ipynb) | 30 min | MUS, mesure d'incohérence, révision AGM, MaxSAT → étape 2 |
| 5 | [Tweety-5-Abstract-Argumentation](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-5-Abstract-Argumentation.ipynb) | 45 min | **cœur** : sémantiques de Dung (grounded, preferred, stable) → étapes 2-4 |
| 6 | [Tweety-6-Structured-Argumentation](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-6-Structured-Argumentation.ipynb) | 30 min | ASPIC+, DeLP, ABA, ASP (Clingo) → étape 5 |
| 7 | [Tweety-7a-Extended-Frameworks](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-7a-Extended-Frameworks.ipynb) | 30 min | ADF, bipolaire, WAF, attaques récursives → étape 5 |
| 8 | [Tweety-7b-Ranking-Probabilistic](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-7b-Ranking-Probabilistic.ipynb) | 30 min | classement et probabilités sur arguments → étape 5 |
| 9 | [Tweety-8-Agent-Dialogues](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-8-Agent-Dialogues.ipynb) | 30 min | protocoles de dialogue, jeux grounded → étape 6 |
| 10 | [Tweety-9-Preferences](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-9-Preferences.ipynb) | 30 min | préférences, vote (Borda, Condorcet) → étape 6 |

### Bloc 2 — Décision automatique : SMT (Z3, étapes 11-18, 3 h 45)

La passerelle industrielle du bloc 1 : les mêmes questions de satisfaisabilité,
dans un solveur SOTA (Microsoft Research). Sélection dans la série
[Z3-API](../../MyIA.AI.Notebooks/SymbolicAI/SMT/) — les étapes non listées
(Einstein, cryptarithmes, bit-vectors…) sont des entraînements libres.

| # | Notebook | Durée | Apporte → Suppose |
|---|---|---|---|
| 11 | [Z3-Python-01-Introduction](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/Z3-Python-01-Introduction.ipynb) | 30 min | z3-py, premier solve/check → logique PL (étape 2) |
| 12 | [Z3-Python-02-Sudoku](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/Z3-Python-02-Sudoku.ipynb) | 15 min | modélisation contraintes d'un puzzle → étape 11 |
| 13 | [Z3-Python-03-Tactics](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/Z3-Python-03-Tactics.ipynb) | 30 min | tactiques, simplify, contrôler le solveur → étape 11 |
| 14 | [Z3-Python-04-Strings-Regex](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/Z3-Python-04-Strings-Regex.ipynb) | 30 min | théorie des chaînes et regex symboliques → étape 11 |
| 15 | [Z3-Python-05-Quantifiers-Proofs](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/Z3-Python-05-Quantifiers-Proofs.ipynb) | 30 min | quantificateurs, **preuves** — vers le bloc 4 → étape 2 (FOL) |
| 16 | [Z3-Python-06-Advanced-Optimization](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/Z3-Python-06-Advanced-Optimization.ipynb) | 30 min | Optimize, soft constraints → étape 13 |
| 17 | [Z3-Python-13-UnsatCores](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/Z3-Python-13-UnsatCores.ipynb) | 30 min | cœurs insatisfaisables — écho des MUS de l'étape 4 → étape 4 |
| 18 | [Z3-Python-16-Meal-Planner](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/Z3-Python-16-Meal-Planner.ipynb) | 30 min | **capstone** : optimisation sous contraintes réelles → étapes 12+16 |

### Bloc 3 — Planification (étapes 19-25, 4 h 45)

Du *dire* au *faire* : la planification automatique classique
([Planners](../../MyIA.AI.Notebooks/SymbolicAI/Planners/)), du PDDL à
OR-Tools. L'étape 22 (heuristiques) est celle que le bloc 4 certifiera.

| # | Notebook | Durée | Apporte → Suppose |
|---|---|---|---|
| 19 | [Planners-0-Setup](../../MyIA.AI.Notebooks/SymbolicAI/Planners/00-Environment/Planners-0-Setup.ipynb) | 30 min | environnements + fast-downward local → rien |
| 20 | [Planners-2-PDDL-Basics](../../MyIA.AI.Notebooks/SymbolicAI/Planners/01-Foundation/Planners-2-PDDL-Basics.ipynb) | 30 min | domaine/problème PDDL → étape 19 |
| 21 | [Planners-3-State-Space](../../MyIA.AI.Notebooks/SymbolicAI/Planners/01-Foundation/Planners-3-State-Space.ipynb) | 45 min | espaces d'états, recherche → étape 20 |
| 22 | [Planners-4-Fast-Downward](../../MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/Planners-4-Fast-Downward.ipynb) | 45 min | le solveur SOTA de planification → étape 21 |
| 23 | [Planners-5-Heuristics](../../MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/Planners-5-Heuristics.ipynb) | 45 min | h-add, h-max, relaxation — **objet du companion 28** → étape 22 |
| 24 | [Planners-6-Domains](../../MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/Planners-6-Domains.ipynb) | 45 min | domaines classiques (blocksworld, logistics) → étape 23 |
| 25 | [Planners-7-OR-Tools](../../MyIA.AI.Notebooks/SymbolicAI/Planners/03-Advanced/Planners-7-OR-Tools.ipynb) | 45 min | CP-SAT, le pendant Google → étape 23 |

### Bloc 4 — Le verrou de rigueur : Lean (étapes 26-29, 1 h 45 + rampe)

Le bloc le plus court en heures est le plus dense : trois companions Lean
rejouent en preuve formelle ce que les blocs 1-3 ont *calculé*. La rampe
d'entrée recommandée est le *Natural Number Game* (3-4 h,
[LEAN_PREREQUISITES.md](../../MyIA.AI.Notebooks/GameTheory/social_choice_lean/LEAN_PREREQUISITES.md)
« Parcours 1 — Débutant ») : tactiques `rw`, `apply`, `exact`, `intro`.

| # | Notebook | Durée | Apporte → Suppose |
|---|---|---|---|
| 26 | [Lean-1-Setup](../../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-1-Setup.ipynb) | 30 min | WSL, elan, Mathlib — l'environnement du bloc → WSL2 + elan vérifiés |
| 27 | [Tweety-5b-Lean-Argumentation](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-5b-Lean-Argumentation.ipynb) | 30 min | **Dung prouvé** : le companion 0-sorry de l'étape 5 → rampe NNG + étape 5 |
| 28 | [Planners-5b-Lean-Relaxation](../../MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/Planners-5b-Lean-Relaxation.ipynb) | 15 min | **h-add formalisé** dans `planning_lean` — companion de l'étape 23 → étape 27 |
| 29 | [Tweety-5d-Stable-Synthesis](../../MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-5d-Stable-Synthesis-Lean.ipynb) | 30 min | **Z3 → Lean** : synthèse certifiée d'extensions stables — la boucle bloc 2 ⇄ bloc 4 → étapes 15+27 |

## Portes de sortie (hors colonne vertébrale, citées)

Le parcours déborde volontairement la colonne vertébrale : chaque famille
voisine a son embryon recensé dans [_inventory.md](_inventory.md) et se prend
comme suite naturelle, sans être comptée dans les ~20 h.

- **Web sémantique** (~5 h profil Python) — le
  [README SemanticWeb](../../MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/README.md)
  propose trois profils (Python-only / data engineer / ontologue), modèle
  « qui-suis-je » du dépôt (inventaire #13). Suite logique du bloc 1 (les
  logiques de description de l'étape 3 deviennent OWL).
- **Smart contracts** (8 h Solidity intensif → 22 h complet) — la table
  « Quel parcours choisir » du
  [README SmartContracts](../../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/README.md)
  est le modèle canonique multi-profils (inventaire #14). Suite logique du
  bloc 2 (Foundry, vérification formelle) et du bloc 4 (le companion
  `sensitivity_lean`). Prendre le parcours **parent**, pas les six
  sous-parcours 0X-* qui le répètent (avertissement #111 de l'inventaire).
- **Apprentissage symbolique** (~9 h 30) — le
  [README SymbolicLearning](../../MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/README.md)
  (inventaire #11) : induction, EBL, FOIL, L*, jusqu'au capstone LLM + graphe
  de connaissances. Le pont vers le neuronal.
- **Pont LLM / argumentation** (~4 h) — la série Argument Analysis
  (inventaire #9-10) : détection de sophismes par LLM, formalisation,
  validation Tweety. Suppose le bloc 1 **et** une clé API OpenAI.
- **Choix social** — [SocialChoice](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/README.md)
  (inventaire #35, cinq angles du même résultat dont preuve Lean et SAT-Z3) :
  la suite « recherche » de l'étape 10, dans GameTheory. Sa rampe d'entrée
  Lean est précisément LEAN_PREREQUISITES.
- **Pour aller plus loin en Lean** — les niveaux 2 (Intermédiaire) et 3
  (Avancé) de LEAN_PREREQUISITES, puis la
  [série Lean](../../MyIA.AI.Notebooks/SymbolicAI/Lean/README.md) (49
  notebooks, inventaire #7) : Mathlib, intégration LLM, théorèmes 2026.

## Comment ce parcours a été construit

Sources citées, rien réécrit ex nihilo (critère d'acceptation #13844) : le
découpage du bloc 1 vient du README Tweety (phases 1-5) ; l'ordre d'entrée
« Tweety → SMT → Planners → Lean » est la lecture recommandée du
[README SymbolicAI](../../MyIA.AI.Notebooks/SymbolicAI/README.md) ; la rampe
et les companions du bloc 4 viennent de LEAN_PREREQUISITES et des fiches des
séries concernées ; les durées sont les `duree_estimee` du catalogue, la
fenêtre ~20 h est le compte double colonne vertébrale (16 h 15) + rampe NNG
(3-4 h). Les mêmes embryons sont recensés dans [_inventory.md](_inventory.md)
entrées #8-14, #35.
