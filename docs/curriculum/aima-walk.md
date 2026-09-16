<!--
  FICHIER MANUEL — parcours narratif pilote (EPIC #13844 Phase 2, issue #15807).
  Écrit à la main à partir de docs/curriculum/_inventory.md : contrairement aux
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
prérequis (modèle de la clause de `GameTheory/README.md` §Parcours alternatifs).

## Durée estimée — base mesurée, pas une durée fantôme

Le **noyau mesure 21 h 15** : somme des `duree_estimee` du `COURSE_CATALOG.generated.json`
pour les 29 notebooks cités ci-dessous (le détail par phase porte la somme de ses étapes ;
seule la phase 8, qui renvoie au README de sa série, n'est pas re-chiffrée). Les
**compagnons optionnels** (twins C# des mêmes étapes ≈ +7 h, side-tracks Lean ≈ +3 h)
portent la fourchette à **25-30 h** — fourchette assumée comme telle, conformément au
critère #13844 : l'estimation s'appuie sur le catalogue, pas sur une intuition.

## Sortie concrète

À la fin, vous avez **exécuté** : un A* avec heuristiques pondérées et pattern databases,
un solveur CSP avec propagation de cohérence, un solveur logique Tweety en FOL, un réseau
bayésien PyMC avec inférence causale, un équilibre de Nash calculé, un CFR sur poker
imparfait, un agent RL entraîné, et un pipeline LLM complet (prompting → RAG → raisonnement).
Vous savez surtout **où le corpus dépasse AIMA** (théorie des jeux formelle, IIT,
métaheuristiques composées) — l'épilogue le nomme.

---

## Le fil — AIMA comme ossature, chapitre par chapitre

### Phase 1 — Résoudre des problèmes par la recherche (AIMA ch. 3) — Search-01→03, ~3 h 45

1. **`Search/Part1-Foundations/Search-01-StateSpace.ipynb`** (45 min) — espaces d'états,
   formulation problème/successeurs/but. *Suppose : bases de graphes. Apporte : le vocabulaire
   que toutes les étapes suivantes utilisent.*
2. **`Search-02-Uninformed.ipynb`** (1 h) + **`Search-02b-NetworkX.ipynb`** (45 min) — BFS,
   DFS, coût uniforme, puis la mise en œuvre NetworkX. *Suppose : Phase 1.*
3. **`Search-03-Informed.ipynb`** (45 min) — A*, admissibilité, cohérence.
   **`Search-03e-AStar-Optimality.ipynb`** (30 min) — compagnon formel : l'optimalité d'A*
   relue sur le notebook (cf #13685).

### Phase 2 — Au-delà du classique : recherche locale (AIMA ch. 4) — Search-04→05, ~2 h 15

4. **`Search-04-LocalSearch.ipynb`** (45 min) — hill-climbing, simulated annealing.
5. **`Search-05-GeneticAlgorithms.ipynb`** (1 h) — algorithmes génétiques.
   **`Search/Part4-Metaheuristics/MGS-01-Introduction.ipynb`** (30 min) — ouverture du
   dépôt **au-delà d'AIMA** : métaheuristiques composées (série MetaGeneticSharp).

### Phase 3 — Recherche adversariale (AIMA ch. 5) — Search-06→07, ~1 h 30

6. **`Search-06-AdversarialSearch.ipynb`** (45 min) — minimax, alpha-bêta. *Suppose : arbres
   de jeu, Phase 1.*
7. **`Search-07-MCTS-And-Beyond.ipynb`** (45 min) — Monte-Carlo Tree Search, pont vers le RL
   de la Phase 9.

### Phase 4 — Problèmes de satisfaction de contraintes (AIMA ch. 6) — CSP-1→2, ~1 h 45

8. **`Search/Part2-CSP/CSP-1-Fundamentals.ipynb`** (1 h) — modélisation CSP, backtracking.
9. **`CSP-2-Consistency.ipynb`** (45 min) — AC-3, MRV, forward-checking. *La série continue
   jusqu'à CSP-9 (temporel, distribué) pour qui veut prolonger.*

### Phase 5 — Logique classique (AIMA ch. 7-8) — Tweety, ~2 h 15

10. **`SymbolicAI/Tweety/Tweety-2-Basic-Logics.ipynb`** (45 min) — logique propositionnelle
    avec la bibliothèque Tweety (Java). *Suppose : prérequis 3 (Java).*
11. **`Tweety-2c-FOL-Csharp.ipynb`** (45 min) — logique du premier ordre, twin .NET.
12. **`Tweety-3-Advanced-Logics.ipynb`** (45 min) — logiques non classiques (défaut,
    modales). *Pont : `Tweety-11-Causal.ipynb` pour la jonction avec la Phase 6.*

### Phase 6 — Raisonnement probabiliste (AIMA ch. 12-16) — PyMC, ~1 h

13. **`Probas/PyMC/PyMC-04-Bayesian-Networks.ipynb`** (30 min) — réseaux bayésiens, inférence
    exacte puis MCMC. *Suppose : bases de probabilités.*
14. **`PyMC-05-Causal-Inference.ipynb`** (30 min) — do-calculus, contre-factuels — la
    jonction moderne d'AIMA ch. 16. *Annexe probabiliste : le README PyMC (4 parcours,
    ~10 h) prolonge cette phase (embryon #5 de `_inventory.md`).*

### Phase 7 — Décision multi-agents (AIMA ch. 5 approfondi + théorie des jeux) — GameTheory, ~2 h 30

15. **`GameTheory/GameTheory-02-NormalForm.ipynb`** (45 min) — formes normales, équilibres
    purs et mixtes. *Suppose : Phase 3 (minimax).*
16. **`GameTheory-06-EvolutionTrust.ipynb`** (45 min) — tournoi d'Axelrod, émergence de la
    coopération — la pause narrative du parcours.
17. **`GameTheory-13-ImperfectInfo-CFR.ipynb`** (1 h) — information imparfaite, counterfactual
    regret minimization (poker AI). *Companion formel optionnel :
    `GameTheory-02b-Lean-Definitions.ipynb`* (45 min) — les mêmes définitions en Lean 4
    (embryon #7 : les lacs Lean comme compagnons formels).

### Phase 8 — Planification (AIMA ch. 10-11) — série Planners (durée non chiffrée ici)

18. **`SymbolicAI/Planners/`** — PDDL, STRIPS, planification temporelle et hiérarchique.
    Entrée par le README de la série, dont le parcours existe déjà (embryon #12 de
    `_inventory.md` — il est `INTEGRATE`, donc cité, pas réécrit) ; sa durée se lit dans le
    README de la série, ce parcours ne la re-chiffre pas. *Suppose : Phase 4 (CSP) —
    la planification est un CSP séquencé.*

### Phase 9 — Apprentissage par renforcement (AIMA ch. 21-22) — RL, ~2 h 15

19. **`RL/rl_1_intro_cartpole.ipynb`** (45 min) — MDP, Q-learning, Gymnasium. *Suppose :
    Phase 3 (arbres de décision séquentiels).*
20. **`rl_3_experience_replay_her.ipynb`** (45 min) — replay, HER, stabilité.
21. **`rl_15_grpo_group_relative_policy.ipynb`** (45 min) — policy gradients modernes
    (GRPO) — la jonction explicite avec les LLM de la Phase 10.

### Phase 10 — Langage et LLM (AIMA ch. 23-24, actualisés) — GenAI/Texte, ~2 h 30

22. **`GenAI/Texte/01_OpenAI_Intro.ipynb`** (30 min) + **`02_PromptEngineering.ipynb`**
    (45 min) — API, prompting. *Suppose : prérequis 4 (clé API).*
23. **`05_RAG_Modern.ipynb`** (45 min) — retrieval-augmented generation.
24. **`08_Reasoning_Models.ipynb`** (30 min) — modèles de raisonnement — ce qu'AIMA
    appelait « agents logiques », relu en 2026.

### Épilogue — Où le corpus dépasse AIMA, ~45 min

25. **`IIT/IIT-01-IntroToPyPhi.ipynb`** (45 min) — théorie de l'information intégrée :
    hors AIMA, propre au dépôt. Prolongements nommés : `Search-09d-Lean-Discrepancy-Komlos`
    (recherche **formelle**, compagnon Lean de la phase 2), la série IIT complète (59
    notebooks de la famille la plus dense du dépôt, cf `docs/curriculum/recherche.md`).

---

## Ce que chaque étape suppose — règle de lecture

Chaque phase énonce ses **prérequis amont** (phases précédentes du parcours) ; le critère de
succès de l'EPIC — « un apprenant qui suit le parcours dans l'ordre peut compléter chacun des
notebooks référencés avec ses prérequis satisfaits » — se vérifie **notebook par notebook** :
si une étape exige un environnement absent de la table des prérequis vérifiables, c'est un
défaut de ce parcours, pas de l'apprenant.

## Sources — ce parcours recolle, il ne réinvente pas

La structure « Phase N — Titre (notebooks, durée) » généralise `GameTheory/README.md`
(embryon #1 de `_inventory.md`) ; la clause de prérequis explicite reprend sa formulation
(embryon #7 pour les compagnons Lean) ; l'index multi-stack ML sert d'aiguillage (embryon
#3) ; `Search/README.md` est la structure socle des phases 1-3 (embryon #15) ; l'annexe
probabiliste PyMC est l'embryon #5. Inventaire complet des embryons :
`docs/curriculum/_inventory.md` (Phase 0 de l'EPIC #13844).

*Hors périmètre de ce fichier (cf #15807) : moteur Quarto (#10921), outillage de génération
de parcours (#14620), réécriture de `PARCOURS.md` (Phase 3, après les trois pilotes).*
