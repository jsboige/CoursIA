# Search — Partie 5 : Frontières

[<- Applications (cas pratiques)](../Applications/README.md) | [Partie 4 : Métaheuristiques](../Part4-Metaheuristics/README.md) | [Retour à la série Search](../README.md)

La frontière entre le cours et la recherche : des carnets qui ne traitent pas un problème classique pour l'apprendre — ils **auditent une garantie** (vérifier empiriquement ce qu'un solveur ou un théorème récent autorise réellement à affirmer) ou **distillent un preprint** (rendre opérable un résultat publié). Chaque carnet confronte une affirmation récente à un oracle indépendant, un certificat ou un témoin vérifiable à la main.

Sous-série d'audits et de distillations | Python 3.10+ (`ortools`, `pulp`, `scikit-learn`, `pandas`, `matplotlib`). Les volumes sont portés par le marqueur `CATALOG-STATUS` du [README de la série](../README.md).

## Pourquoi cette partie

La partie est prévue pour dix carnets (`Frontieres-01..10`) ; ce premier lot du séquencement en pose sept
(01 à 06 et 10) — les carnets 07 à 09 (SALBP, assemblage orbital, RCPSP/max) suivent dans le second lot.
Chaque carnet **audite une garantie** (vérifier empiriquement ce qu'un solveur ou un théorème récent
autorise réellement à affirmer) ou **distille un preprint** (rendre opérable un résultat publié), et confronte
une affirmation récente — théorème arXiv, preprint de conception de solveurs, garanties d'un mécanisme d'enchère —
à un oracle indépendant, un certificat ou un témoin vérifiable à la main. La partie porte sa propre numérotation
(`Frontieres-01..10`) ; les critères d'entrée et la délimitation galerie/frontières sont fixés par la carte du
2026-10-05 ([#19253](https://github.com/jsboige/CoursIA/issues/19253), arbitrée sur
[#17802](https://github.com/jsboige/CoursIA/issues/17802)) : la clause « audite une garantie » porte sur ce que
le carnet déclare vouloir établir ; l'hommage commémoratif et l'hommage à un travail étudiant restent en galerie.
(01 à 06 et 10) — les carnets 07 à 09 (SALBP, assemblage orbital, RCPSP/max) suivent dans le second lot. Chaque carnet — ils **auditent une garantie** (vérifier empiriquement ce qu'un solveur ou un théorème récent autorise réellement à affirmer) ou **distillent un preprint** (rendre opérable un résultat publié). Chaque carnet confronte une affirmation récente — théorème arXiv, preprint de conception de solveurs, garanties d'un mécanisme d'enchère — à un oracle indépendant, un certificat ou un témoin vérifiable à la main. La partie porte sa propre numérotation (`Frontieres-01..10`) ; les critères d'entrée et la délimitation galerie/frontières sont fixés par la carte du 2026-10-05 ([#19253](https://github.com/jsboige/CoursIA/issues/19253), arbitrée sur [#17802](https://github.com/jsboige/CoursIA/issues/17802)) : la clause « audite une garantie » porte sur ce que le carnet déclare vouloir établir ; l'hommage commémoratif et l'hommage à un travail étudiant restent en galerie.

**Critère d'entrée** (carte [#19253](https://github.com/jsboige/CoursIA/issues/19253)) : le carnet vérifie empiriquement un résultat récent — théorème arXiv, preprint de conception de solveurs, garantie d'un mécanisme — avec les outils de la série, et confronte la claim à un oracle indépendant, un certificat ou un témoin vérifiable à la main. La date d'arrivée n'est pas un critère.

## Objectifs d'apprentissage

1. **Techniques** — construire un oracle indépendant (validateur, certificateur) qui ne partage aucun état avec le solveur audité ; distinguer statut, borne et optimum ; matérialiser un contre-exemple documenté en exécutable.
2. **Méthodologiques** — lire un preprint récent et en extraire la claim testable ; choisir le témoin (certificat, circuit, front de Pareto) qui prouve ou réfute ; rapporter un verdict honnête : garantie établie, écart mesuré, ou non comparable.
3. **Applicatifs** — prolonger un projet étudiant sans le recopier ; articuler preuve formelle et vérification empirique ; replacer un audit dans le parcours (fondements, CSP, métaheuristiques).

## Notebooks

| # | Notebook | Durée | Contenu | Source |
|---|----------|-------|---------|--------|
| 1 | [Frontieres-01-EdgeColoring-Tutte-Python](Frontieres-01-EdgeColoring-Tutte-Python.html) | ~45 min | Coloration d'arêtes cubiques : Vizing, Petersen, ponts, graphes apex et CP-SAT — vérification empirique d'un théorème récent (arXiv 2608.22870) | Nouveau |
| 2 | [Frontieres-02-Factorio-Balancer-Python](Frontieres-02-Factorio-Balancer-Python.html) | ~35 min | Belt balancer Factorio : MIP continu vs CP-SAT discret sur cas borné, N×N throughput-unlimited | Distillation Venturini 2024 |
| 3 | [Frontieres-03-MAPF-Guarantee-Audit-Python](Frontieres-03-MAPF-Guarantee-Audit-Python.html) | ~60 min | MAPF : validateur indépendant, oracle CP-SAT time-expanded, réfutation OD-A*, arrêt CBS au but, audit des garanties ECBS — distillation PrCon G3 (Matteo Atkinson, Paul Witkowski) | Projet étudiant (PrCon PRs #33/#36/#42) |
| 4 | [Frontieres-04-CombinatorialAuctions-WDP-VCG-Python](Frontieres-04-CombinatorialAuctions-WDP-VCG-Python.html) | ~60 min | Enchères combinatoires : WDP exact CP-SAT vs force brute, langage XOR, budget global, paiements VCG et audit de leurs garanties, contre-exemple de manipulation sous budget matérialisé, forensics `PRICE_SCALE` sur 18 instances CATS — distillation PrCon J2 (Majerczyk, Chartouni, Wangon-Zekou) | Projet étudiant (PrCon PR #26) |
| 5 | [Frontieres-05-CoveringArrays-Guarantee-Audit-Python](Frontieres-05-CoveringArrays-Guarantee-Audit-Python.html) | ~55 min | Covering Arrays : oracle constraint-aware, set cover CP-SAT exact, bornes et baselines IPOG/AETG-like — distillation PrCon H4 (Valérian Pichot) | Projet étudiant (PrCon PR #58) |
| 6 | [Frontieres-06-LearningToBranch-Generalization-Audit-Python](Frontieres-06-LearningToBranch-Generalization-Audit-Python.html) | ~75 min | Learning to branch : dérivation de dom/wdeg, splits groupés, transfert inter-familles, performance intégrée, coût d'inférence et seuil d'amortissement — distillation PrCon G4 (Simon Naulet, Matis Codjia) | Projet étudiant (PrCon PR #46) |
| 10 | [Frontieres-10-NeuralDiving-Coloration-Python](Frontieres-10-NeuralDiving-Coloration-Python.html) | ~60 min | Neural diving : un plongeur MLP prédit une affectation partielle, injectée comme hint réparable dans CP-SAT ; la médiane des branches recule (2829 → 2325, 25/25 instances améliorées) alors que ≈ 49 % des arêtes du hint violent l'adjacence — cohérence du hint avec les contraintes, pas précision par bit — hommage Nair et al. 2021 | Recherche (Nair et al. 2021) |

## Prérequis par notebook

| Notebook | Fondations requises | Dépendances |
|----------|--------------------|-------------|
| Frontieres-01 EdgeColoring-Tutte | coloration de graphes, CSP-3 | networkx, ortools |
| Frontieres-02 Factorio-Balancer | CSP-3 (CP-SAT), CSP-4 | ortools (SCIP + CP-SAT), numpy, matplotlib |
| Frontieres-03 MAPF Guarantee Audit | Search-3 (A*), CSP-3/CSP-4, heuristiques admissibles | ortools, pandas, matplotlib |
| Frontieres-04 CombinatorialAuctions-WDP-VCG | CSP-3 (CP-SAT), CSP-5 (optimisation), GameTheory-16 (VCG) | ortools, pandas, matplotlib |
| Frontieres-05 CoveringArrays Guarantee Audit | CSP-3, CSP-5 | ortools, pandas, matplotlib |
| Frontieres-06 LearningToBranch Generalization Audit | CSP-6 (heuristiques), MGS-16 (sélection d'algorithmes) | numpy, pandas, scikit-learn |
| Frontieres-10 NeuralDiving Coloration | Frontieres-06 (composante branchement), CSP-3 (CP-SAT), MGS-16 (sélection d'algorithmes) | ortools, scikit-learn, numpy, pandas |

## Origine des projets

La plupart des carnets prolongent des projets étudiants réalisés dans le cadre de cours d'IA, sans en recopier le code : les références spécifiques sont indiquées dans chaque carnet.

Le [Frontieres-03-MAPF-Guarantee-Audit-Python](Frontieres-03-MAPF-Guarantee-Audit-Python.html) distille le projet PrCon G3 de **Matteo Atkinson** et **Paul Witkowski**, *« Coordination de drones par Multi-Agent Path Finding »*, PRs [PrCon #33](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/33), [#36](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/36) et [#42](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/42). Un rerun frais alimente un validateur et un oracle CP-SAT indépendants ; le notebook distingue trajectoire valide, optimum observé et garantie réellement établie, avec provenance détaillée dans [`data/app24-mapf-audit/SOURCE.md`](data/app24-mapf-audit/SOURCE.md).

Le [Frontieres-04-CombinatorialAuctions-WDP-VCG-Python](Frontieres-04-CombinatorialAuctions-WDP-VCG-Python.html) distille le projet PrCon J2 de **Lucas Majerczyk**, **Nabil Chartouni** et **Wilfrid Wangon-Zekou**, *« Enchères combinatoires et Winner Determination »*, PR [PrCon #26](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/26). Le notebook ré-écrit le solveur WDP (CP-SAT, prix entiers milli-unités bout-en-bout) sans importer le package `wdp/` des étudiants ; il re-résout les 18 instances CATS, **matérialise en exécutable** le contre-exemple de manipulation sous budget documenté mais jamais testé dans la source, et audite honnêtement l'écart `PRICE_SCALE` entre les outputs committés et le code au commit source. Données et provenance : [`data/app25-wdp-vcg-audit`](data/app25-wdp-vcg-audit/).

Le [Frontieres-05-CoveringArrays-Guarantee-Audit-Python](Frontieres-05-CoveringArrays-Guarantee-Audit-Python.html) distille le projet PrCon H4 de **Valérian Pichot**, *« Covering Arrays »*, PR [PrCon #58](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/58). Sans recopier le générateur étudiant, le notebook reconstruit un oracle indépendant, un set cover CP-SAT exact et deux baselines approchées ; il reproduit surtout le faux verdict d'un validateur qui exige des interactions sémantiquement impossibles, puis le répare par un univers constraint-aware. Provenance : [`data/app26-covering-arrays-audit/SOURCE.md`](data/app26-covering-arrays-audit/SOURCE.md).

Le [Frontieres-06-LearningToBranch-Generalization-Audit-Python](Frontieres-06-LearningToBranch-Generalization-Audit-Python.html) distille le projet PrCon G4 de **Simon Naulet** et **Matis Codjia**, *« Apprentissage d'heuristiques de branchement pour solveur CP »*, PR [PrCon #46](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/46). La reproduction est entièrement réécrite : elle remplace le split par lignes par des instances disjointes, ajoute trois transferts leave-one-family-out et compare l'arbre, le temps total et le coût d'inférence à une baseline choisie sur le train uniquement. Elle établit un résultat négatif utile : une imitation locale fidèle ne garantit ni un arbre plus petit ni un solveur plus rapide. Provenance : [`data/app28-learning-to-branch-audit/SOURCE.md`](data/app28-learning-to-branch-audit/SOURCE.md).




Le [Frontieres-10-NeuralDiving-Coloration-Python](Frontieres-10-NeuralDiving-Coloration-Python.html) rend hommage au second geste de l'article de Nair et al. (2021), *« Solving Mixed Integer Programs Using Neural Networks »* (arXiv:2012.13349) : le **diving**, qui apprend une solution partielle pour guider un solveur MIP. Frontieres-06 a audité la composante *branching* (politique de branchement apprise) ; Frontieres-10 enchaîne sur l'autre composante : un plongeur MLP prédit une affectation des 60 sommets d'une coloration de graphe, injectée comme `hint` réparable dans OR-Tools CP-SAT, et l'on mesure l'effet sur les branches de preuve. La famille est calibrée pour qu'une fenêtre existe : les set-cover denses s'effondrent au presolve (`nodes = 0`) et les knapsack corrélés ne se prouvent pas en fenêtre notebook ; la coloration 60 sommets / 3 arêtes branche (médiane 2742, 2303-3799 sur les 60 instances d'entraînement) et se prouve (< 0,1 s). Verdict mesuré sur 25 instances de test, sur un run déterministe (`num_workers = 1`) : la médiane des branches recule (2829 → 2325, ≈ −18 %), les 25 instances s'améliorent (gain relatif médian ≈ 15 %, de 8 % à 28 %), et ≈ 49 % des arêtes du hint (44 sur ~90) sont en conflit avec l'adjacence — la cohérence, pas la précision par bit, détermine l'effet du hint. Le notebook ne copie aucun code, donnée, figure ou prose de l'article, archivé au gisement `G:\Mon Drive\MyIA\IA\Bibliographie IA\Search\`. Provenance : [`data/app33-neural-diving/SOURCE.md`](data/app33-neural-diving/SOURCE.md).

## Ponts inter-séries

| Série | Lien | Relation |
| ------- | ------ | ---------- |
| [Partie 1 : Search](../Part1-Foundations/README.md) | Fondamentaux | Heuristiques admissibles, A* (Frontieres-03) |
| [Partie 2 : CSP](../Part2-CSP/README.md) | Programmation par contraintes | CP-SAT, scheduling, optimisation (toute la partie) |
| [Partie 4 : Métaheuristiques](../Part4-Metaheuristics/README.md) | Sélection d'algorithmes | MGS-16 : Rice, No Free Lunch (Frontieres-06, Frontieres-10) |
| [GameTheory](../../GameTheory/README.md) | GameTheory-16 (VCG) | Paiements VCG et garanties d'enchères (Frontieres-04) |
| [SymbolicAI — Planners](../../SymbolicAI/Planners/README.md) | Planners-8 (temporel) | Réseaux de contraintes temporelles (carnet Frontieres-09, second lot du séquencement #19253) |
| [Langlands](../../SymbolicAI/Lean/Langlands/) | Szpiro–Pasten 2026 | La distillation arithmétique (App-32) reliée à la sous-série Langlands (#18368) |

## Références

| Notebook | Références |
|----------|-----------|
| Frontieres-03 (MAPF Guarantee Audit) | Stern, R., et al. (2019) — « Multi-Agent Pathfinding: Definitions, Variants, and Benchmarks », *SoCS* ; Sharon, G., et al. (2015) — « Conflict-Based Search for Optimal Multi-Agent Path Finding », *Artificial Intelligence* 219 ; Standley, T. (2010) — « Finding Optimal Solutions to Cooperative Pathfinding Problems », *AAAI* ; Barer, M., et al. (2014) — « Suboptimal Variants of the Conflict-Based Search Algorithm for the Multi-Agent Pathfinding Problem », *SoCS*. |
| Frontieres-04 (CombinatorialAuctions-WDP-VCG) | Rothkopf, M. H., Pekeč, A., & Harstad, R. M. (1998) — « Computationally Combinatorial Auction Design », *Management Science* 44(8) ; Sandholm, T. (2002) — « Algorithm for Optimal Winner Determination in Combinatorial Auctions », *Artificial Intelligence* 135 ; Leyton-Brown, K., Pearson, M., & Shoham, Y. (2000) — « Towards a Universal Test Suite for Combinatorial Auction Design », *EC 2000* (générateur CATS) ; Nisan, N. (2000) — « Bidding and Allocation in Combinatorial Auctions », *EC 2000* (langage XOR) ; Lehmann, D., O'Callaghan, L., & Shoham, Y. (2002) — « Truth Revelation in Approximately Efficient Combinatorial Auctions », *JACM* 49(5) (glouton √m, enchérisseurs single-minded). |
| Frontieres-05 (CoveringArrays Guarantee Audit) | Cohen, D. M., Dalal, S. R., Fredman, M. L., & Patton, G. C. (1997) — « The AETG System: An Approach to Testing Based on Combinatorial Design », *IEEE TSE* 23(7) ; Lei, Y., Kacker, R., Kuhn, D. R., Okun, V., & Lawrence, J. (2007) — « IPOG: A General Strategy for T-Way Software Testing », *ECBS 2007*. |
| Frontieres-06 (LearningToBranch Generalization Audit) | Boussemart, F., Hemery, F., Lecoutre, C., & Sais, L. (2004) — « Boosting Systematic Search by Weighting Constraints », *ECAI* (dom/wdeg) ; Kotthoff, L. (2014) — « Algorithm Selection for Combinatorial Search Problems: A Survey », *AI Magazine* 35(3) ; Bengio, Y., Lodi, A., & Prouvost, A. (2021) — « Machine Learning for Combinatorial Optimization: a Methodological Tour d'Horizon », *European Journal of Operational Research* 290(2) ; Balcan, M.-F., Dick, T., Sandholm, T., & Vitercik, E. (2020) — « Learning to Branch: Generalization Guarantees and Limits of Data-Independent Discretization », *JACM* 67(6). |
| Frontieres-10 (Neural Diving Coloration) | Nair, V., Bartunov, S., Gimeno, F., et al. (2021) — « Solving Mixed Integer Programs Using Neural Networks », arXiv:2012.13349 (v3, juillet 2021) ; Bengio, Y., Lodi, A., & Prouvost, A. (2021) — « Machine Learning for Combinatorial Optimization: a Methodological Tour d'Horizon », *European Journal of Operational Research* 290(2). |

## Navigation

[<- Applications (cas pratiques)](../Applications/README.md) | [Partie 4 : Métaheuristiques](../Part4-Metaheuristics/README.md) | [Retour à la série Search](../README.md)
