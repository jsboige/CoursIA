# Parcours — Le décideur face à un système d'IA

> Pli P1 « Décideur » de l'EPIC [#28136](https://github.com/jsboige/CoursIA/issues/28136) (issue feuille [#28465](https://github.com/jsboige/CoursIA/issues/28465)). Parcours narratif composé **exclusivement à partir de carnets existants sur `main`** — chaque étape renvoie au carnet réel et cite un fait mesuré dans sa sortie committée, chiffres et décimales tels qu'ils y figurent. Modèle de structure : « Parcours transverses » du [README GameTheory](../../MyIA.AI.Notebooks/GameTheory/README.md), le parcours [IA hybride](ia-hybride.md) et le parcours [IA, société et responsabilité](ia-societe-responsabilite.md), issus de l'EPIC [#13844](https://github.com/jsboige/CoursIA/issues/13844).

## La thèse du parcours

Une organisation ne confie jamais une décision à un système d'IA : elle lui confie un calcul et garde la signature. Ce qui reste au signataire se chiffre — ce que vaut l'information qu'il donne au système (acte 1), ce que coûte l'erreur qu'il tolère (acte 2), ce que paient ceux pour qui le système décide sans les voir (acte 3), ce que doit le système une fois déployé (acte 4). Ce parcours traverse le dépôt en quatre actes pour répondre à une seule question : **que doit avoir mesuré celui qui signe, pour répondre d'une décision dont le calcul est confié à un système d'IA ?**

## Profil

- **Pour qui** : manager, élu, responsable de direction ou de service qui arbitre un projet d'IA — acheter une étude, valider un modèle, autoriser un déploiement — sans en écrire le code ; le profil du commanditaire, pas celui de l'ingénieur.
- **Prérequis** : pour lire les sorties, une espérance, une probabilité et un tableau de chiffres suffisent ; **aucun** code à écrire et **aucune** clé d'API (balayage des sources des seize carnets : aucune lecture de clé), les carnets s'exécutent tels quels, et le préflight `python scripts/notebook_tools/learner_preflight.py --parcours local` vérifie l'environnement avant le premier. Ce qui n'est **pas** supposé : la théorie de la décision, l'actuariat, le choix social ni la théorie des jeux — leurs carnets partent de la question du métier (« faut-il payer pour mieux connaître son risque ? », « quel capital initial pour que le portefeuille survive, et que coûte ce capital ? »), pas d'un cours préalable. Trois réserves déclarées par les séries : les étapes 5, 9, 14, 15 et 16 viennent du cours 02 d'apprentissage automatique, dont elles présupposent le vocabulaire (entraînement, seuil, validation croisée) pour qui veut les exécuter ; l'étape 12 est classée « Recherche » par sa série ; l'étape 13 exige une carte graphique et un serveur de modèles local pour être rejouée. Leurs sorties committées suffisent à les lire.
- **Format** : 16 étapes en 4 actes. Chaque carnet est exécutable et committé avec ses sorties ; les durées ne sont citées que lorsqu'elles sont publiées par la série d'origine.

## Acte 1 — Ce que vaut l'information qu'on achète

Un modèle ne vaut que par ce qu'on lui demande et ce qu'on lui donne : quatre carnets de théorie de la décision chiffrent le goût du risque, le choix du critère et le prix de l'information, avant toute question de modèle.

| # | Étape | Durée | Ce qu'on y voit |
|---|---|---|---|
| 1 | [DecPyMC-02 : utilité et argent](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecPyMC/DecPyMC-02-Utility-Money.ipynb) | — | **La même loterie ne vaut pas la même chose pour deux décideurs** : sur 50 % +5000 / 50 % -1000 à richesse 10000 (E[X] = 12000 EUR), la prime de risque vaut 494.1 EUR pour « Audacieux », 923.1 EUR pour « Modere », 1503.3 EUR pour « Prudent » — l'aversion au risque se déclare avant de comparer deux projets |
| 2 | [DecPyMC-06 : critères de décision](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecPyMC/DecPyMC-06-Expert-Systems.ipynb) | — | **Trois critères, trois décisions sur la même matrice** (récession 25 %, stable 50 %, croissance 25 %) : l'utilité espérée retient Actions (50000), le minimax Obligations (pire cas 30000), le minimax-regret Immobilier (regret maximal 40000) — le critère est un choix, pas une technique neutre |
| 3 | [DecPyMC-05 : valeur de l'information](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecPyMC/DecPyMC-05-Value-Information.ipynb) | — | **L'information parfaite a un plafond, et le test parfait n'existe pas** : sur le forage, EVPI 90.0, EVSI 23.0 pour un coût de 50, net -27.0 (milliers d'EUR) — « Decision : NE PAS faire le test » ; l'imagerie médicale, efficace à 54 pct, coûte 500 pour 13.0 de valeur, net -487.0 |
| 4 | [Actuariat-05 : valeur de l'information à la souscription](../../MyIA.AI.Notebooks/Probas/DecisionTheory/Actuariat/Actuariat-05-Valeur-Info-Souscription.ipynb) | — | **Le signal le plus informatif est celui qu'il ne faut pas acheter** : sur un plafond de 558 EUR par candidat, l'examen capte 55.7 % de la valeur parfaite pour 90.0 EUR de coût et laisse 220.8 EUR nets ; la télématique capte 85.7 % pour 500.0 EUR et laisse -21.7 EUR |

**Fil de l'acte** : le meilleur système ne rattrape pas une mauvaise méthode — le profil de risque se déclare (1), le critère se choisit (2), et l'information s'achète sous son plafond (3) ou ne s'achète pas (4).

## Acte 2 — Ce que coûte l'erreur qu'on tolère

Un système qui se trompe ne coûte pas des points d'accuracy : il coûte des faux négatifs, des contrats perdus et du capital immobilisé. Quatre carnets mettent ce coût en chiffres, de la métrique du modèle à la ruine de l'assureur.

| # | Étape | Durée | Ce qu'on y voit |
|---|---|---|---|
| 5 | [2.12-Donnees-Desequilibrees](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.12-Donnees-Desequilibrees.ipynb) | — | **La métrique qui rassure est celle qui ment** : sur 0.034 de positifs, un modèle qui ne détecte jamais rien affiche 0.966 d'accuracy et 0.000 de rappel ; le seuil qui minimise le coût attendu — un faux négatif compté 5 fois un faux positif — est 0.21, pour un coût attendu minimal de 153.0 |
| 6 | [DecPyMC-08 : tarifer un risque](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecPyMC/DecPyMC-08-Actuariat-Capstone.ipynb) | — | **La prime paie l'espérance et la variance** : prime pure 208.50, chargement proportionnel 31.27, chargement de variance 66.01, prime commerciale 305.79 qui couvre E[S] « a hauteur de 146.7% », pour un écart-type de S de 660.11 — soit 317 % de la prime pure |
| 7 | [Actuariat-01 : prime pure et chargement](../../MyIA.AI.Notebooks/Probas/DecisionTheory/Actuariat/Actuariat-01-Prime-Pure-Chargement.ipynb) | — | **Le tarif unique fabrique sa propre fuite** : avec deux types cachés et une surprime tolérable, la prime demandée à tous passe de 10988 à 16205 EUR entre le tour 0 et le tour 5, tandis que la part des bons risques tombe de 0.500 à 0.025 — alors qu'un bon risque n'accepte de payer que 6180 EUR/an |
| 8 | [Actuariat-04 : ruine de Lundberg](../../MyIA.AI.Notebooks/Probas/DecisionTheory/Actuariat/Actuariat-04-Ruine-Lundberg.ipynb) | — | **La taille du portefeuille est un instrument de sécurité** : à capital initial égal (50 % de la prime annuelle) et à paramètres vrais identiques, la probabilité de ruine à un an est 26.00 pour 60 assurés contre 0.43 pour 2000, et 61.25 contre 4.50 à dix ans (colonne psi, en %) |

**Fil de l'acte** : le coût de l'erreur ne se lit pas dans le score (5) : il se lit dans la prime, qui paie la variance (6) puis la sélection qu'elle provoque (7), et dans le capital, qui décide si l'on survit à une mauvaise année (8).

## Acte 3 — Décider pour ceux qui ne sont pas dans la salle

Un système qui décide pour plusieurs personnes n'agrège pas des préférences neutres : il choisit un remède, une règle, un axiome et un expéditeur. Quatre carnets montrent ce que chaque choix coûte à quelqu'un.

| # | Étape | Durée | Ce qu'on y voit |
|---|---|---|---|
| 9 | [2.5c-Equite-Sous-Groupes](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.5c-Equite-Sous-Groupes.ipynb) | — | **Le prix de l'équité dépend du remède** : partant de 0.964 d'accuracy globale, les seuils par groupe la ramènent à 0.937 quand le reweighting la fait tomber à 0.547 — et le carnet prévient que son tableau « ne garantit pas la parite hors echantillon » |
| 10 | [SC-07 : élections de comité et core](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-07-Committees-Core-Python.ipynb) | 40 min | **La règle d'élection décide qui reste dehors** : sur un profil en deux blocs (3 votants {a, b}, 3 votants {c, d}, comité de 2), l'approbation simple élit `['a', 'b']`, hors du core, bloquée par les votants [3, 4, 5] ; PAV et la règle entropique élisent `['a', 'c']`, dans le core — sur 25 instances, les trois règles y tombent 25/25 |
| 11 | [SC-04 : agrégation computationnelle SAT et Z3](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-04-Computational-Aggregation-SAT-Z3-Python.ipynb) | 45 min | **Le décideur choisit l'axiome qu'il abandonne** : les trois axiomes réunis, le solveur rend UNSAT et vérifie Arrow ; mais chaque paire est « REALISABLE » — sans non-dictature une dictature satisfait les deux autres, sans IIA Borda, sans Pareto un classement constant |
| 12 | [GT-17e : persuasion bayésienne](../../MyIA.AI.Notebooks/GameTheory/GameTheory-17e-Bayesian-Persuasion-Python.ipynb) | — | **Celui qui fabrique le signal fabrique la décision** : face à un juge qui acquitte sans information (prior 0.30) et ne condamne qu'à partir d'un posterior de 0.5, un procureur qui veut condamner obtient 0.000000 sans information, 0.300000 en divulguant tout et 0.600000 avec le signal optimal — deux messages, dont l'un garde un posterior [0.5 0.5] |

**Fil de l'acte** : décider pour plusieurs, c'est choisir qui paie — la parité se paie en accuracy (9), la représentation en règle d'élection (10), la cohérence en axiome abandonné (11) — et le signal a toujours un auteur (12).

## Acte 4 — Répondre du système qu'on déploie

Le déploiement ajoute trois dettes que la validation ne voit pas : une facture, une dérive et une erreur localisée. Quatre carnets les chiffrent et referment la responsabilité sur une personne précise.

| # | Étape | Durée | Ce qu'on y voit |
|---|---|---|---|
| 13 | [11b : matériel, débit, coût](../../MyIA.AI.Notebooks/GenAI/Texte/11b_Materiel_Debit_Cout.ipynb) | 60 min | **Un coût d'exploitation se mesure, il ne se devine pas** : sur la machine du carnet, le coût local total est 1.018 EUR par million de jetons — 0.923 d'amortissement (hypothèses 1000 EUR / 3 ans / 20 % d'utilisation) et 0.094 d'énergie (0.25 EUR/kWh) — et 1.018 EUR/M jetons est le tarif API au-dessus duquel le local gagne : en dessous, « le local ne se justifie pas par le prix » |
| 14 | [2.5d-Derive-Distribution-Deploiement](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.5d-Derive-Distribution-Deploiement.ipynb) | — | **La même validation couvre trois mondes, dont un où elle est fausse** : les 0.919 annoncés tiennent sous dérive d'étiquettes (0.918, écart 0.001), se dégradent sous dérive de covariables (0.692, écart 0.227) et s'effondrent sous dérive de concept (0.068, écart 0.850), où le modèle « predit l'envers » |
| 15 | [2.13-Analyse-Erreurs](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.13-Analyse-Erreurs.ipynb) | — | **L'erreur n'est pas répartie, elle est concentrée** : la poche (55+ Nord, 2+ contacts) est à 67.6 % d'erreur quand le reste du portefeuille est à 14.6 % ; auditer les lignes corrompues du train (seniors 55+ du Nord avec 2+ contacts support) la ramène à 25.4 % (-42.3 points) pour -1.8 points d'erreur globale (17.8 % à 15.9 %) et +0.7 point sur le reste (14.6 % à 15.3 %) |
| 16 | [2.14 : expliquer un refus](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.14-Explicabilite-SHAP-LIME-Contrefactuels.ipynb) | — | **Répondre d'un refus, c'est dire ce qui le porte et ce qui l'aurait évité** : le dossier fil rouge est refusé à 0.707, décomposé depuis une base de 0.3135 — dont 0.1166 pour `checking_status` — et trois contrefactuels ramènent la probabilité à 0.349, 0.400 et 0.370, tous acceptés |

**Fil de l'acte** : répondre d'un système déployé, c'est opposer trois chiffres à la promesse initiale — ce qu'il coûte (13), ce qu'il tient encore après la dérive (14), et ce qu'il fait à la personne qu'il refuse (15, 16).

## Prolongements (hors parcours)

- [DecPyMC-01 : fondements de l'utilité](../../MyIA.AI.Notebooks/Probas/DecisionTheory/DecPyMC/DecPyMC-01-Utility-Foundations.ipynb) — l'assurance comme pari sur l'utilité : **prime maximale acceptable de 3691 EUR** pour couvrir un risque de 5 % de tout perdre sur une richesse de 10000 EUR.
- [Actuariat-03 : crédibilité de Bühlmann](../../MyIA.AI.Notebooks/Probas/DecisionTheory/Actuariat/Actuariat-03-Actuarial-Credibility.ipynb) — **le poids de l'expérience propre se calcule** : K = 250.69, Z_i = 0.166 pour une exposition de 50 contre 0.952 pour 5000, et une exposition de 2256.2 pour atteindre Z = 0.9.
- [2.5b-Calibration-Probabilites](../../MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.5b-Calibration-Probabilites.ipynb) — **une probabilité doit être calibrée pour que le coût attendu soit un coût** : à AUC identique (0.9129), l'espérance moyenne des dix mêmes patients passe de +4.8 avec les probabilités brutes à +9.0 avec les probabilités calibrées.
- [Planners-07-OR-Tools-Python](../../MyIA.AI.Notebooks/SymbolicAI/Planners/03-Advanced/Planners-07-OR-Tools-Python.ipynb) (45 min) — l'optimisation sous contraintes pour l'arbitrage de ressources : **un plan à 96 de distance totale, deux véhicules chargés 7/8** pour une capacité de 8 chacun.
- [GT-16k : enchères de Myerson](../../MyIA.AI.Notebooks/GameTheory/GameTheory-16k-Theorie-des-Encheres-Myerson-Python.ipynb) — **la réserve optimale rapporte d'autant plus que la concurrence est maigre** : 25.00 % avec 2 acheteurs, 6.25 % avec 3, 0.00 % avec 12.

## Pourquoi ce parcours existe

Ce parcours ne crée aucun contenu : il ordonne l'existant. Les carnets qu'il traverse sont tous sur `main`, exécutés avec leurs sorties, et il les range selon la seule séquence qu'un signataire puisse suivre — chiffrer ce qu'il achète (acte 1), tarifer ce qu'il tolère (acte 2), arbitrer entre des personnes qu'il ne voit pas (acte 3), répondre de ce qu'il déploie (acte 4). Le pli P1 de l'EPIC #28136 demandait exactement cela : un chemin pour celui qui signe, pas pour celui qui code.

*Pli P1 « Décideur » de l'[EPIC #28136](https://github.com/jsboige/CoursIA/issues/28136), issue feuille [#28465](https://github.com/jsboige/CoursIA/issues/28465). La ligne de ce parcours dans la table de [`PARCOURS.md`](../../PARCOURS.md) et son entrée dans [`docs/README.md`](../README.md) sont ajoutées dans la même PR que cette page.*
