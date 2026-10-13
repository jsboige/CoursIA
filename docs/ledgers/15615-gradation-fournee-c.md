# Ledger — Issue #15615 (gradation GameTheory, fournée C : blocs 11 à 15)

> **Bornage strict** : ce ledger couvre les **carnets des blocs 11, 12, 13, 14 et 15** de la série GameTheory sur `origin/main` au 2026-10-11 (head `5e96ffec4cb`). Il poursuit la fournée A (`15615-gradation-fournee-a.md`, PR #20288 — carnets 01/04/05), la fournée B (`15615-gradation-fournee-b.md`, PR #20289 — blocs 06-10) et la strate « Fondations » (`15615-gradation-foundations.md`, carnets 02 + 03).

## Origine

Issue #15615 — audit de gradation, plan en fournées A-D posté au fil. Fournée C annoncée « ~25 carnets » au cadrage ; **l'arbre au 2026-10-11 en porte 21** (11×3, 12×2, 13×5, 14×2, 15×9) — l'arbre fait foi, même règle qu'en fournées A et B.

## Méthode

Identique aux ledgers précédents : prérequis déclarés (section dédiée ou front-matter, extraits verbatim), concepts introduits (première section définissante), difficulté sur l'échelle **Basse / Moyenne / Haute / Très haute** (combinatoire du sujet + longueur comme proxy), jumeau (Py/C# ou principal/Lean).

## Tableau de gradation — fournée C (blocs 11-15)

| # | Carnet | Prérequis déclarés | Concepts introduits | Cells | Diff. | Jumeau |
|---|---|---|---|---:|---|---|
| 11 | [GameTheory-11-BayesianGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-11-BayesianGames-Python.ipynb) | Notebooks 1-10, probas (règle de Bayes), jeux extensifs + induction avant | Jeux bayésiens (Harsanyi) : types, croyances, BNE par best-response, Cournot à coûts incertains, enchère au premier prix + équivalence du revenu, signaling (Spence) | 47 (15 code) | **Haute** | Oui (C#) |
| 11-cs | [GameTheory-11-BayesianGames-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-11-BayesianGames-CSharp.ipynb) | 02-NormalForm-CSharp (Nash info complète) + probabilités conditionnelles | Twin C# : même plateau (BNE, Cournot incertain, enchères, revenu, Spence) | 34 (13 code) | Haute | Oui (Py) |
| 11b | [GameTheory-11b-Lean-BayesianGamesExt-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-11b-Lean-BayesianGamesExt-Lean.ipynb) | Aucune déclarée — compagnon Lean natif du 11-Python | Restatement Lean 4 via kernel `lean4-wsl` : Harsanyi, BNE (`isBNE`), enchère de Vickrey (second prix), **monotonie de Blackwell** (valeur de l'information), information nuisible — 0 sorry, banc d'essai du BG-prover | 43 (19 code) | **Très haute** | Non |
| 12 | [GameTheory-12-ReputationGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-12-ReputationGames-Python.ipynb) | Notebooks 1-11, en particulier 11 (types, BNE), mise à jour bayésienne + induction arrière | Jeux de réputation : cheap talk et ses limites, Kreps-Wilson, KMRW, équilibres séquentiels (PBE) | 29 (13 code) | Haute | Oui (C#) |
| 12-cs | [GameTheory-12-ReputationGames-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-12-ReputationGames-CSharp.ipynb) | Aucune déclarée (twin) | Twin C# from-scratch (BCL seule, 0 NuGet) : cheap talk, Kreps-Wilson, KMRW, PBE | 27 (10 code) | Haute | Oui (Py) |
| 13 | [GameTheory-13-ImperfectInfo-CFR-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13-ImperfectInfo-CFR-Python.ipynb) | Notebooks 1-11 (notamment 07-ExtensiveForm) | Information imparfaite + **CFR complet** : regret contrefactuel, circuits de regret / treeplex (théorème 4.1, éq. 4), CFR+, Deep CFR, moteur SOTA OpenSpiel, Kuhn Poker et Leduc, 8 exercices — le plus gros carnet de la fournée | 64 (26 code) | **Très haute** | Oui (C#) |
| 13-cs | [GameTheory-13-ImperfectInfo-CFR-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13-ImperfectInfo-CFR-CSharp.ipynb) | Aucune déclarée (twin) | Twin C# : Kuhn Poker, regret matching, CFR/CFR+ ; annexe pont .NET→PythonNet→OpenSpiel (#10459), parité #4956 | 30 (11 code) | Haute | Oui (Py) |
| 13b | [GameTheory-13b-Safe-Subgame-Solving-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13b-Safe-Subgame-Solving-Python.ipynb) | Aucune déclarée — compagnon du 13 | Safe subgame solving : blueprint, recollement naïf vs safe, loi obstruction→témoin | 26 (12 code) | Haute | Oui (13c) |
| 13c | [GameTheory-13c-Safe-Subgame-Solving-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13c-Safe-Subgame-Solving-CSharp.ipynb) | Aucune déclarée (twin de 13b) | « Le twin qui vérifie, puis qui casse » : reproduction fidèle de 13b, puis audit (double comptage, vraie best-response — le « Nash » de 13b n'en est pas un), énumération corrigée | 24 (10 code) | Haute | Oui (13b) |
| 13d | [GameTheory-13d-Optimistic-CFR-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13d-Optimistic-CFR-Python.ipynb) | Aucune déclarée — compagnon du 13, socle #13350 réutilisé | CFR optimiste : OFTRL stable-prédictif, DCFR (mémoire oublieuse), verdict honnête, 3 exercices | 17 (7 code) | Haute | Non |
| 14 | [GameTheory-14-DifferentialGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-14-DifferentialGames-Python.ipynb) | Notebooks 1-12, calcul différentiel | Jeux différentiels : boucle ouverte/fermée, LQ et équations de Riccati, feedback Nash, Stackelberg dynamique (open-loop/feedback, capital durable), étude policy-gradient : non-convergence + contrôles négatifs (mono-agent, zéro-somme), 6 exercices | 51 (19 code) | **Très haute** | Oui (C#) |
| 14-cs | [GameTheory-14-DifferentialGames-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-14-DifferentialGames-CSharp.ipynb) | Aucune déclarée (twin) | Twin C# : intégrateur **RK4 from-scratch**, Cournot/Stackelberg analytiques, LQ stationnaire vérifié (Math Verification), poursuite-évasion d'Isaacs (3 cas dont un non résoluble analytiquement), tranche 2 cross-check **MathNet.Numerics** (moteur SOTA .NET), 4 exercices | 29 (12 code) | **Très haute** | Oui (Py) |
| 15 | [GameTheory-15-CooperativeGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-15-CooperativeGames-Python.ipynb) | Notebooks 1-13, en particulier 14 (transition coopération) ; coalition, utilité transférable | Jeux coopératifs TU : fonction caractéristique, **valeur de Shapley** (axiomes, complexité, Monte Carlo), Banzhaf, core + Bondareva-Shapley, visualisation 3D du core, jeux convexes, **jeux d'assistance** (Off-Switch Game, POLA/SUR), coalition de gauche 2024 | 69 (30 code) | **Très haute** | Oui (C#) |
| 15-cs | [GameTheory-15-CooperativeGames-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-15-CooperativeGames-CSharp.ipynb) | 02-NormalForm + 04-Nash (C#) | Twin C# from-scratch (BCL .NET 9, 0 NuGet) : Shapley, Banzhaf, core, jeux convexes (tarification aéroport), jeux d'assistance, application politique NFP 2024 (exact vs Monte Carlo), 6 exercices | 65 (24 code) | **Très haute** | Oui (Py) |
| 15b | [GameTheory-15b-Lean-CooperativeGames-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-15b-Lean-CooperativeGames-Lean.ipynb) | Aucune déclarée — compagnon formel du 15 | Formalisation Lean 4 (kernel WSL, projet Lake/Mathlib) : TU games, axiomes de Shapley, théorème d'unicité, core, jeux de vote, **mariages stables** (Gale-Shapley, Lean + pont Python), exercices avec corrections enseignant | 51 (20 code) | **Très haute** | Non (15c compagnon) |
| 15c-cs | [GameTheory-15c-CooperativeGames-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-15c-CooperativeGames-CSharp.ipynb) | Aucune déclarée | Side-track C# : Shapley BCL, jeu de gants, core vide du jeu de majorité, Banzhaf (mini-ONU), convexité ; **core/least-core/nucleolus par LP** via Google.OrTools (Glop) en parité HiGHS (#10382) | 43 (19 code) | Haute | Oui (parité HiGHS) |
| 15c | [GameTheory-15c-CooperativeGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-15c-CooperativeGames-Python.ipynb) | Aucune déclarée — compagnon Python du 15b | Illustrations Python du 15b : gants, core vide, Banzhaf, convexité ; core/nucleolus par LP, **certificat Bondareva-Shapley** (collection équilibrée), 3 exercices | 58 (21 code) | Haute | Oui (15c-cs) |
| 15d | [GameTheory-15d-Mobius-Coalitions-Lean-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-15d-Mobius-Coalitions-Lean-Python.ipynb) | Aucune déclarée | Décomposition de **Möbius** sur le treillis des coalitions : coefficient m(T), synergie irréductible (jeu du trésor), lien avec Shapley, lecture directe des sources `game_theory_lean`, 4 exercices | 26 (9 code) | Haute | Non |
| 15e | [GameTheory-15e-Coalition-Power-SMT-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-15e-Coalition-Power-SMT-Python.ipynb) | Aucune déclarée — question directrice ; distille le projet T1 Kalalou/Grall (EPITA 2026) | Poids nominal vs pouvoir réel : coalitions minimales, trois indices de pouvoir, **énumération de modèles SMT** (Z3) bornée en seconde voie, hiérarchie des garanties SAT/UNSAT, photographie structurelle de l'Assemblée, contrefactuel contrôlé | 33 (11 code) | Haute | Non |
| 15f | [GameTheory-15f-Shapley-Groupes-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-15f-Shapley-Groupes-Python.ipynb) | Aucune déclarée — article distillé Flores/Molina/Tejeda 2019 (4OR) | **Shapley de groupe** : jeu fusionné, axiome G-SPB, exemple 1 en arithmétique exacte, profitabilité/complémentarité, mariages florentins (Médicis), club de karaté de Zachary, estimation Monte Carlo quand 2^n explose | 44 (17 code) | Haute | Non |
| 15g | [GameTheory-15g-AssistanceGames-2026-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-15g-AssistanceGames-2026-Python.ipynb) | Aucune déclarée | Assistance games (résultat 2026) : modèle formel §3, instance jouet, politique jointe optimale oracle, **EXP3** (no-regret) pour l'assistant, bench empirique √T vs T^(3/4) | 15 (8 code) | Haute | Non |

**Totaux** : 21 carnets. Répartition difficulté : 7 Très haute (11b, 13, 14, 14-cs, 15, 15-cs, 15b), 14 Haute, aucune Moyenne ni Basse — la série y atteint son plateau maximal.

## Observations

### Le bloc 13 est le sommet algorithmique de la série

Le 13-Python est **le plus gros carnet de la fournée** : CFR complet jusqu'aux circuits de regret et au treeplex (théorème 4.1), Deep CFR, OpenSpiel, Leduc. Il porte quatre side-tracks dont deux objets pédagogiques uniques dans la série : la paire **13b/13c « qui vérifie, puis qui casse »** (le twin C# audite son modèle Python — double comptage, fausse best-response — puis corrige l'énumération), et 13d qui enseigne le **verdict honnête** (l'optimisme aide en théorie, le champion empirique est DCFR).

### Le bloc 15 est le second continent de la série

9 carnets sur 21 — derrière le bloc 06 (13 carnets, fournée B) mais devant tout le reste. Trois langages (Python, C#, Lean 4) autour de la valeur de Shapley, plus quatre extensions : Möbius (15d), SMT comme instrument de preuve (15e), Shapley de groupe sur réseaux (15f), assistance games résultat 2026 (15g). Le 15-Python et son twin C# (65) sont les deux plus gros carnets de la fournée après le 13.

### Les twins C# portent les ponts SOTA et la parité de solveurs

13-cs (pont .NET→PythonNet→OpenSpiel, #10459, parité #4956), 14-cs (cross-check MathNet.Numerics, RK4 et Riccati from-scratch), 15c-cs (parité de solveurs LP Glop⇄HiGHS, #10382). La série C# confirme son rôle de vitrine SOTA observé en fournée B.

### Deux distillations externes dans le bloc 15

15e distille un **projet étudiant** (T1 Kalalou/Grall, EPITA 2026) et 15f un **article** (Flores-Molina-Tejeda 2019, 4OR). Le bloc 15 est la porte d'entrée des contributions externes dans la série — précéder le crédit par la source est ce qui les distingue d'un contenu interne.

### Croix de renum / suffixe pour #16231/#14944 (hors scope gradation)

1. **15c-Python renvoie au « notebook 14 » pour les implémentations complètes de Shapley et Core** (« Pour les implementations completes de Shapley et Core, voir le notebook 14 ») — or le 14 est DifferentialGames ; le renvoi date d'avant la renum (les implémentations vivent dans le 15). Renvoi pré-renum à corriger.
2. **Le suffixe « 15c » désigne deux rôles distincts** : `15c-CooperativeGames-Python` est le compagnon Python du 15b Lean (titré « Jeux Cooperatifs Lean (Python) »), tandis que `15c-CooperativeGames-CSharp` est un side-track de parité runtimes. Même famille d'ambiguïté que `06b-...-Lean-Python` signalée en fournée B.
3. Mineur : la nav de 15b porte une double parenthèse fermante et « Autrès side tracks » ; les en-têtes internes de 15c-cs mélangent `### Section N` (texte) et sections réelles — cosmétique.

### Prérequis en plages plutôt qu'en blocs

Les carnets 11 à 15 déclarent leurs prérequis en plages (« Notebooks 1-10 », « 1-11 », « 1-12 », « 1-13 ») plutôt qu'en blocs nommés — cohérent avec un track principal séquentiel, mais moins actionnable qu'un renvoi ciblé (le 13 dit heureusement « notamment 07-ExtensiveForm »). Les twins C# héritent du pont (11-cs renvoie à 02 + probas) ou ne déclarent rien (12-cs, 13-cs, 14-cs) — même désalignement mineur que celui noté en fournée B sur 06c.

## Hors périmètre (fournées suivantes)

- **Fournée D** : blocs 16-25 (~26 carnets au cadrage).
- **Tableau consolidé** des 21+27+12+15 carnets des fournées A-C : conditionné à l'arbitrage #18001 (cf. ledger Fondations).

## Source des données

- Lecture firsthand des 21 carnets (front-matter + section 1 + navigation) via `git show origin/main:<carnet>` au 2026-10-11, head `5e96ffec4cb`.
- Statistiques cellules : extraction JSON par script de session (kernelspec, comptes code/markdown, headers).
- Comptage de périmètre : `git ls-tree origin/main MyIA.AI.Notebooks/GameTheory/` filtré blocs 11-15 (11×3, 12×2, 13×5, 14×2, 15×9).

## Voir aussi

- #15615 — issue pivot (plan en fournées A-D)
- `15615-gradation-fournee-a.md` (PR #20288) — carnets 01/04/05
- `15615-gradation-fournee-b.md` (PR #20289) — blocs 06-10
- [15615-gradation-foundations.md](15615-gradation-foundations.md) — carnets 02 + 03 (PR #18195)
- #16231 / #14944 — renum et colonne canonique (destinataires des croix n°1-2)
- #18001 — PR `rename GameTheory — 93 carnets` (mergée 2026-09-29), condition du tableau consolidé
