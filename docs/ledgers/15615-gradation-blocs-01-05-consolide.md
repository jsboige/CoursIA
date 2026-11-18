# Ledger — Issue #15615 (gradation GameTheory, tableau consolidé des blocs 01-05)

> **Bornage strict** : ce ledger couvre les **blocs 01 à 05** de la série GameTheory — **29 carnets** — sur `origin/main` au **2026-10-24**, tête `8957d81ad44`. Il **remplace comme source de vérité** les tables de [15615-gradation-foundations.md](15615-gradation-foundations.md) (2026-09-28) et [15615-gradation-fournee-a.md](15615-gradation-fournee-a.md) (2026-10-10), qui restent en place comme **mesures datées** de leur arbre respectif. Les blocs 06 et au-delà restent hors périmètre (fournées B-D).

## Origine

Issue #15615 — audit de gradation demandé après le nit user du 2026-09-11 (« remettre un peu de cohérence dans la gradation »). Le fil a posé un plan en fournées A-D. Deux ledgers ont livré les blocs 01-05 en deux temps : 15 carnets pour la strate « Fondations » (02 + 03, PR #18195) puis 12 carnets pour la seconde moitié de la fournée A (01, 04, 05).

Les deux ledgers s'accordaient sur un point de blocage : le **tableau consolidé** des carnets 01-05 « dépend de l'arbitrage #18001 ». Ce ledger est ce tableau.

## Périmètre réel de la série — le recensement à jour

Les quatre ledgers de fournée (A-D) ont été rédigés du 2026-10-10 au 2026-10-11. La fournée D conclut : « **La série s'arrête au bloc 20** : cette fournée clôt le périmètre de l'audit », et corrige un compte au passage — « le tableau consolidé conditionné à #18001 doit donc partir de **100**, pas de 99 ».

Mesure sur l'arbre au 2026-10-24 : **111 carnets**, et **le bloc 21 existe** — `GameTheory-21-Capstone-Choix-Social-Python.ipynb`, entré **après** la fournée D. La série n'est donc pas close au bloc 20, et le compte de 100 n'est plus le bon. Ce compte de 111 couvre les carnets préfixés `GameTheory-` ; **16 autres** `.ipynb` vivent sous `GameTheory/` hors de ce préfixe et du périmètre gradué : `SocialChoice/` (14), `Dynamics/Dynamics-09-Biens-Publics` (1 — le carnet sorti, cf. ci-dessous) et `gateway/openspiel-cfr-service` (1).

| Bloc | Carnets | Bloc | Carnets | Bloc | Carnets |
|---|---:|---|---:|---|---:|
| 01 | 1 | 08 | 6 | 15 | 9 |
| 02 | 8 | 09 | 5 | 16 | 12 |
| 03 | 7 | 10 | 2 | 17 | 7 |
| 04 | 10 | 11 | 4 | 18 | 3 |
| 05 | 3 | 12 | 2 | 19 | 2 |
| 06 | 14 | 13 | 8 | 20 | 3 |
| 07 | 2 | 14 | 2 | **21** | **1** |
| | | | | **Total** | **111** |

Les blocs 01-20 totalisent **110** carnets ; le bloc 21 en ajoute un. Le chiffre de « 100 » de la fournée D était déjà une correction d'un compte antérieur — il est aujourd'hui en retard de onze carnets, dont un bloc entier. **Un tableau consolidé bâti sur 100 raterait le bloc 21 et onze carnets**, ce qui est exactement le défaut que la fournée D cherchait à éviter en corrigeant 99 en 100.

## Ce que la mesure a changé

### #18001 est mergée, et c'est le fait que les deux ledgers ignoraient

Le ledger Fondations conclut sa recommandation par « option B, **tant que la PR #18001 OPEN** (rename GameTheory — 93 carnets) n'est pas arbitrée ». Le ledger fournée A range le tableau consolidé en « hors périmètre » pour le même motif.

Mesure : **`#18001` est MERGED**, le **2026-09-29T22:39:32Z**, commit `09e96fa5eaf` — « passage unique GameTheory -- 93 carnets (relettrage 03, gradation, departages, suffixes noyau) ».

Le ledger Fondations est daté du **2026-09-28**, soit **la veille du merge** : sa table décrit donc l'arbre **d'avant le relettrage**, et ses noms de carnets n'existent plus sous cette forme. Ce n'est pas une erreur de rédaction, c'est une mesure qui a vieilli de 24 h — mais un lecteur qui l'ouvre aujourd'hui cherche des fichiers absents.

### Table de renommage appliquée par #18001 (blocs 01-05)

Relevée par `git show --name-status -M 09e96fa5eaf` :

| Avant #18001 | Après #18001 |
|---|---|
| `GameTheory-01-Setup` | `GameTheory-01-Setup-Python` |
| `GameTheory-02-NormalForm` | `GameTheory-02-NormalForm-Python` |
| `GameTheory-02-NormalForm-Csharp` | `GameTheory-02-NormalForm-CSharp` |
| `GameTheory-02-NormalForm-Csharp-Part2` | `GameTheory-02-NormalForm-Part2-CSharp` |
| `GameTheory-02b-Lean-Definitions` | `GameTheory-02b-Lean-Definitions-Lean` |
| `GameTheory-02c-Travelers-Dilemma` | `GameTheory-02c-Travelers-Dilemma-Python` |
| `GameTheory-02c-Travelers-Dilemma-Csharp` | `GameTheory-02c-Travelers-Dilemma-CSharp` |
| `GameTheory-03-Topology2x2` | `GameTheory-03-Topology2x2-Python` |
| `GameTheory-03-Topology2x2-Csharp` | `GameTheory-03-Topology2x2-CSharp` |
| `GameTheory-03a-Chemins-de-Swaps` | `GameTheory-03b-Chemins-de-Swaps-Lean-Python` |
| `GameTheory-03b-Chambres-et-Murs` | `GameTheory-03c-Chambres-et-Murs-Python` |
| `GameTheory-03c-Le-Joueur-LLM` | `GameTheory-03d-Le-Joueur-LLM-Python` |
| `GameTheory-03d-Plan-de-deformation` | `GameTheory-03e-Plan-de-deformation-Python` |
| `GameTheory-03e-Meta-Actions-Tarifees` | `GameTheory-03f-Meta-Actions-Tarifees-Python` |
| `GameTheory-03h-Deux-Especes-de-Fleches` | `GameTheory-03g-Deux-Especes-de-Fleches-Python` |
| `GameTheory-04-*` … `GameTheory-05b-Lean-Minimax` | suffixe noyau `-Python` / `-CSharp` / `-Lean` |

Le décalage d'une lettre que le ledger fournée A signalait (« 03a → 03b, 03e → 03f, 03h → 03g ») est **entièrement expliqué par ce seul commit**, et non par des renumérotations successives.

### Un carnet est sorti de la série, un autre y est entré

| Mouvement | Carnet | Commit | Date |
|---|---|---|---|
| **Sortie** | `03e-Plan-de-deformation-Python` → `Dynamics-09-Biens-Publics` | `c6258b90627` — « refactor(gametheory,#16231): GT-03e Plan-deformation -> Dynamics-09 Biens-Publics (#19484) » | 2026-10-13 |
| **Entrée** | `02d-Epistemique-Connaissance-Commune-Python` | `ee5350789c4` — « Add: GameTheory 02d — annexe épistémique, connaissance commune et croyances (#19461) (#22048) » | — |
| **Entrée** | `04g-Supermodularite-Python` | `b6a955ce7e1` — « Add(gt,#21931): GameTheory-04g — supermodularité et treillis des équilibres purs (#21938) » | — |
| **Entrée** | `04h-Routing-PriceOfAnarchy-Python` | `0dbdd963ecb` — « Add(gametheory,#21927): carnet 04g jeux de routage & price of anarchy (PoA mesuré, Pigou 4/3) (#21979) » | — |

Le carnet Plan-de-déformation **n'est pas perdu** : il a changé de série. Une table qui le compte encore dans le bloc 03 pointe un fichier absent — c'est le seul point où les deux ledgers induisaient en erreur, et non des moindres.

Conséquence arithmétique, vérifiée contre l'arbre : le solde des entrées et des sorties de la période redonne exactement ce que `git ls-tree` dénombre, et c'est ce contrôle qui a validé la fusion Fondations + fournée A. Le détail des mouvements est dans les deux tables ci-dessus ; les totaux, eux, appartiennent au catalogue.

## Méthode

Identique aux deux ledgers précédents, pour que les trois tables restent comparables :

1. **Prérequis** : carnets dont la section 1 ou la navigation déclare explicitement les acquis utilisés.
2. **Concepts introduits** : première section markdown qui définit une notion nouvelle.
3. **Difficulté** : échelle **Basse / Moyenne / Haute / Très haute**, mesurée sur la combinatoire du sujet et la longueur du carnet (cellules total / cellules code) — la longueur est un **proxy**, pas un verdict. Les trois carnets entrés depuis les ledgers précédents ont été lus (introduction + première section) pour être gradés sur leur contenu, pas sur leur seule longueur ; la colonne `Cells` a été **re-mesurée** pour les 29 carnets, ce qui explique les écarts de quelques unités avec les tables antérieures.
4. **Jumeau** : `True` si le carnet existe en deux versions (Python + C#/.NET), ou `Lean` pour une piste formelle séparée.

## Tableau de gradation — blocs 01-05 (29 carnets)

| # | Carnet | Prérequis déclarés | Concepts introduits | Cells | Diff. | Jumeau |
|---|---|---|---|---:|---|---|
| 01 | `GameTheory-01-Setup-Python` | Aucun — Python 3.9+, bases NumPy | Environnement de la série (Nashpy, OpenSpiel, WSL), Dilemme du Prisonnier résolu, plan des 4 parties | 69 (22 code) | **Basse** | Non |
| 02 | `GameTheory-02-NormalForm-Python` | 01-Setup | Jeu sous forme normale $(N,S,u)$, profil, fonction d'utilité $u_i : S \to \mathbb{R}$ | 46 (16 code) | **Basse** | Oui (C#) |
| 02-cs | `GameTheory-02-NormalForm-CSharp` | 01 + 02-Python | Implémentation C#/.NET from-scratch de la classe `NormalFormGame` | 30 (12 code) | Basse | Oui (Py) |
| 02-P2 | `GameTheory-02-NormalForm-Part2-Python` | 02-Python | Support enumeration, équilibre mixte NxN, vérification `nashpy` | 34 (14 code) | Moyenne | Oui (C#) |
| 02-P2-cs | `GameTheory-02-NormalForm-Part2-CSharp` | 02-CSharp + 02-Part2-Python | Support enumeration en C#/.NET | 36 (14 code) | Moyenne | Oui (Py) |
| 02b | `GameTheory-02b-Lean-Definitions-Lean` | 02-Python — kernel Lean 4 WSL | Formalisation Lean 4 des définitions de base (Partie 4 de la série) | 52 (21 code) | Moyenne | Lean |
| 02c | `GameTheory-02c-Travelers-Dilemma-Python` | 02-Python | Fonction de paiement, raisonnement sur un cas non trivial (Traveler's Dilemma) | 32 (8 code) | Moyenne | Oui (C#) |
| 02c-cs | `GameTheory-02c-Travelers-Dilemma-CSharp` | 02c-Python + 02-CSharp | Twin C# du 02c | 29 (8 code) | Moyenne | Oui (Py) |
| **02d** | `GameTheory-02d-Epistemique-Connaissance-Commune-Python` | 02-Python (élimination itérée) | Modèle à **partitions** (mondes $\Omega$, information $P_i$), opérateur de connaissance $K_i$ et axiomes **S5**, **connaissance commune** comme point fixe (distincte de la connaissance mutuelle), **agreeing to disagree** d'Aumann 1976 démontré par énumération exhaustive avec contrôle négatif | 23 (8 code) | **Moyenne** | Non |
| 03 | `GameTheory-03-Topology2x2-Python` | 02-Python | Représentation ordinale (rangs 1-4), 576 jeux 2x2, archétypes Robinson-Goforth | 82 (26 code) | **Moyenne** | Oui (C#) |
| 03-cs | `GameTheory-03-Topology2x2-CSharp` | 03-Python + 02-CSharp | Twin C# — classification ordinale from-scratch | 40 (13 code) | Moyenne | Oui (Py) |
| **03b** | `GameTheory-03b-Chemins-de-Swaps-Lean-Python` | 03-Python **+ 03c** (murs) | Distance de swap, BFS sur les 576 sommets, sphères | 33 (13 code) | Haute | Non |
| **03c** | `GameTheory-03c-Chambres-et-Murs-Python` | 03-Python | Ordres faibles $\mathbb{R}^4$, **murs** (joints de codimension), botanique des jeux à égalités | 38 (13 code) | Haute | Non |
| **03d** | `GameTheory-03d-Le-Joueur-LLM-Python` | 03-Python | LLM-as-agent, six familles (win-win, dilemme, unfair, cyclique, biaisé, …) | 26 (11 code) | Haute | Non |
| **03f** | `GameTheory-03f-Meta-Actions-Tarifees-Python` | 03-Python + 03c + 03d | Méta-actions tarifées, parcours complet d'un agent qui change les règles | 70 (27 code) | **Très haute** | Non |
| **03g** | `GameTheory-03g-Deux-Especes-de-Fleches-Python` | 03-Python + 03c | Distinction flèche-transformation vs flèche-morphisme (catégoriel) | 30 (10 code) | Très haute | Non |
| 04 | `GameTheory-04-NashEquilibrium-Python` | 01-03, best response, algèbre linéaire | Équilibre de Nash pur/mixte, théorème de Nash 1950, condition d'indifférence, support enumeration, analyse paramétrique | 38 (14 code) | **Moyenne** | Oui (C#) |
| 04-cs | `GameTheory-04-NashEquilibrium-CSharp` | 04-Python + twins C# de 02 | Support enumeration from-scratch (élimination de Gauss), ponts Gambit CLI (NFG) et `nashpy`, comparaison multi-moteurs | 39 (17 code) | Haute | Oui (Py) |
| 04b | `GameTheory-04b-Lean-NashExistence-Lean` | 02b-Lean, topologie (continuité, compacité, convexité), tactiques Lean | Simplexe standard, point fixe de Brouwer, correspondance de meilleure réponse perturbée, preuve d'existence de Nash **formalisée** | 44 (20 code) | **Très haute** | Lean |
| 04c | `GameTheory-04c-NashExistence-Python` | 04-Python | Illustrations numériques de Brouwer (1D puis simplexe), itération de points fixes, contre-exemples (non compact / discontinu / non convexe), lecture guidée de `math-xmum/Brouwer` | 40 (15 code) | Haute | Oui (C#) |
| 04c-cs | `GameTheory-04c-NashExistence-CSharp` | 04-Python, .NET 9 + dotnet-interactive | Point fixe 1D → simplexe, dynamique de meilleure réponse, visualisation ASCII — **from-scratch, zéro lib externe** | 25 (10 code) | Haute | Oui (Py) |
| 04d | `GameTheory-04d-Marchandage-Asymetrique-Python` | 04-Python | Point de désaccord (Nash 1950), désir (composante) vs dépendance (faisceau entier), contre-exemple au principe du moindre intérêt, robustesse au générateur de poids | 24 (12 code) | Haute | Non |
| **04g** | `GameTheory-04g-Supermodularite-Python` | 04-Python + 04c-Python | **Treillis** produit, ordre composante par composante, **supermodularité**, différences croissantes, clôture de l'ensemble des équilibres purs ; réutilise l'organe `game_theory_utils.py` (`NormalFormGame`, `find_pure_nash`, `gale_shapley`) | 38 (13 code) | **Haute** | Non |
| **04h** | `GameTheory-04h-Routing-PriceOfAnarchy-Python` | 04-Python | Jeux de **routage / congestion** à flux fractionnaire, **équilibre de Wardrop** (= Nash du jeu de routage), **optimum social**, **price of anarchy mesuré** (exemple de Pigou, borne 4/3) | 20 (8 code) | **Moyenne** | Non |
| 04e | `GameTheory-04e-Reflective-Oracles-Python` | Aucune section Prérequis — side track de 04 ; source primaire Fallenstein/Taylor/Christiano 2015 | Oracles réflexifs, requête $(M,p)$, menteur probabiliste, décision causale et oracle utilitaire (thm 3.1), agents intégrés et équilibre de Nash (thm 4.1), restriction finie (thm 5.1) | 39 (18 code) | **Très haute** | Non |
| 04f | `GameTheory-04f-Theories-Decision-Predicteur-Python` | 04e (chaîné par navigation), probabilités et calcul causal | Problème de Newcomb, EDT/CDT/UDT, lésion de Fisher, CCDT d'Edgington ≡ EDT, 2TDT-1CDT (réplicateur), inattention rationnelle (Blahut-Arimoto) | 63 (23 code) | **Très haute** | Non |
| 05 | `GameTheory-05-ZeroSum-Minimax-Python` | 01-04, stratégie mixte, bases de PL | Jeux à somme nulle, maximin/minimax purs, point-selle, minimax de von Neumann 1928, résolution par `linprog`, dualité forte, Colonel Blotto | 39 (14 code) | **Moyenne** | Oui (C#) |
| 05-cs | `GameTheory-05-ZeroSum-Minimax-CSharp` | 05-Python + twin C# de 04 | Minimax résolu par **trois moteurs** : simplexe from-scratch, Google.OrTools (Glop LP), Gambit CLI — verdict SOTA-OK, dualité primal/dual | 38 (15 code) | Haute | Oui (Py) |
| 05b | `GameTheory-05b-Lean-Minimax-Lean` | 05-Python, pratique du lake Lean | Companion formel de `minimax_lean` : matrice de gains, payoff bilinéaire, concavité/convexité, quatre hypothèses de Sion, point-selle de von Neumann **zéro `sorry`** (`#print axioms`) | 19 (5 code) | **Très haute** | Lean |

Les numéros en gras sont ceux qui **diffèrent de la numérotation citée dans les deux ledgers antérieurs** (décalage d'une lettre sur le bloc 03, entrées nouvelles) : c'est la colonne à recouper si l'on relit les anciennes tables.

## Paliers consolidés

Les deux ledgers décrivaient chacun leurs paliers localement ; recoupés sur 29 carnets, il en reste **cinq** — effectifs réels **1 / 2 / 11 / 9 / 6** — et la frontière entre les deux derniers s'est déplacée.

1. **Entrée (Basse)** — `01-Setup` seul carnet sans prérequis : il pose l'environnement **et** le premier exemple. Point d'entrée unique de la série.
2. **Cadre formel (Basse)** — `02-Python` et son twin C#. Le jumeau ne s'ajoute pas à la théorie, il la re-dérive : pour une audience Python-first, lire le Python d'abord ; la réciproque vaut pour .NET-first.
3. **Application (Moyenne)** — `02-Part2*` (équilibres mixtes), `02b` (formalisation), `02c*` (cas empirique), **`02d`** (épistémique), `03`/`03-cs` (classification des 576 jeux), `04` (Nash), **`04h`** (PoA), `05` (minimax et dualité). Onze carnets — tous ceux gradés Moyenne : c'est le plateau le plus large de la série, et le seul où un lecteur peut s'arrêter sans manquer une marche.
4. **Twins enrichis et géométrie ordinale (Haute)** — `03b`, `03c`, `03d`, `04-cs`, `04c`/`04c-cs`, `04d`, **`04g`**, `05-cs`. Le constat du ledger fournée A se confirme et s'élargit : **en 04/05 le twin C# dépasse son Python** (`04-cs` ajoute Gauss + Gambit + `nashpy`, `05-cs` arbitre trois moteurs LP), alors qu'en 02/03 il le re-dérive.
5. **Murs (Très haute)** — `03f`, `03g`, `04b`, `04e`, `04f`, `05b`. Ces six carnets supposent le track principal acquis **et** un bagage externe (tactiques Lean, topologie, littérature MIRI/decision theory, catégories). `03f` est le plus dense en code de la série et le seul à faire changer les règles par l'agent lui-même ; `03-Topology2x2` reste le plus long toutes catégories.

## Ordre cible proposé (scope 2 de l'acceptance)

L'acceptance de #15615 demande un « ordre cible validé (user ou coordinateur) avant toute exécution ». Le voici, dérivé des prérequis **déclarés** dans les carnets — pas d'une préférence éditoriale.

### La séquence

```text
01
  → 02 → 02-cs → 02-P2 → 02-P2-cs → 02b → 02c → 02c-cs → 02d
  → 03 → 03-cs → 03c → 03b → 03d → 03f → 03g
  → 04 → 04-cs → 04b → 04c → 04c-cs → 04d → 04g → 04h → 04e → 04f
  → 05 → 05-cs → 05b
```

### Les quatre écarts à l'ordre numérique, chacun justifié par un prérequis déclaré

| Écart | Motif mesuré |
|---|---|
| **`03c` avant `03b`** | `03b-Chemins-de-Swaps` calcule une distance sur les **murs** que `03c-Chambres-et-Murs` pose. L'inversion existe depuis la numérotation d'origine (le ledger Fondations la signalait déjà comme `03b` avant `03a`) et **#18001 l'a conservée** en décalant les deux ensemble. |
| **`04e`/`04f` en fin de bloc 04** | `04e` ne déclare **aucun** prérequis de la série : il est side track, adossé à une source externe (Fallenstein/Taylor/Christiano 2015). `04f` en dépend par navigation. Les placer après `04h` évite de couper le track principal par un mur. |
| **`04g`/`04h` après `04d`** | Tous deux approfondissent `04` ; `04g` réutilise en plus l'organe de `04c`. Ils ne bloquent rien en aval, donc leur position est libre — et se cale sur l'ordre d'entrée dans la série. |
| **twins C# systématiquement après leur Python** | Le contenu théorique vit d'abord côté Python en 02/03 ; en 04/05 le twin C# **ajoute** des moteurs. Dans les deux cas il se lit après. |

### Ce que l'ordre cible ne demande pas

**Aucun renommage.** #18001 vient de renuméroter 93 carnets ; renuméroter une seconde fois pour déplacer `03b` avant `03c` coûterait une vague équivalente pour un gain de lecture marginal. La part documentaire de l'option B du ledger Fondations est **déjà en place** : `03b` porte sa ligne de prérequis dès l'introduction (« **Prérequis** : GameTheory-3 (générateurs), GameTheory-3b (codimension, murs, facettes), GameTheory-03h (deux espèces de flèches) »). Ce qui reste à corriger est autre chose, et chiffré : cette ligne **nomme les ordinaux d'avant #18001** — `GameTheory-3b` est le `03c` actuel, `GameTheory-03h` le `03g` actuel — et **5 carnets sur 29** gardent leur ordinal périmé en H1 : `03b` titré « GameTheory-3a », `03c` « GameTheory 3b », `03d` « GameTheory-3c », `03f` « GameTheory 3e », `03g` « GameTheory-03h ». Le résiduel exécutable est donc exactement le balayage des titres H1 listés ci-dessus plus la ligne de prérequis de `03b`, un balayage markdown-only sans renommage de fichier — les ordinaux des **fichiers**, eux, sont corrects depuis #18001.

**Aucun remplissage de trou.** Le bloc 03 porte désormais deux ordinaux libres : `03a` (jamais réattribué après le relettrage) et `03e` (libéré par la sortie du carnet Plan-de-déformation vers Dynamics). Ils **restent libres** : sur une série à numérotation par accrétion, un trou est une trace, pas un défaut — le combler imposerait de renuméroter les carnets postérieurs.

## Hors périmètre — et ce qui reste à faire pour clore l'issue

Ce ledger livre la **tranche 01-05** du tableau consolidé (29 carnets sur 111). Il ne prétend pas clore le step final de #15615 ; il en lève les deux obstacles qui bloquaient son démarrage, et laisse le reste mesuré plutôt que supposé.

| Reste à faire | État au 2026-10-24 |
|---|---|
| **Blocs 06-20** (81 carnets) | Déjà mesurés par les fournées B (#20289), C (#20294) et D — mais **aux têtes `a492cda2b33`, `5e96ffec4cb`, `cfa6bbaea4ca`**, soit avant les mouvements constatés ici. Une re-mesure est due avant de les fusionner dans une table unique. |
| **Bloc 21** (1 carnet) | **Jamais gradé** : il est postérieur à la fournée D, qui déclarait la série close au bloc 20. |
| **Recensement** | Établi ici (111 carnets, 21 blocs) — c'est la base de comptage que la fournée D cherchait (elle corrigeait 99 en 100). |
| **Exécution du réordonnancement** (scope 3) | Dépend de la validation de l'ordre cible ci-dessus. Le tableau se propose, il ne s'applique pas. |

Les fournées B/C/D et ce ledger partagent le **même protocole** (prérequis déclarés, concepts de la première section, difficulté sur la combinatoire et la longueur, jumeau) : la fusion en une table unique est mécanique dès que les trois fournées sont re-mesurées à une tête commune.

## Source des données

- Arbre : `git ls-tree --name-only origin/main MyIA.AI.Notebooks/GameTheory/` filtré sur `GameTheory-0[1-5]`, tête `8957d81ad44` (2026-10-24) → **29 carnets**.
- Comptes de cellules : `git show origin/main:<carnet>` puis comptage JSON (`cell_type == "code"`), sur les 29 carnets — **re-mesure**, d'où les écarts de quelques unités avec les tables du 2026-09-28 et du 2026-10-10.
- Table de renommage : `git show --name-status -M 09e96fa5eaf -- MyIA.AI.Notebooks/GameTheory/` (blocs 01-05).
- État de #18001 : `gh pr view 18001 --json state,mergedAt` → **MERGED**, `2026-09-29T22:39:32Z`.
- Histoires de fichiers : `gh api repos/jsboige/CoursIA/commits?path=<carnet>` (le clone local est shallow, `git log` y est muet — l'API fait foi).
- Lecture firsthand des trois carnets entrés (`02d`, `04g`, `04h`) : introduction + première section, pour la colonne « concepts introduits ».

## Voir aussi

- #15615 — issue pivot (plan en fournées A-D, acceptance scope 1-3)
- [15615-gradation-foundations.md](15615-gradation-foundations.md) — mesure du 2026-09-28, **antérieure à #18001** (blocs 02 + 03, 15 carnets), PR #18195
- [15615-gradation-fournee-a.md](15615-gradation-fournee-a.md) — mesure du 2026-10-10, blocs 01/04/05 (12 carnets)
- #18001 — **MERGED** le 2026-09-29 : le relettrage dont les deux ledgers attendaient l'arbitrage
- #19484 — sortie de `03e-Plan-de-deformation-Python` vers `Dynamics-09-Biens-Publics`
- #19461 / #22048 — entrée de `02d` · #21931 / #21938 — entrée de `04g` · #21927 / #21979 — entrée de `04h`
- [15573-cadrage-granulaire.md](15573-cadrage-granulaire.md) — le ledger parent qui a détecté le cadrage par item unitaire sur #15615
