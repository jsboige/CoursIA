# Ledger — Issue #15615 (gradation GameTheory, fournée B : blocs 06 à 10)

> **Bornage strict** : ce ledger couvre les **carnets des blocs 06, 07, 08, 09 et 10** de la série GameTheory sur `origin/main` au 2026-10-10 (head `a492cda2b33`). Il poursuit la fournée A (`15615-gradation-fournee-a.md`, PR #20288 — carnets 01/04/05) et la strate « Fondations » (`15615-gradation-foundations.md`, carnets 02 + 03).

## Origine

Issue #15615 — audit de gradation, plan en fournées A-D posté au fil. Fournée B annoncée « ~30 carnets » au cadrage ; **l'arbre au 2026-10-10 en porte 27** (06×13, 07×2, 08×6, 09×4, 10×2) — l'arbre fait foi, même règle qu'en fournée A.

## Méthode

Identique aux ledgers précédents : prérequis déclarés (section 1 / front-matter), concepts introduits (première section définissante), difficulté sur l'échelle **Basse / Moyenne / Haute / Très haute** (combinatoire du sujet + longueur comme proxy), jumeau (Py/C# ou principal/Lean).

## Tableau de gradation — fournée B (blocs 06-10)

| # | Carnet | Prérequis déclarés | Concepts introduits | Cells | Diff. | Jumeau |
|---|---|---|---|---:|---|---|
| 06 | [GameTheory-06-EvolutionTrust-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06-EvolutionTrust-Python.ipynb) | Notebooks 1-5, stratégie dominante/DP, bases de dynamique | Dilemme du Prisonnier Itéré, tournoi d'Axelrod (bruit), dynamique du réplicateur, ESS/NSS, processus de Moran, comparaison au moteur SOTA `axelrod` | 63 (23 code) | **Moyenne** | Oui (C#) |
| 06-cs | [GameTheory-06-EvolutionTrust-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06-EvolutionTrust-CSharp.ipynb) | 06-Python + jumeaux C# (pont twin) | Tournoi Axelrod **from-scratch**, trace ASCII, réplicateur, ESS/NSS (#12472), pont .NET→PythonNet→`axelrod` (#10459) | 45 (16 code) | Haute | Oui (Py) |
| 06b | [GameTheory-06b-Lean-RepeatedGames-Lean-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06b-Lean-RepeatedGames-Lean-Python.ipynb) | Aucune section déclarée — compagnon formel de 06c | Carte du lake `game_theory_lean` : Stage, Discounting (seuil critique), GrimTrigger (frontière d'incitation), Folk (STRETCH honnête), ConeKernel (Bondareva-Farkas) — kernel **Python** présentant le Lean | 30 (11 code) | Haute | Non |
| 06c | [GameTheory-06c-RepeatedGames-FolkTheorem-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06c-RepeatedGames-FolkTheorem-Python.ipynb) | 06-EvolutionTrust | Jeux répétés finis/infinis, facteur d'escompte δ, grim trigger $\delta \ge (T-R)/(T-P)$, Folk Theorem (SPNE), retrait de la punition, statique comparative de α | 36 (14 code) | Moyenne | Oui (C#) |
| 06c-cs | [GameTheory-06c-RepeatedGames-FolkTheorem-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06c-RepeatedGames-FolkTheorem-CSharp.ipynb) | 02-NormalForm + 04-Nash + notions C#/.NET | Jumeau C# du 06c, statique comparative avec MathNet | 25 (10 code) | Moyenne | Oui (Py) |
| 06d | [GameTheory-06d-Sympathie-vs-Engagement-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06d-Sympathie-vs-Engagement-Python.ipynb) | 06c §7 + numpy + intuition de MLE | Protocole de mesure sympathie vs engagement : grille de gains d'autrui, trois mécanismes, estimation par pente puis vraisemblance, contrôles négatifs, IRLS/bootstrap | 37 (14 code) | Haute | Non |
| 06e | [GameTheory-06e-Open-Source-Game-Theory-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06e-Open-Source-Game-Theory-Python.ipynb) | 06, 06c, 06d | Transparence des programmes : `ProgramAgent`, cinq bots, matrice de confrontation, trois états (preuve / absence bornée / non-termination), vérificateur indépendant | 33 (7 code) | Haute | Non |
| 06f-Lean | [GameTheory-06f-Bounded-Agents-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06f-Bounded-Agents-Lean.ipynb) | Aucune déclarée — pivot conceptuel 06e | Companion Lean natif de `ProgramGames.Bounded` : code public, budget de raisonnement fini, interprète total, quatre familles de certificats (coopération, inexploitation, Nash borné, ordre fini des gains) | 31 (12 code) | **Très haute** | Oui (Py) |
| 06f-Py | [GameTheory-06f-Bounded-Agents-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06f-Bounded-Agents-Python.ipynb) | Aucune déclarée — compagnon du module Lean | Rejeu Python des certificats Lean : organes calculables, miroir décidable du Bounded Nash | 34 (11 code) | Haute | Oui (Lean) |
| 06g | [GameTheory-06g-Simulation-Based-Program-Equilibria-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06g-Simulation-Based-Program-Equilibria-Python.ipynb) | Aucune déclarée (nav ← 06j) | Équilibres de jeux-programmes par **simulation** : équivalence comportementale vs preuve syntaxique, analogue fini d'`εGroundedπBot`, trois joueurs et aléa partagé | 24 (8 code) | Haute | Non |
| 06h | [GameTheory-06h-Transparent-Institutions-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06h-Transparent-Institutions-Python.ipynb) | Nash en stratégies pures + PD forme normale (lectures utiles : 06e, 06g) | Programmes transparents comme **institutions** (Critch-Dennis-Russell 2022) : CUPOD, DUPOC, PrudentBot, CIMCIC, sémantique bornée terminante, deux implémentations indépendantes, dix problèmes ouverts | 39 (16 code) | **Très haute** | Non |
| 06i | [GameTheory-06i-Ensembles-Limites-Poincare-Bendixson-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06i-Ensembles-Limites-Poincare-Bendixson-Python.ipynb) | Aucune déclarée — socle implicite : réplicateur de 06 §5 | Théorème de Poincaré-Bendixson en dimension 2 : point fixe / orbite périodique / cycle hétéroclinique, mur $w = l$ dans l'espace des jeux | 27 (11 code) | Haute | Non |
| 06j | [GameTheory-06j-Bounded-Proofs-Reasoning-Costs-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06j-Bounded-Proofs-Reasoning-Costs-Python.ipynb) | Aucune déclarée — prolonge 06e (instrument identique) | Preuves bornées et coût du raisonnement : seuil DUPOC(k) avec courbe, coût $\varepsilon \times$ profondeur, contrôle négatif de restauration de la défection | 24 (11 code) | Haute | Non |
| 07 | [GameTheory-07-ExtensiveForm-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-07-ExtensiveForm-Python.ipynb) | Notebooks 1-6, arbres/graphes, forme normale | Forme extensive : arbre de jeu, ensembles d'information, théorème de Kuhn, nœuds de nature, Kuhn Poker (OpenSpiel), conversion vers forme normale | 35 (15 code) | **Moyenne** | Oui (C#) |
| 07-cs | [GameTheory-07-ExtensiveForm-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-07-ExtensiveForm-CSharp.ipynb) | 07-Python (pont twin) | Twin C# from-scratch, rendu ASCII de l'arbre, infosets, conversion — annexe pont .NET→PythonNet→`pyspiel` (CFR vers la valeur de Kuhn, #10459) | 32 (11 code) | Haute | Oui (Py) |
| 08 | [GameTheory-08-CombinatorialGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-08-CombinatorialGames-Python.ipynb) | Notebooks 1-7, combinatoire | Jeux combinatoires impartiaux : positions P/N, Nim et théorème de Bouton, mex, valeurs de Grundy, théorème de Sprague-Grundy | 34 (11 code) | **Moyenne** | Oui (C#) |
| 08-cs | [GameTheory-08-CombinatorialGames-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-08-CombinatorialGames-CSharp.ipynb) | 08-Python (pont twin) | Twin C# : classification P/N, nim-sum, Sprague-Grundy vérifié sur sommes, parité #4956 | 32 (11 code) | Moyenne | Oui (Py) |
| 08b | [GameTheory-08b-Lean-CombinatorialGames-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-08b-Lean-CombinatorialGames-Lean.ipynb) | 08-CombinatorialGames + bases Lean 4 | `PGame` dans mathlib4 : jeux primitifs, Nim formel, Grundy, **nombres surréels**, API mathlib4 | 22 (7 code) | **Très haute** | Non (companion 08c) |
| 08c | [GameTheory-08c-CombinatorialGames-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-08c-CombinatorialGames-Python.ipynb) | 08 (P/N, Bouton, Grundy, SG) | Approfondissement : périodicité des valeurs de Grundy (Guy 1996), jeu de Wythoff (P-positions, ratio d'or), jeux multi-composantes, Chomp (théorème de Gale) | 40 (14 code) | Haute | Oui (C#) |
| 08c-cs | [GameTheory-08c-CombinatorialGames-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-08c-CombinatorialGames-CSharp.ipynb) | 08 idem | Twin C# du 08c | 31 (14 code) | Haute | Oui (Py) |
| 08d | [GameTheory-08d-Lean-CGT-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-08d-Lean-CGT-Lean.ipynb) | Aucune déclarée — suite 8b/8c (nav) | Lake natif `conway_cgt_lean` : `IGame`/`Game` deux couches, nombres surréels (arithmétique, plongements), nimbers, Sprague-Grundy **exécuté**, module de visite `CGTTour` | 23 (10 code) | **Très haute** | Non |
| 09 | [GameTheory-09-BackwardInduction-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-09-BackwardInduction-Python.ipynb) | Notebooks 7-8, Nash/best response, récursivité | Induction arrière : algorithme, mille-pattes (paradoxe), guerre d'usure, chaîne de magasins (Selten), limites de la rationalité | 39 (15 code) | **Moyenne** | Oui (C#) |
| 09-cs | [GameTheory-09-BackwardInduction-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-09-BackwardInduction-CSharp.ipynb) | Aucune déclarée (twin ; renvoie à « 11-BayesianGames-CSharp » — croix n°3) | Twin C# from-scratch (BCL seule, 0 NuGet) : arbre, induction arrière, centipede/attrition/chain-store, visualisation ASCII | 26 (11 code) | Moyenne | Oui (Py) |
| 09b | [GameTheory-09b-Commitment-Stackelberg-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-09b-Commitment-Stackelberg-Python.ipynb) | Aucune déclarée — socle : matrices de 04 | Stackelberg et performativité : engagement d'une action dominée, félicité et caution ($s^*$ couvre la tentation), quatre régimes, témoin de retenue | 25 (11 code) | Haute | Non |
| 09c | [GameTheory-09c-Stackelberg-SecurityGame-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-09c-Stackelberg-SecurityGame-Python.ipynb) | Aucune déclarée — prolonge 09b (nav) | Stackelberg Security Game : patrouille sur graphe de cibles, capteur imparfait, transition de phase à $p_{fn} = 0{,}5$, signaling | 14 (7 code) | Haute | Non |
| 10 | [GameTheory-10-ForwardInduction-SPE-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-10-ForwardInduction-SPE-Python.ipynb) | Notebooks 7-9, sous-jeu/SPE, jeux de coordination | Raffinements : SPE par induction arrière, menaces crédibles, **induction avant** (Chasse au Cerf avec option extérieure), perfection en mains tremblantes, Burn Money, hiérarchie des raffinements | 37 (15 code) | **Haute** | Oui (C#) |
| 10-cs | [GameTheory-10-ForwardInduction-SPE-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-10-ForwardInduction-SPE-CSharp.ipynb) | 04 (Nash) + 07 (forme extensive) | Twin C# from-scratch (0 NuGet) des raffinements : SPE, trembling-hand $\varepsilon$, induction avant, Beer-Quiche | 39 (14 code) | Haute | Oui (Py) |

## Observations

### Le bloc 06 est le continent de la série

13 carnets sur 27 : le track principal (06) ouvre, puis **dix side tracks** s'empilent (06b à 06j) dont une lignée entière — **les jeux-programmes / AI safety** (06e, 06f×2, 06g, 06h, 06i, 06j : Critch, Barasz, program equilibria, institutions transparentes). C'est la zone Très-haute la plus dense de la série. Ordre de lecture recommandé dans cette lignée : `06e → 06f-Py → 06f-Lean → 06g → 06j → 06h` (06h déclare lui-même 06e/06g comme lectures utiles).

### Track principal = plateau Moyenne, sommet en 10

06, 07, 08, 09 = Moyenne (pédagogie canonique guidée) ; **10 = Haute** (les raffinements — induction avant, trembling-hand — sont le sommet conceptuel du track principal). Les twins C# montent d'un cran quand ils portent un pont PythonNet (#10459 : axelrod, pyspiel) — la série C# est devenue la vitrine SOTA.

### Trois croix de numérotation pour #16231/#14944 (hors scope gradation)

1. **`06f-Bounded-Agents-Lean` est titrée « 06g »** dans sa première cellule — collision de titre avec le fichier `06g-Simulation-Based` (deux carnets affichent « 06g »).
2. **`06j-Bounded-Proofs` est titrée « 06f »** — la permutation des lettres 06f/06g/06j dans les titres ne correspond pas aux noms de fichiers.
3. **`09-cs` se déclare « suite de GameTheory-11-BayesianGames-CSharp »** — le 11 comme prédécesseur du 09 (renvoi de jumeau antérieur à une renum).

S'ajoute une ambiguïté de suffixe : `06b-...-Lean-Python` (kernel **Python** qui dévoile le lake Lean) — le suffixe `-Lean-Python` se lit comme un jumeau alors que c'est un carnet Python à part entière.

### Désalignement mineur de prérequis entre jumeaux

`06c-Python` déclare `06-EvolutionTrust` en prérequis ; son jumeau `06c-C#` déclare `02 + 04` (pas le 06). Les deux sont défendables, mais un lecteur croisé des jumeaux voit deux portes d'entrée différentes — à harmoniser lors d'un sweep doc.

## Hors périmètre (fournées suivantes)

- **Fournée C** : blocs 11-15 (~25 carnets).
- **Fournée D** : blocs 16-25 (~26 carnets).
- **Tableau consolidé** des 54 carnets 01-10 : conditionné à l'arbitrage #18001 (cf. ledger Fondations).

## Source des données

- Lecture firsthand des 27 carnets (front-matter + section 1 + navigation) via `git show origin/main:<carnet>` au 2026-10-10, head `a492cda2b33`.
- Statistiques cellules : extraction JSON par script de session (kernelspec, comptes code/markdown, headers).
- Comptage de périmètre : `git ls-tree origin/main MyIA.AI.Notebooks/GameTheory/` filtré blocs 06-10.

## Voir aussi

- #15615 — issue pivot (plan en fournées A-D)
- `15615-gradation-fournee-a.md` (PR #20288) — carnets 01/04/05
- [15615-gradation-foundations.md](15615-gradation-foundations.md) — carnets 02 + 03 (PR #18195)
- #16231 / #14944 — renum et colonne canonique (destinataires des croix n°1-3)
- #18001 — PR `rename GameTheory — 93 carnets` (mergée 2026-09-29), condition du tableau consolidé
