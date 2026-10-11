# Ledger — Issue #15615 (gradation GameTheory, fournée A : carnets 01, 04, 05)

> **Bornage strict** : ce ledger couvre les **carnets 01, 04 et 05** de la série GameTheory sur `origin/main` au 2026-10-10. Il **complète la fournée A** (blocs 01-05) ouverte par la strate « Fondations » ([15615-gradation-foundations.md](15615-gradation-foundations.md), carnets 02 + 03). Les blocs 06 et au-delà font l'objet des fournées B-D.

## Origine

Issue #15615 — audit de gradation demandé après le nit user du 2026-09-11 (« remettre un peu de cohérence dans la gradation »). Le fil a depuis posé un plan en fournées A-D (A = blocs 01-05) ; la strate « Fondations » a livré la première moitié (15 carnets, PR #18195). Ce ledger livre la seconde moitié : **12 carnets** (01 × 1, 04 × 8, 05 × 3).

**Mesure de périmètre** : le cadrage de la fournée A annonçait 33 carnets ; l'arbre au 2026-10-10 en porte **27** pour les blocs 01-05 (01×1, 02×7, 03×8, 04×8, 05×3). L'écart vient des renuméros/absorptions intervenus entre la rédaction du cadrage et la mesure — **l'arbre fait foi**. Fournée A = complète avec ce ledger (12) + Fondations (15).

## Méthode

Identique au ledger Fondations, pour chaque carnet :

1. **Prérequis** : carnets dont la section 1 déclare explicitement les acquis utilisés (lecture du front-matter, de la cellule d'introduction, des liens de navigation).
2. **Concepts introduits** : première section markdown qui définit une notion nouvelle.
3. **Difficulté** : échelle **Basse / Moyenne / Haute / Très haute**, mesurée sur la combinatoire du sujet et la longueur du carnet (cellules total / cellules code) — la longueur est un **proxy** de difficulté technique, pas un verdict.
4. **Jumeau** : `True` si le carnet existe en deux versions (Python + C#/.NET, ou track principal + track Lean).

## Tableau de gradation — fournée A (blocs 01, 04, 05)

| # | Carnet | Prérequis déclarés | Concepts introduits | Cells | Diff. | Jumeau |
|---|---|---|---|---:|---|---|
| 01 | [GameTheory-01-Setup-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-01-Setup-Python.ipynb) | Aucun carnet — Python 3.9+, bases Python/NumPy | Environnement de la série (Nashpy, OpenSpiel, WSL), premier exemple : Dilemme du Prisonnier, matrice de gains, recherche d'équilibre, plan des 4 parties | 69 (22 code) | **Basse** | Non |
| 04 | [GameTheory-04-NashEquilibrium-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04-NashEquilibrium-Python.ipynb) | Notebooks 1-3 (forme normale, topologie 2x2), best response, algèbre linéaire | Équilibre de Nash pur/mixte, théorème de Nash 1950, condition d'indifférence, support enumeration, analyse paramétrique | 36 (14 code) | **Moyenne** | Oui (C#) |
| 04-cs | [GameTheory-04-NashEquilibrium-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04-NashEquilibrium-CSharp.ipynb) | 04-Python + jumeaux C# de 02 | Support enumeration **from-scratch** (élimination de Gauss), ponts Gambit CLI (format NFG) et nashpy, comparaison multi-moteurs | 38 (17 code) | Haute | Oui (Py) |
| 04b | [GameTheory-04b-Lean-NashExistence-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04b-Lean-NashExistence-Lean.ipynb) | 02b-Lean-Definitions, topologie (continuité, compacité, convexité), tactiques Lean | Simplexe standard, théorème du point fixe de Brouwer, correspondance de meilleure réponse perturbée, structure de la preuve d'existence de Nash — **formalisée en Lean 4** | 44 (20 code) | **Très haute** | Non (track Lean) |
| 04c | [GameTheory-04c-NashExistence-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04c-NashExistence-Python.ipynb) | 04 (définition et calcul), numpy/matplotlib | Illustrations numériques de Brouwer (1D puis simplexe), itération de points fixes, Matching Pennies comme point fixe, contre-exemples (non compact / discontinu / non convexe), lecture guidée du dépôt math-xmum/Brouwer | 40 (15 code) | Haute | Oui (C#) |
| 04c-cs | [GameTheory-04c-NashExistence-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04c-NashExistence-CSharp.ipynb) | 04-Python, notions de théorie des jeux, .NET 9 + dotnet-interactive | Point fixe par itération 1D → simplexe, dynamique de meilleure réponse (convergence vers Nash), visualisation ASCII — **from-scratch C# pur, zéro lib externe** | 25 (10 code) | Haute | Oui (Py) |
| 04d | [GameTheory-04d-Marchandage-Asymetrique-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04d-Marchandage-Asymetrique-Python.ipynb) | 04 (équilibres purs et mixtes), intuitions sur préférences et alternatives extérieures | Point de désaccord (Nash 1950), désir (composante) vs dépendance (faisceau entier), contre-exemple au principe du moindre intérêt, robustesse au générateur de poids | 24 (12 code) | Haute | Non |
| 04e | [GameTheory-04e-Reflective-Oracles-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04e-Reflective-Oracles-Python.ipynb) | Aucune section Prérequis déclarée — positionné side track de 04 ; source primaire Fallenstein/Taylor/Christiano 2015 | Oracles réflexifs, requête $(M,p)$, menteur probabiliste, décision causale et oracle utilitaire (thm 3.1), agents intégrés et équilibre de Nash (thm 4.1), restriction finie et jeu auxiliaire (thm 5.1) | 39 (18 code) | **Très haute** | Non |
| 04f | [GameTheory-04f-Theories-Decision-Predicteur-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-04f-Theories-Decision-Predicteur-Python.ipynb) | 04e (chaîné par navigation), probabilités et calcul causal | Problème de Newcomb, EDT/CDT/UDT, lésion de Fisher, CCDT d'Edgington ≡ EDT, 2TDT-1CDT (dynamique du réplicateur), inattention rationnelle (Blahut-Arimoto) | 63 (23 code) | **Très haute** | Non |
| 05 | [GameTheory-05-ZeroSum-Minimax-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-05-ZeroSum-Minimax-Python.ipynb) | Notebooks 1-4 (fondations, forme normale, topologie, Nash), stratégie mixte, bases de PL | Jeux à somme nulle, stratégies maximin/minimax (pures), point-selle, théorème minimax de Von Neumann 1928, résolution par programmation linéaire (`linprog`), dualité forte, Colonel Blotto | 38 (14 code) | **Moyenne** | Oui (C#) |
| 05-cs | [GameTheory-05-ZeroSum-Minimax-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-05-ZeroSum-Minimax-CSharp.ipynb) | 05-Python + twin C# de 04 | Théorème minimax résolu par **trois moteurs** : simplexe from-scratch, Google.OrTools (Glop LP), Gambit CLI — verdict SOTA-OK, dualité primal/dual | 38 (15 code) | Haute | Oui (Py) |
| 05b | [GameTheory-05b-Lean-Minimax-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-05b-Lean-Minimax-Lean.ipynb) | 05 (théorème minimax), pratique du lake Lean | Companion formel du lake `minimax_lean` : matrice de gains, payoff bilinéaire, concavité/convexité, quatre hypothèses de Sion, point-selle de von Neumann **zéro `sorry`** (`#print axioms`) | 19 (5 code) | **Très haute** | Non (companion formel) |

## Observations

### Quatre paliers dans la fournée A

1. **Palier « Entrée » (Basse)** : `01-Setup` — le seul carnet sans prérequis de la série ; il pose l'environnement ET le premier exemple (Dilemme du Prisonnier résolu par Nashpy). La strate Fondations avait commencé à 02 en le laissant implicite : ce ledger referme la lacune, 01 est bien le point d'entrée.
2. **Palier « Track principal » (Moyenne)** : `04` et `05` — la colonne vertébrale Nash puis minimax, à lire dans l'ordre après les Fondations.
3. **Palier « Jumeaux C# enrichis » (Haute)** : `04-cs`, `04c`, `04c-cs`, `04d`, `05-cs` — les twins C# ne se contentent plus de re-dériver : ils ajoutent des moteurs que le Python n'a pas (Gambit CLI, OrTools/Glop).
4. **Palier « Side tracks de recherche » (Très haute)** : `04b` (Brouwer formalisé), `04e` (oracles réflexifs), `04f` (théories de la décision), `05b` (Sion/von Neumann) — le mur de la fournée A. Ces carnets supposent le track principal acquis ET un bagage externe (tactiques Lean, littérature MIRI/decision theory).

### Inversion du pattern jumeau vs strate Fondations

En 02/03, la substance théorique vit côté Python et le twin C# re-dérive ([Fondations, Observations](15615-gradation-foundations.md)). En 04/05 c'est l'inverse : le twin C# **dépasse** son Python d'origine — `04-cs` ajoute Gauss from-scratch + Gambit + nashpy ; `05-cs` arbitre trois moteurs LP (simplexe, Glop, Gambit, verdict SOTA-OK). La recommandation de lecture (Python d'abord pour la théorie) reste valable, mais le twin C# est ici un **enrichissement**, pas une copie.

### Paire companion 04b/04c : pas de boucle de prérequis

Contrairement à la lacune 03a/03b des Fondations, la paire Lean/Python de l'existence de Nash est saine : `04c-Python` déclare `04` en prérequis (pas `04b`), et `04b-Lean` déclare `02b`. Les deux se lisent indépendamment, l'un formel, l'autre numérique.

### Deux croix de lecture pour la consolidation (hors scope gradation)

- **Référence périmée dans 04c-Python** : l'introduction dit « accompagne le notebook Lean 18 » — vestige d'une numérotation antérieure (aucun carnet 18 dans la série aujourd'hui). À corriger lors d'un sweep doc.
- **Décalage d'ordinaux bloc 03** : le ledger Fondations nomme `03a-Chemins-de-Swaps` … `03e`/`03h` ; l'arbre courant porte `03b-Chemins-de-Swaps` … `03f`/`03g` (renum intervenue après #18195). Un lecteur croisant les deux ledgers doit appliquer le décalage d'une lettre. Une resynchronisation du ledger Fondations est souhaitable avant le tableau consolidé.

## Hors périmètre (fournées suivantes)

- **Fournée B** : blocs 06-10 (Evolution/Trust, jeux dynamiques, répétés, bayésiens) — ~30 carnets.
- **Fournées C-D** : blocs 11-25.
- **Tableau consolidé** des 27 carnets 01-05 (fusion Fondations + fournée A) : dépend de l'arbitrage #18001, comme recommandé par le ledger Fondations.

## Source des données

- Lecture firsthand des 12 carnets (front-matter + section 1 + liens de navigation) via `git show origin/main:<carnet>` au 2026-10-10, head `a492cda2b33`.
- Statistiques cellules : extraction JSON par script de session (kernelspec, comptes code/markdown, headers).
- Comptage de périmètre : `git ls-tree origin/main MyIA.AI.Notebooks/GameTheory/` filtré blocs 01-05.

## Voir aussi

- #15615 — issue pivot (plan en fournées A-D)
- [15615-gradation-foundations.md](15615-gradation-foundations.md) — strate « Fondations » (carnets 02 + 03), PR #18195
- #14944 — Epic renum (mécanique)
- #18001 — PR `rename GameTheory — 93 carnets` dont l'arbitrage conditionne le tableau consolidé
- [15573-cadrage-granulaire.md](15573-cadrage-granulaire.md) — ledger parent
