# Complexity — Théorie de la complexité calculatoire

Série d'hommage aux fondateurs et aux moments fondateurs de la théorie de la complexité.
Chaque notebook prend un texte fondateur, le fait **tourner** (machines construites pas
à pas, comptes d'opérations exacts, simulations Monte Carlo, chronos encadrés), puis
confronte sa formalisation à l'état de
[Mathlib](https://github.com/leanprover-community/mathlib4) — ce qui y existe, ce qui
n'y existe pas encore, et pourquoi.

## Notebooks

| Notebook | Hommage | Contenu | Langue |
|---|---|---|---|
| [`Complexity-01-HartmanisStearns-TimeHierarchy.ipynb`](Complexity-01-HartmanisStearns-TimeHierarchy.ipynb) | Juris Hartmanis & Richard E. Stearns (prix Turing 1993, « On the Computational Complexity of Algorithms », 1965) | Machines de Turing multi-rubans simulées avec comptage exact des pas ; trois croissances mesurées ($n \log n$, $n^2$, $2^n$) ; subset-sum comme séparatrice honnête (force brute vs programmation dynamique, compteurs déterministes) ; diagonalisation budgétée sur une famille finie ; théorème de hiérarchie en temps $\mathrm{TIME}(f) \subsetneq \mathrm{TIME}(f \log f)$ ; encart sur le **gap Mathlib** (aucune couche `Computability/Complexity` : pas de $\mathrm{TIME}(f)$, pas de machine universelle avec overhead temporel, pas de théorème de hiérarchie) | Français |
| [`Complexity-02-OnlineConjectures-Secretary-KServer.ipynb`](Complexity-02-OnlineConjectures-Secretary-KServer.ipynb) | Sahil Singla & Christian Coester, Elias Koutsoupias, Marek Zbysiński (les deux preprints de septembre 2026 : conjecture du secrétaire matroïdal 2007 et conjecture k-server ~1990, tombées à 24 h d'écart) | Baseline $1/e$ du secrétaire classique mesurée par Monte Carlo ($n$ = 20/100/1000) ; deux matroïdes à oracle d'indépendance (uniforme, graphique) avec optimum offline exact et compétitivité de deux stratégies online ; **work function algorithm implémenté exactement** (DP sur les $\binom{m}{2}$ configurations) : sur le cycle $C_5$, ratio WFA 1,67 sous la borne $k=2$ quand greedy explose (20 à 60 requêtes, 160 à 480 — non compétitif) ; tableau du double visage randomisation/déterminisme ; trois niveaux épistémiques Mesuré/Cité/Absent (prudence « preuve annoncée ») ; encart **gap Mathlib** (matroïdes présents, compétitivité/k-server/work functions absents) | Français |

## Position dans le dépôt

La série rejoint le dialogue formel existant : les jumeaux Lean (`Search/discrepancy_lean/`,
`GameTheory/social_choice_lean/`, …) montrent ce que Mathlib **sait** prouver ; cette série
montre, machines en main, ce que la couche complexité **exigerait** — et mesure le manque
(`Mathlib/Computability/` couvre machines de Turing, halting, degrés de Turing, mais aucune
classe de complexité temporelle : encart §6 du notebook 01 ; `Mathlib.Combinatorics.Matroid`
existe mais compétitivité, k-server et work functions sont absents : encart §6 du notebook 02).
Le notebook 02 fonde la saisie de l'**algorithmique online** dans le dépôt — décisions
irréversibles sous incertitude, ratio compétitif — reliée à la RL et à la théorie des jeux.

## Prérequis

Python 3.10+ (kernel `python3`) : `numpy`, `matplotlib` — le socle standard du dépôt.
Aucune dépendance externe : tout est construit dans le notebook, rubans, transitions,
oracles d'indépendance et work functions compris, pour que chaque pas soit auditable.

## Exercices

Chaque notebook embarque au moins trois exercices (`TODO etudiant`) : étendre une machine,
dériver un compte, déplacer un budget — les stubs s'exécutent sans erreur (règle C.1 du
dépôt) et les corrigés restent la propriété de l'étudiant.
