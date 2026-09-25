# Complexity — Théorie de la complexité calculatoire

La série s'ouvre sur deux notebooks de **découverte** (01-02) qui ne supposent que Python :
compter les pas d'un algorithme, puis distinguer *vérifier* de *trouver* (P, NP, réduction).
Elle continue en hommage aux fondateurs et aux moments fondateurs de la théorie de la
complexité : chaque notebook d'hommage prend un texte fondateur, le fait **tourner**
(machines construites pas à pas, comptes d'opérations exacts, simulations Monte Carlo, chronos encadrés), puis
confronte sa formalisation à l'état de
[Mathlib](https://github.com/leanprover-community/mathlib4) — ce qui y existe, ce qui
n'y existe pas encore, et pourquoi.

## Notebooks

| Notebook | Public | Accrétion | Hommage | Contenu | Langue |
|---|---|---|---|---|---|
| [`Complexity-01-StepCounting.ipynb`](Complexity-01-StepCounting.ipynb) | Découverte | — | — (socle) | Le chronomètre ment un peu : compter des **pas** plutôt que des secondes ; taille d'entrée ; machine de Turing construite pas à pas (incrément binaire, palindrome en $n^2$) ; trois croissances comptées ($n \log n$, $n^2$, $2^n$) par le test de doublement et les pentes log-log ; table de budget à $10^8$ pas/s : ce que chaque croissance permet de traiter en une seconde, une minute, un jour | Français |
| [`Complexity-02-P-NP-Reduction.ipynb`](Complexity-02-P-NP-Reduction.ipynb) | Découverte | — | — (socle) | Vérifier contre trouver sur le Sudoku (324 lectures contre des centaines de milliers d'appels) et sur subset-sum ; programmation dynamique **pseudo-polynomiale** mesurée ; définitions de P et NP ; réduction subset-sum → Partition **exécutée de bout en bout** (transformer, résoudre, retraduire le certificat) et testée sur 400 instances ; le mur exponentiel face à une machine mille fois plus rapide | Français |
| [`Complexity-03-TimeHierarchy.ipynb`](Complexity-03-TimeHierarchy.ipynb) | Licence | — | — (socle) | Budgets imbriqués, inclusion contre séparation stricte, diagonale finie et limites d'une simulation bornée ; trois exercices exécutables | Français |
| [`Complexity-03b-HartmanisStearns-TimeHierarchy.ipynb`](Complexity-03b-HartmanisStearns-TimeHierarchy.ipynb) | Recherche | approfondissement de **03 — Plus de temps, plus de problèmes** | Juris Hartmanis & Richard E. Stearns (prix Turing 1993, « On the Computational Complexity of Algorithms », 1965) | Machines de Turing multi-rubans simulées avec comptage exact des pas ; trois croissances mesurées ($n \log n$, $n^2$, $2^n$) ; subset-sum comme séparatrice honnête (force brute vs programmation dynamique, compteurs déterministes) ; diagonalisation budgétée sur une famille finie ; théorème de hiérarchie en temps $\mathrm{TIME}(f) \subsetneq \mathrm{TIME}(f \log f)$ ; encart sur le **gap Mathlib** (aucune couche `Computability/Complexity` : pas de $\mathrm{TIME}(f)$, pas de machine universelle avec overhead temporel, pas de théorème de hiérarchie) | Français |
| [`Complexity-04-OnlineConjectures-Secretary-KServer.ipynb`](Complexity-04-OnlineConjectures-Secretary-KServer.ipynb) | Recherche | deviendra **04b**, approfondissement du futur 04 *Décider sans connaître la suite* | Sahil Singla & Christian Coester, Elias Koutsoupias, Marek Zbysiński (les deux preprints de septembre 2026 : conjecture du secrétaire matroïdal 2007 et conjecture k-server ~1990, tombées à 24 h d'écart) | Baseline $1/e$ du secrétaire classique mesurée par Monte Carlo ($n$ = 20/100/1000) ; deux matroïdes à oracle d'indépendance (uniforme, graphique) avec optimum offline exact et compétitivité de deux stratégies online ; **work function algorithm implémenté exactement** (DP sur les $\binom{m}{2}$ configurations) : sur le cycle $C_5$, ratio WFA 1,67 sous la borne $k=2$ quand greedy explose (20 à 60 requêtes, 160 à 480 — non compétitif) ; tableau du double visage randomisation/déterminisme ; trois niveaux épistémiques Mesuré/Cité/Absent (prudence « preuve annoncée ») ; encart **gap Mathlib** (matroïdes présents, compétitivité/k-server/work functions absents) | Français |
| [`Complexity-05-AaronsonArkhipov-PermanenteBosonSampling.ipynb`](Complexity-05-AaronsonArkhipov-PermanenteBosonSampling.ipynb) | Recherche | deviendra **05b**, approfondissement du futur 05 *Compter est plus dur que vérifier* | Scott Aaronson & Alex Arkhipov (*The Computational Complexity of Linear Optics*, 2011 — la permanente comme frontière quantique) | La définition $n!$ **exécutée** avec comptes canoniques, vérifiée contre l'énumération brute des couplages parfaits (perm(0/1)) ; **Ryser vectorisé réemployé de Sudoku-15** (`batch_perm8`, généralisé à toute taille) contre Gauss instrumenté : comptes exacts par formules fermées validées par instrumentation — à $n=20$, définition $4{,}9 \times 10^{19}$ opérations contre 5 149 pour Gauss, Ryser/det ≈ $1{,}6 \times 10^4$ en temps à $n=16$ ; #P-difficulté (Valiant 1979) maintenue au niveau **Cité**, FPRAS non négatif (Jerrum–Sinclair–Vigoda) en exception qui désigne les signes ; **BosonSampling jouet** : unitaire Haar (QR, Mezzadri), loi $\lvert\mathrm{perm}\rvert^2$ exacte sur 56/924/12 870 sorties, TV(échantillon, exact) → 0, coût d'énumération extrapolé jusqu'à ~1 an à 1 TFLOP/s pour $(20, 40)$ ; encart **gap Mathlib** — premier verdict **positif** de la série : `Matrix.permanent` existe (114 lignes, forme $n!$) face à un dossier `Determinant/` entier, mais ni Ryser ni couche complexité | Français |
| [`Complexity-06-Aaronson-Dequantification-Stabilizer.ipynb`](Complexity-06-Aaronson-Dequantification-Stabilizer.ipynb) | Recherche | deviendra **06b**, approfondissement du futur 06 *Simuler un circuit quantique classiquement* | Scott Aaronson & Daniel Gottesman (*Improved Simulation of Stabilizer Circuits*, 2004 — déquantifier les suprématies par l'arbitre exécutable) | Le formalisme stabilisateur **exécuté** : table de phase et conjugaison CHP **dérivées des matrices 2×2**, jamais recopiées ; port CHP complet (rowsum, portes, mesures — déterministe par lecture GF(2), aléatoire par re-stabilisation) croisé contre l'état complet 2^n : **84 valeurs propres stabilisatrices exactes au 1e-9** (zéro bruit), distributions TV sous 6× le bruit de sondage, stim en troisième juge ; banc discriminant : bascule **mesurée** dès ~12 qubits, ratio ~1600× à n=20, échelons locaux au-dessus du plancher 2× (le mur réel est plus raide que 2^n : la mémoire aussi a une loi) ; une **seule** porte T ferme le port **et** stim (`no attribute 't'`) — la frontière est Clifford/le-reste, pas quantique/classique | Français |
| [`Complexity-07-ComplexityZoo-Navigation.ipynb`](Complexity-07-ComplexityZoo-Navigation.ipynb) | Recherche | deviendra **07b**, approfondissement du futur 07 *La chaîne des inclusions : L, NL, P, NP* | Scott Aaronson (fondateur du Complexity Zoo, 2004 — plus de 500 classes répertoriées) ; Theodore Baker, John Gill, Robert Solovay (*Relativizations of the P=?NP Question*, 1975) | La chaîne $L \subseteq NL \subseteq P \subseteq NP$ **tournée sur instances** : atteignabilité décidée deux fois — vérificateur à 2 mots de mémoire (certificat lu une fois, accord sur 4 tailles, faux témoin amputé refusé) contre DFS dont la pile explore ~$n/3$ sommets ; 2-SAT (Kosaraju, linéaire, $n=800$) contre 3-SAT (DPLL, densité-seuil $4{,}267n$) : facteurs de croissance **mesurés** par variable (~1,10× en noeuds, ~1,16× en temps), 20 certificats sur 20 vérifiés en polynomial ; **Baker–Gill–Solovay exécuté** — monde A : oracle diagonal, 4 machines vaincues par basculement d'un seul témoin, le côté NP exhaustif confirme $L_O$ sur chaque stade ; monde B : l'oracle QBF donne $P^B = NP^B$ en une requête — la barrière de relativisation vue du jouet ; carte du Zoo à 8 arêtes classées Mesuré/Cité/Ouvert (+ carte mermaid) ; encart **gap Mathlib** : `Computability/` couvre la calculabilité, mais aucune classe à bornage — le Zoo est absent | Français |

## Parcours

La série se lit de haut en bas : chaque notebook principal ne suppose que ceux qui le
précèdent. Les notebooks d'hommage, écrits pour un lecteur déjà familier du domaine,
deviennent des **approfondissements** (suffixe `b`) : chacun se greffe sur un notebook
principal de niveau licence qui en pose d'abord les notions.

| Position | Notebook principal | Public | Approfondissement |
|---|---|---|---|
| 01 | Compter des pas | Découverte | — |
| 02 | Vérifier ou trouver : P, NP, certificat, réduction | Découverte | — |
| 03 | [Plus de temps, plus de problèmes](Complexity-03-TimeHierarchy.ipynb) | Licence | [03b — Hartmanis–Stearns](Complexity-03b-HartmanisStearns-TimeHierarchy.ipynb) |
| 04 | Décider sans connaître la suite *(à venir)* | Licence | 04b — conjectures online (aujourd'hui 04) |
| 05 | Compter est plus dur que vérifier *(à venir)* | Licence | 05b — Aaronson–Arkhipov (aujourd'hui 05) |
| 06 | Simuler un circuit quantique classiquement *(à venir)* | Licence | 06b — Aaronson–Gottesman (aujourd'hui 06) |
| 07 | La chaîne des inclusions : L, NL, P, NP *(à venir)* | Licence | 07b — Zoo et oracles (aujourd'hui 07) |

## Position dans le dépôt

La série rejoint le dialogue formel existant : les jumeaux Lean (`Search/discrepancy_lean/`,
`GameTheory/social_choice_lean/`, …) montrent ce que Mathlib **sait** prouver ; cette série
montre, machines en main, ce que la couche complexité **exigerait** — et mesure le manque
(`Mathlib/Computability/` couvre machines de Turing, halting, degrés de Turing, mais aucune
classe de complexité temporelle : encart §6 de 03b ; `Mathlib.Combinatorics.Matroid`
existe mais compétitivité, k-server et work functions sont absents : encart §6 du notebook 04).
Le notebook 04 saisit l'**algorithmique online** côté Complexity — décisions
irréversibles sous incertitude, ratio compétitif — en écho aux notebooks sœurs
`RL/rl_17_k_server_wfa` et `RL/rl_18_matroid_secretary` qui distillent les mêmes
preprints côté RL.
Le notebook 05 étend la mesure **côté algèbre** : pour la première fois la série rend un
verdict Mathlib positif (`Matrix.permanent` existe — mais à l'état de définition $n!$,
sans Ryser ni #P : encart §5), et relie la permanente au dépôt existant — couplages
parfaits de [Sudoku-15](../Sudoku/Sudoku-15-Infer-Python.ipynb), dont le schéma Ryser
vectorisé est réemployé tel quel.

Le notebook 06 amène la série **côté simulation** : les notebooks précédents
mesuraient des coûts combinatoires (permanente, work functions) ; celui-ci
construit la machine qui *réfute* — le simulateur stabilisateur comme
instrument de méthode. C'est aussi le premier notebook de la série à croiser
trois moteurs (port pédagogique, état complet, stim), chacun validant les
deux autres.

Le notebook 07 referme la boucle **côté carte** : les précédents mesuraient des
points (hiérarchie, permanente, simulation) ; celui-ci navigue le tableau entier —
chaque arête d'inclusion porte son témoin exécutable, chaque arête ouverte porte sa
raison visible (les mondes d'oracles de Baker–Gill–Solovay, construits et exécutés),
et le gap Mathlib devient structurel : la calculabilité est formalisée, la complexité
pas encore.

## Prérequis

Python 3.10+ (kernel `python3`) : `numpy`, `matplotlib` — le socle standard du dépôt.
Les notebooks 01 et 02 ne supposent rien d'autre que la lecture d'un programme Python ;
les notebooks principaux annoncent leurs prérequis dans une section « Ce que ce notebook
suppose ».
Aucune dépendance externe : tout est construit dans le notebook, rubans, transitions,
oracles d'indépendance et work functions compris, pour que chaque pas soit auditable.
Le notebook 06 ajoute une dépendance **optionnelle** :
[`stim`](https://github.com/quantumlib/Stim) (troisième juge du croisement et banc
d'échelle). Sans lui, le notebook s'exécute intégralement avec les deux machines
qu'il construit — le banc affiche alors sa colonne vide et le dit.

## Exercices

Chaque notebook embarque au moins trois exercices (`TODO etudiant`) : étendre une machine,
dériver un compte, déplacer un budget — les stubs s'exécutent sans erreur (règle C.1 du
dépôt) et les corrigés restent la propriété de l'étudiant.
