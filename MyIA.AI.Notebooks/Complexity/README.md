# Complexity — Théorie de la complexité calculatoire

La série se lit en deux étages. Deux notebooks de **découverte** (01-02) ne supposent que
Python : compter les pas d'un algorithme, puis distinguer *vérifier* de *trouver*
(P, NP, réduction). Les positions de **licence** — 03 et 04 livrées, 05 et 06 à venir —
posent ensuite une notion par notebook sans rien supposer d'autre que les positions
précédentes. Chaque position a son **approfondissement** (lettre `b`, niveau **Recherche**) :
un texte fondateur, **fait tourner** (machines construites pas à pas, comptes d'opérations
exacts, simulations Monte Carlo, chronos encadrés), puis confronté à l'état de
[Mathlib](https://github.com/leanprover-community/mathlib4) — ce qui y existe, ce qui
n'y existe pas encore, et pourquoi.

## Notebooks

| Notebook | Public | Accrétion | Hommage | Contenu | Langue |
|---|---|---|---|---|---|
| [`Complexity-01-StepCounting.ipynb`](Complexity-01-StepCounting.ipynb) | Découverte | — | — (socle) | Le chronomètre ment un peu : compter des **pas** plutôt que des secondes ; taille d'entrée ; machine de Turing construite pas à pas (incrément binaire, palindrome en $n^2$) ; trois croissances comptées ($n \log n$, $n^2$, $2^n$) par le test de doublement et les pentes log-log ; table de budget à $10^8$ pas/s : ce que chaque croissance permet de traiter en une seconde, une minute, un jour | Français |
| [`Complexity-02-P-NP-Reduction.ipynb`](Complexity-02-P-NP-Reduction.ipynb) | Découverte | — | — (socle) | Vérifier contre trouver sur le Sudoku (324 lectures contre des centaines de milliers d'appels) et sur subset-sum ; programmation dynamique **pseudo-polynomiale** mesurée ; définitions de P et NP ; réduction subset-sum → Partition **exécutée de bout en bout** (transformer, résoudre, retraduire le certificat) et testée sur 400 instances ; le mur exponentiel face à une machine mille fois plus rapide | Français |
| [`Complexity-03-TimeHierarchy.ipynb`](Complexity-03-TimeHierarchy.ipynb) | Licence | — | — (socle) | Budgets imbriqués, inclusion contre séparation stricte, diagonale finie et limites d'une simulation bornée ; trois exercices exécutables | Français |
| [`Complexity-03b-HartmanisStearns-TimeHierarchy.ipynb`](Complexity-03b-HartmanisStearns-TimeHierarchy.ipynb) | Recherche | approfondissement de **03 — Plus de temps, plus de problèmes** | Juris Hartmanis & Richard E. Stearns (prix Turing 1993, « On the Computational Complexity of Algorithms », 1965) | Machines de Turing multi-rubans simulées avec comptage exact des pas ; trois croissances mesurées ($n \log n$, $n^2$, $2^n$) ; subset-sum comme séparatrice honnête (force brute vs programmation dynamique, compteurs déterministes) ; diagonalisation budgétée sur une famille finie ; théorème de hiérarchie en temps $\mathrm{TIME}(f) \subsetneq \mathrm{TIME}(f \log f)$ ; encart sur le **gap Mathlib** (aucune couche `Computability/Complexity` : pas de $\mathrm{TIME}(f)$, pas de machine universelle avec overhead temporel, pas de théorème de hiérarchie) | Français |
| [`Complexity-03c-ComplexityZoo-Navigation-Python.ipynb`](Complexity-03c-ComplexityZoo-Navigation-Python.ipynb) | Recherche | approfondissement de **03 — Plus de temps, plus de problèmes** | Scott Aaronson (fondateur du Complexity Zoo, 2004 — plus de 500 classes répertoriées) ; Theodore Baker, John Gill, Robert Solovay (*Relativizations of the P=?NP Question*, 1975) | La chaîne $L \subseteq NL \subseteq P \subseteq NP$ **tournée sur instances** : atteignabilité décidée deux fois — vérificateur à 2 mots de mémoire (certificat lu une fois, accord sur 4 tailles, faux témoin amputé refusé) contre DFS dont la pile explore ~$n/3$ sommets ; 2-SAT (Kosaraju, linéaire, $n=800$) contre 3-SAT (DPLL, densité-seuil $4{,}267n$) : facteurs de croissance **mesurés** par variable (~1,10× en noeuds, ~1,16× en temps), 20 certificats sur 20 vérifiés en polynomial ; **Baker–Gill–Solovay exécuté** — monde A : oracle diagonal, 4 machines vaincues par basculement d'un seul témoin, le côté NP exhaustif confirme $L_O$ sur chaque stade ; monde B : l'oracle QBF donne $P^B = NP^B$ en une requête — la barrière de relativisation vue du jouet ; carte du Zoo à 8 arêtes classées Mesuré/Cité/Ouvert (+ carte mermaid) ; encart **gap Mathlib** : `Computability/` couvre la calculabilité, mais aucune classe à bornage — le Zoo est absent | Français |
| [`Complexity-04-OnlineAlgorithms-Python.ipynb`](Complexity-04-OnlineAlgorithms-Python.ipynb) | Licence | — | — (socle) | Louer ou acheter des skis : balayage des seuils, pire rapport $2 - 1/B$ atteint exactement au seuil $T = B$, puis distribution randomisée dont le pire rapport **converge vers $e/(e-1) \approx 1{,}58198$** ; pagination : Belady hors ligne contre LRU et FIFO — rapport tendant vers $k$ sur le motif cyclique ($4{,}84$ à $k=5$), retombant à $1{,}47$ sur requêtes aléatoires ; secrétaire : fraction d'observation balayée, sommet **plat** autour de $1/e$ (indiscernable de $0{,}4$ à $0{,}003$ près) ; quatre énoncés séparés Mesuré/Cité ; trois exercices exécutables | Français |
| [`Complexity-04b-OnlineConjectures-Secretary-KServer.ipynb`](Complexity-04b-OnlineConjectures-Secretary-KServer.ipynb) | Recherche | approfondissement de **04 — Décider sans connaître la suite** | Sahil Singla & Christian Coester, Elias Koutsoupias, Marek Zbysiński (les deux preprints de septembre 2026 : conjecture du secrétaire matroïdal 2007 et conjecture k-server ~1990, tombées à 24 h d'écart) | Baseline $1/e$ du secrétaire classique mesurée par Monte Carlo ($n$ = 20/100/1000) ; deux matroïdes à oracle d'indépendance (uniforme, graphique) avec optimum offline exact et compétitivité de deux stratégies online ; **work function algorithm implémenté exactement** (DP sur les $\binom{m}{2}$ configurations) : sur le cycle $C_5$, ratio WFA 1,67 sous la borne $k=2$ quand greedy explose (20 à 60 requêtes, 160 à 480 — non compétitif) ; tableau du double visage randomisation/déterminisme ; trois niveaux épistémiques Mesuré/Cité/Absent (prudence « preuve annoncée ») ; encart **gap Mathlib** (matroïdes présents, compétitivité/k-server/work functions absents) | Français |
| [`Complexity-04c-KServer-WorkFunction-Python.ipynb`](Complexity-04c-KServer-WorkFunction-Python.html) | Recherche | lettre de la marche **04 — Décider sans connaître la suite** | Manasse, McGeoch & Sleator (conjecture k-server, ~1990) ; Christian Coester, Elias Koutsoupias, Marek Zbysiński (preprint arXiv 2609.15979) | **Un** des deux problèmes de 04b, mesuré à fond : la **work function** implémentée comme DP exact sur les configurations — elle **est** l'optimum offline —, WFA en ligne sur ligne, cycle et métrique uniforme, vérification par instance WFA ≤ k×OPT (aucune violation sur les instances seedées), duel WFA contre LRU et FIFO sur la pagination (boucle k+2 : LRU devant WFA en fautes, les deux sous k×OPT), work function visualisée en heatmap des configurations. Bandeau d'honnêteté : les ratios réalisés (~1,1-1,6) restent sous la garantie pire-cas k — mesuré n'est pas prouvé, et le preprint n'est pas relu | Français |
| [`Complexity-04d-Secretaire-Matroidal-Python.ipynb`](Complexity-04d-Secretaire-Matroidal-Python.html) | Recherche | lettre de la marche **04 — Décider sans connaître la suite** | Sahil Singla (conjecture du secrétaire matroïdal, 2007) ; preprint arXiv 2609.14555 | L'**autre** problème de 04b, élément par élément : trois matroïdes jouets par oracle d'indépendance (uniforme, partition, graphique), l'algorithme de Singla reconstruit (échantillon Bin(n,1/2), configuration virtuelle, glouton des deux côtés — purement ordinal, ne connaît que n), banc de mesure P[accept \| e ∈ OPT] sur plusieurs instances × milliers d'essais : la garantie 1/4 jamais violée et **serrée sur les rangs 1-2**, E[ALG]/OPT ≈ 0,44, prix de l'universalité 0,41 → 0,26 contre le seuil 1/e classique. La garantie sert de **test exécutable** : c'est le banc qui a détecté le bug du prototype | Français |
| [`Complexity-05-CountingHarder-Permanent.ipynb`](Complexity-05-CountingHarder-Permanent.ipynb) | Licence | — | — (socle) | De vérifier (02) à **compter** : la classe #P déroulée à la main sur une expression à trois variables (huit certificats énumérés, quatre témoins) ; le **déterminant** défini par la même somme de $n!$ produits mais tombé à $O(n^3)$ par Gauss — chronométré au doublement des tailles (facteur borné, la signature du polynôme) ; la **permanente** sans les signes : la définition $n!$ exécutée telle quelle (copie pédagogique déclarée), comptes canoniques validés (identité, tout-un $= n!$, la $3	imes3$ déroulée terme à terme) ; l'écart **mesuré** côte à côte jusqu'à $n = 10$ avec extrapolation du mur factoriel ; Valiant 1979 (#P-difficile même en 0/1) au niveau **Cité** ; le pont aux graphes : compter les couplages parfaits d'un biparti **est** une permanente — vérifié par deux machines indépendantes | Français |
| [`Complexity-05b-AaronsonArkhipov-PermanenteBosonSampling.ipynb`](Complexity-05b-AaronsonArkhipov-PermanenteBosonSampling.ipynb) | Recherche | approfondissement de **05 — Compter est plus dur que vérifier** | Scott Aaronson & Alex Arkhipov (*The Computational Complexity of Linear Optics*, 2011 — la permanente comme frontière quantique) | La définition $n!$ **exécutée** avec comptes canoniques, vérifiée contre l'énumération brute des couplages parfaits (perm(0/1)) ; **Ryser vectorisé réemployé de Sudoku-15** (`batch_perm8`, généralisé à toute taille) contre Gauss instrumenté : comptes exacts par formules fermées validées par instrumentation — à $n=20$, définition $4{,}9 \times 10^{19}$ opérations contre 5 149 pour Gauss, Ryser/det ≈ $1{,}6 \times 10^4$ en temps à $n=16$ ; #P-difficulté (Valiant 1979) maintenue au niveau **Cité**, FPRAS non négatif (Jerrum–Sinclair–Vigoda) en exception qui désigne les signes ; **BosonSampling jouet** : unitaire Haar (QR, Mezzadri), loi $\lvert\mathrm{perm}\rvert^2$ exacte sur 56/924/12 870 sorties, TV(échantillon, exact) → 0, coût d'énumération extrapolé jusqu'à ~1 an à 1 TFLOP/s pour $(20, 40)$ ; encart **gap Mathlib** — premier verdict **positif** de la série : `Matrix.permanent` existe (forme $n!$) face à un dossier `Determinant/` entier, mais ni Ryser ni couche complexité | Français |
| [`Complexity-06-Aaronson-Dequantification-Stabilizer.ipynb`](Complexity-06-Aaronson-Dequantification-Stabilizer.ipynb) | Recherche | deviendra **06b**, approfondissement du futur 06 *Simuler un circuit quantique classiquement* | Scott Aaronson & Daniel Gottesman (*Improved Simulation of Stabilizer Circuits*, 2004 — déquantifier les suprématies par l'arbitre exécutable) | Le formalisme stabilisateur **exécuté** : table de phase et conjugaison CHP **dérivées des matrices 2×2**, jamais recopiées ; port CHP complet (rowsum, portes, mesures — déterministe par lecture GF(2), aléatoire par re-stabilisation) croisé contre l'état complet 2^n : **84 valeurs propres stabilisatrices exactes au 1e-9** (zéro bruit), distributions TV sous 6× le bruit de sondage, stim en troisième juge ; banc discriminant : bascule **mesurée** dès ~12 qubits, ratio ~1600× à n=20, échelons locaux au-dessus du plancher 2× (le mur réel est plus raide que 2^n : la mémoire aussi a une loi) ; une **seule** porte T ferme le port **et** stim (`no attribute 't'`) — la frontière est Clifford/le-reste, pas quantique/classique | Français |
| [`Complexity-07-KolmogorovBornee-Sequences-Python.ipynb`](Complexity-07-KolmogorovBornee-Sequences-Python.html) | Recherche | arrivé de Search/Applications (ex-App-34) — renuméroté 07 : la complexité de Kolmogorov **bornée** est une notion de complexité ; le pli Kolmogorov/MDL de l’EPIC Compression [#18706](https://github.com/jsboige/CoursIA/issues/18706) pourra y renvoyer | Strannegård, Nizamati, Sjöberg & Engström (*Bounded Kolmogorov Complexity Based on Cognitive Models*, AGI 2013 — modéliser le sujet à mémoire limitée plutôt que la séquence) | K(x) opérationnalisée en coût **à mémoire bornée** : langage de termes (numérales, position n, regard arrière f(n−c), opérations binaires) résolu par énumération par longueur croissante ; trois expériences falsifiables — E1 balayage de la borne de mémoire (score(B) sur batterie de 30 items), E2 discrimination à la borne (seuils prédits par bounded_mul contre basculements mesurés), E3 baselines honnêtes (interpolation polynomiale, différences finies) ; verdicts rendus par les cellules, y compris négatifs ; limites déclarées (batterie maison, TRS opérationnalisé) | Français |

## Parcours

La série se lit de haut en bas : chaque notebook principal ne suppose que ceux qui le
précèdent. Les notebooks d'hommage, écrits pour un lecteur déjà familier du domaine,
deviennent des **approfondissements** (suffixe `b`, puis `c` quand le palier en compte déjà un) : chacun se greffe sur un notebook
principal de niveau licence qui en pose d'abord les notions.

| Position | Notebook principal | Public | Approfondissement |
|---|---|---|---|
| 01 | Compter des pas | Découverte | — |
| 02 | Vérifier ou trouver : P, NP, certificat, réduction | Découverte | — |
| 03 | [Plus de temps, plus de problèmes](Complexity-03-TimeHierarchy.ipynb) | Licence | [03b — Hartmanis–Stearns](Complexity-03b-HartmanisStearns-TimeHierarchy.ipynb), [03c — Zoo et oracles](Complexity-03c-ComplexityZoo-Navigation-Python.ipynb) |
| 04 | [Décider sans connaître la suite](Complexity-04-OnlineAlgorithms-Python.ipynb) | Licence | [04b — conjectures online](Complexity-04b-OnlineConjectures-Secretary-KServer.ipynb), [04c — k-server, work function](Complexity-04c-KServer-WorkFunction-Python.html), [04d — secrétaire matroïdal](Complexity-04d-Secretaire-Matroidal-Python.html) |
| 05 | [Compter est plus dur que vérifier](Complexity-05-CountingHarder-Permanent.ipynb) | Licence | [05b — La permanente, frontière quantique](Complexity-05b-AaronsonArkhipov-PermanenteBosonSampling.ipynb) |
| 06 | Simuler un circuit quantique classiquement *(à venir)* | Licence | 06b — Aaronson–Gottesman (aujourd'hui 06) |
| 07 | La chaîne des inclusions : L, NL, P, NP *(à venir)* | Licence | — |

## Position dans le dépôt

La série rejoint le dialogue formel existant : les jumeaux Lean (`Search/discrepancy_lean/`,
`GameTheory/social_choice_lean/`, …) montrent ce que Mathlib **sait** prouver ; cette série
montre, machines en main, ce que la couche complexité **exigerait** — et mesure le manque
(`Mathlib/Computability/` couvre machines de Turing, halting, degrés de Turing, mais aucune
classe de complexité temporelle : encart §6 de 03b ; `Mathlib.Combinatorics.Matroid`
existe mais compétitivité, k-server et work functions sont absents : encart §6 du notebook 04).
Le notebook 04 pose l'**algorithmique online** côté Complexity — décisions
irréversibles sous incertitude, ratio compétitif — sur trois objets classiques (skis,
pagination, secrétaire) ; son approfondissement 04b y ajoute le secrétaire matroïdal et
le k-server. Les lettres **04c** et **04d** prennent chacune **un** de ces deux problèmes
et le mesurent à fond — 04c la work function algorithm du k-server (la conjecture de 1990,
vérifiée instance par instance), 04d l'algorithme de Singla pour le secrétaire matroïdal
(sa garantie 1/4 comme banc d'exécution). Elles distillent les mêmes preprints.
Le notebook 05 amène la série **côté comptage** : après vérifier (02) et décider sans
connaître la suite (04), compter — la classe #P, le déterminant polynomial face à la
permanente factorielle, l'écart chronométré et le pont aux couplages parfaits des graphes
bipartis. Son approfondissement 05b étend la mesure **côté algèbre** : pour la première fois
la série rend un
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

Le notebook 03c referme la boucle **côté carte** : les précédents mesuraient des
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
