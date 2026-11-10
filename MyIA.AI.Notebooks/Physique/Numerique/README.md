# Sous-série Numérique — analyse numérique vérifiée

Sous-série de la série Physique (EPIC #23161, tranche T3). Elle confronte les **schémas numériques**
pour les lois de conservation aux **preuves formelles** disponibles : chaque carnet mesure ce qu'un
solveur fait réellement, puis énonce, lacune par lacune, ce qui relève de la mesure et ce qui
relèverait d'une preuve — sans jamais écrire « vérifié de bout en bout ».

## Carnets

### [Numerique-01-Burgers-Volumes-Finis-Python.ipynb](Numerique-01-Burgers-Volumes-Finis-Python.ipynb)

**Ce qu'il mesure.** La condition de Rankine-Hugoniot dérivée de la forme intégrale, la solution
exacte du problème de Riemann de Burgers (choc et raréfaction), les schémas de Godunov et Rusanov
avec leur condition CFL, le taux de convergence L1 mesuré par régression log-log, et le temps de
formation d'un choc mesuré directement sur les caractéristiques puis confronté à la prédiction
analytique $t^* = -1/\\min u_0'$.

**Ses outils.** `numpy` et `matplotlib` uniquement — CPU, déterministe, aucune graine : chaque
exécution rejoue les mêmes nombres.

**Sa place dans le fil.** Premier carnet de la sous-série : il pose le socle continu (solutions
faibles, entropie, Riemann) et le socle numérique (volumes finis d'ordre 1), puis fixe la frontière
honnête entre mesure et preuve (table des lacunes avec verdict écrit par lacune, critère de sortie
T3 de #23161). Les grains ouverts qu'il nomme — inventaire du contenu formel des théorèmes
`BurgersEquation`, preuve de correction d'un schéma, pont preuve/code — alimentent les carnets
suivants de la sous-série.

**Rattachements.** EPIC #23161 (tranche T3) · #19741 (question de la preuve de correction d'un
schéma) · PR #23101 (document de l'étape 3, source des mesures rapportées sur les dépôts Lanyon).

### [Numerique-02-Maxwell-Relativiste-Volumes-Finis-C.ipynb](Numerique-02-Maxwell-Relativiste-Volumes-Finis-C.ipynb)

**Ce qu'il mesure.** Les 18 noyaux `static inline` du dépôt `lanyonai/GeneralRelativisticMaxwell`,
téléchargés à une empreinte SHA-256 épinglée puis compilés tels quels sous C99, pilotés par un driver
qui n'écrit **aucune** formule physique. Sur une tranche plate ($\alpha = 1$, $\beta = 0$, $c = 1$) :
conservation exacte de la masse à $10^{-15}$, préservation exacte de l'état propre $D_y = \pm cB_z$
($\max\lvert D_y - cB_z\rvert = 0$), vitesse de propagation mesurée à `+1.000000000000` pour l'onde
droite aux cinq résolutions, et à `-1.000000000000` pour l'onde gauche aux deux résolutions testées
($N = 128$ et $N = 512$) — même valeur absolue, signes opposés. L'ordre de convergence est 1 (ordres
locaux 0,745 → 0,948, pente ajustée 0,861), et la diffusion numérique est visible comme la chute de
$\max D_y$ de 1 à 0,659 à $N = 64$. Une
seconde mesure relie le schéma à la preuve : les vitesses de la famille Lax-Friedrichs valent
exactement $\pm(\alpha c + \lvert\beta_x\rvert)$, ce qui explique mécaniquement la diffusion observée.
La Partie 4 sépare par écrit ce qui est **mesuré ici**, **rapporté** de l'inventaire, et **hors de
portée** — au premier rang desquels le fait qu'aucun `@[extern]` ne relie les 156 théorèmes Lean au
code C.

**Ses outils.** `gcc` (WSL Ubuntu, `-O2 -std=c99`) pour la compilation, `urllib` + `hashlib` pour la
récupération épinglée du fichier amont, `numpy` et `matplotlib` pour les tables et les figures. Aucune
graine : chaque exécution rejoue les mêmes nombres, la chaîne est vérifiable de bout en bout depuis le
carnet.

**Sa place dans le fil.** Deuxième carnet de la sous-série, et premier à sortir du Python : il applique
à un dépôt **externe** la méthode posée par `Numerique-01` — mesurer ce que le solveur fait réellement,
puis nommer les lacunes au lieu de les combler par une formule rhétorique. La leçon centrale du carnet
est que « vérifié » ne veut pas dire « relié » : le dépôt prouve une transcription Lean et livre du C
que rien ne rattache à elle. Le carnet mesure le C, et rend explicite le saut qu'il ne franchit pas.

**Rattachements.** EPIC #23161 (tranche T3) · #24439 (inventaire du dépôt et de ce qu'il déclare
calculable) · PR #24667 (inventaire `lanyonai/GeneralRelativisticMaxwell` fusionné) ·
[gorard-lanyonai-etape3.md](../../../docs/reference/gorard-lanyonai-etape3.md) (cadre de méthode).
