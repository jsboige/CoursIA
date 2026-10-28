# Sous-série Numérique — analyse numérique vérifiée

Sous-série de la série Physique (EPIC #23161, tranche T3). Elle confronte les **schémas numériques**
pour les lois de conservation aux **preuves formelles** disponibles : chaque carnet mesure ce qu'un
solveur fait réellement, puis énonce, lacune par lacune, ce qui relève de la mesure et ce qui
relèverait d'une preuve — sans jamais écrire « vérifié de bout en bout ».

## Carnets

### [Numerique-01-Burgers-Volumes-Finis-Python.ipynb](Numerique-01-Burgers-Volumes-Finis-Python.ipynb)

**Ce qu'il démontre.** La condition de Rankine-Hugoniot dérivée de la forme intégrale, la solution
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
