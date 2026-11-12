# Histoires et causalité du multiway (pli 5)

Le grain B fusionne les histoires arrivant au même multiensemble d'arêtes. Il ne
permet donc pas de lire leur graphe causal : une fusion d'états ne fusionne pas
nécessairement les événements qui les ont produits. `causal.cpp` énumère les
histoires jusqu'à quatre pas, avec les mêmes règles, graine et matcher officiel
que `MULTIWAY-PROTOCOLE.md`. Chaque branche est rejouée dans un
`TokenEventGraph` indépendant. Un lien va du créateur d'un jeton à l'événement
qui le consomme ; l'événement artificiel de la graine est exclu des liens.
La hauteur est la génération maximale calculée par le moteur.

Contrôles : à chaque profondeur, l'ensemble des états doit égaler le témoin
complet du grain B ; supprimer la seconde règle doit faire échouer ce témoin.
Avant le relevé final, on contrôle également les formules de ce cas particulier :
à l'étape i, i jetons sont actifs et chacun admet deux choix, soit `2^n n!`
histoires ; chaque événement après le premier consomme un jeton créé par un
événement précédent, soit n−1 liens par histoire. Ce contrôle ne valide pas une
reconstruction causale générale pour des règles à plusieurs entrées.

Reproduction après compilation de libSetReplace au commit indiqué dans le README :

```bash
c++ -O2 -std=c++17 -I /tmp/SetReplace/libSetReplace scripts/hypergraph/causal.cpp /tmp/setreplace-build/libSetReplace.a -o /tmp/causal
/tmp/causal
```

Les hauteurs observées sont des propriétés de ces histoires, pas des distances
physiques ni un test des résultats de Gorard. Cette tranche n'établit pas le
pont bibliographique ni le choix de l'hôte du carnet. Le nombre d'histoires
croît factoriellement : la limite à quatre pas est intentionnelle. Les IDs des
jetons restent propres à chaque histoire ; aucun quotient par isomorphisme ou
fusion des graphes causaux n'est effectué. Idées de la matrice #19766 :
réécriture locale, embranchements multiway et dépendances causales.
