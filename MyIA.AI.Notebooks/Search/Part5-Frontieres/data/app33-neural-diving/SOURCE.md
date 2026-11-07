# Provenance `app33-neural-diving`

Ce répertoire accompagne App-33, reproduction locale de la composante
**diving** de l'article Nair et al. (2021) sur le terrain contrôlé de la
coloration de graphe.

| Champ | Valeur |
|---|---|
| **Travail original** | *Solving Mixed Integer Programs Using Neural Networks* — Nair, V., Bartunov, S., Gimeno, F., et al. |
| **Publication** | arXiv:2012.13349 (v3, juillet 2021) |
| **Gisement partagé** | `G:\Mon Drive\MyIA\IA\Bibliographie IA\Search\2021 - Nair et al - Solving Mixed Integer Programs Using Neural Networks.pdf` |
| **Verdict audité** | run déterministe (`num_workers = 1`) : médiane des branches 2829 → 2325 (−18 %) ; **25/25 instances améliorées**, gain relatif 8-28 % croissant avec la dureté (ρ = 0,60) ; ≈ 49 % des arêtes du hint en conflit avec l'adjacence sans annuler le gain net |

## Ce qui est attribué

Le geste intellectuel conservé est la **question** : un plongeur appris
prédit une affectation partielle, injectée comme `hint` (conseil réparable)
dans un solveur réel — OR-Tools CP-SAT — et l'on mesure l'effet sur la
recherche (`NumBranches()`), pas sur une métrique locale de précision.

Aucune cellule, fonction, donnée, figure ou prose de l'article n'est copiée.
Le générateur de graphes, le modèle CP-SAT, la canonisation des solutions
(ordre de première occurrence) et le plongeur MLP sont une réécriture
indépendante CoursIA, prototypée puis mesurée avant la rédaction du notebook
(mesures du 2026-09-23, rejouées à l'identique le 2026-11-07, seeds constants,
`random_seed=7`).

## Maturation CoursIA

Le prototype a écarté une famille d'instances avant l'écriture du
notebook : les knapsack multidimensionnels corrélés, qui ne se prouvent pas
dans une fenêtre de notebook. Le set-cover, lui, n'a pas été éliminé : il a
été **calibré sur deux régimes**, parce que sa densité est le cadran qui
fait basculer le solveur du presolve vers le branchement — à 10 % le
presolve suffit (`nodes = 0`, contre-exemple qui situe le seuil), à 30 % la
même instance branche (314 nœuds) et prouve l'optimalité. La coloration
60 sommets / 3 arêtes par sommet reste la famille fenêtre, celle que le
carnet instrumente : elle branche (médiane 2742 sur les 60 instances
d'entraînement, 2303-3799) et se prouve en quelques centièmes de seconde.
La leçon méthodologique est mesurée, pas postulée : sur la
médiane, le hint coûte ; sur la queue, il stabilise ; la précision par bit
ne prédit pas l'effet, la cohérence avec les contraintes oui.

## Artefacts

| Fichier | Contenu |
|---|---|
| `diving_results.csv` | 25 lignes × 7 colonnes : seed, kA/k, nA/nB (branches), tA/tB (s), hint_conflicts — le CSV frais relu par la cellule de lecture |