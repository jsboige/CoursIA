# Provenance `app32-neural-diving`

Ce répertoire accompagne App-32, reproduction locale de la composante
**diving** de l'article Nair et al. (2021) sur le terrain contrôlé de la
coloration de graphe.

| Champ | Valeur |
|---|---|
| **Travail original** | *Solving Mixed Integer Programs Using Neural Networks* — Nair, V., Bartunov, S., Gimeno, F., et al. |
| **Publication** | Nature 607 (2021) |
| **Gisement partagé** | `G:\Mon Drive\MyIA\IA\Bibliographie IA\Search\2021 - Nair et al - Solving Mixed Integer Programs Using Neural Networks.pdf` |
| **Verdict audité** | médiane des branches 790 → 880 (dégradation ≈ 10 %) ; égarements de la recherche (nA jusqu'à 3972) majoritairement ramenés ≤ 900 ; 40-45 % des arêtes du hint en conflit avec les contraintes |

## Ce qui est attribué

Le geste intellectuel conservé est la **question** : un plongeur appris
prédit une affectation partielle, injectée comme `hint` (conseil réparable)
dans un solveur réel — OR-Tools CP-SAT — et l'on mesure l'effet sur la
recherche (`NumBranches()`), pas sur une métrique locale de précision.

Aucune cellule, fonction, donnée, figure ou prose de l'article n'est copiée.
Le générateur de graphes, le modèle CP-SAT, la canonisation des solutions
(ordre de première occurrence) et le plongeur MLP sont une réécriture
indépendante CoursIA, prototypée puis mesurée avant la rédaction du notebook
(mesures du 2026-09-23, seeds constants, `random_seed=7`).

## Maturation CoursIA

Le prototype a éliminé deux familles d'instances avant l'écriture du
notebook : les set-cover denses (résolus au presolve, `nodes = 0` — aucune
recherche à influencer) et les knapsack multidimensionnels corrélés
(pas de preuve en fenêtre notebook). La coloration 60 sommets / 3 arêtes par
sommet est la famille fenêtre : elle branche (500-800 nœuds) et se prouve
(< 0,1 s). La leçon méthodologique est mesurée, pas postulée : sur la
médiane, le hint coûte ; sur la queue, il stabilise ; la précision par bit
ne prédit pas l'effet, la cohérence avec les contraintes oui.

## Artefacts

| Fichier | Contenu |
|---|---|
| `diving_results.csv` | 25 lignes × 7 colonnes : seed, kA/k, nA/nB (branches), tA/tB (s), hint_conflicts — le CSV frais relu par la cellule de lecture |