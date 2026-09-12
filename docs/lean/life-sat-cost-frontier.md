# Frontière de coût du synthétiseur SAT de motifs Life

Cette étude mesure la zone où le synthétiseur SAT de motifs de Conway Life reste informatif sous un budget borné. Le résultat principal n'est pas une promesse de temps universelle : c'est une frontière reproductible entre trois verdicts distincts.

- `FOUND` : une taille minimale a été trouvée après réfutation de toutes les tailles inférieures ;
- `IMPOSSIBLE` : toutes les tailles de `1` à `max_cells` ont été réfutées par Z3 ;
- `TIMEOUT` : les tailles listées sont réfutées, mais la première taille non tranchée est exposée séparément. Un timeout n'est jamais converti en preuve d'impossibilité.

Le runner est [`scripts/lean/life_sat_cost_frontier.py`](../../scripts/lean/life_sat_cost_frontier.py). Le moteur mesuré est [`scripts/lean/life_synthesize_sat.py`](../../scripts/lean/life_synthesize_sat.py).

## Méthode

Pour chaque taille exacte `k`, le moteur reconstruit un solveur Z3 qui encode :

1. un motif initial non vide contenu dans une boîte `box_w × box_h` ;
2. la règle locale de Life pendant `n` générations ;
3. l'égalité `evolve^n(T) = shift_v(T)` sur une fenêtre assez large pour que l'extérieur mort soit exact ;
4. la cardinalité exacte `|T| = k`.

La recherche monte `k` de 1 à `max_cells`. Le budget `--timeout-ms` est appliqué à **chaque** appel `solver.check()` pour une taille donnée, et non à la campagne entière. Les tentatives sont conservées dans le JSON avec leur statut `SAT`, `UNSAT` ou `TIMEOUT` et leur durée observée.

Le runner ajoute quatre mesures structurelles : largeur et hauteur de la fenêtre encodée, cellules encodées par génération, et nombre de variables booléennes d'état `(n + 1) × largeur × hauteur`. Ce dernier nombre décrit la taille de l'état, pas le nombre total de contraintes ni la difficulté complète de la formule.

Les motifs trouvés sont rejoués par le moteur B1 indépendant (`evolve` et `shift_v`). Les tests recoupent également le glider et le LWSS avec l'énumération exhaustive là où celle-ci reste praticable.

## Reproduction

Environnement de la campagne du 11 septembre 2026 :

- Windows 11 `10.0.26200` ;
- Python 3.13.14 ;
- Z3 4.16.0 ;
- budget : 10 000 ms par taille `k` ;
- `enumerate_all=False`, afin de mesurer la première solution et non l'énumération de toutes ses symétries.

Campagne complète, une répétition :

```powershell
python scripts/lean/life_sat_cost_frontier.py `
  --timeout-ms 10000 `
  --output life-sat-frontier.json
```

Répétition ciblée des contrôles et points pivots :

```powershell
python scripts/lean/life_sat_cost_frontier.py `
  --timeout-ms 10000 --repeats 3 `
  --case control-found-glider `
  --case control-impossible-superluminal `
  --case period-n2 --case period-n3 --case period-n4 `
  --case displacement-orthogonal-c2 `
  --case displacement-orthogonal-c4 `
  --case box-3x3 --case box-4x4 --case box-5x5 `
  --output life-sat-frontier-targeted-3x.json
```

Le processus retourne 2 si un contrôle perd son pouvoir discriminant. Avec plusieurs répétitions, **chaque** occurrence des contrôles doit respecter son verdict attendu. Le synthétiseur direct retourne 3 lorsqu'il produit `TIMEOUT`.

## Contrôles discriminants

| Contrôle | Spécification | Attendu | Résultat, 3 répétitions | Justification indépendante |
|---|---:|---:|---:|---|
| Glider | `n=4`, `v=(1,-1)`, boîte 4×4, `k≤5` | `FOUND`, minimum 5 | 3/3 `FOUND`, minimum 5 | motif canonique connu et rejoué par B1 |
| Supraluminique | `n=2`, `v=(3,0)`, boîte 3×3, `k≤4` | `IMPOSSIBLE` | 3/3 `IMPOSSIBLE` | l'information se propage d'au plus une cellule par génération |

Ces contrôles empêchent deux campagnes non informatives : un solveur qui ne trouverait plus un motif connu et un solveur qui déclarerait tout satisfiable.

## Campagne factorielle complète

La première campagne couvre 14 points et les quatre axes demandés. Elle dure 191,059 s et rend 7 `FOUND`, 6 `IMPOSSIBLE` et 1 `TIMEOUT`.

| Cas | Axe | Variables d'état | Verdict | Frontière logique | Temps (s) |
|---|---|---:|---|---|---:|
| `control-found-glider` | contrôle | 1 280 | `FOUND` | minimum 5 ; `1..4` réfutés | 3,182 |
| `control-impossible-superluminal` | contrôle | 675 | `IMPOSSIBLE` | `1..4` réfutés | 1,938 |
| `period-n2` | période | 432 | `IMPOSSIBLE` | `1..6` réfutés | 2,086 |
| `period-n3` | période | 784 | `IMPOSSIBLE` | `1..6` réfutés | 6,532 |
| `period-n4` | période | 1 280 | `IMPOSSIBLE` | `1..6` réfutés | 11,509 |
| `displacement-diagonal` | déplacement | 1 280 | `FOUND` | minimum 5 ; `1..4` réfutés | 9,375 |
| `displacement-orthogonal-c2` | déplacement | 1 805 | `FOUND` | minimum 9 ; `1..8` réfutés | 22,226 |
| `displacement-orthogonal-c4` | déplacement | 1 445 | `TIMEOUT` | `1..5` réfutés ; `k=6` non tranché | 32,011 |
| `box-3x3` | boîte | 1 125 | `FOUND` | minimum 5 ; `1..4` réfutés | 6,219 |
| `box-4x4` | boîte | 1 280 | `FOUND` | minimum 5 ; `1..4` réfutés | 8,623 |
| `box-5x5` | boîte | 1 445 | `FOUND` | minimum 5 ; `1..4` réfutés | 9,617 |
| `cardinality-k7` | cardinalité | 1 805 | `IMPOSSIBLE` | `1..7` réfutés | 25,861 |
| `cardinality-k8` | cardinalité | 1 805 | `IMPOSSIBLE` | `1..8` réfutés | 25,136 |
| `cardinality-k9` | cardinalité | 1 805 | `FOUND` | minimum 9 ; `1..8` réfutés | 26,655 |

Dans l'axe cardinalité, `IMPOSSIBLE` signifie exactement « aucune solution jusqu'à la borne indiquée », pas « aucune solution sans borne ». Le passage de `k≤8` à `k≤9` retrouve le LWSS à neuf cellules.

## Répétitions ciblées

Les dix points ciblés ont été exécutés trois fois dans le même processus, soit 30 résultats et 353,209 s. Les verdicts sont invariants : 15 `FOUND`, 12 `IMPOSSIBLE`, 3 `TIMEOUT`.

| Cas | Variables d'état | Verdicts | Temps min / médiane / max (s) |
|---|---:|---:|---:|
| `control-found-glider` | 1 280 | 3/3 `FOUND` | 2,79 / 6,67 / 8,73 |
| `control-impossible-superluminal` | 675 | 3/3 `IMPOSSIBLE` | 1,90 / 2,73 / 3,41 |
| `period-n2` | 432 | 3/3 `IMPOSSIBLE` | 2,17 / 2,53 / 4,12 |
| `period-n3` | 784 | 3/3 `IMPOSSIBLE` | 5,16 / 7,64 / 7,94 |
| `period-n4` | 1 280 | 3/3 `IMPOSSIBLE` | 13,12 / 16,90 / 16,91 |
| `displacement-orthogonal-c2` | 1 805 | 3/3 `FOUND`, minimum 9 | 24,64 / 27,37 / 33,54 |
| `displacement-orthogonal-c4` | 1 445 | 3/3 `TIMEOUT` à `k=6` | 30,38 / 30,65 / 33,01 |
| `box-3x3` | 1 125 | 3/3 `FOUND`, minimum 5 | 6,03 / 6,28 / 7,09 |
| `box-4x4` | 1 280 | 3/3 `FOUND`, minimum 5 | 7,02 / 7,21 / 10,70 |
| `box-5x5` | 1 445 | 3/3 `FOUND`, minimum 5 | 7,88 / 8,73 / 9,86 |

La variabilité du glider, pourtant identique entre occurrences, interdit de lire les chronos uniques comme une loi fine. En revanche, deux conclusions résistent aux répétitions :

1. à spécification et borne constantes, l'axe période augmente à la fois l'état encodé (432 → 784 → 1 280 variables) et le coût médian observé (2,53 → 7,64 → 16,90 s) ;
2. le cas orthogonal `c/4` atteint toujours le budget à `k=6`, après réfutation de `k=1..5`. La dernière tentative dure 11,10 à 11,42 s en temps mural : le budget Z3 de 10 s ne couvre pas le coût Python de construction et de retour du solveur.

Le cas orthogonal `c/2` est plus grand structurellement (1 805 variables), mais reste résolu : `k=1..8` sont réfutés puis un LWSS à neuf cellules est trouvé. La taille structurelle seule ne prédit donc pas le verdict ; la géométrie de la contrainte compte.

## Point de bascule et limites

Sous ce protocole et sur cette machine, la frontière pratique la plus nette est :

- **encore tranché** : translation orthogonale `c/2`, boîte 5×5, minimum 9, médiane 27,37 s ;
- **non tranché sous 10 s par taille** : translation orthogonale `c/4`, boîte 5×5, `k=1..5` réfutés puis `k=6` en timeout, médiane totale 30,65 s.

Cette frontière n'est ni une preuve d'intractabilité asymptotique ni une comparaison générale des algorithmes SAT. Elle dépend de la version de Z3, de la machine, de l'ordre des contraintes et du budget. Les répétitions sont séquentielles dans un même processus : elles mesurent la variabilité observée, pas une distribution indépendante entre machines.

Enfin, `IMPOSSIBLE` reste une propriété **bornée par `max_cells` et la boîte initiale**. `TIMEOUT` conserve seulement le préfixe effectivement prouvé ; aucune conclusion n'est tirée sur `size_unresolved` ni sur les tailles supérieures.

## Validation

Les tests couvrent notamment :

- la distinction `unknown` / `unsat` dans Z3 ;
- la conservation des tailles réfutées avant timeout ;
- le code de sortie 3 du synthétiseur direct ;
- le rejet des budgets et nombres de répétitions non positifs ;
- la conservation de chaque répétition dans le JSON ;
- la validation de toutes les occurrences des contrôles ;
- les dimensions structurelles de l'encodage ;
- le recoupement avec le moteur B1 et l'énumération exhaustive.

Commande de validation :

```powershell
python -m pytest `
  scripts/lean/tests/test_life_synthesize_sat.py `
  scripts/lean/tests/test_life_sat_cost_frontier.py -q
```
