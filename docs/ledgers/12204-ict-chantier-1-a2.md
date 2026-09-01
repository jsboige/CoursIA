# Chantier 1 — tranche A2 : l'opération 1 (*Recoordonner*) passe de `RAPPORTE` à `FIRSTHAND`

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-ai-01:CoursIA` · **date de mesure** 2026-09-01
**Tranches sœurs** : [A3](12204-ict-chantier-1-a3.md) (opérations 3, 9) · [audit froid](12204-ict-chantier-1-audit-froid.md) (les 14 opérations, trois axes)

## Ce que cette tranche fait, et ce qu'elle ne fait pas

L'audit froid avait laissé l'opération 1 en `TABLE` avec un seul reproche : `RAPPORTE`. Son verdict le disait sans détour — « reste à passer FIRSTHAND (grain A2) ». La tranche ne **re-décide** donc rien : elle **relit les trois attestations dans le dépôt** et rapporte ce que la lecture change.

Elle ne touche à aucune autre opération. Elle ne promeut ni ne dégrade le nombre d'attestations : l'opération en avait `2+`, elle en a toujours `2+`. Ce qui change est l'axe de **provenance**, et — c'est le vrai apport — la **précision de la dette**.

## Rappel de l'énoncé mesuré

> **1 — Recoordonner** : changer la représentation sous laquelle le problème est soumis.
> *La forme d'émission décide du destin : même contrainte, deux formes, deux destins.*
> Objet qui atterrit : le 9x9 complet ; la preuve devenue presque triviale après canonisation.
> Dette déclarée : **non-canonicité — aucune théorie du « bon » changement**.

## Attestation 1 — MGS-21, *Représentation contre algorithme* (empirique)

`MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-21-Representation-vs-Algorithme.ipynb`
État mécanique mesuré : **9 cellules code / 9 exécutées / 9 avec sorties / 0 erreur**, kernel `.net-csharp`.

Plan factoriel **2 × 2** pré-enregistré — deux algorithmes (PSO à vélocité, GA) × deux représentations (R1 continue + arrondi, R2 permutation + échange) — à **problème, budget et graines identiques** (population 40 × 200 générations, graines {0, 1, 7, 42}, évaluations instrumentées). Le critère de dominance est fixé **avant** l'exécution.

| Effet mesuré | Amplitude |
|---|---|
| Représentation, colonne PSO | 45,0 → 6,0 de médiane (−39 conflits, ×7,5) |
| Représentation, colonne GA | 10,5 → 0,0 — et **0/4 → 4/4 résolus** |
| Algorithme, ligne R1 | 45,0 → 10,5 (×4,3) |
| Algorithme, ligne R2 | 6,0 → 0,0 |

**Ce que la lecture firsthand ajoute — et retire.** Le notebook applique lui-même son critère pré-enregistré et conclut que la dominance est établie **au sens strict sur la seule colonne PSO** (39 > 34,5 et 6), **atténuée sur la colonne GA**. L'énoncé de l'opération 1 est donc attesté, mais **pas universellement** : à représentation fixée, l'algorithme compte encore (×4,3). Une table qui aurait écrit « la représentation domine » sans réserve aurait sur-lu sa propre source.

**Ce qu'elle ajoute en revanche** : une **cause mesurée**, que le corps de l'EPIC n'avait pas. **200 candidats R1 sur 200 (100 %)** décodent hors de l'espace admissible, contre **0 sur 200** en R2. L'arrondi n'ajoute pas du bruit — il *expulse de l'espace*. C'est une projection discontinue, pas une imprécision qui s'atténuerait à la convergence. L'opération 1 cesse d'être un constat d'effet pour devenir un constat de **mécanisme**.

## Attestation 2 — Sudoku-13, *le Sudoku comme regex symbolique* (empirique)

`MyIA.AI.Notebooks/Sudoku/Sudoku-13-SymbolicAutomata-Csharp.ipynb` (**20/20 exécutées, 0 erreur**)
`MyIA.AI.Notebooks/Sudoku/Sudoku-13-SymbolicAutomata-Python.ipynb` (**11/11 exécutées, 0 erreur**)
Companion : `Sudoku-12-Z3-Csharp.ipynb` (**19/19 exécutées, 0 erreur**)

C'est l'attestation la plus littérale de l'énoncé : **une même contrainte** — le Sudoku comme intersection de contraintes régulières — **trois formes d'émission**, **trois destins**, que le notebook tabule lui-même :

| Forme d'émission | Moteur réel | Destin |
|---|---|---|
| Conway / backtracking (`(?R)`, déroulé Griffis) | le moteur regex lui-même | fragile (timeout / faux négatif) |
| SFA / produit d'automates (Automata.NET 2020) | produit de DFA + témoin SFAz3 | jouets oui ; grille → **deux murs** |
| regex → théorie des chaînes SMT *directe* | solveur de chaînes Z3, **aucun automate matérialisé** | **4x4 complet ; 9x9 complet** |

Les deux murs de 2020 sont nommés et sont tous deux des murs **de l'automate** : déterminisation explosive, et témoin capé (~21 caractères). Ils tombent non par une meilleure tactique mais parce qu'on **change de moteur** — la contrainte, elle, n'a pas bougé. C'est exactement « l'objet qui atterrit » de l'énoncé : le 9x9 complet.

Le notebook distingue par ailleurs **reconnaître** de **résoudre**, et note que RE# (2025) est *recognition-only* — donc en temps linéaire mais sans témoin. Cette distinction est la charnière de la **Loi II** (recoordonner + passer du vérificateur au constructeur) : elle est ici attestée dans les deux sens sur le même objet.

## Attestation 3 — `conway_lean/Conway/Life.lean` (Lean-formel)

`MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life.lean`

Le module porte **deux recoordinations emboîtées**, chacune justifiée par une mesure et non par un goût :

1. **`Finset` → `List`** (docstring L22-27). L'égalité de `Finset` construite via `image`/`biUnion`/`filter` sur `Int × Int` fait buter le noyau sur le goulot `Quot.lift` / `Eq.rec`. L'égalité de liste « se réduit à une comparaison structurelle cons-par-cons, que le noyau et le générateur de code natif traitent efficacement ».
2. **`mergeSort` → `insertionSort`** (docstring L124-136). Le réducteur du noyau **évalue complètement** `List.insertionSort` là où `List.mergeSort` reste **bloqué** (son `merge` imbriqué est opaque à `decide`). La mesure est isolée : probe `decide` par cible, po-2026 c.786 — `mergeSort` bloque pour les types d'éléments **`Nat` ET `Int`**, donc « le blocage vient de l'algorithme de tri, pas du type de coordonnées ». POC vérifié sur `eater1` (7 cellules), cas #8749. Le swap **préserve** les coordonnées et produit une liste canonique **byte-identique**.

**Mesure firsthand de l'effet, avec son contrôle positif.** Les sept théorèmes de motifs du module sont prouvés **`by decide`** — noyau — et **aucun** par `native_decide` :

```
231: theorem block_still_life      : isStillLife block = true            := by decide
234: theorem beehive_still_life    : isStillLife beehive = true          := by decide
237: theorem blinker_period_two    : isOscillator blinker_h 2 = true     := by decide
240: theorem blinker_step          : (step blinker_h == blinker_v) = true := by decide
243: theorem toad_period_two       : isOscillator toad 2 = true          := by decide
246: theorem beacon_period_two     : isOscillator beacon 2 = true        := by decide
249: theorem glider_spaceship      : isSpaceship glider 4 (1, -1) = true := by decide
```

Ce zéro est **un vrai zéro, pas un motif qui rate** : le même motif de détection trouve bien `native_decide` **en tactique** ailleurs dans le lake — `Conway/LookAndSayLemmas.lean:33` et `:37`. L'absence dans `Life.lean` est donc une propriété du module, pas un angle mort de l'instrument.

**Ce que cela change pour la force de l'attestation.** `native_decide` appartient à la classe d'axiomes `forbidden` (§B de `pr-review-discipline` : réduction par le noyau natif *sans preuve*). La recoordination ne rend donc pas seulement les preuves *plus rapides* : elle les fait **changer de statut épistémique** — de « évaluées par du code natif » à « décidées par le noyau ». C'est un cran au-dessus de ce que le corps de l'EPIC revendiquait (« la preuve devenue presque triviale »).

**Dérive de documentation relevée au passage** (hors périmètre de cette tranche, portée en issue) : `Life.lean` mentionne `native_decide` **six fois en prose** (L20, L65, L167, L195, L224, L225) alors que ses tactiques sont toutes `decide`. La prose décrit une stratégie que le module a quittée.

Pour mémoire, l'instrument canonique sur ce lake : `python scripts/lean/count_code_sorry.py --json` → `naive_sorry: 169`, **`distinct_code_sorry: 1`**. L'écart 169 → 1 est lui-même une illustration de la règle d'instrument (`grep -c sorry` sur-compte la prose d'un facteur 169).

## Verdict de la tranche

| Axe | Avant (audit froid) | Après (cette tranche) |
|---|---|---|
| provenance | `RAPPORTE` | **`FIRSTHAND`** |
| attestations | `2+` (Sudoku-13, `conway_lean`, MGS) | `2+` — **inchangé**, les trois tiennent |
| force | empirique + Lean-formel | empirique **avec cause mesurée** + Lean-formel **kernel-décidable** |
| statut | `TABLE` | **`TABLE`** — confirmée |

## La dette, reformulée par la lecture

Le corps de l'EPIC écrivait : « non-canonicité : aucune théorie du "bon" changement ». La lecture firsthand ne la contredit pas — elle la **précise**, et la rend plus embarrassante :

> Dans les **trois** attestations, la bonne représentation a été trouvée **par la mesure, après un échec**, jamais dérivée d'un principe. MGS-21 : le croisement 2 × 2 *constate* que R2 domine, il ne le prédit pas. Sudoku-13 : la voie SMT est trouvée après avoir buté sur deux murs de l'automate. `Life.lean` : `insertionSort` est retenu après qu'une probe a établi que `mergeSort` bloque.

Autrement dit la dette n'est pas « nous n'avons pas encore écrit la théorie » mais « **nos trois attestations sont trois post-mortems** ». Une théorie du bon changement se reconnaîtrait à ceci qu'elle permettrait de choisir la représentation **avant** de payer l'échec — aucune des trois ne le permet. C'est l'énoncé que la table doit porter, et il est plus utile que le précédent parce qu'il dit à quoi ressemblerait sa levée.

## Suites ouvertes par cette tranche

- **Dérive de docstring `Life.lean`** (6 mentions `native_decide` en prose vs 7 tactiques `decide`) — issue de suivi, pas corrigée ici (hors périmètre A2 : cette tranche lit, elle ne modifie pas les modules attestants).
- **A4** reste le prochain grain de vérification (opérations 4, 5 + dette du recouvrement).
- **Loi II** gagne une lecture firsthand sur son versant Sudoku (reconnaître ≠ résoudre, tabulé dans Sudoku-13) — mais son versant Hashlife (« synthèse non encore franchie ») n'est pas touché par cette tranche.
