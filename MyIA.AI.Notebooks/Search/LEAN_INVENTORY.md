# Inventaire des projets Lean 4 — `Search`

Inventaire transverse des projets de formalisation Lean 4 sous `Search/`, sur le modèle de
[`GameTheory/LEAN_INVENTORY.md`](../GameTheory/LEAN_INVENTORY.md) et
[`SymbolicAI/Lean/LEAN_INVENTORY.md`](../SymbolicAI/Lean/LEAN_INVENTORY.md). Source de
vérité : corps de l'Epic
[#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification `firsthand`. Colonne
*Sorry (production)* = métrique CI `standalone-tactic` (les mentions prose « 0 sorry »
n'entrent pas dans ce compte ; cf.
`lean-ci-sorry-filter`).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `search_lean` | v4.32.1 | 0 | 5 | 0¹ | PEDA/REF | #4048, #4038, #3801 |
| `discrepancy_lean` | v4.32.1 | 0 | 3 | 0² | PEDA/REF | #12823 |
| **Total** | — | **0** | **8** | — | — | — |

¹ Aucun notebook Lean dédié. Companion conceptuel = la série **Search** (CSP/Foundations,
A* vs BFS sur terrain pondéré — convention sibling-lake). Répond aussi au prong-B de l'Epic
[#3801](https://github.com/jsboige/CoursIA/issues/3801) : démontrer le moteur A* sur un
problème non-trivial (heuristique discriminante), pas un graphe à coût uniforme où A*
dégénère en BFS.

² Notebook compagnon prévu : `Search-15-CombinatorialDiscrepancy` (livrable A de
[#12823](https://github.com/jsboige/CoursIA/issues/12823)) — Beck–Fiala 2k−1 implémenté +
CP-SAT en oracle exact. Pas encore câblé.

---

## Par lake

### search_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : correction de l'algorithme A* sous une heuristique **admissible** puis
**consistante**. Lake de la série Search (roadmap #4038 Tier 1, #4048), déployé en 3 phases
(phase-1 modélisation, phase-2 admissibilité, phase-3 consistance).

- **Toolchain** : v4.31.0-rc1 · **Dépendance** : Mathlib4
- **lib** : `Astar` (`globs := #[.submodules \`Astar]`)
- **Modules** : `Astar/Graph.lean`, `Astar/Heuristic.lean`, `Astar/Optimality.lean`,
  `Astar/Consistency.lean` + umbrella `Astar.lean`
- **sorry (production)** : **0**. `lake build Astar` SUCCESS (8497 jobs, 0 error 0 warning).

#### Théorèmes prouvés (0 sorry)

- **`admissible_implies_optimal`** (flagship, phase-2) : A* sous heuristique admissible
  renvoie un chemin de coût optimal.
- **`consistent_implies_path_bound`** / **`consistent_implies_admissible_bound`** (phase-2) :
  consistance ⟹ admissibilité par téléscopage.
- **`consistent_implies_f_monotone`** (phase-3) : consistance ⟹ la fonction d'évaluation
  `f = g + h` est non-décroissante (pas de re-expansion de nœuds).
- `admissible_implies_optimal_start` (cas de base), `admissible_head_bound` (borne sur le
  nœud de tête), lemmes de support sur `head?`/`getLast?`.

#### Honnêteté du périmètre (G.3/G.9)

La **correction sous admissibilité et consistance** est prouvée 0 sorry. Ce qui reste
**OPEN (non sorry-backed)**, documenté honnêtement :

- **Atteignabilité effective de `h*`** (coût réel optimal) sur graphe fini — la
  modélisation suppose l'existence du coût optimal, ne le calcule pas (problème
  computationnel, pas un théorème laissé en `sorry`).
- **Phase-4 : modélisation de la priority-queue** (le « no-re-expansion » lui-même comme
  invariant opérationnel) — différée.

Axiomes `[propext, Classical.choice, Quot.sound]` (Mathlib standard, **pas de `sorryAx`**).

### discrepancy_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : formalisation de la **discrépance combinatoire** (issue #12823,
distillation Bansal–Jiang 2025, arXiv:2508.03961) : colorations `±1` de
systèmes d'ensembles de degré `≤ k`, bornes de la pire somme colorée.
Première formalisation du sujet (dépôt + Mathlib : 0 hit, vérifié 2026-08-24).
Désambiguïsation : sans rapport avec la Limited Discrepancy Search de Search-13.

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4 (`520045ab`)
- **lib** : `Discrepancy` (`globs := #[.submodules \`Discrepancy, \`Discrepancy]`)
- **Modules** : `Discrepancy/Basic.lean`, `Discrepancy/Komlos.lean` + umbrella
  `Discrepancy.lean`
- **sorry (production)** : **0** (conjectures = `def ... : Prop` nommées,
  jamais de théorème tronqué).

#### Prouvé (P0) vs ouvert

- **Prouvé** (P0) : 3 lemmes-limites — `discrepancy_empty`,
  `discrepancy_singleton_empty`, `degree_le_card`.
- **Énoncés posés, preuves à venir** (registre
  [`FORMAL_STATUS.md`](discrepancy_lean/FORMAL_STATUS.md)) : cible
  `BeckFialaClassic` (`disc ≤ 2k − 1`, boutes `b1..b4`), `BeckFialaConjecture`
  (`O(√k)`, ouverte), `KomlosConjecture` (`O(1)`, ouverte),
  `BansalJiangLargeDegree` + `KomlosBansalJiangWeak` (P3 non engagé : SDP et
  concentration matricielle absents de Mathlib). P2 = borne inférieure
  Erdős–Spencer en réutilisant le kernel `PacLearning/Hoeffding.lean`.

## Notes transverses

- **WDAC workaround** (RECOVERABLE-LOCAL) : `lake exe cache get` bloqué → réutilise les
  oleans `.lake/packages/` d'un lake frère binairement compatible. Cf.
  `lean-wdac-olean-wholesale-copy`.
- **Mathlib v4.31.0-rc1 tactic learnings** (documentés durably) : `subst` sur l'égalité de
  tête d'induction élimine l'AUTRE variable → utiliser `hd` dans le corps ; lemmes de
  `head?`/`getLast?` non nommés → `simp`/`simp_all` plutôt que lemme nommé ; warnings
  `simp only [..]` unused-arg → préférer `linarith`/`rw` ; le glob `.submodules Astar` build
  les sous-modules, PAS l'umbrella `.olean`.
- CI : `.github/workflows/lean-astar.yml` (`sorry-filter-mode: standalone-tactic`,
  baseline `"0"`).
- **EPIC #3801 prong-B** : le lake pose un graphe pondéré où l'heuristique discrimine, en
  réponse au grief BFS-vs-A* sur terrain à coût uniforme (commit `8905f8845`).
