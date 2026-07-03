# Inventaire des projets Lean 4 — `SymbolicAI/Lean`

Inventaire transverse de tous les projets de formalisation Lean 4 sous `SymbolicAI/Lean/`,
sur le modèle de [`GameTheory/LEAN_INVENTORY.md`](../../GameTheory/LEAN_INVENTORY.md).
Source de vérité : corps de l'Epic
[#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification `firsthand` (issue
[#4041](https://github.com/jsboige/CoursIA/issues/4041)). Colonne *sorry (production)* =
métrique CI `standalone-tactic` (les mentions prose « 0 sorry »/« sans sorry » et les
définitions `:= sorry` non-tactique n'entrent pas dans ce compte ; cf.
`lean-ci-sorry-filter`).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `grothendieck_lean` | v4.30.0-rc2 | 0 | 23 | 4 | REF | #2159, #1646 |
| `conway_lean` | v4.30.0-rc2 | 4¹ | 23 | 24 | PEDA | #1453, #1651, #2162 |
| `knot_lean` | v4.31.0-rc1 | 3² | 6 | 2 | PEDA/REF | #2874, #3003 |
| `finiteness_lean` | v4.30.0-rc2 | 0 | 1 | 2 | REF | #3111 |
| `sensitivity_lean` | v4.30.0-rc2 | 0 | 4 | 2 | PEDA/REF | famille calibration |
| `calibration_lean` | v4.30.0-rc2 | 0³ | 3 | 0 | HARNESS | #1764 |
| `mathlib_examples` | v4.30.0-rc2 | 0 | 1 | 0 | REF | référence |
| **Total** | — | **7** | **61** | — | — | — |

¹ Les 4 `sorry` de `conway_lean` sont des **cibles de prover intentionnelles** dans
`Conway/Life/HashlifeCorrectness.lean` (Hashlife) — chaque `sorry` est un sous-but
auto-contenu destiné au harnais de preuve (`agent_tests/prover/`), pas une régression de
contenu pédagogique. Le reste de la série Conway (Doomsday, FRACTRAN, Look-and-Say, Nim,
Angel) est prouvé 0 sorry. Vérifié 2026-07-01 (comment-stripped grep, après #4780 :
P4 décomposé en 3 sous-lemmes sorry-free à énoncé réel `p4_double_nine_shape`,
`p4_wave1_ih`, `p4_wave2_ih`, restent 4 cibles tactic `p4_half_steps_compose`/`p4_succ_membership`/`p5_large_n_jump`/`p5_inductive_step`).
² `knot_lean` = **research-HOLD** : théorie des nœuds (#2874). Les `sorry` sont des
définitions non définies (`AreMutants`, `alexanderPolynomial`, `IsSmoothlySlice`,
`IsTopologicallySlice := sorry`) et des preuves de transfert classique ouvertes. Le pont
GF(3) Path B (`triColorFoxCondition_iff_sum_mod_three`) est prouvé (#3003, sorry net-zéro
vs `main`). Niveau recherche, pas un gap pédagogique.
³ `calibration_lean` est un **composant de harnais** (prover calibration, déplacé depuis
GameTheory, #1764). Les `· sorry` inline de `Calibration/Nash.lean` sont un **fixture de
test intentionnel** (le harnais doit gérer un *sorry-increase* 1→2 sans régression) — pas
du code de production, donc *sorry (production) = 0*.

---

## Par lake

### 1. grothendieck_lean — REFERENCE (recherche)

**Objectif** : formalisation étendue de résultats à la Grothendieck (topos, sites,
faisceaux, topologie dense, foncteur constant, lemme d'Yoneda, conservativité).

- **Toolchain** : v4.30.0-rc2 · **Dépendance** : Mathlib4
- **Modules** : `Grothendieck/` (23 fichiers) + umbrella `Grothendieck.lean`
- **sorry (production)** : **0** — entièrement prouvé à la création (« All `sorry`s
  eliminated at creation »). Build SUCCESS.
- **Notebook câblé** : 4 notebooks (série SymbolicAI/Lean).
- **Suivi** : Epic #1646, #2159 (Phase 6-8).

### 2. conway_lean — PEDAGOGIQUE (hommage Conway)

**Objectif** : hommage à John H. Conway — Doomsday, FRACTRAN, Look-and-Say, Nim, Angel,
Game of Life / Hashlife.

- **Toolchain** : v4.30.0-rc2 · **Dépendance** : Mathlib4
- **Modules** : `Conway/` (23 fichiers) + umbrella + `patterns/` + `scripts/`
- **sorry (production)** : **4** (cibles de prover Hashlife, voir note ¹). Sujets non-Hashlife
  prouvés (Doomsday, FRACTRAN, etc. via `native_decide`).
- **Notebook câblé** : 24 notebooks (série Conway la plus câblée).
- **Suivi** : Epic #1453, #1651 ; Conway P5 (#2162) = research-HOLD.

### 3. knot_lean — PEDAGOGIQUE / REFERENCE (research-HOLD)

**Objectif** : théorie des nœuds — tricolorabilité, polynôme d'Alexander, mutants, slicing,
théorème de Conway.

- **Toolchain** : v4.31.0-rc1 (diffère de la cohorte SymbolicAI — cohorte knot/kelly/planning)
  · **Dépendance** : Mathlib4
- **Modules** : `Knots/` (6 fichiers) + umbrella `Knots.lean`
- **sorry (production)** : **3** + définitions `:= sorry` (research-HOLD, voir note ²).
- **Notebook câblé** : 2 notebooks.
- **Suivi** : #2874 (mandate-C trio MERGED #3997/#3999/#4003), #3003 (Path B GF(3) SHIPPED).

### 4. finiteness_lean — REFERENCE

**Objectif** : formalisation compacte d'un résultat de finitude.

- **Toolchain** : v4.30.0-rc2 · **Dépendance** : Mathlib4
- **Modules** : `Finiteness/` (1 fichier) + umbrella `Finiteness.lean`
- **sorry (production)** : **0**. Build SUCCESS.
- **Notebook câblé** : 2 notebooks.
- **Suivi** : #3111 (MERGED).

### 5. sensitivity_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : analyse de sensibilité / calibration (proche de la famille calibration).

- **Toolchain** : v4.30.0-rc2 · **Dépendance** : Mathlib4
- **Modules** : `Sensitivity/` (4 fichiers) + umbrella + `NOTICE.md`
- **sorry (production)** : **0**. Build SUCCESS.
- **Notebook câblé** : 2 notebooks.
- **Suivi** : famille calibration.

### 6. calibration_lean — HARNESS (prover calibration)

**Objectif** : composant du harnais de calibration du prouveur (cibles de test pour le
prover, déplacé depuis GameTheory).

- **Toolchain** : v4.30.0-rc2 · **Dépendance** : Mathlib4
- **Modules** : `Calibration/` (3 fichiers) + umbrella `Calibration.lean`
- **sorry (production)** : **0** (les `· sorry` inline sont un fixture de test intentionnel,
  voir note ³).
- **Notebook câblé** : 0 (composant harnais, pas pédagogique).
- **Suivi** : #1764.

### 7. mathlib_examples — REFERENCE

**Objectif** : exemples de référence illustrant l'usage de Mathlib.

- **Toolchain** : v4.30.0-rc2 · **Dépendance** : Mathlib4
- **Modules** : `MathLibExamples/` (1 fichier) + umbrella `MathLibExamples.lean`
- **sorry (production)** : **0**.
- **Notebook câblé** : 0 (référence).
- **Suivi** : référence (pas d'issue dédiée).

---

## Classes (taxonomie Epic #4038)

| Classe | Définition | Lakes |
|--------|-----------|-------|
| **PEDA** | Pédagogique (enseigne un concept,面向 étudiants, notebooks compagnons) | conway_lean, knot_lean, sensitivity_lean |
| **REF** | Formalisation de référence / recherche (pas directement pédagogique) | grothendieck_lean, finiteness_lean, mathlib_examples |
| **HARNESS** | Composant de harnais (prover calibration / test fixture) | calibration_lean |
| **SCAFFOLD** | Échafaudage partiel / en cours | _(aucun — tous sont buildables)_ |

## Notes transverses

- **WDAC workaround** (Windows Defender Application Control bloque `clang.exe` + `lake exe
  cache get`) : tous les lakes se construisent en réutilisant le `.lake` d'un lake frère
  binairement compatible (wholesale `cp -r sibling/.lake` + `lake-manifest.json`), à
  condition d'une révision Mathlib identique. Cohorte v4.30.0-rc2 (calibration, conway,
  finiteness, grothendieck, mathlib_examples, sensitivity, decision_theory) ; cohorte
  v4.31.0-rc1 (knot, kelly, planning, perceptron, astar, erc20, argumentation, minimax,
  sudoku, cooperative).
- **`SymbolicAI/Lean/examples/llm_assisted_proof.lean`** (2 `sorry`) est un *exemple
  pédagogique* (non production) — non compté dans le tableau ci-dessus.
- **`finiteness_lean`** est également référencé depuis l'Epic finitude-derivatives (#2978,
  coordination vérifiée avec `decision_theory_lean` Gittins — pas de chevauchement).
