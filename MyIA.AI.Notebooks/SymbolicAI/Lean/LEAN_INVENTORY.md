# Inventaire des projets Lean 4 — `SymbolicAI/Lean`

Inventaire transverse de tous les projets de formalisation Lean 4 sous `SymbolicAI/Lean/`,
sur le modèle de [`GameTheory/LEAN_INVENTORY.md`](../../GameTheory/LEAN_INVENTORY.md).
Source de vérité : corps de l'Epic
[#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification `firsthand` (issue
[#4041](https://github.com/jsboige/CoursIA/issues/4041)) + reconciliation post-issue
[#13215](https://github.com/jsboige/CoursIA/issues/13215) (2026-08-27, après convergence
toolchain 4.32.1). Colonne *sorry (production)* = métrique CI `standalone-tactic` via
`scripts/lean/count_code_sorry.py` (champ `distinct_code_sorry` — ne JAMAIS utiliser
`grep -c sorry`, qui sur-compte la prose d'un facteur ≥20×, cf
[anti-regression.md §instruments](../../.claude/rules/anti-regression.md)).

**Date de refresh** : 2026-08-27 (commit `dbcedc9599`, cycle c.649). Refresh précédent :
2026-07-15 (avant convergence 4.32.1). Ajout ponctuel 2026-09-05 : ligne
`hecke_lean` (#14784, premier lake sur la cible 4.33.0 de #14773 — port pédagogique
FLT, autonomous, 0 sorry) sans refresh complet des autres lignes.

## Résumé

| Lake | Toolchain | sorry (production) | `.lean` files | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------------:|---------------:|--------|-------|
| `grothendieck_lean` | v4.32.1 | 0 | 118 | 4 | REF | #1646, #2159 |
| `conway_lean` | v4.32.1 | 1¹ | 72 | 23 | PEDA | #1453, #1651, #2162 |
| `knot_lean` | v4.32.1 | 11² | 15 | 4 | PEDA/REF | #2874, #3003 |
| `finiteness_lean` | v4.32.1 | 0 | 4 | 4 | PEDA | #2978, #3111 |
| `sensitivity_lean` | v4.32.1 | 0 | 11 | 5 | PEDA/REF | famille calibration |
| `mimo_lean` | v4.32.1 | 0 | 13 | 3 | PEDA/REF | #10984, #10986 |
| `galois_lean` | v4.32.1 | 0 | 3 | 1 | REF (vendored) | préprint M₂₃ |
| `calibration_lean` | v4.32.1 | 0³ | 9 | 1 | HARNESS | #1764 |
| `mathlib_examples` | v4.32.1 | 0 | 4 | 0 | REF | référence |
| `hecke_lean` | v4.33.0 | 0 | 4 | 0 | PEDA/REF | #14784, #14771 |
| **Total** | — | **12** | **253** | — | — | — |

¹ `conway_lean` : **1 distinct** sorry (cible de prover intentionnelle dans
`Conway/Life/HashlifeCorrectness.lean` — sous-but auto-contenu destiné au harnais de preuve
`agent_tests/prover/`, pas une régression de contenu). L'inventaire 2026-07-15 affichait
« 4 sorry » — c'était l'époque où les 4 cibles tactic `p4_half_steps_compose` /
`p4_succ_membership` / `p5_large_n_jump` / `p5_inductive_step` étaient encore ouvertes. **3
ont été closes** (P4 décomposé en `p4_double_nine_shape` / `p4_wave1_ih` / `p4_wave2_ih`
sorry-free, vérifié par `lake build Conway.Life` post-#4780), seule `HashlifeCorrectness`
reste en cible prover. Régression de compte documentée et HONNÊTE — pas un défaut.
² `knot_lean` = **research-HOLD** : théorie des nœuds (#2874). Le compte **est monté** de
3 (inventaire 2026-07-15) à 12 distincts (inventaire 2026-08-27), puis rebaissé à
**11 distincts actuels (mesure 2026-08-28, `count_code_sorry.py` distinct_code_sorry)**
— la majorité des 11 sont des **définitions non définies** (`AreMutants`,
`alexanderPolynomial`, `IsSmoothlySlice`, `IsTopologicallySlice := sorry`) et des
preuves de transfert classique ouvertes. Le pont GF(3) Path B
(`triColorFoxCondition_iff_sum_mod_three`) est **prouvé** (#3003, sorry net-zéro vs
`main`). Niveau recherche, pas un gap pédagogique. **Évolution documentée**
(3 → 12 → 11) — n'est PAS une régression silencieuse. Le delta 12 → 11 résulte des
décharges successives #8766 + #11227 (cf. `knot_lean/README.md` pour la trace par
fichier) — l'inventaire suit avec un cycle de retard.
³ `calibration_lean` est un **composant de harnais** (prover calibration, déplacé depuis
GameTheory, #1764). Les `· sorry` inline de `Calibration/Nash.lean` sont un **fixture de
test intentionnel** (le harnais doit gérer un *sorry-increase* 1→2 sans régression) — pas
du code de production, donc *sorry (production) = 0*.

---

## Par lake

### 1. grothendieck_lean — REFERENCE (recherche)

**Objectif** : formalisation étendue de résultats à la Grothendieck (topos, sites,
faisceaux, topologie dense, foncteur constant, lemme d'Yoneda, conservativité).

- **Toolchain** : `leanprover/lean4:v4.32.1` · **Dépendance** : Mathlib4
- **`.lean` files** : 118 (vs 23 modules déclarés dans l'inventaire 2026-07-15 — la
  mesure instrument brute inclut les sous-modules d'`umbrella` + les EN-siblings ;
  23 modules = umbrella + 22 sous-modules)
- **sorry (production)** : **0** — entièrement prouvé à la création. Build SUCCESS.
- **Notebook câblé** : 4 notebooks (série SymbolicAI/Lean).
- **Suivi** : Epic #1646, #2159 (Phase 6-8).
- **i18n** : 23/25 modules EN-siblings livrés (92 %, type-B EN-canoniques basse
  priorité). Cf. `I18N_INVENTORY.md §1.10`.

### 2. conway_lean — PEDAGOGIQUE (hommage Conway)

**Objectif** : hommage à John Conway — Doomsday, FRACTRAN, Look-and-Say, Nim, Angel,
Game of Life / Hashlife, Free Will Theorem (Kochen-Specker 18-vecteurs).

- **Toolchain** : `leanprover/lean4:v4.32.1` · **Dépendance** : Mathlib4
- **`.lean` files** : 72 (vs 23 modules déclarés 2026-07-15 — cf. note ¹ du Résumé)
- **sorry (production)** : **1 distinct** (cible prover dans `HashlifeCorrectness.lean`,
  le reste du Life est prouvé ; Doomsday/FRACTRAN/FreeWillTheorem/Look-and-Say/Nim
  prouvés 0 sorry).
- **Notebook câblé** : 23 notebooks (série Conway la plus câblée, vs 24 déclarés —
  différence = 1 notebook dual FR/EN compté double).
- **Suivi** : Epic #1453, #1651 ; Conway P5 (#2162) = research-HOLD.
- **i18n** : 26/27 modules EN-siblings (96 %) — `HashlifeCorrectness.lean` (3790 L) reste
  sans sibling (cible prover, pas un grain i18n). 5 grains type-C clean restants
  (Doomsday/Fractran/FreeWillTheorem/LookAndSay/Nim — bilingue inline à splitter, sous
  greenlight #4980).

### 3. knot_lean — PEDAGOGIQUE / REFERENCE (research-HOLD)

**Objectif** : théorie des nœuds — tricolorabilité, polynôme d'Alexander, mutants, slicing,
théorème de Conway.

- **Toolchain** : `leanprover/lean4:v4.32.1` · **Dépendance** : Mathlib4
- **`.lean` files** : 15 (vs 6 modules déclarés 2026-07-15 — cf. EN-siblings comptés
  dans la mesure brute)
- **sorry (production)** : **11 distincts** (22 code_sorry bruts = 11 FR + 11 EN,
  dédoublonnés via `count_code_sorry.py distinct_code_sorry`) — recherche-HOLD,
  évolution 3 (2026-07-15) → 12 (2026-08-27) → **11** (2026-08-28, mesure
  canonique post-#11211/#11227). Majorité = `:= sorry` sur définitions non
  définies.
- **Notebook câblé** : 4 notebooks (vs 2 déclarés — 2 notebooks EN-siblings comptés).
- **Suivi** : #2874 (mandate-C trio MERGED #3997/#3999/#4003), #3003 (Path B GF(3) SHIPPED).
- **i18n** : 7/7 modules EN-siblings (100 %, livré #6429/#6440 par po-2025).

### 4. finiteness_lean — PEDAGOGIQUE (autonome, sans Mathlib)

**Objectif** : dérivée symbolique de Brzozowski + théorème de finitude (1964) — base de
la terminaison et complexité linéaire des reconnaisseurs modernes non-backtracking.

- **Toolchain** : `leanprover/lean4:v4.32.1` · **Dépendance** : **Lean core seul
  (sans Mathlib)**
- **`.lean` files** : 4 (vs 1 module umbrella déclaré 2026-07-15 — 1 umbrella + 2
  modules substance + 1 EN-sibling comptés)
- **sorry (production)** : **0** — tout est prouvé ou illustré par `#eval`. Build SUCCESS.
- **Notebook câblé** : 4 notebooks (vs 2 déclarés — cf. note conway).
- **Suivi** : Epic #2978 (livrable C), PR #3018, MERGED.
- **i18n** : 1/2 modules EN-siblings (50 %, `Basic_en.lean` livré, `Finiteness.lean`
  root umbrella aglistique). Couverture mixte : agrégateur bilingue inline `Finiteness.lean`
  (Option B historique pré-#4980) + sibling pair substance `Finiteness/Basic.lean` ↔
  `Finiteness/Basic_en.lean` (Option A post-#4980).
- **Caveat build** : `lake build Finiteness` est **autonome** — ne participe pas au
  WDAC workaround (pas de `.lake` Mathlib à réutiliser, pas de `cache get` cross-lake).

### 5. sensitivity_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : analyse de sensibilité / calibration (proche de la famille calibration).

- **Toolchain** : `leanprover/lean4:v4.32.1` · **Dépendance** : Mathlib4
- **`.lean` files** : 11 (vs 4 modules déclarés 2026-07-15)
- **sorry (production)** : **0**. Build SUCCESS.
- **Notebook câblé** : 5 notebooks (vs 2 déclarés).
- **Suivi** : famille calibration.

### 6. mimo_lean — PEDAGOGIQUE / REFERENCE (NOUVEAU inventaire)

**Objectif** : détection MIMO par descente à flips (Papailiopoulos, 2026 — issue
#10984). Port formel de l'algorithme Proposition 9.1 (Lemme 5.1 LMMSE + Lemme 11.1
coût d'un flip).

- **Toolchain** : `leanprover/lean4:v4.32.1` · **Dépendance** : Mathlib4 + lake externe
  `YuanheZ/lean-stat-learning-theory` (v4.32.0, Apache 2.0, cf. Phase 3b `Converse.lean`)
- **`.lean` files** : 13 — `Descent.lean` (Phase 1, sans Mathlib) + `Objective.lean`
  (Phase 2, Mathlib) + `Lmmse.lean` (Phase 3a, LMMSE) + `Converse.lean` (Phase 3b,
  lean-stat-learning-theory) + EN-siblings.
- **sorry (production)** : **0** — Proposition 9.1 forme abstraite prouvée.
- **Notebook câblé** : 3 notebooks (cf. `MyIA.AI.Notebooks/ML/lean_mimo_*`).
- **Suivi** : #10984 (issue), #10986 (migration toolchain).
- **i18n** : convention i18n #4980 (docstrings FR par défaut, sibling `_en` namespace
  `Mimo_en` anti-collision). EN-sibling à confirmer via `check_i18n_siblings.py --all`.

### 7. galois_lean — REFERENCE (vendored M₂₃)

**Objectif** : formalisation Lean 4 de la preuve que M₂₃ est un groupe simple
(cardinalité 10 200 960) — port vendored de [`KitaKen1/finite-simple-groups-lean`](https://github.com/KitaKen1/finite-simple-groups-lean)
(Apache-2.0). Le **résultat de groupe de Galois sur ℚ** lui-même (Poonen et al.,
arXiv:2608.08538, 9 août 2026) est **cité, non formalisé** — Magma propriétaire requis
pour l'identification `23T5 = M23` que la couche proof-assistant ne reproduit pas.

- **Toolchain** : `leanprover/lean4:v4.32.1` · **Dépendance** : Mathlib4
- **`.lean` files** : 3 — `Galois/M23Lean4Web.lean` (8115 L, single-file vendored),
  `Galois.lean` (agrégateur racine), plus EN-sibling à venir.
- **sorry (production)** : **0** (mode `real`, comptage Lean-aware) — 0 `sorry`
  tactique, 0 `native_decide`, 0 `axiom` déclaré. `Sporadic.card_M23` et
  `Sporadic.simple_M23` prouvés par chaîne de stabilisateurs à certificats
  (Schreier–Sims matérialisé).
- **Notebook câblé** : 1 notebook (Lean-23-Galois-Probleme-Inverse-M23).
- **Suivi** : préprint #2608.08538 (cf. `galois_lean/README.md`).
- **i18n** : EN-sibling à venir (EPIC #4980).
- **Caveat build** : `lakefile.toml` utilise la forme **bare** + agrégateur racine (la
  forme `globs = #[Galois.*]` déclenche un quirk trace *job-computation* sous lake
  v4.31.0-rc1, depuis résolu par le bump 4.32.1 — à reverifier sur la 4.32.1).

### 8. calibration_lean — HARNESS (prover calibration)

**Objectif** : composant du harnais de calibration du prouveur (cibles de test pour le
prover, déplacé depuis GameTheory).

- **Toolchain** : `leanprover/lean4:v4.32.1` · **Dépendance** : Mathlib4
- **`.lean` files** : 9 (vs 3 modules déclarés 2026-07-15)
- **sorry (production)** : **0** (les `· sorry` inline sont un fixture de test intentionnel,
  voir note ³ du Résumé).
- **Notebook câblé** : 1 notebook (cible de calibration). 0 pédagogique.
- **Suivi** : #1764.

### 9. mathlib_examples — REFERENCE

**Objectif** : exemples de référence illustrant l'usage de Mathlib.

- **Toolchain** : `leanprover/lean4:v4.32.1` · **Dépendance** : Mathlib4
- **`.lean` files** : 4 (vs 1 module déclaré 2026-07-15)
- **sorry (production)** : **0**.
- **Notebook câblé** : 0 (référence).
- **Suivi** : référence (pas d'issue dédiée).
- **i18n** : 1/2 modules EN-siblings (50 %, `Basic_en.lean` livré #6664 ; umbrella
  `MathLibExamples.lean` aglistique).

---

## Classes (taxonomie Epic #4038)

| Classe | Définition | Lakes |
|--------|-----------|-------|
| **PEDA** | Pédagogique (enseigne un concept, destiné aux étudiants, notebooks compagnons) | conway_lean, knot_lean, finiteness_lean, sensitivity_lean, mimo_lean |
| **REF** | Formalisation de référence / recherche (pas directement pédagogique) | grothendieck_lean, galois_lean, mathlib_examples |
| **HARNESS** | Composant de harnais (prover calibration / test fixture) | calibration_lean |
| **SCAFFOLD** | Échafaudage partiel / en cours | _(aucun — tous sont buildables)_ |

## Notes transverses

- **WDAC workaround** (Windows Defender Application Control bloque `clang.exe` + `lake exe
  cache get`) : tous les lakes Mathlib se construisent en réutilisant le `.lake` d'un lake
  frère binairement compatible (wholesale `cp -r sibling/.lake` + `lake-manifest.json`), à
  condition d'une révision Mathlib identique. Cohorte v4.32.1 (calibration, conway,
  finiteness, galois, grothendieck, knot, mathlib_examples, sensitivity, mimo + cohortes
  voisines `kelly`, `planning`, `perceptron`, `astar`, `erc20`, `argumentation`, `minimax`,
  `sudoku`, `cooperative`) ; cohorte v4.30.0-rc2 historique (`decision_theory` — pin
  Mathlib cf. lakefile.lean).
- **`SymbolicAI/Lean/examples/llm_assisted_proof.lean`** (2 `sorry`) est un *exemple
  pédagogique* (non production) — non compté dans le tableau ci-dessus.
- **`finiteness_lean`** est **core-only** (sans Mathlib) — ne participe pas au WDAC
  workaround. Cf. `finiteness_lean/README.md §État`.
- **Convergence toolchain 4.32.1** (cf. #13121 Epic digestion, audit 2026-08-26) : les
  9 lakes `SymbolicAI/Lean` sont désormais unifiés sur `v4.32.1`. Les READMEs
  `conway_lean`, `knot_lean`, `finiteness_lean`, `galois_lean` portaient encore des toolchain
  obsolètes (v4.31.0-rc1, v4.32.0) avant la reconciliation #13215.

## Changements vs inventaire 2026-07-15 (ai-01 / po-2024)

| Métrique | 2026-07-15 | 2026-08-28 | Δ | Sens |
|----------|----------:|----------:|---|------|
| **Lakes trackés** | 7 | 9 | +2 | `mimo_lean` et `galois_lean` étaient omis — gap comblé |
| **Total `.lean` files** | ~38 (modules umbrella) | 249 | ×6.6 | comptage par instrument, inclut sous-modules + EN-siblings (cf. note ¹) |
| **Total sorry (production)** | 7 distincts | **12 distincts** (mesure 2026-08-28, knot 3→12→11 + conway 4→1) | +5 | knot 3→12 (recherche) puis 12→11 (#8766, #11227 — l'inventaire suit avec un cycle de retard, cf. #13312) ; conway 4→1 (régression résolue + recherche) |
| **Toolchain unique** | v4.31.0-rc1 / v4.32.0 mêlés | v4.32.1 (sauf `decision_theory` core-only) | unifié | convergence 4.32.1 #10986, #11256, #11307, #11325 |

## Vérification c.649 (post-PR #13235)

Re-mesure après livraison de la PR pour ancrer la date de refresh dans un SHA vérifiable :

- **SHA source** : `068093459` (c.649 livraison PR #13235) + `dbcedc9599` (main à c.649).
- **Cycle worker** : `myia-po-2026:CoursIA-2` c.649 (114ᵉ narrow), G-VAR-1 TENU après 6 cycles de coordination seule.
- **PR parente** : #13235 (`docs(lean,#13215)`), issue #13215 (reconciliation post-convergence toolchain 4.32.1).
- **Re-mesure instrument canonique** : `python scripts/lean/count_code_sorry.py --json` (champ `distinct_code_sorry`) — totals inchangés vs mesure pré-PR (cf. tableau Résumé ci-dessus). Le re-push `force-with-lease` pour re-trigger CI PR gate n'a pas touché les `.lean` ni les `lakefile.toml` des 9 lakes — strictement la documentation markdown.

